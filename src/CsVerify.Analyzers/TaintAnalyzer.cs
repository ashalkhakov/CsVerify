using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Diagnostics;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Analyzers
{
    /// <summary>
    /// Sensitive values never reach a log. A taint analysis of explicit flows: the sources are [Sensitive] fields,
    /// properties, parameters, results and types, and what Sealed.Unseal gives; what's computed from a source is
    /// sensitive, up to a [Declassify] method; a sink is a [LogSink] method, a logger's, the console's, Debug's or
    /// Trace's. A sink given a sensitive value, or an object whose text shows a [Sensitive] member, is CSV0030, and so
    /// is an exception made with one (exceptions are logged). Sealed values: Sealed.Unseal only in an [Unseals]
    /// method's own body (CSV0031), which must have a precondition, the access check (CSV0032).
    /// Branching on a sensitive value (an implicit flow) is not followed; sealing is what rules it out.
    /// </summary>
    [DiagnosticAnalyzer(LanguageNames.CSharp)]
    public sealed class TaintAnalyzer : DiagnosticAnalyzer
    {
        public override ImmutableArray<DiagnosticDescriptor> SupportedDiagnostics =>
            ImmutableArray.Create(Descriptors.SensitiveLogged, Descriptors.UnsealOutsideUnseals, Descriptors.UnsealsWithoutCheck);

        public override void Initialize(AnalysisContext context)
        {
            context.ConfigureGeneratedCodeAnalysis(GeneratedCodeAnalysisFlags.None);
            context.EnableConcurrentExecution();
            context.RegisterOperationAction(CheckUnseal, OperationKind.Invocation);
            context.RegisterOperationBlockAction(CheckUnsealsMethod);
            context.RegisterCompilationAction(c => new Flow(c.Compilation).Run(c.ReportDiagnostic));
        }

        internal static bool IsUnseal(IMethodSymbol m) => m != null && m.Name == "Unseal" && SpecSymbols.IsCsVerifyType(m.ContainingType, "Sealed");

        private static bool IsUnsealsMethod(ISymbol s) =>
            SpecSymbols.HasAttribute(s, "UnsealsAttribute") || s is IMethodSymbol m && m.AssociatedSymbol != null && SpecSymbols.HasAttribute(m.AssociatedSymbol, "UnsealsAttribute");

        private static void CheckUnseal(OperationAnalysisContext context)
        {
            var op = (IInvocationOperation)context.Operation;
            if (!IsUnseal(op.TargetMethod) || context.ContainingSymbol?.ContainingNamespace?.ToDisplayString() == SpecSymbols.Namespace)
            {
                return;
            }
            // (in the method's own body: a lambda or a local function may run later, where its check no longer holds)
            bool nested = Ancestors(op).Any(a => a is IAnonymousFunctionOperation || a is ILocalFunctionOperation);
            if (nested || !IsUnsealsMethod(context.ContainingSymbol))
            {
                context.ReportDiagnostic(Diagnostic.Create(Descriptors.UnsealOutsideUnseals, op.Syntax.GetLocation()));
            }
        }

        private static void CheckUnsealsMethod(OperationBlockAnalysisContext context)
        {
            if (!(context.OwningSymbol is IMethodSymbol m) || !IsUnsealsMethod(m))
            {
                return;
            }
            bool checks = context.OperationBlocks.SelectMany(b => b.DescendantsAndSelf()).OfType<IInvocationOperation>()
                .Any(i => SpecSymbols.IsSpecClass(i.TargetMethod.ContainingType) && i.TargetMethod.Name == "Requires");
            if (!checks)
            {
                var named = m.AssociatedSymbol ?? m;
                context.ReportDiagnostic(Diagnostic.Create(Descriptors.UnsealsWithoutCheck, named.Locations.FirstOrDefault(), named.Name));
            }
        }

        private static IEnumerable<IOperation> Ancestors(IOperation op)
        {
            for (var p = op.Parent; p != null; p = p.Parent)
            {
                yield return p;
            }
        }

        /// <summary>The whole program's flows: facts about methods, parameters and fields, to a fixed point; then the sinks.</summary>
        private sealed class Flow
        {
            private readonly Compilation _compilation;
            /// <summary>Parameters some caller passes a sensitive value, and why.</summary>
            private readonly Dictionary<IParameterSymbol, string> _params = new Dictionary<IParameterSymbol, string>(SymbolEqualityComparer.Default);
            /// <summary>Fields and properties a sensitive value is stored in, and why.</summary>
            private readonly Dictionary<ISymbol, string> _members = new Dictionary<ISymbol, string>(SymbolEqualityComparer.Default);
            /// <summary>Methods that return a sensitive value given none, and why.</summary>
            private readonly Dictionary<IMethodSymbol, string> _returns = new Dictionary<IMethodSymbol, string>(SymbolEqualityComparer.Default);
            /// <summary>Parameters of a type that hides its members (object, an interface, a T) some caller passes an object a serializer would write a [Sensitive] member of, and why.</summary>
            private readonly Dictionary<IParameterSymbol, string> _shapes = new Dictionary<IParameterSymbol, string>(SymbolEqualityComparer.Default);
            /// <summary>The parameters (by ordinal) whose values a method of the program may return.</summary>
            private readonly Dictionary<IMethodSymbol, HashSet<int>> _passes = new Dictionary<IMethodSymbol, HashSet<int>>(SymbolEqualityComparer.Default);
            /// <summary>The methods whose bodies the analysis sees.</summary>
            private readonly HashSet<IMethodSymbol> _seen = new HashSet<IMethodSymbol>(SymbolEqualityComparer.Default);
            private bool _changed;

            public Flow(Compilation compilation)
            {
                _compilation = compilation;
            }

            public void Run(System.Action<Diagnostic> report)
            {
                var bodies = Bodies().ToList();
                foreach (var (_, owner) in bodies)
                {
                    if (owner is IMethodSymbol m)
                    {
                        _seen.Add(m.OriginalDefinition);
                    }
                }
                for (int round = 0; round < 50; round++)
                {
                    _changed = false;
                    foreach (var (body, owner) in bodies)
                    {
                        new Method(this, body, owner, callers: false, report: null).Run();
                        new Method(this, body, owner, callers: true, report: null).Run();
                        // (which parameters it may return: each on its own)
                        for (int i = 0; owner is IMethodSymbol om && i < om.Parameters.Length; i++)
                        {
                            new Method(this, body, owner, callers: false, report: null, probe: i).Run();
                        }
                    }
                    if (!_changed)
                    {
                        break;
                    }
                }
                foreach (var (body, owner) in bodies)
                {
                    new Method(this, body, owner, callers: true, report: report).Run();
                }
            }

            /// <summary>Each member's code (methods, accessors, constructors, initializers), with its symbol; not CsVerify's own.</summary>
            private IEnumerable<(IOperation body, ISymbol owner)> Bodies()
            {
                foreach (var tree in _compilation.SyntaxTrees)
                {
                    var model = _compilation.GetSemanticModel(tree);
                    foreach (var node in tree.GetRoot().DescendantNodes())
                    {
                        if (!(node is BaseMethodDeclarationSyntax || node is AccessorDeclarationSyntax || node is ArrowExpressionClauseSyntax a && a.Parent is BasePropertyDeclarationSyntax ||
                              node is EqualsValueClauseSyntax e && (e.Parent is VariableDeclaratorSyntax { Parent.Parent: FieldDeclarationSyntax } || e.Parent is PropertyDeclarationSyntax)))
                        {
                            continue;
                        }
                        var owner = node is ArrowExpressionClauseSyntax arrow ? (model.GetDeclaredSymbol(arrow.Parent) as IPropertySymbol)?.GetMethod
                            : node is EqualsValueClauseSyntax init ? model.GetDeclaredSymbol(init.Parent)
                            : model.GetDeclaredSymbol(node);
                        if (owner == null || owner.ContainingNamespace?.ToDisplayString() == SpecSymbols.Namespace)
                        {
                            continue;
                        }
                        if (model.GetOperation(node) is IOperation body)
                        {
                            yield return (body, owner);
                        }
                    }
                }
            }

            internal string Param(IParameterSymbol p)
            {
                if (SpecSymbols.HasAttribute(p, "SensitiveAttribute"))
                {
                    return $"[Sensitive] parameter '{p.Name}'";
                }
                return null;
            }

            /// <summary>Why a caller's argument makes this parameter sensitive: given at this parameter, or at the member it overrides or implements.</summary>
            internal string CallerParam(IParameterSymbol p)
            {
                foreach (var q in Corresponding(p))
                {
                    if (_params.TryGetValue(q, out var why))
                    {
                        return why;
                    }
                }
                return null;
            }

            private IEnumerable<IParameterSymbol> Corresponding(IParameterSymbol p)
            {
                yield return p.OriginalDefinition;
                if (!(p.ContainingSymbol is IMethodSymbol m))
                {
                    yield break;
                }
                for (var o = m.OverriddenMethod; o != null; o = o.OverriddenMethod)
                {
                    if (p.Ordinal < o.Parameters.Length)
                    {
                        yield return o.Parameters[p.Ordinal].OriginalDefinition;
                    }
                }
                foreach (var i in m.ContainingType?.AllInterfaces.SelectMany(t => t.GetMembers(m.Name).OfType<IMethodSymbol>()) ?? Enumerable.Empty<IMethodSymbol>())
                {
                    if (SymbolEqualityComparer.Default.Equals(m.ContainingType.FindImplementationForInterfaceMember(i), m) && p.Ordinal < i.Parameters.Length)
                    {
                        yield return i.Parameters[p.Ordinal].OriginalDefinition;
                    }
                }
            }

            internal void GivenTo(IParameterSymbol p, string why)
            {
                if (p != null && !_params.ContainsKey(p.OriginalDefinition))
                {
                    _params[p.OriginalDefinition] = why;
                    _changed = true;
                }
            }

            internal void ShapeGiven(IParameterSymbol p, string why)
            {
                if (p != null && !_shapes.ContainsKey(p.OriginalDefinition))
                {
                    _shapes[p.OriginalDefinition] = why;
                    _changed = true;
                }
            }

            internal string CallerShape(IParameterSymbol p) => Corresponding(p).Select(q => _shapes.TryGetValue(q, out var why) ? why : null).FirstOrDefault(w => w != null);

            /// <summary>A type whose static members don't say what its values hold: object, an interface, a type parameter.</summary>
            internal static bool Hides(ITypeSymbol t) =>
                t != null && (t.SpecialType == SpecialType.System_Object || t.TypeKind == TypeKind.Interface || t.TypeKind == TypeKind.TypeParameter);

            /// <summary>A type of the program's, whose code the analysis sees.</summary>
            internal static bool InSource(ITypeSymbol t) =>
                t != null && t.DeclaringSyntaxReferences.Length > 0 && t.ContainingNamespace?.ToDisplayString() != SpecSymbols.Namespace;

            /// <summary>
            /// An HTTP exchange (HttpClient's Send, Get, Post, Put, Patch, Delete, and the JSON extensions'): what it gives
            /// is the server's answer, not the request it was given, whatever the request held.
            /// </summary>
            internal static bool IsHttpExchange(IMethodSymbol m)
            {
                var type = (m.ReducedFrom ?? m).ContainingType?.ToDisplayString() ?? "";
                return (type is "System.Net.Http.HttpClient" or "System.Net.Http.HttpMessageInvoker" or "System.Net.Http.Json.HttpClientJsonExtensions") &&
                       (m.Name.StartsWith("Send") || m.Name.StartsWith("Get") || m.Name.StartsWith("Post") || m.Name.StartsWith("Put") ||
                        m.Name.StartsWith("Patch") || m.Name.StartsWith("Delete"));
            }

            /// <summary>A JSON serializer: its result (text, bytes, a document, an HTTP body) is made of the members of what it is given.</summary>
            internal static bool IsSerializer(IMethodSymbol m)
            {
                var type = m.ContainingType?.ToDisplayString() ?? "";
                return type == "Newtonsoft.Json.JsonConvert" && m.Name == "SerializeObject" ||
                       type is "Newtonsoft.Json.Linq.JToken" or "Newtonsoft.Json.Linq.JObject" or "Newtonsoft.Json.Linq.JArray" && m.Name == "FromObject" ||
                       type == "System.Text.Json.JsonSerializer" && m.Name.StartsWith("Serialize") ||
                       type == "System.Net.Http.Json.JsonContent" && m.Name == "Create";
            }

            /// <summary>
            /// Why a serializer's text of a value of this type shows a [Sensitive] member: one of its fields or properties,
            /// public or not (a serializer may be told to write private ones), not [JsonIgnore]d, or one of the members' own.
            /// </summary>
            internal static string Serializes(ITypeSymbol t) => Serializes(t, new HashSet<ITypeSymbol>(SymbolEqualityComparer.Default));

            private static string Serializes(ITypeSymbol t, HashSet<ITypeSymbol> seen)
            {
                if (t is IArrayTypeSymbol at)
                {
                    return Serializes(at.ElementType, seen);
                }
                if (!(t is INamedTypeSymbol n) || n.SpecialType != SpecialType.None || !seen.Add(n))
                {
                    return null;
                }
                foreach (var arg in n.TypeArguments)
                {
                    if (Serializes(arg, seen) is string inner)
                    {
                        return inner;
                    }
                }
                if (n.DeclaringSyntaxReferences.Length == 0)
                {
                    return null;
                }
                for (var c = n; c != null && c.SpecialType == SpecialType.None; c = c.BaseType)
                {
                    foreach (var m in c.GetMembers().Where(x => (x is IFieldSymbol || x is IPropertySymbol) && !x.IsStatic && !(x is IFieldSymbol { AssociatedSymbol: not null }) &&
                                                                !x.GetAttributes().Any(a => a.AttributeClass?.Name == "JsonIgnoreAttribute")))
                    {
                        var type = m is IFieldSymbol f ? f.Type : ((IPropertySymbol)m).Type;
                        if (SpecSymbols.HasAttribute(m, "SensitiveAttribute") || SensitiveType(type) != null)
                        {
                            return $"serialized, it writes {Describe(m)} of '{n.Name}'";
                        }
                        if (Serializes(type, seen) is string inner)
                        {
                            return inner;
                        }
                    }
                }
                return null;
            }

            internal void StoredIn(ISymbol member, string why)
            {
                if (member != null && !_members.ContainsKey(member.OriginalDefinition) && member.Locations.Any(l => l.IsInSource))
                {
                    _members[member.OriginalDefinition] = why;
                    _changed = true;
                }
            }

            internal string Stored(ISymbol member) => _members.TryGetValue(member.OriginalDefinition, out var why) ? why : null;

            internal void Passes(IMethodSymbol m, int ordinal)
            {
                if (!_passes.TryGetValue(m.OriginalDefinition, out var set))
                {
                    _passes[m.OriginalDefinition] = set = new HashSet<int>();
                }
                _changed |= set.Add(ordinal);
            }

            /// <summary>
            /// Does a call of this method give a sensitive value given one at this parameter? For a method of the program's
            /// that isn't dispatched (not virtual, abstract or an override), only if its body may return it; otherwise yes.
            /// </summary>
            internal bool PassesOn(IMethodSymbol m, IParameterSymbol p)
            {
                var d = m.ReducedFrom ?? m;
                if (p == null || !_seen.Contains(d.OriginalDefinition) || d.IsVirtual || d.IsAbstract || d.IsOverride)
                {
                    return true;
                }
                return _passes.TryGetValue(d.OriginalDefinition, out var set) && set.Contains(p.Ordinal);
            }

            internal void Returns(IMethodSymbol m, string why)
            {
                if (m != null && !_returns.ContainsKey(m.OriginalDefinition))
                {
                    _returns[m.OriginalDefinition] = why;
                    _changed = true;
                }
            }

            /// <summary>Why a call of this method gives a sensitive value whatever its arguments: its own result, or an override's.</summary>
            internal string Returned(IMethodSymbol m)
            {
                if (SpecSymbols.HasAttribute(m, "SensitiveAttribute") || m.GetReturnTypeAttributes().Any(a => a.AttributeClass?.Name == "SensitiveAttribute"))
                {
                    return $"returned by [Sensitive] '{m.Name}'";
                }
                if (_returns.TryGetValue(m.OriginalDefinition, out var why))
                {
                    return why;
                }
                // (a virtual call may run an override that returns one)
                foreach (var kv in _returns)
                {
                    for (var o = kv.Key.OverriddenMethod; o != null; o = o.OverriddenMethod)
                    {
                        if (SymbolEqualityComparer.Default.Equals(o.OriginalDefinition, m.OriginalDefinition))
                        {
                            return kv.Value;
                        }
                    }
                    if (m.ContainingType?.TypeKind == TypeKind.Interface && kv.Key.ContainingType != null &&
                        SymbolEqualityComparer.Default.Equals(kv.Key.ContainingType.FindImplementationForInterfaceMember(m)?.OriginalDefinition, kv.Key))
                    {
                        return kv.Value;
                    }
                }
                return null;
            }

            /// <summary>A [Sensitive] type (or one derived from it): all its values are.</summary>
            internal static string SensitiveType(ITypeSymbol t)
            {
                if (t is INamedTypeSymbol { OriginalDefinition.SpecialType: SpecialType.System_Nullable_T } nt)
                {
                    t = nt.TypeArguments[0];
                }
                for (var c = t; c != null; c = c.BaseType)
                {
                    if (SpecSymbols.HasAttribute(c, "SensitiveAttribute"))
                    {
                        return $"of [Sensitive] type '{c.Name}'";
                    }
                }
                return null;
            }

            /// <summary>
            /// Why a value of this type shows a [Sensitive] member when it is written as text: a record's ToString prints
            /// every property; any ToString of the program's that returns one; and for a logger, which may destructure the
            /// object ({@x}), any public one.
            /// </summary>
            internal string TextShows(ITypeSymbol t, bool logger)
            {
                if (t == null || t.SpecialType != SpecialType.None || SpecSymbols.IsCsVerifyType(t, "Sealed`1"))
                {
                    return null;
                }
                var members = new List<ISymbol>();
                for (var c = t; c != null && c.SpecialType == SpecialType.None; c = c.BaseType)
                {
                    members.AddRange(c.GetMembers().Where(m => m is IFieldSymbol || m is IPropertySymbol)
                        .Where(m => SpecSymbols.HasAttribute(m, "SensitiveAttribute") || !(m is IFieldSymbol { AssociatedSymbol: not null }) && SensitiveType(m is IFieldSymbol f ? f.Type : ((IPropertySymbol)m).Type) != null));
                }
                if (members.Count == 0)
                {
                    return null;
                }
                var toString = Enumerable.Repeat(t, 1).Concat(BaseTypes(t)).SelectMany(c => c.GetMembers("ToString").OfType<IMethodSymbol>())
                    .FirstOrDefault(m => m.Parameters.Length == 0 && !m.IsStatic);
                if (t.IsRecord && (toString == null || toString.IsImplicitlyDeclared))
                {
                    return $"its ToString, a record's, prints {Describe(members[0])}";
                }
                if (toString != null && !toString.IsImplicitlyDeclared && Returned(toString) is string why)
                {
                    return $"its ToString returns what's {why}";
                }
                var shown = members.FirstOrDefault(m => m.DeclaredAccessibility == Accessibility.Public);
                return logger && shown != null ? $"a logger may write its public {Describe(shown)} ({{@...}})" : null;
            }

            /// <summary>A member that holds a sensitive value: [Sensitive] itself, or of a [Sensitive] type.</summary>
            private static string Describe(ISymbol m) =>
                SpecSymbols.HasAttribute(m, "SensitiveAttribute") ? $"[Sensitive] '{m.Name}'" : $"'{m.Name}', {SensitiveType(m is IFieldSymbol f ? f.Type : ((IPropertySymbol)m).Type)}";

            private static IEnumerable<ITypeSymbol> BaseTypes(ITypeSymbol t)
            {
                for (var c = t.BaseType; c != null && c.SpecialType != SpecialType.System_Object; c = c.BaseType)
                {
                    yield return c;
                }
            }

            /// <summary>A sink: a [LogSink] method (or one it overrides or implements), a logger's, the console's, Debug's or Trace's; its name; and whether it's a logger's.</summary>
            internal static (string name, bool logger)? Sink(IMethodSymbol m)
            {
                for (var o = m; o != null; o = o.OverriddenMethod)
                {
                    if (SpecSymbols.HasAttribute(o, "LogSinkAttribute"))
                    {
                        return (o.ContainingType.Name + "." + o.Name, false);
                    }
                }
                var type = (m.ReducedFrom ?? m).ContainingType?.ToDisplayString() ?? "";
                if (type == "Microsoft.Extensions.Logging.LoggerExtensions" && m.Name.StartsWith("Log") || type.StartsWith("Microsoft.Extensions.Logging.ILogger") && m.Name == "Log" ||
                    m.ContainingType?.AllInterfaces.Any(i => i.ToDisplayString() == "Microsoft.Extensions.Logging.ILogger") == true && m.Name == "Log")
                {
                    return ("the logger's " + m.Name, true);
                }
                if (type == "System.Console" && m.Name.StartsWith("Write") ||
                    (type == "System.Diagnostics.Debug" || type == "System.Diagnostics.Trace") && (m.Name.StartsWith("Write") || m.Name is "Print" or "Fail" or "Assert" or "TraceError" or "TraceWarning" or "TraceInformation"))
                {
                    return (m.ContainingType.Name + "." + m.Name, false);
                }
                return null;
            }
        }

        /// <summary>
        /// One member's code: its locals' taint, to a fixed point. With callers, its parameters are as its callers give
        /// them (for the sinks it reaches, what it stores and what it passes on); without, only [Sensitive] ones are
        /// (for what it returns given clean arguments).
        /// </summary>
        private sealed class Method
        {
            private readonly Flow _flow;
            private readonly IOperation _body;
            private readonly ISymbol _owner;
            private readonly bool _callers;
            private readonly System.Action<Diagnostic> _report;
            /// <summary>The parameter followed alone, to see if the method may return it; -1 for none.</summary>
            private readonly int _probe;
            private const string Probed = "\u0001the parameter probed";
            private readonly Dictionary<ISymbol, string> _locals = new Dictionary<ISymbol, string>(SymbolEqualityComparer.Default);
            private bool _grew;

            public Method(Flow flow, IOperation body, ISymbol owner, bool callers, System.Action<Diagnostic> report, int probe = -1)
            {
                _probe = probe;
                _flow = flow;
                _body = body;
                _owner = owner;
                _callers = callers;
                _report = report;
            }

            public void Run()
            {
                var ops = _body.DescendantsAndSelf().ToList();
                for (int round = 0; round < 50; round++)
                {
                    _grew = false;
                    foreach (var op in ops)
                    {
                        Step(op, report: false);
                    }
                    if (!_grew)
                    {
                        break;
                    }
                }
                if (_report != null)
                {
                    foreach (var op in ops)
                    {
                        Step(op, report: true);
                    }
                }
            }

            private void Taint(ISymbol s, string why)
            {
                if (s != null && why != null && !_locals.ContainsKey(s))
                {
                    _locals[s] = why;
                    _grew = true;
                }
            }

            /// <summary>Where a sensitive value written to this target goes: a local, a parameter, a field or property (the program's), an element of one.</summary>
            private void Into(IOperation target, string why)
            {
                switch (target)
                {
                    case ILocalReferenceOperation l:
                        Taint(l.Local, why);
                        break;
                    case IParameterReferenceOperation p:
                        Taint(p.Parameter, why);
                        break;
                    case IFieldReferenceOperation f:
                        if (_callers)
                        {
                            _flow.StoredIn(f.Field, Stored(why, f.Field, target.Syntax));
                        }
                        break;
                    case IPropertyReferenceOperation pr when pr.Arguments.Length == 0:
                        if (_callers)
                        {
                            _flow.StoredIn(pr.Property, Stored(why, pr.Property, target.Syntax));
                        }
                        break;
                    case IPropertyReferenceOperation ix:
                        Into(ix.Instance, why);
                        break;
                    case IArrayElementReferenceOperation a:
                        Into(a.ArrayReference, why);
                        break;
                    case IConversionOperation c:
                        Into(c.Operand, why);
                        break;
                    case IDeclarationExpressionOperation d:
                        Into(d.Expression, why);
                        break;
                    case ITupleOperation t:
                        foreach (var e in t.Elements)
                        {
                            Into(e, why);
                        }
                        break;
                }
            }

            private static string Where(SyntaxNode at)
            {
                var span = at.GetLocation().GetLineSpan();
                return $"{System.IO.Path.GetFileName(span.Path)}({span.StartLinePosition.Line + 1},{span.StartLinePosition.Character + 1})";
            }

            /// <summary>Why a member is a source: what was stored in it, and where (the first place).</summary>
            private static string Stored(string why, ISymbol member, SyntaxNode at) =>
                why.Contains(", stored in '") ? why : $"{why}, stored in '{member.Name}' at {Where(at)}";

            private IMethodSymbol Function(IOperation op)
            {
                foreach (var a in Ancestors(op))
                {
                    if (a is IAnonymousFunctionOperation af)
                    {
                        return af.Symbol;
                    }
                    if (a is ILocalFunctionOperation lf)
                    {
                        return lf.Symbol;
                    }
                }
                return _owner as IMethodSymbol;
            }

            private void Step(IOperation op, bool report)
            {
                switch (op)
                {
                    case IVariableDeclaratorOperation d:
                        Taint(d.Symbol, Why(d.Initializer?.Value ?? d.GetVariableInitializer()?.Value));
                        break;
                    case IAssignmentOperation a:
                        if (Why(a.Value) is string aw)
                        {
                            Into(a.Target, aw);
                        }
                        // (x += secret: what x holds after is sensitive too, as is a.Value)
                        break;
                    case IForEachLoopOperation fe when Why(fe.Collection) is string few:
                        foreach (var l in fe.Locals)
                        {
                            Taint(l, few);
                        }
                        Into(fe.LoopControlVariable, few);
                        break;
                    case IFieldInitializerOperation fi when _callers && Why(fi.Value) is string fiw:
                        foreach (var f in fi.InitializedFields)
                        {
                            _flow.StoredIn(f, Stored(fiw, f, fi.Value.Syntax));
                        }
                        break;
                    case IPropertyInitializerOperation pi when _callers && Why(pi.Value) is string piw:
                        foreach (var p in pi.InitializedProperties)
                        {
                            _flow.StoredIn(p, Stored(piw, p, pi.Value.Syntax));
                        }
                        break;
                    case IReturnOperation r when r.ReturnedValue != null && !_callers && Why(r.ReturnedValue) is string rw:
                        if (_probe < 0)
                        {
                            _flow.Returns(Function(op), rw);
                        }
                        else if (rw == Probed && SymbolEqualityComparer.Default.Equals(Function(op), _owner))
                        {
                            _flow.Passes((IMethodSymbol)_owner, _probe);
                        }
                        break;
                    case IInvocationOperation i:
                        Call(i.TargetMethod, i.Instance, i.Arguments, i, report);
                        break;
                    case IObjectCreationOperation o when o.Constructor != null:
                        Call(o.Constructor, null, o.Arguments, o, report);
                        if (report && IsException(o.Type) && o.Arguments.Select(x => Why(x.Value)).FirstOrDefault(w => w != null) is string ew)
                        {
                            Report(o.Syntax, $"'{o.Syntax}'", ew, "an exception's message, which logs print");
                        }
                        break;
                    case IPropertyReferenceOperation pr when pr.Property.SetMethod != null && pr.Parent is IAssignmentOperation pa && pa.Target == pr && Why(pa.Value) is string sw && _callers:
                        // (a setter of the program's: its value parameter)
                        _flow.GivenTo(pr.Property.SetMethod.Parameters.LastOrDefault(), sw);
                        break;
                }
            }

            private static bool IsException(ITypeSymbol t)
            {
                for (var c = t; c != null; c = c.BaseType)
                {
                    if (c.ToDisplayString() == "System.Exception")
                    {
                        return true;
                    }
                }
                return false;
            }

            private void Call(IMethodSymbol m, IOperation instance, ImmutableArray<IArgumentOperation> args, IOperation at, bool report)
            {
                var whys = args.Select(a => (a, why: Why(a.Value))).ToList();
                var given = whys.Select(x => x.why).Concat(new[] { Why(instance) }).FirstOrDefault(w => w != null);
                if (given != null && !IsDeclassify(m))
                {
                    // (a collection given one holds it; so do ref and out arguments; a lambda given alongside it gets it)
                    if (instance != null && m.MethodKind != MethodKind.PropertyGet && !Flow.InSource(m.ContainingType) && !Flow.IsHttpExchange(m))
                    {
                        Into(instance, given);
                    }
                    foreach (var (a, _) in whys)
                    {
                        if (a.Parameter?.RefKind is RefKind.Ref or RefKind.Out)
                        {
                            Into(a.Value, given);
                        }
                        if (Lambda(a.Value) is IAnonymousFunctionOperation lambda)
                        {
                            foreach (var p in lambda.Symbol.Parameters)
                            {
                                Taint(p, given);
                            }
                        }
                    }
                }
                if (_callers)
                {
                    foreach (var (a, why) in whys.Where(x => x.why != null && x.a.Parameter != null))
                    {
                        var passed = why.Contains(", passed to '") ? why : $"{why}, passed to '{a.Parameter.Name}' of '{m.ContainingType?.Name}.{m.Name}' at {Where(a.Syntax)}";
                        _flow.GivenTo(a.Parameter, passed);
                        // (a record's primary constructor stores its parameters in the properties of their names, in code no body shows)
                        if (m.MethodKind == MethodKind.Constructor && m.ContainingType is { IsRecord: true } rt &&
                            rt.GetMembers(a.Parameter.Name).OfType<IPropertySymbol>().FirstOrDefault() is IPropertySymbol positional && positional.DeclaringSyntaxReferences.Any(r => r.GetSyntax() is ParameterSyntax))
                        {
                            _flow.StoredIn(positional, Stored(passed, positional, a.Syntax));
                        }
                    }
                    // (an object, an interface or a T: what a serializer would write of the value given is the caller's to say)
                    foreach (var a in args.Where(x => x.Parameter != null && Flow.Hides(x.Parameter.OriginalDefinition.Type)))
                    {
                        var u = Unconverted(a.Value);
                        if (u is IParameterReferenceOperation passed && _flow.CallerShape(passed.Parameter) is string on)
                        {
                            _flow.ShapeGiven(a.Parameter, on);
                        }
                        else if (Flow.Serializes(u.Type) is string shape)
                        {
                            _flow.ShapeGiven(a.Parameter, $"{shape}, a '{u.Type.Name}' passed as '{a.Parameter.Name}' of '{m.Name}'");
                        }
                    }
                }
                if (!report || !(Flow.Sink(m) is var (sink, logger)))
                {
                    return;
                }
                // (a params array's elements each, at their own syntax: the array's is the call's)
                var values = args.SelectMany(a => a.ArgumentKind == ArgumentKind.ParamArray && a.Value is IArrayCreationOperation { Initializer: { } init }
                    ? init.ElementValues.AsEnumerable() : new[] { a.Value });
                foreach (var v in values)
                {
                    var shown = Why(v) ?? Shown(v, logger);
                    if (shown != null)
                    {
                        Report(v.Syntax, $"'{v.Syntax}'", shown, sink);
                    }
                }
            }

            /// <summary>An object (or a params array's) whose text shows a [Sensitive] member.</summary>
            private string Shown(IOperation value, bool logger)
            {
                if (value is IArrayCreationOperation arr && arr.Initializer != null)
                {
                    return arr.Initializer.ElementValues.Select(e => Shown(e, logger)).FirstOrDefault(w => w != null);
                }
                return _flow.TextShows(Unconverted(value)?.Type, logger);
            }

            private static IOperation Unconverted(IOperation op)
            {
                while (op is IConversionOperation c)
                {
                    op = c.Operand;
                }
                return op;
            }

            private static IAnonymousFunctionOperation Lambda(IOperation op) =>
                Unconverted(op) is IDelegateCreationOperation dc ? dc.Target as IAnonymousFunctionOperation : Unconverted(op) as IAnonymousFunctionOperation;

            /// <summary>Why the text of a value (its ToString, as interpolation and concatenation take it) shows a [Sensitive] member.</summary>
            private string Text(IOperation value) => value == null ? null : _flow.TextShows(Unconverted(value).Type, logger: false);

            /// <summary>Why a serializer's text of a value shows a [Sensitive] member: of its static type, or of what callers pass a parameter of a type that hides it.</summary>
            private string Serialized(IOperation value)
            {
                var u = Unconverted(value);
                if (_callers && u is IParameterReferenceOperation pr && _flow.CallerShape(pr.Parameter) is string shape)
                {
                    return shape;
                }
                return Flow.Serializes(u?.Type);
            }

            private static bool IsDeclassify(IMethodSymbol m) => SpecSymbols.HasAttribute(m, "DeclassifyAttribute");

            private void Report(SyntaxNode at, string what, string why, string sink)
            {
                _report?.Invoke(Diagnostic.Create(Descriptors.SensitiveLogged, at.GetLocation(), what, why, sink));
            }

            /// <summary>Why a value is sensitive; null where it isn't.</summary>
            private string Why(IOperation op)
            {
                if (op == null)
                {
                    return null;
                }
                // (a sealed value's text is a redaction, and nothing reads it but Unseal)
                if (op.Type != null && SpecSymbols.IsCsVerifyType(op.Type, "Sealed`1"))
                {
                    return null;
                }
                // (a parameter, a local, a member or a result of a [Sensitive] type)
                if (!(op is ILiteralOperation) && Flow.SensitiveType(op.Type) is string tw)
                {
                    return tw;
                }
                switch (op)
                {
                    case ILiteralOperation _:
                    case IDefaultValueOperation _:
                    case ITypeOfOperation _:
                    case INameOfOperation _:
                    case ISizeOfOperation _:
                    case IIsTypeOperation _:
                    case IIsPatternOperation _:
                    case IAnonymousFunctionOperation _:
                    case IDelegateCreationOperation _:
                        return null;
                    case IConversionOperation c:
                        return Why(c.Operand);
                    case IParenthesizedOperation p:
                        return Why(p.Operand);
                    case ILocalReferenceOperation l:
                        return _locals.TryGetValue(l.Local, out var lw) ? lw : null;
                    case IParameterReferenceOperation pr:
                        if (_locals.TryGetValue(pr.Parameter, out var pw))
                        {
                            return pw;
                        }
                        if (_probe >= 0 && pr.Parameter.Ordinal == _probe && SymbolEqualityComparer.Default.Equals(pr.Parameter.ContainingSymbol, _owner))
                        {
                            return Probed;
                        }
                        return _flow.Param(pr.Parameter) ?? (_callers ? _flow.CallerParam(pr.Parameter) : null);
                    case IInstanceReferenceOperation ir:
                        return Flow.SensitiveType(ir.Type);
                    case IFieldReferenceOperation f:
                        return Member(f.Field, f.Type) ?? Why(f.Instance);
                    case IPropertyReferenceOperation p:
                        return Member(p.Property, p.Type) ?? (p.Property.GetMethod != null ? _flow.Returned(p.Property.GetMethod) : null) ??
                               Why(p.Instance) ?? p.Arguments.Select(a => Why(a.Value)).FirstOrDefault(w => w != null);
                    case IInvocationOperation i:
                    {
                        var m = i.TargetMethod;
                        if (IsDeclassify(m))
                        {
                            return null;
                        }
                        if (IsUnseal(m))
                        {
                            return "unsealed";
                        }
                        if (m.Name == "ToString" && m.Parameters.Length == 0 && Text(i.Instance) is string text)
                        {
                            return text;
                        }
                        if (Flow.IsHttpExchange(m))
                        {
                            return null;
                        }
                        if (Flow.IsSerializer(m) && i.Arguments.Select(a => Serialized(a.Value)).FirstOrDefault(w => w != null) is string sz)
                        {
                            return sz;
                        }
                        return _flow.Returned(m) ?? Flow.SensitiveType(i.Type) ?? Why(i.Instance) ??
                               i.Arguments.Where(a => _flow.PassesOn(m, a.Parameter)).Select(a => Why(a.Value)).FirstOrDefault(w => w != null);
                    }
                    case IObjectCreationOperation o:
                        // (a type of the program's: its constructor and initializer store what they're given in members,
                        // which are sources where they're read; a library's is assumed to hold it)
                        return Flow.SensitiveType(o.Type) ?? (Flow.InSource(o.Type) ? null
                            : o.Arguments.Select(a => Why(a.Value)).FirstOrDefault(w => w != null) ?? Why(o.Initializer));
                    case IWithOperation w:
                        return Why(w.Operand) ?? (Flow.InSource(w.Type) ? null : Why(w.Initializer));
                    case IConditionalOperation c:
                        return Why(c.WhenTrue) ?? Why(c.WhenFalse);
                    case IInterpolationOperation io:
                        return Why(io.Expression) ?? Text(io.Expression);
                    case IBinaryOperation b when b.Type?.SpecialType == SpecialType.System_String:
                        return Why(b.LeftOperand) ?? Why(b.RightOperand) ?? Text(b.LeftOperand) ?? Text(b.RightOperand);
                    case IConditionalAccessInstanceOperation ci:
                        return Why(Receiver(ci));
                    case IArrayElementReferenceOperation ae:
                        return Why(ae.ArrayReference);
                    case IAwaitOperation aw:
                        return Why(aw.Operation);
                    default:
                        return op.Descendants().Where(d => d.Parent == op).Select(Why).FirstOrDefault(w => w != null);
                }
            }

            /// <summary>
            /// What a ?. instance stands for: the receiver of the nearest conditional access whose WhenNotNull holds it (in
            /// a?.b?.c, the inner access's receiver a?.b has an instance of its own, a's).
            /// </summary>
            private static IOperation Receiver(IConditionalAccessInstanceOperation ci)
            {
                IOperation child = ci;
                foreach (var a in Ancestors(ci))
                {
                    if (a is IConditionalAccessOperation ca && ca.WhenNotNull == child)
                    {
                        return ca.Operation;
                    }
                    child = a;
                }
                return null;
            }

            private string Member(ISymbol member, ITypeSymbol type)
            {
                if (SpecSymbols.HasAttribute(member, "SensitiveAttribute"))
                {
                    return $"[Sensitive] '{member.Name}'";
                }
                return _flow.Stored(member) ?? Flow.SensitiveType(type);
            }
        }
    }
}
