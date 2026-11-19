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
            private bool _changed;

            public Flow(Compilation compilation)
            {
                _compilation = compilation;
            }

            public void Run(System.Action<Diagnostic> report)
            {
                var bodies = Bodies().ToList();
                for (int round = 0; round < 50; round++)
                {
                    _changed = false;
                    foreach (var (body, owner) in bodies)
                    {
                        new Method(this, body, owner, callers: false, report: null).Run();
                        new Method(this, body, owner, callers: true, report: null).Run();
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

            internal void StoredIn(ISymbol member, string why)
            {
                if (member != null && !_members.ContainsKey(member.OriginalDefinition) && member.Locations.Any(l => l.IsInSource))
                {
                    _members[member.OriginalDefinition] = why;
                    _changed = true;
                }
            }

            internal string Stored(ISymbol member) => _members.TryGetValue(member.OriginalDefinition, out var why) ? why : null;

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
                    members.AddRange(c.GetMembers().Where(m => (m is IFieldSymbol || m is IPropertySymbol) && SpecSymbols.HasAttribute(m, "SensitiveAttribute")));
                }
                if (members.Count == 0)
                {
                    return null;
                }
                var toString = Enumerable.Repeat(t, 1).Concat(BaseTypes(t)).SelectMany(c => c.GetMembers("ToString").OfType<IMethodSymbol>())
                    .FirstOrDefault(m => m.Parameters.Length == 0 && !m.IsStatic);
                if (t.IsRecord && (toString == null || toString.IsImplicitlyDeclared))
                {
                    return $"its ToString, a record's, prints [Sensitive] '{members[0].Name}'";
                }
                if (toString != null && !toString.IsImplicitlyDeclared && Returned(toString) is string why)
                {
                    return $"its ToString returns what's {why}";
                }
                var shown = members.FirstOrDefault(m => m.DeclaredAccessibility == Accessibility.Public);
                return logger && shown != null ? $"a logger may write its public [Sensitive] '{shown.Name}' ({{@...}})" : null;
            }

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
            private readonly Dictionary<ISymbol, string> _locals = new Dictionary<ISymbol, string>(SymbolEqualityComparer.Default);
            private bool _grew;

            public Method(Flow flow, IOperation body, ISymbol owner, bool callers, System.Action<Diagnostic> report)
            {
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
                            _flow.StoredIn(f.Field, why);
                        }
                        break;
                    case IPropertyReferenceOperation pr when pr.Arguments.Length == 0:
                        if (_callers)
                        {
                            _flow.StoredIn(pr.Property, why);
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
                    case IReturnOperation r when r.ReturnedValue != null && !_callers && Why(r.ReturnedValue) is string rw:
                        _flow.Returns(Function(op), rw);
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
                    if (instance != null && !(m.MethodKind == MethodKind.PropertyGet))
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
                        _flow.GivenTo(a.Parameter, why);
                    }
                }
                if (!report || !(Flow.Sink(m) is var (sink, logger)))
                {
                    return;
                }
                foreach (var (a, why) in whys)
                {
                    var shown = why ?? Shown(a.Value, logger);
                    if (shown != null)
                    {
                        Report(a.Value.Syntax, $"'{a.Value.Syntax}'", shown, sink);
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
                        return _locals.TryGetValue(pr.Parameter, out var pw) ? pw : _flow.Param(pr.Parameter) ?? (_callers ? _flow.CallerParam(pr.Parameter) : null);
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
                        return _flow.Returned(m) ?? Flow.SensitiveType(i.Type) ?? Why(i.Instance) ?? i.Arguments.Select(a => Why(a.Value)).FirstOrDefault(w => w != null);
                    }
                    case IObjectCreationOperation o:
                        return Flow.SensitiveType(o.Type) ?? o.Arguments.Select(a => Why(a.Value)).FirstOrDefault(w => w != null) ?? Why(o.Initializer);
                    case IConditionalOperation c:
                        return Why(c.WhenTrue) ?? Why(c.WhenFalse);
                    case IConditionalAccessInstanceOperation ci:
                        return Ancestors(ci).OfType<IConditionalAccessOperation>().Select(a => Why(a.Operation)).FirstOrDefault();
                    case IArrayElementReferenceOperation ae:
                        return Why(ae.ArrayReference);
                    case IAwaitOperation aw:
                        return Why(aw.Operation);
                    default:
                        return op.Descendants().Where(d => d.Parent == op).Select(Why).FirstOrDefault(w => w != null);
                }
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
