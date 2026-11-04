using System;
using System.Collections;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Text;
using CsVerify.Analyzers;
using CsVerify.Verifier;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Xunit;

namespace CsVerify.Tests
{
    /// <summary>
    /// Stub conformance: every [ContractsFor] stub of CsVerify's BCL contracts is run against the real BCL on random
    /// inputs. A stub's contract is trusted (its postconditions are assumed, never proved), so a wrong one makes wrong
    /// things provable; this is what checks them.
    ///
    /// For each stub method a checker is generated and compiled: it assumes the preconditions (skipping inputs that
    /// break them), takes the Spec.Old values and the model state of every argument, calls the real member, and checks
    /// the postconditions, and that only the objects Spec.Modifies names changed their models. The model functions
    /// and Seq/Map/Ghost/ObjSet get run-time meanings here (<see cref="Shim"/>): Items() is the list's elements, Size()
    /// its Count, and so on. A model's value where it means nothing (a list's Items() past its Size()) is undetermined,
    /// and matches anything. A [Pure] stub's member must not throw where its preconditions hold (the verifier assumes it
    /// returns); any other member may (calls may throw in CsVerify's model), and then its EnsuresOnThrow and frame are
    /// checked. Type parameters are instantiated with int (T, V) and string (K).
    /// </summary>
    public class StubConformanceTests
    {
        private const int Trials = 300;

        [Fact]
        public void BclStubs_HoldOfTheRealBcl()
        {
            var compilation = SpecCompilation();
            var stubs = ContractStubs.For(compilation);
            Assert.Empty(stubs.Errors.Select(e => e.message));
            var pairs = stubs.Pairs.ToList();
            Assert.True(pairs.Count > 90, $"only {pairs.Count} stubs found");
            var failures = Run(compilation, pairs);
            Assert.True(failures.Count == 0, $"{failures.Count} of {pairs.Count} stubs do not hold of the BCL:\n" + string.Join("\n", failures));
        }

        /// <summary>The checkers catch wrong stubs: each of these is wrong in its own way.</summary>
        [Fact]
        public void WrongStubs_AreCaught()
        {
            const string wrong = @"
namespace Wrong
{
    using System.Collections.Generic;
    using CsVerify;
    using CsVerify.Bcl;

    [ContractsFor(typeof(List<>))]
    public static class WrongListContracts<T>
    {
        public static void Add(List<T> @this, T item)
        {
            Spec.Modifies(ObjSet.Of(@this));
            Spec.Ensures(@this.Size() == Spec.Old(@this.Size()) + 2);
            throw null!;
        }

        public static void Clear(List<T> @this) { throw null!; }

        // (Insert changes the list's version: its enumerators would throw)
        public static void Insert(List<T> @this, int index, T item)
        {
            Spec.Requires(0 <= index && index <= @this.Size());
            Spec.Modifies(ObjSet.Of(@this));
            Spec.Ensures(@this.Version() == Spec.Old(@this.Version()));
            throw null!;
        }

        [Pure]
        public static T get_Item(List<T> @this, int index)
        {
            Spec.Ensures<T>(r => Ghost.Of(r) == @this.Items()[index]);
            throw null!;
        }

        public static void Reverse(List<T> @this)
        {
            Spec.Modifies(ObjSet.Of(@this));
            Spec.Ensures(Spec.Forall(0, @this.Size(), i => @this.Items()[i] == Spec.Old(@this.Items())[i]));
            throw null!;
        }
    }

    [ContractsFor(typeof(string))]
    public static class WrongStringContracts
    {
        public static string Substring(string @this, int startIndex)
        {
            Spec.Requires(0 <= startIndex && startIndex <= @this.Length);
            Spec.Ensures<string>(r => r.Length == startIndex);
            throw null!;
        }
    }
}";
            var compilation = SpecCompilation(wrong);
            var pairs = ContractStubs.For(compilation).Pairs.Where(p => p.stub.ContainingNamespace.Name == "Wrong").ToList();
            Assert.Equal(6, pairs.Count);
            var failures = string.Join("\n", Run(compilation, pairs));
            Assert.Contains("List<T>.Add(T): postcondition does not hold: @this.Size() == Spec.Old(@this.Size()) + 2", failures);
            Assert.Contains("List<T>.Clear(): changed List`1, outside its Spec.Modifies", failures);
            Assert.Contains("List<T>.this[int].get: [Pure], but threw ArgumentOutOfRangeException", failures);
            Assert.Contains("List<T>.Reverse(): postcondition does not hold: Spec.Forall", failures);
            Assert.Contains("string.Substring(int): postcondition does not hold: r => r.Length == startIndex", failures);
            Assert.Contains("List<T>.Insert(int, T): postcondition does not hold: @this.Version() == Spec.Old(@this.Version())", failures);
        }

        /// <summary>Runs each stub's checker on random inputs: what fails, one line each.</summary>
        private static List<string> Run(Compilation compilation, IEnumerable<(IMethodSymbol member, IMethodSymbol stub)> stubs)
        {
            var pairs = stubs.OrderBy(p => p.stub.ContainingType.Name, StringComparer.Ordinal)
                .ThenBy(p => p.stub.ToDisplayString(), StringComparer.Ordinal).ToList();
            var checkers = pairs.Select((p, i) => Generate(compilation, p.member, p.stub, i)).ToList();
            var assembly = Compile(checkers);

            var failures = new List<string>();
            foreach (var c in checkers)
            {
                var type = assembly.GetType("CsVerify.Conformance." + c.ClassName + (c.ClassArity > 0 ? "`" + c.ClassArity : ""));
                if (c.ClassArity > 0) type = type.MakeGenericType(c.ClassTypeParameters.Select(Instance).ToArray());
                var method = type.GetMethod("Check");
                if (method.IsGenericMethodDefinition) method = method.MakeGenericMethod(c.MethodTypeParameters.Select(Instance).ToArray());
                int held = 0;
                var random = new Random(7919 * c.Index + 1);
                for (int trial = 0; trial < Trials; trial++)
                {
                    object[] args;
                    try { args = Inputs(method.GetParameters(), random); }
                    catch (NotSupportedException e) { failures.Add($"{c.Member}: no inputs for {e.Message}"); goto next; }
                    var shown = Show(args);
                    string outcome;
                    try { outcome = (string)method.Invoke(null, args); }
                    catch (TargetInvocationException e) { outcome = "the checker threw " + e.InnerException; }
                    if (outcome == "skip") continue;
                    held++;
                    if (outcome != null)
                    {
                        failures.Add($"{c.Member}: {outcome}, on ({shown})");
                        goto next;
                    }
                }
                if (held == 0) failures.Add($"{c.Member}: its preconditions held for none of {Trials} random inputs");
            next:;
            }
            return failures;
        }

        // ------------------------------------------------------------------------------------- the stubs

        /// <summary>The Spec library's sources (so its stubs are found as CsVerify's own), and any more.</summary>
        private static CSharpCompilation SpecCompilation(string more = null)
        {
            var dir = Path.Combine(Harness.RepoRoot(), "src", "CsVerify.Spec");
            var parse = new CSharpParseOptions(LanguageVersion.Latest, preprocessorSymbols: new[] { "CSVERIFY_SPEC" });
            var trees = Directory.GetFiles(dir, "*.cs", SearchOption.AllDirectories)
                .Where(f => !f.Contains(Path.DirectorySeparatorChar + "obj" + Path.DirectorySeparatorChar) &&
                            !f.Contains(Path.DirectorySeparatorChar + "bin" + Path.DirectorySeparatorChar))
                .Select(f => CSharpSyntaxTree.ParseText(File.ReadAllText(f), parse, "<CsVerify.Spec>/" + Path.GetRelativePath(dir, f))).ToList();
            if (more != null) trees.Add(CSharpSyntaxTree.ParseText(more, parse, "more.cs"));
            var c = CSharpCompilation.Create("CsVerifySpec", trees, Engine.FrameworkReferences(),
                new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary, nullableContextOptions: NullableContextOptions.Enable));
            Assert.Empty(c.GetDiagnostics().Where(d => d.Severity == DiagnosticSeverity.Error).Select(d => d.ToString()));
            return c;
        }

        private sealed class Checker
        {
            public int Index;
            public string Member, ClassName, Code;
            public int ClassArity;
            public string[] ClassTypeParameters, MethodTypeParameters;
        }

        private static readonly SymbolDisplayFormat Full = SymbolDisplayFormat.FullyQualifiedFormat
            .WithMiscellaneousOptions(SymbolDisplayFormat.FullyQualifiedFormat.MiscellaneousOptions | SymbolDisplayMiscellaneousOptions.IncludeNullableReferenceTypeModifier);

        private static string Name(string n) => SyntaxFacts.GetKeywordKind(n) != SyntaxKind.None ? "@" + n : n;

        private static string RefKindText(RefKind k) => k switch { RefKind.Out => "out ", RefKind.Ref => "ref ", _ => "" };

        /// <summary>The checker for one stub method: its contract around a call of the real member.</summary>
        private static Checker Generate(Compilation compilation, IMethodSymbol member, IMethodSymbol stub, int index)
        {
            var decl = (MethodDeclarationSyntax)stub.DeclaringSyntaxReferences[0].GetSyntax();
            var model = compilation.GetSemanticModel(decl.SyntaxTree);
            var klass = stub.ContainingType;
            var pre = new List<string>();
            var post = new List<(string code, string text)>();
            var onThrow = new List<(string type, string code, string text)>();
            string frame = null;
            foreach (var st in decl.Body?.Statements ?? default)
            {
                if (st is ThrowStatementSyntax) continue;
                if (st is ExpressionStatementSyntax { Expression: AssignmentExpressionSyntax }) continue; // out parameters set for C#
                if (!(st is ExpressionStatementSyntax { Expression: InvocationExpressionSyntax inv }) ||
                    !(model.GetSymbolInfo(inv).Symbol is IMethodSymbol spec) || spec.ContainingType.Name != "Spec")
                    throw new InvalidOperationException($"{stub}: unexpected statement '{st}'");
                var arg = inv.ArgumentList.Arguments[0].Expression;
                string Code(ExpressionSyntax e) => new OldAndResult(model, stub).Visit(e).ToFullString();
                switch (spec.Name)
                {
                    case "Requires": pre.Add(Code(arg)); break;
                    case "Modifies": frame = Code(arg); break;
                    case "Ensures" when spec.IsGenericMethod:
                        post.Add(($"((global::System.Func<{spec.TypeArguments[0].ToDisplayString(Full)}, bool>)({Code(arg)}))(__r)", arg.ToString()));
                        break;
                    case "Ensures": post.Add((Code(arg), arg.ToString())); break;
                    case "EnsuresOnThrow": onThrow.Add((spec.TypeArguments[0].ToDisplayString(Full), Code(arg), arg.ToString())); break;
                    default: throw new InvalidOperationException($"{stub}: unexpected Spec.{spec.Name}");
                }
            }

            bool receiver = ContractStubs.TakesReceiver(stub);
            var ps = stub.Parameters;
            var callArgs = ps.Skip(receiver ? 1 : 0).Select(p => RefKindText(p.RefKind) + Name(p.Name)).ToList();
            var target = member.ContainingType.OriginalDefinition;
            var targetType = target.IsGenericType ? target.Construct(klass.TypeParameters.Cast<ITypeSymbol>().ToArray()) : target;
            string typeText = targetType.ToDisplayString(Full);
            string call;
            switch (member.MethodKind)
            {
                case MethodKind.Constructor:
                    call = $"new {typeText}({string.Join(", ", callArgs)})";
                    break;
                case MethodKind.PropertyGet:
                {
                    var prop = (IPropertySymbol)member.AssociatedSymbol;
                    string on = member.IsStatic ? typeText : "@this";
                    call = prop.IsIndexer ? $"{on}[{string.Join(", ", callArgs)}]" : $"{on}.{prop.Name}";
                    break;
                }
                case MethodKind.PropertySet:
                {
                    var prop = (IPropertySymbol)member.AssociatedSymbol;
                    string on = member.IsStatic ? typeText : "@this";
                    var idx = callArgs.Take(callArgs.Count - 1);
                    call = (prop.IsIndexer ? $"{on}[{string.Join(", ", idx)}]" : $"{on}.{prop.Name}") + " = " + callArgs.Last();
                    break;
                }
                default:
                {
                    string on = receiver ? "@this" : typeText;
                    string typeArgs = stub.IsGenericMethod ? "<" + string.Join(", ", stub.TypeParameters.Select(t => t.Name)) + ">" : "";
                    call = $"{on}.{member.Name}{typeArgs}({string.Join(", ", callArgs)})";
                    break;
                }
            }
            bool returns = !stub.ReturnsVoid && member.MethodKind != MethodKind.PropertySet &&
                           !(stub.IsAsync && stub.ReturnType is INamedTypeSymbol { TypeArguments.Length: 0 });
            var resultType = stub.IsAsync && stub.ReturnType is INamedTypeSymbol { TypeArguments.Length: 1 } task ? task.TypeArguments[0] : stub.ReturnType;

            // the objects whose models are compared before and after: the arguments of reference type
            var objects = ps.Where(p => p.RefKind != RefKind.Out && !p.Type.IsValueType && p.Type.SpecialType != SpecialType.System_String)
                .Select(p => Name(p.Name)).ToList();
            var sb = new StringBuilder();
            string className = "C" + index;
            string classTps = klass.TypeParameters.Length > 0 ? "<" + string.Join(", ", klass.TypeParameters.Select(t => t.Name)) + ">" : "";
            string methodTps = stub.TypeParameters.Length > 0 ? "<" + string.Join(", ", stub.TypeParameters.Select(t => t.Name)) + ">" : "";
            string constraints = string.Concat(klass.TypeParameters.Concat(stub.TypeParameters).Where(t => t.HasNotNullConstraint).Select(t => $" where {t.Name} : notnull"));
            sb.AppendLine($"    // {member.ToDisplayString()}");
            sb.AppendLine($"    public static class {className}{classTps}{(stub.TypeParameters.Length == 0 ? constraints : "")}");
            sb.AppendLine("    {");
            // a span can't be boxed for reflection: the checker takes an array and makes the span of it
            bool IsSpanParam(IParameterSymbol p) => p.Type is INamedTypeSymbol n && (n.OriginalDefinition.ToDisplayString() == "System.Span<T>" || n.OriginalDefinition.ToDisplayString() == "System.ReadOnlySpan<T>");
            var sig = ps.Select(p => IsSpanParam(p)
                ? $"{((INamedTypeSymbol)p.Type).TypeArguments[0].ToDisplayString(Full)}[] __span_{p.Name}"
                : $"{RefKindText(p.RefKind)}{p.Type.ToDisplayString(Full)} {Name(p.Name)}");
            sb.AppendLine($"        public static string Check{methodTps}({string.Join(", ", sig)}){(stub.TypeParameters.Length > 0 ? constraints : "")}");
            sb.AppendLine("        {");
            foreach (var p in ps.Where(IsSpanParam)) sb.AppendLine($"            {p.Type.ToDisplayString(Full)} {Name(p.Name)} = __span_{p.Name};");
            foreach (var p in ps.Where(p => p.RefKind == RefKind.Out)) sb.AppendLine($"            {Name(p.Name)} = default!;");
            if (pre.Count > 0) sb.AppendLine($"            if (!({string.Join(") || !(", pre)})) return \"skip\";");
            foreach (var p in ps.Where(p => p.RefKind != RefKind.Out && !IsSpanParam(p)))
                sb.AppendLine($"            var __pre_{p.Name} = global::CsVerify.Conformance.Models.Copy({Name(p.Name)});");
            sb.AppendLine($"            var __objects = new object?[] {{ {string.Join(", ", objects)} }};");
            sb.AppendLine("            global::CsVerify.Spec.Args = __objects;");
            sb.AppendLine("            var __before = global::CsVerify.Conformance.Models.Snapshot(__objects);");
            sb.AppendLine($"            var __frame = {frame ?? "global::CsVerify.ObjSet.Empty"};");
            if (returns) sb.AppendLine($"            {resultType.ToDisplayString(Full)} __r;");
            sb.AppendLine("            try");
            sb.AppendLine("            {");
            // an async stub: its contract is of what the task gives
            sb.AppendLine($"                {(returns ? "__r = " : "")}{(stub.IsAsync ? $"({call}).GetAwaiter().GetResult()" : call)};");
            sb.AppendLine("            }");
            sb.AppendLine("            catch (global::System.Exception __x) when (!(__x is global::CsVerify.Conformance.Undetermined))");
            sb.AppendLine("            {");
            if (SpecSymbols.IsPure(stub))
                sb.AppendLine("                return \"[Pure], but threw \" + __x.GetType().Name + \" where its preconditions hold\";");
            else
            {
                sb.AppendLine("                var __thrownFrame = global::CsVerify.Conformance.Models.Changed(__before, __frame);");
                sb.AppendLine("                if (__thrownFrame != null) return \"threw \" + __x.GetType().Name + \", and changed \" + __thrownFrame + \", outside its Spec.Modifies\";");
                foreach (var (type, code, text) in onThrow)
                    sb.AppendLine($"                if (__x is {type} && !({code})) return \"threw \" + __x.GetType().Name + \", and EnsuresOnThrow does not hold: {Escape(text)}\";");
                sb.AppendLine("                return null; // (calls may throw: what it promises on a throw held)");
            }
            sb.AppendLine("            }");
            sb.AppendLine("            var __changed = global::CsVerify.Conformance.Models.Changed(__before, __frame);");
            sb.AppendLine("            if (__changed != null) return \"changed \" + __changed + \", outside its Spec.Modifies\";");
            foreach (var (code, text) in post)
                sb.AppendLine($"            if (!({code})) return \"postcondition does not hold: {Escape(text)}\";");
            sb.AppendLine("            return null;");
            sb.AppendLine("        }");
            sb.AppendLine("    }");
            return new Checker
            {
                Index = index, Member = member.ToDisplayString(), ClassName = className, ClassArity = klass.TypeParameters.Length,
                ClassTypeParameters = klass.TypeParameters.Select(t => t.Name).ToArray(),
                MethodTypeParameters = stub.TypeParameters.Select(t => t.Name).ToArray(),
                Code = sb.ToString(),
            };
        }

        private static string Escape(string s) => s.Replace("\\", "\\\\").Replace("\"", "\\\"").Replace("\r", " ").Replace("\n", " ");

        /// <summary>
        /// Spec.Old(e) becomes e over copies of the arguments taken before the call (__pre_x for x, which may be under
        /// a quantifier: Spec.Old(a[i])); Spec.Result() becomes the call's result.
        /// </summary>
        private sealed class OldAndResult : CSharpSyntaxRewriter
        {
            private readonly SemanticModel _model;
            private readonly IMethodSymbol _stub;
            private bool _old;
            public OldAndResult(SemanticModel model, IMethodSymbol stub) { _model = model; _stub = stub; }

            public override SyntaxNode VisitInvocationExpression(InvocationExpressionSyntax node)
            {
                if (_model.GetSymbolInfo(node).Symbol is IMethodSymbol m && m.ContainingType.Name == "Spec")
                {
                    if (m.Name == "Result") return SyntaxFactory.IdentifierName("__r").WithTriviaFrom(node);
                    if (m.Name == "Old")
                    {
                        _old = true;
                        try { return SyntaxFactory.ParenthesizedExpression((ExpressionSyntax)Visit(node.ArgumentList.Arguments[0].Expression)).WithTriviaFrom(node); }
                        finally { _old = false; }
                    }
                }
                return base.VisitInvocationExpression(node);
            }

            public override SyntaxNode VisitIdentifierName(IdentifierNameSyntax node) =>
                _old && _model.GetSymbolInfo(node).Symbol is IParameterSymbol p && SymbolEqualityComparer.Default.Equals(p.ContainingSymbol, _stub)
                    ? SyntaxFactory.IdentifierName("__pre_" + p.Name).WithTriviaFrom(node)
                    : base.VisitIdentifierName(node);
        }

        private static Assembly Compile(List<Checker> checkers)
        {
            var code = new StringBuilder();
            code.AppendLine("#nullable enable");
            code.AppendLine("namespace CsVerify.Conformance");
            code.AppendLine("{");
            code.AppendLine("    using System; using System.Collections.Generic; using System.IO; using System.Text; using CsVerify; using CsVerify.Bcl;");
            foreach (var c in checkers) code.Append(c.Code);
            code.AppendLine("}");
            var trees = new[]
            {
                CSharpSyntaxTree.ParseText(code.ToString(), new CSharpParseOptions(LanguageVersion.Latest), "checkers.cs"),
                CSharpSyntaxTree.ParseText(Shim, new CSharpParseOptions(LanguageVersion.Latest), "shim.cs"),
            };
            var compilation = CSharpCompilation.Create("CsVerifyConformance", trees, Engine.FrameworkReferences(),
                new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary, nullableContextOptions: NullableContextOptions.Enable));
            using var ms = new MemoryStream();
            var emit = compilation.Emit(ms);
            Assert.True(emit.Success, "the checkers do not compile:\n" + string.Join("\n", emit.Diagnostics.Where(d => d.Severity == DiagnosticSeverity.Error)));
            return Assembly.Load(ms.ToArray());
        }

        /// <summary>
        /// The run-time meaning of what the stubs' contracts use: Spec's quantifiers and Fresh, ghost values, sequences
        /// and maps whose values may be undetermined, object sets, and the model functions of the BCL objects.
        /// </summary>
        private const string Shim = @"
#nullable enable
namespace CsVerify
{
    using System; using System.Collections.Generic; using System.Linq;

    public static class Spec
    {
        public static object?[] Args = Array.Empty<object?>();
        public static bool Forall(int lo, int hi, Func<int, bool> p) { for (int i = lo; i < hi; i++) if (!p(i)) return false; return true; }
        public static bool Exists(int lo, int hi, Func<int, bool> p) { for (int i = lo; i < hi; i++) if (p(i)) return true; return false; }
        // a result distinct from every object the call was handed
        public static bool Fresh(object? o) => o != null && !Args.Any(a => ReferenceEquals(a, o));
        public static bool Equal<T>(Ghost<T> a, Ghost<T> b) => !a.Known || !b.Known || EqualityComparer<T>.Default.Equals(a.V, b.V);
    }

    // a ghost value, or an undetermined one (a model where it means nothing), which matches anything
    public readonly struct Ghost<T>
    {
        internal readonly bool Known; internal readonly T V;
        internal Ghost(T v, bool known) { V = v; Known = known; }
        public T Value => Known ? V : throw new CsVerify.Conformance.Undetermined();
        public static bool operator ==(Ghost<T> a, Ghost<T> b) => !a.Known || !b.Known || EqualityComparer<T>.Default.Equals(a.V, b.V);
        public static bool operator !=(Ghost<T> a, Ghost<T> b) => !(a == b);
        public override bool Equals(object? o) => o is Ghost<T> g && this == g;
        public override int GetHashCode() => 0;
    }

    public static class Ghost { public static Ghost<T> Of<T>(T value) => new Ghost<T>(value, true); }

    // known at some indices, undetermined elsewhere
    public sealed class Seq<T>
    {
        internal readonly Dictionary<int, T> Known;
        internal Seq(Dictionary<int, T> known) { Known = known; }
        public static Seq<T> Of(IEnumerable<T> items) { var d = new Dictionary<int, T>(); int i = 0; foreach (var x in items) d[i++] = x; return new Seq<T>(d); }
        public Ghost<T> this[int index] => Known.TryGetValue(index, out var v) ? new Ghost<T>(v, true) : default;
        public Seq<T> Update(int index, Ghost<T> value)
        {
            var d = new Dictionary<int, T>(Known);
            if (value.Known) d[index] = value.V; else d.Remove(index);
            return new Seq<T>(d);
        }
        public Seq<T> Drop(int count) => new Seq<T>(Known.Where(kv => kv.Key >= count).ToDictionary(kv => kv.Key - count, kv => kv.Value));
        public Seq<T> Concat(int count, Seq<T> rest)
        {
            var d = Known.Where(kv => kv.Key < count).ToDictionary(kv => kv.Key, kv => kv.Value);
            foreach (var kv in rest.Known) if (kv.Key >= 0) d[kv.Key + count] = kv.Value;
            return new Seq<T>(d);
        }
        public static bool operator ==(Seq<T> a, Seq<T> b) => a.Known.All(kv => !b.Known.TryGetValue(kv.Key, out var v) || EqualityComparer<T>.Default.Equals(kv.Value, v));
        public static bool operator !=(Seq<T> a, Seq<T> b) => !(a == b);
        public override bool Equals(object? o) => o is Seq<T> s && this == s;
        public override int GetHashCode() => 0;
    }

    public static class Seq
    {
        public static Seq<object?> Contents(Array a) { var d = new Dictionary<int, object?>(); for (int i = 0; i < a.Length; i++) d[i] = a.GetValue(i); return new Seq<object?>(d); }
    }

    // a total map: its value at each key given, or else a default (known or undetermined)
    public sealed class Map<K, V> where K : notnull
    {
        internal readonly Dictionary<K, V> Given; internal readonly Ghost<V> Default;
        internal Map(Dictionary<K, V> given, Ghost<V> @default) { Given = given; Default = @default; }
        public Ghost<V> this[K key] => Given.TryGetValue(key, out var v) ? new Ghost<V>(v, true) : Default;
        public Map<K, V> Update(K key, Ghost<V> value)
        {
            var d = new Dictionary<K, V>(Given);
            if (value.Known) d[key] = value.V; else d.Remove(key);
            return new Map<K, V>(d, Default);
        }
        public static bool operator ==(Map<K, V> a, Map<K, V> b) =>
            a.Given.Keys.Concat(b.Given.Keys).All(k => a[k] == b[k]) && a.Default == b.Default;
        public static bool operator !=(Map<K, V> a, Map<K, V> b) => !(a == b);
        public override bool Equals(object? o) => o is Map<K, V> m && this == m;
        public override int GetHashCode() => 0;
    }

    public static class Map { public static Map<K, V> Const<K, V>(V value) where K : notnull => new Map<K, V>(new Dictionary<K, V>(), new Ghost<V>(value, true)); }

    public readonly struct ObjSet
    {
        internal readonly object?[]? Items;
        private ObjSet(object?[] items) { Items = items; }
        public static ObjSet Empty => new ObjSet(Array.Empty<object?>());
        public static ObjSet Of(object? item) => new ObjSet(new[] { item });
        public bool Contains(object? item) => (Items ?? Array.Empty<object?>()).Any(x => ReferenceEquals(x, item));
        public ObjSet Add(object? item) => new ObjSet((Items ?? Array.Empty<object?>()).Append(item).ToArray());
        public ObjSet Union(ObjSet other) => new ObjSet((Items ?? Array.Empty<object?>()).Concat(other.Items ?? Array.Empty<object?>()).ToArray());
    }
}

namespace CsVerify.Bcl
{
    using System.Collections.Generic; using System.Linq; using System.Text;

    public static class Models
    {
        public static Seq<T> Items<T>(this List<T> list) => Seq<T>.Of(list);
        public static int Size<T>(this List<T> list) => list.Count;
        public static Map<K, bool> Domain<K, V>(this Dictionary<K, V> d) where K : notnull => new Map<K, bool>(d.Keys.ToDictionary(k => k, k => true), Ghost.Of(false));
        public static Map<K, V> Entries<K, V>(this Dictionary<K, V> d) where K : notnull => new Map<K, V>(new Dictionary<K, V>(d), default);
        public static int Size<K, V>(this Dictionary<K, V> d) where K : notnull => d.Count;
        public static int Version<T>(this List<T> l) => CsVerify.Conformance.Models.VersionOf(l);
        public static int Version<K, V>(this Dictionary<K, V> d) where K : notnull => CsVerify.Conformance.Models.VersionOf(d);
    }

    public static class CollectionModels
    {
        public static Map<T, bool> Members<T>(this HashSet<T> set) where T : notnull => new Map<T, bool>(set.ToDictionary(x => x, x => true), Ghost.Of(false));
        public static int Size<T>(this HashSet<T> set) => set.Count;
        public static Seq<T> Items<T>(this Stack<T> stack) => Seq<T>.Of(stack.Reverse());
        public static int Size<T>(this Stack<T> stack) => stack.Count;
        public static Seq<T> Items<T>(this Queue<T> queue) => Seq<T>.Of(queue);
        public static int Size<T>(this Queue<T> queue) => queue.Count;
        public static int Version<T>(this HashSet<T> s) => CsVerify.Conformance.Models.VersionOf(s);
        public static int Version<T>(this Stack<T> s) => CsVerify.Conformance.Models.VersionOf(s);
        public static int Version<T>(this Queue<T> q) => CsVerify.Conformance.Models.VersionOf(q);
    }

    public static class TextModels
    {
        public static int Size(this StringBuilder builder) => builder.Length;
    }
}

namespace CsVerify.Conformance
{
    using System; using System.Collections; using System.Collections.Generic; using System.Linq; using System.Text;

    // a postcondition read a model's value where it is undetermined
    public sealed class Undetermined : Exception { public Undetermined() : base(""a model value that means nothing here was read"") { } }

    public static class Models
    {
        // what the models of each object say: a list's elements, a dictionary's entries, a builder's length, an array's elements
        private static object? State(object? o) => o switch
        {
            null => null,
            Array a => a.Cast<object?>().ToArray(),
            StringBuilder sb => sb.Length,
            IDictionary d => d.Keys.Cast<object>().OrderBy(k => k.ToString(), StringComparer.Ordinal).Select(k => (k, d[k])).ToArray(),
            IList l => l.Cast<object?>().ToArray(),
            IEnumerable e when !(o is string) => e.Cast<object?>().ToArray(),
            _ => null,
        };

        public static (object? o, object? state)[] Snapshot(object?[] objects) => objects.Select(o => (o, State(o))).ToArray();

        // a collection's version: its private _version (what its enumerators check); a copy made for Spec.Old has its original's
        private static readonly System.Runtime.CompilerServices.ConditionalWeakTable<object, object> Versions = new System.Runtime.CompilerServices.ConditionalWeakTable<object, object>();
        public static int VersionOf(object o) =>
            Versions.TryGetValue(o, out var v) ? (int)v
            : (int)o.GetType().GetField(""_version"", System.Reflection.BindingFlags.NonPublic | System.Reflection.BindingFlags.Instance)!.GetValue(o)!;
        private static C Versioned<C>(C copy, object original) where C : class { Versions.AddOrUpdate(copy, VersionOf(original)); return copy; }

        // an argument as it was before the call, for Spec.Old
        public static T Copy<T>(T x) => x;
        public static T[]? Copy<T>(T[]? a) => (T[]?)a?.Clone();
        public static Array? Copy(Array? a) => (Array?)a?.Clone();
        public static List<T>? Copy<T>(List<T>? l) => l == null ? null : Versioned(new List<T>(l), l);
        public static Dictionary<K, V>? Copy<K, V>(Dictionary<K, V>? d) where K : notnull => d == null ? null : Versioned(new Dictionary<K, V>(d), d);
        public static StringBuilder? Copy(StringBuilder? sb) => sb == null ? null : new StringBuilder(sb.ToString());
        public static HashSet<T>? Copy<T>(HashSet<T>? s) => s == null ? null : Versioned(new HashSet<T>(s, s.Comparer), s);
        public static Stack<T>? Copy<T>(Stack<T>? s) => s == null ? null : Versioned(new Stack<T>(s.Reverse()), s);
        public static Queue<T>? Copy<T>(Queue<T>? q) => q == null ? null : Versioned(new Queue<T>(q), q);

        // the first object outside the frame whose models changed, or null
        public static string? Changed((object? o, object? state)[] before, ObjSet frame)
        {
            foreach (var (o, state) in before)
            {
                if (o == null || frame.Contains(o)) continue;
                var now = State(o);
                bool same = state is Array a && now is Array b ? a.Cast<object?>().SequenceEqual(b.Cast<object?>()) : Equals(state, now);
                if (!same) return o.GetType().Name;
            }
            return null;
        }
    }
}
";

        // ------------------------------------------------------------------------------------- the inputs

        private static Type Instance(string typeParameter) => typeParameter == "K" ? typeof(string) : typeof(int);

        private static readonly string[] Strings = { "", "a", "ab", "abc", " a b ", "Ab0", "-12", "123", "007", "2147483648", "{0}", "x{1}y", "\t", "aaa" };
        private static readonly char[] Chars = { 'a', 'b', 'Z', '0', '9', ' ', '-', '\t', '{' };
        private static readonly string[] Keys = { "a", "b", "c", "d" };
        // parameters where any int is safe to try (no sizes or counts, which could allocate gigabytes)
        private static readonly HashSet<string> AnyInt = new HashSet<string> { "value", "min", "max", "item", "arg0", "arg1" };
        private static readonly NullabilityInfoContext Nullability = new NullabilityInfoContext();

        private static object[] Inputs(ParameterInfo[] ps, Random r)
        {
            var pool = new List<object>();
            return ps.Select(p => p.IsOut ? null : Input(p.ParameterType.IsByRef ? p.ParameterType.GetElementType() : p.ParameterType,
                                                          p.Name, Nullability.Create(p).ReadState == NullabilityState.Nullable && p.Name != "this", r, pool)).ToArray();
        }

        private static int SmallInt(Random r) => r.Next(10) < 8 ? r.Next(-2, 9) : r.Next(-3, 20);

        private static object Input(Type t, string name, bool nullable, Random r, List<object> pool)
        {
            if (t == typeof(int)) return AnyInt.Contains(name) && r.Next(6) == 0 ? new[] { int.MinValue, int.MaxValue, -1, 0, 1 }[r.Next(5)] : SmallInt(r);
            if (t == typeof(long)) return r.Next(6) == 0 ? new[] { long.MinValue, long.MaxValue, -1L, (long)int.MaxValue + 1 }[r.Next(4)] : (long)SmallInt(r);
            if (t == typeof(bool)) return r.Next(2) == 0;
            if (t == typeof(char)) return Chars[r.Next(Chars.Length)];
            if (nullable && !t.IsValueType && r.Next(8) == 0) return null;
            // an object already made for this call, so that aliasing (a list added to itself, an array copied onto itself) is tried
            if (!t.IsValueType && t != typeof(string) && t != typeof(object) && r.Next(4) == 0 && pool.FirstOrDefault(t.IsInstanceOfType) is object again) return again;
            object made;
            if (t == typeof(string)) made = name == "key" ? Keys[r.Next(Keys.Length)] : Strings[r.Next(Strings.Length)];
            else if (t == typeof(object)) made = r.Next(2) == 0 ? (object)SmallInt(r) : Strings[r.Next(Strings.Length)];
            else if (t == typeof(object[])) made = Enumerable.Range(0, r.Next(4)).Select(_ => (object)SmallInt(r)).ToArray();
            else if (t == typeof(int[]) || t == typeof(IEnumerable<int>) && r.Next(2) == 0) made = Enumerable.Range(0, r.Next(9)).Select(_ => SmallInt(r)).ToArray();
            else if (t == typeof(char[])) made = Enumerable.Range(0, r.Next(9)).Select(_ => Chars[r.Next(Chars.Length)]).ToArray();
            else if (t == typeof(Array)) made = r.Next(3) == 0 ? (Array)Enumerable.Range(0, r.Next(9)).Select(_ => (long)SmallInt(r)).ToArray()
                                                                : Enumerable.Range(0, r.Next(9)).Select(_ => SmallInt(r)).ToArray();
            else if (t == typeof(List<int>) || t == typeof(IEnumerable<int>)) made = Enumerable.Range(0, r.Next(9)).Select(_ => SmallInt(r)).ToList();
            else if (t == typeof(Dictionary<string, int>))
            {
                var d = new Dictionary<string, int>();
                foreach (var k in Keys) if (r.Next(2) == 0) d[k] = SmallInt(r);
                made = d;
            }
            else if (t == typeof(StringBuilder)) made = new StringBuilder(Strings[r.Next(Strings.Length)]);
            else if (t == typeof(HashSet<int>)) made = new HashSet<int>(Enumerable.Range(0, r.Next(6)).Select(_ => SmallInt(r)));
            else if (t == typeof(Stack<int>)) made = new Stack<int>(Enumerable.Range(0, r.Next(6)).Select(_ => SmallInt(r)));
            else if (t == typeof(Queue<int>)) made = new Queue<int>(Enumerable.Range(0, r.Next(6)).Select(_ => SmallInt(r)));
            else if (t == typeof(TextWriter)) made = new StringWriter();
            else if (t == typeof(System.Text.Encoding)) made = new[] { System.Text.Encoding.UTF8, System.Text.Encoding.Latin1, System.Text.Encoding.ASCII }[r.Next(3)];
            else if (t.IsEnum) { var values = Enum.GetValues(t); return values.GetValue(r.Next(values.Length)); }
            else if (t == typeof(byte[])) made = Enumerable.Range(0, r.Next(9)).Select(_ => (byte)r.Next(256)).ToArray();
            else if (t == typeof(Stream)) made = new MemoryStream(Enumerable.Range(0, r.Next(12)).Select(_ => (byte)r.Next(256)).ToArray());
            else throw new NotSupportedException(t.ToString());
            pool.Add(made);
            return made;
        }

        private static string Show(object[] args) => string.Join(", ", args.Select(Show));

        private static string Show(object a) => a switch
        {
            null => "null",
            string s => "\"" + s + "\"",
            char c => "'" + c + "'",
            StringBuilder sb => "StringBuilder(\"" + sb + "\")",
            IDictionary d => "{" + string.Join(", ", d.Keys.Cast<object>().Select(k => k + ": " + d[k])) + "}",
            IEnumerable e => a.GetType().Name + "[" + string.Join(", ", e.Cast<object>().Select(Show)) + "]",
            _ => a.ToString(),
        };
    }
}
