using System;
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
    /// LINQ's definitions (the [Comprehensions] classes of the Spec library, Bcl/Linq.cs) are what the verifier reads
    /// LINQ as, so a wrong one makes wrong things provable. This runs each against the member it defines, on random
    /// sources and a menu of lambdas: the definition (copied, with CsVerify.Q, which runs) and the real member must
    /// agree on what they give, element by element; where the definition's Spec.Requires does not hold, the member
    /// must throw, and where it holds the member must not; its Spec.Ensures must hold of the member's result. A
    /// definition that only gives a precondition (throw null!) is checked for that alone. Type parameters are int.
    /// </summary>
    public class QueryConformanceTests
    {
        private const int Trials = 300;

        [Fact]
        public void Definitions_AgreeWithLinq()
        {
            var compilation = SpecCompilation();
            var stubs = ContractStubs.For(compilation);
            Assert.Empty(stubs.Errors.Select(e => e.message));
            var pairs = stubs.QueryPairs.OrderBy(p => p.query.ContainingType.Name, StringComparer.Ordinal).ThenBy(p => p.query.ToDisplayString(), StringComparer.Ordinal).ToList();
            Assert.True(pairs.Count >= 100, $"only {pairs.Count} definitions found");
            var failures = Run(compilation, pairs);
            Assert.True(failures.Count == 0, $"{failures.Count} of {pairs.Count} definitions disagree with LINQ:\n" + string.Join("\n", failures));
        }

        /// <summary>The checks catch wrong definitions: each of these is wrong in its own way.</summary>
        [Fact]
        public void WrongDefinitions_AreCaught()
        {
            const string wrong = @"
#nullable enable
namespace Wrong
{
    using System;
    using System.Collections.Generic;
    using System.Linq;
    using CsVerify;

    [ContractsFor(typeof(Enumerable)), Comprehensions]
    public static class WrongQueries
    {
        // Where keeps the matches, not the others
        public static IEnumerable<T> Where<T>(IEnumerable<T> source, Func<T, bool> predicate) => Q.For(source, x => Q.If(!predicate(x), Q.Yield(x)));

        // Take of more than there are is all of them
        public static IEnumerable<T> Take<T>(IEnumerable<T> source, int count) => Q.For(Q.Range(0, Math.Max(count, 0)), i => Q.Yield(Q.At(source, i)));

        // First of an empty sequence throws
        public static T First<T>(IEnumerable<T> source) => Q.Count(source) > 0 ? Q.At(source, 0) : default!;

        // and Max is not less than every element
        public static int Max(IEnumerable<int> source)
        {
            Spec.Requires(Q.Count(source) > 0);
            Spec.Ensures<int>(r => Spec.Forall(0, Q.Count(source), i => r < Q.At(source, i)));
            throw null!;
        }
    }
}";
            var compilation = SpecCompilation(wrong);
            var pairs = ContractStubs.For(compilation).QueryPairs.Where(p => p.query.ContainingNamespace.Name == "Wrong").ToList();
            Assert.Equal(4, pairs.Count);
            var failures = string.Join("\n", Run(compilation, pairs));
            Assert.Contains("Where<TSource>(System.Collections.Generic.IEnumerable<TSource>, System.Func<TSource, bool>): gave", failures);
            Assert.Contains("Take<TSource>(System.Collections.Generic.IEnumerable<TSource>, int):", failures);
            Assert.Contains("First<TSource>(System.Collections.Generic.IEnumerable<TSource>): threw InvalidOperationException where the definition's precondition holds", failures);
            Assert.Contains("Max(System.Collections.Generic.IEnumerable<int>): an Ensures does not hold", failures);
        }

        // ------------------------------------------------------------------ running

        private static List<string> Run(Compilation compilation, List<(IMethodSymbol member, IMethodSymbol query)> pairs)
        {
            var code = new StringBuilder();
            code.AppendLine("#nullable disable");
            code.AppendLine("namespace CsVerify.Conformance");
            code.AppendLine("{");
            code.AppendLine("    using System; using System.Collections.Generic; using System.Linq; using CsVerify;");
            foreach (var klass in pairs.Select(p => p.query.ContainingType).Distinct<INamedTypeSymbol>(SymbolEqualityComparer.Default))
                code.AppendLine(ModelOf(klass));
            code.AppendLine("    public static class Checks");
            code.AppendLine("    {");
            var members = new List<string>();
            for (int i = 0; i < pairs.Count; i++)
            {
                var (member, query) = pairs[i];
                string check = CheckOf(i, member, query);
                members.Add(member.ToDisplayString());
                code.AppendLine(check ?? $"        public static string Check{i}(Random r) => \"no inputs for its parameters\";");
            }
            code.AppendLine("    }");
            code.AppendLine("}");

            var trees = new[]
            {
                CSharpSyntaxTree.ParseText(code.ToString(), new CSharpParseOptions(LanguageVersion.Latest), "checks.cs"),
                CSharpSyntaxTree.ParseText(File.ReadAllText(Path.Combine(Harness.RepoRoot(), "src", "CsVerify.Spec", "Query.cs")), new CSharpParseOptions(LanguageVersion.Latest), "Query.cs"),
                CSharpSyntaxTree.ParseText(Runtime, new CSharpParseOptions(LanguageVersion.Latest), "runtime.cs"),
            };
            var c = CSharpCompilation.Create("CsVerifyQueryConformance", trees, Engine.FrameworkReferences(),
                new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary, nullableContextOptions: NullableContextOptions.Disable));
            using var ms = new MemoryStream();
            var emit = c.Emit(ms);
            Assert.True(emit.Success, "the checks do not compile:\n" + string.Join("\n", emit.Diagnostics.Where(d => d.Severity == DiagnosticSeverity.Error)));
            var checks = Assembly.Load(ms.ToArray()).GetType("CsVerify.Conformance.Checks");

            var failures = new List<string>();
            for (int i = 0; i < pairs.Count; i++)
            {
                var method = checks.GetMethod("Check" + i);
                var random = new Random(7919 * i + 1);
                for (int trial = 0; trial < Trials; trial++)
                {
                    string outcome;
                    try { outcome = (string)method.Invoke(null, new object[] { random }); }
                    catch (TargetInvocationException e) { outcome = "the check threw " + e.InnerException; }
                    if (outcome != null)
                    {
                        failures.Add($"{members[i]}: {outcome}");
                        break;
                    }
                }
            }
            return failures;
        }

        /// <summary>A definition class as running code: its Requires throw Precondition, its Ensures are kept to check.</summary>
        private static string ModelOf(INamedTypeSymbol klass)
        {
            var decl = (ClassDeclarationSyntax)klass.DeclaringSyntaxReferences[0].GetSyntax();
            var model = (ClassDeclarationSyntax)new ToRunning().Visit(decl);
            model = model.WithAttributeLists(default).WithIdentifier(SyntaxFactory.Identifier(klass.Name + "Model"));
            return model.NormalizeWhitespace().ToFullString();
        }

        private sealed class ToRunning : CSharpSyntaxRewriter
        {
            public override SyntaxNode VisitExpressionStatement(ExpressionStatementSyntax node)
            {
                if (node.Expression is InvocationExpressionSyntax inv && inv.Expression is MemberAccessExpressionSyntax ma &&
                    ma.Expression.ToString() == "Spec")
                {
                    var arg = inv.ArgumentList.Arguments[0].Expression.ToString();
                    if (ma.Name.Identifier.Text == "Requires")
                        return SyntaxFactory.ParseStatement($"if (!({arg})) throw new global::CsVerify.Conformance.Precondition();");
                    if (ma.Name is GenericNameSyntax g && g.Identifier.Text == "Ensures")
                    {
                        var t = g.TypeArgumentList.Arguments[0].ToString();
                        return SyntaxFactory.ParseStatement($"global::CsVerify.Conformance.Run.Ensured.Add(__r => ((Func<{t}, bool>)({arg}))(({t})__r));");
                    }
                }
                return base.VisitExpressionStatement(node);
            }

            public override SyntaxNode VisitThrowStatement(ThrowStatementSyntax node) =>
                SyntaxFactory.ParseStatement("throw new global::CsVerify.Conformance.Unspecified();");
        }

        /// <summary>The check for one member: inputs for its parameters (type parameters int), the definition, the member.</summary>
        private static string CheckOf(int index, IMethodSymbol member, IMethodSymbol query)
        {
            bool receiver = ContractStubs.TakesReceiver(query);
            var body = new StringBuilder();
            var names = new List<string>();
            var modelArgs = new List<string>();
            var realArgs = new List<string>();
            foreach (var p in query.Parameters)
            {
                string n = "a" + p.Ordinal;
                string type = Substituted(p.Type);
                string make = type switch
                {
                    "System.Collections.Generic.IEnumerable<int>" => "In.Ints(r)",
                    "System.Collections.Generic.IEnumerable<long>" => "In.Longs(r)",
                    "System.Collections.Generic.IEnumerable<double>" => "In.Doubles(r)",
                    "System.Collections.Generic.List<int>" => "In.Ints(r).ToList()",
                    "int[]" => "In.Ints(r).ToArray()",
                    "int" => "In.Int(r)",
                    "System.Func<int, bool>" => "In.Test(r, __shown)",
                    "System.Predicate<int>" => "new Predicate<int>(In.Test(r, __shown))",
                    "System.Func<int, int>" => "In.Map(r, __shown)",
                    "System.Func<int, int, int>" => "In.Map2(r, __shown)",
                    "System.Func<int, System.Collections.Generic.IEnumerable<int>>" => "In.Many(r, __shown)",
                    "System.Func<int, System.Collections.Generic.IEnumerable<int>, int>" => "In.OfGroup(r, __shown)",
                    "System.Func<int, long>" => "In.ToLong(r, __shown)",
                    "System.Func<int, double>" => "In.ToDouble(r, __shown)",
                    "System.Func<int, int, bool>" => "In.Test2(r, __shown)",
                    "System.Func<int, int, System.Collections.Generic.IEnumerable<int>>" => "In.Many2(r, __shown)",
                    "System.Linq.IOrderedEnumerable<int>" => null,
                    _ => "",
                };
                if (make == "") return null;
                if (make == null)
                {
                    // a sort: Q.Sort for the definition, the real OrderBy for the member, of the same list and key
                    body.AppendLine($"            var {n}base = In.Ints(r); var {n}key = In.Map(r, __shown); bool {n}down = r.Next(2) == 0;");
                    body.AppendLine($"            __shown.Add(\"source \" + In.Show({n}base) + ({n}down ? \", descending\" : \"\"));");
                    modelArgs.Add($"global::CsVerify.Q.Sort({n}base, {n}key, {n}down)");
                    realArgs.Add($"({n}down ? Enumerable.OrderByDescending({n}base, {n}key) : Enumerable.OrderBy({n}base, {n}key))");
                    continue;
                }
                body.AppendLine($"            var {n} = {make};");
                if (!type.StartsWith("System.Func") && !type.StartsWith("System.Predicate")) body.AppendLine($"            __shown.Add(In.Show({n}));");
                modelArgs.Add(n);
                realArgs.Add(n);
            }
            string typeArgs = query.TypeParameters.Length > 0 ? "<" + string.Join(", ", query.TypeParameters.Select(_ => "int")) + ">" : "";
            string klass = query.ContainingType.Name + "Model" + (query.ContainingType.TypeParameters.Length > 0 ? "<int>" : "");
            string modelCall = $"{klass}.{query.Name}{typeArgs}({string.Join(", ", modelArgs)})";
            string realCall = receiver
                ? $"{realArgs[0]}.{member.Name}({string.Join(", ", realArgs.Skip(1))})"
                : $"Enumerable.{member.Name}{typeArgs}({string.Join(", ", realArgs)})";
            var sb = new StringBuilder();
            sb.AppendLine($"        public static string Check{index}(Random r)");
            sb.AppendLine("        {");
            sb.AppendLine("            var __shown = new List<string>();");
            sb.Append(body);
            sb.AppendLine($"            return Run.Compare(() => {modelCall}, () => {realCall}, __shown);");
            sb.AppendLine("        }");
            return sb.ToString();
        }

        private static string Substituted(ITypeSymbol t) => t switch
        {
            ITypeParameterSymbol _ => "int",
            IArrayTypeSymbol a => Substituted(a.ElementType) + "[]",
            INamedTypeSymbol n when n.TypeArguments.Length > 0 =>
                n.ContainingNamespace.ToDisplayString() + "." + n.Name + "<" + string.Join(", ", n.TypeArguments.Select(Substituted)) + ">",
            _ => t.ToDisplayString(),
        };

        private static CSharpCompilation SpecCompilation(string more = null)
        {
            var dir = Path.Combine(Harness.RepoRoot(), "src", "CsVerify.Spec");
            var parse = new CSharpParseOptions(LanguageVersion.Latest, preprocessorSymbols: new[] { "CSVERIFY_SPEC" });
            var trees = Directory.GetFiles(dir, "*.cs", SearchOption.AllDirectories)
                .Where(f => !f.Contains(Path.DirectorySeparatorChar + "obj" + Path.DirectorySeparatorChar) &&
                            !f.Contains(Path.DirectorySeparatorChar + "bin" + Path.DirectorySeparatorChar) &&
                            !f.Contains(Path.DirectorySeparatorChar + "Ef" + Path.DirectorySeparatorChar)) // (EF Core's model: EfConformanceTests)
                .Select(f => CSharpSyntaxTree.ParseText(File.ReadAllText(f), parse, "<CsVerify.Spec>/" + Path.GetRelativePath(dir, f))).ToList();
            if (more != null) trees.Add(CSharpSyntaxTree.ParseText(more, parse, "more.cs"));
            var c = CSharpCompilation.Create("CsVerifySpec", trees, Engine.FrameworkReferences(),
                new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary, nullableContextOptions: NullableContextOptions.Enable));
            Assert.Empty(c.GetDiagnostics().Where(d => d.Severity == DiagnosticSeverity.Error).Select(d => d.ToString()));
            return c;
        }

        /// <summary>
        /// What the definitions use at run time (Spec's quantifiers and equality, ghost values), the inputs, and the
        /// comparison of a definition's outcome with the member's.
        /// </summary>
        private const string Runtime = @"
#nullable disable
namespace CsVerify
{
    using System; using System.Collections.Generic;

    public static class Spec
    {
        public static bool Forall(int lo, int hi, Func<int, bool> p) { for (int i = lo; i < hi; i++) if (!p(i)) return false; return true; }
        public static bool Exists(int lo, int hi, Func<int, bool> p) { for (int i = lo; i < hi; i++) if (p(i)) return true; return false; }
        public static bool Equal<T>(Ghost<T> a, Ghost<T> b) => EqualityComparer<T>.Default.Equals(a.V, b.V);
    }

    public readonly struct Ghost<T>
    {
        public readonly T V;
        public Ghost(T v) { V = v; }
    }

    public static class Ghost
    {
        public static Ghost<T> Of<T>(T v) => new Ghost<T>(v);
    }
}

namespace CsVerify.Conformance
{
    using System; using System.Collections; using System.Collections.Generic; using System.Linq;

    public sealed class Precondition : Exception { }
    public sealed class Unspecified : Exception { }

    public static class Run
    {
        [ThreadStatic] private static List<Func<object, bool>> _ensured;
        public static List<Func<object, bool>> Ensured => _ensured ??= new List<Func<object, bool>>();

        /// <summary>A result as a value: sequences enumerated (a group with its key), so that comparing compares them.</summary>
        private static object Force(object o)
        {
            if (o is string || !(o is IEnumerable e)) return o;
            var key = o.GetType().GetInterfaces().FirstOrDefault(i => i.IsGenericType && i.GetGenericTypeDefinition() == typeof(IGrouping<,>))?.GetProperty(""Key"")?.GetValue(o);
            var items = e.Cast<object>().Select(Force).ToList();
            return key != null ? (object)(key, items) : items;
        }

        public static string Compare(Func<object> model, Func<object> real, List<string> shown)
        {
            Ensured.Clear();
            object m = null, v = null;
            bool holds = true, unspecified = false;
            Exception mx = null, rx = null;
            try { m = Force(model()); }
            catch (Precondition) { holds = false; }
            catch (Unspecified) { unspecified = true; }
            catch (Exception e) { mx = e; }
            var ensured = Ensured.ToList();
            try { v = Force(real()); }
            catch (Exception e) { rx = e; }
            string on = ""on ("" + string.Join(""; "", shown) + "")"";
            if (mx != null) return ""the definition threw "" + mx.GetType().Name + "" "" + on + "": "" + mx.Message;
            if (!holds) return rx != null ? null : ""returned "" + In.Show(v) + "" where the definition's precondition does not hold, "" + on;
            if (rx != null) return ""threw "" + rx.GetType().Name + "" where the definition's precondition holds, "" + on;
            foreach (var e in ensured) if (!e(v)) return ""an Ensures does not hold of "" + In.Show(v) + "", "" + on;
            if (!unspecified && In.Show(m) != In.Show(v)) return ""gave "" + In.Show(v) + "", the definition "" + In.Show(m) + "", "" + on;
            return null;
        }
    }

    public static class In
    {
        private static int Small(Random r) => r.Next(10) < 8 ? r.Next(-3, 9) : r.Next(-5, 20);

        public static int Int(Random r) => Small(r);

        public static IEnumerable<int> Ints(Random r)
        {
            var a = new int[r.Next(7)];
            for (int i = 0; i < a.Length; i++)
                a[i] = r.Next(12) == 0 ? new[] { int.MaxValue, int.MinValue, int.MaxValue - 1 }[r.Next(3)] : Small(r);
            return r.Next(2) == 0 ? (IEnumerable<int>)a : a.ToList();
        }

        public static IEnumerable<long> Longs(Random r) => Ints(r).Select(x => r.Next(10) == 0 ? long.MaxValue : (long)x).ToList();

        // with NaN, the infinities, -0.0, fractions (sums that round) and a near overflow
        private static readonly double[] Odd = { double.NaN, double.PositiveInfinity, double.NegativeInfinity, -0.0, 0.1, 0.3, 1e308, -1e308 };
        public static IEnumerable<double> Doubles(Random r)
        {
            var a = Ints(r).Select(x => r.Next(6) == 0 ? Odd[r.Next(Odd.Length)] : (double)x).ToList();
            if (r.Next(8) == 0) a = a.Select(_ => -0.0).ToList();
            return r.Next(2) == 0 ? (IEnumerable<double>)a : a.ToArray();
        }

        private static readonly (string, Func<int, bool>)[] Tests =
            { (""x > 0"", x => x > 0), (""x % 2 == 0"", x => x % 2 == 0), (""true"", x => true), (""false"", x => false), (""x < 3"", x => x < 3) };
        private static readonly (string, Func<int, int>)[] Maps =
            { (""x"", x => x), (""x % 3"", x => x % 3), (""-x"", x => unchecked(-x)), (""x / 2"", x => x / 2), (""7"", x => 7) };
        private static readonly (string, Func<int, int, int>)[] Maps2 =
            { (""a - b"", (a, b) => unchecked(a - b)), (""a"", (a, b) => a), (""b"", (a, b) => b), (""a % 3 + b"", (a, b) => unchecked(a % 3 + b)) };
        private static readonly (string, Func<int, IEnumerable<int>>)[] Manys =
            { (""x => x, x + 1, .. (|x| % 3 of them)"", x => Enumerable.Range(0, Math.Abs(x % 3)).Select(k => unchecked(x + k)).ToArray()), (""none"", x => new List<int>()), (""[x]"", x => new[] { x }) };

        private static readonly (string, Func<int, long>)[] ToLongs =
            { (""x"", x => x), (""x * 2^40"", x => (long)x << 40), (""long.MaxValue"", x => long.MaxValue) };
        private static readonly (string, Func<int, double>)[] ToDoubles =
            { (""x"", x => x), (""x / 10.0"", x => x / 10.0), (""1.0 / x"", x => 1.0 / x), (""x == 0 ? NaN : x"", x => x == 0 ? double.NaN : x), (""-0.0"", x => -0.0) };
        private static readonly (string, Func<int, IEnumerable<int>, int>)[] OfGroups =
            { (""(k, g) => g.Count()"", (k, g) => g.Count()), (""(k, g) => k"", (k, g) => k), (""(k, g) => g.Any() ? g.First() : -1"", (k, g) => g.Any() ? g.First() : -1),
              (""(k, g) => k * 100 + g.Count(x => x > 0)"", (k, g) => unchecked(k * 100 + g.Count(x => x > 0))) };

        private static readonly (string, Func<int, int, bool>)[] Tests2 =
            { (""x > i"", (x, i) => x > i), (""i % 2 == 0"", (x, i) => i % 2 == 0), (""x > 0"", (x, i) => x > 0), (""i < 2"", (x, i) => i < 2) };
        private static readonly (string, Func<int, int, IEnumerable<int>>)[] Manys2 =
            { (""(x, i) => i of x"", (x, i) => Enumerable.Repeat(x, i % 3).ToArray()), (""(x, i) => [x, i]"", (x, i) => new[] { x, i }) };

        private static F Pick<F>(Random r, (string, F)[] menu, List<string> shown)
        {
            var (name, f) = menu[r.Next(menu.Length)];
            shown.Add(name);
            return f;
        }

        public static Func<int, bool> Test(Random r, List<string> shown) => Pick(r, Tests, shown);
        public static Func<int, int> Map(Random r, List<string> shown) => Pick(r, Maps, shown);
        public static Func<int, int, int> Map2(Random r, List<string> shown) => Pick(r, Maps2, shown);
        public static Func<int, IEnumerable<int>> Many(Random r, List<string> shown) => Pick(r, Manys, shown);
        public static Func<int, long> ToLong(Random r, List<string> shown) => Pick(r, ToLongs, shown);
        public static Func<int, double> ToDouble(Random r, List<string> shown) => Pick(r, ToDoubles, shown);
        public static Func<int, int, bool> Test2(Random r, List<string> shown) => Pick(r, Tests2, shown);
        public static Func<int, int, IEnumerable<int>> Many2(Random r, List<string> shown) => Pick(r, Manys2, shown);
        public static Func<int, IEnumerable<int>, int> OfGroup(Random r, List<string> shown) => Pick(r, OfGroups, shown);

        public static string Show(object o) => o switch
        {
            null => ""null"",
            ValueTuple<object, List<object>> g => Show(g.Item1) + "": "" + Show(g.Item2),
            string s => ""\"""" + s + ""\"""",
            double d => d.ToString(""R"", System.Globalization.CultureInfo.InvariantCulture),
            IEnumerable e => ""["" + string.Join("", "", e.Cast<object>().Select(Show)) + ""]"",
            _ => o.ToString(),
        };
    }
}";
    }
}
