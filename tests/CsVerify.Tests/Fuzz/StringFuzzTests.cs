using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using CsVerify.Verifier;
using Xunit;
using Xunit.Abstractions;

namespace CsVerify.Tests.Fuzz
{
    /// <summary>
    /// Strings with known answers. Each check is a small method of its own: random string expressions over parameters
    /// pinned to constants (the compiler cannot fold those, as it would two literals), with the answer worked out here in
    /// .NET. A fact must verify and its negation must not, so a wrong model of characters shows at once. In the random
    /// programs of <see cref="VerifierFuzzTests"/> it mostly would not: a method there often fails to verify for other reasons.
    /// CSVERIFY_FUZZ_SEEDS=from..to runs more.
    /// </summary>
    public class StringFuzzTests
    {
        private readonly ITestOutputHelper _out;
        public StringFuzzTests(ITestOutputHelper output) { _out = output; }

        private static readonly string[] Pieces = { "", "a", "b", "ab", "ba", "abc", "aba", "0l" };
        private const string Letters = "ab0lz";

        private sealed class Check { public string Requires, True, False, Template = "⟨A⟩"; }

        private sealed class Generator
        {
            private readonly Random _r;
            private string _p, _q;
            public Generator(int seed) { _r = new Random(seed); }

            private string Piece() => Pieces[_r.Next(Pieces.Length)];
            private static string Q(string x) => $"\"{x}\"";
            private static string C(char c) => $"'{c}'";

            /// <summary>An expression, with its value.</summary>
            private (string text, string value) Expr(int depth)
            {
                if (depth <= 0 || _r.Next(4) == 0)
                    switch (_r.Next(3))
                    {
                        case 0: return ("p", _p);
                        case 1: return ("q", _q);
                        default: { var lit = Piece(); return (Q(lit), lit); }
                    }
                var e = Expr(depth - 1);
                switch (_r.Next(3))
                {
                    case 0: { var f = Expr(depth - 1); return ($"({e.text} + {f.text})", e.value + f.value); }
                    case 1: { int start = _r.Next(e.value.Length + 1); return ($"{e.text}.Substring({start})", e.value.Substring(start)); }
                    default:
                    {
                        int start = _r.Next(e.value.Length + 1), length = _r.Next(e.value.Length - start + 1);
                        return ($"{e.text}.Substring({start}, {length})", e.value.Substring(start, length));
                    }
                }
            }

            private char Letter() => Letters[_r.Next(Letters.Length)];

            public Check Next()
            {
                _p = Piece();
                _q = Piece();
                var requires = $"p == {Q(_p)} && q == {Q(_q)}";
                var (e, v) = Expr(3);
                var c = Letter();
                string fact;
                switch (_r.Next(10))
                {
                    case 0: fact = $"{e}.Length == {v.Length}"; break;
                    case 1:
                    {
                        // (its own value, or another: strings that differ, also only in length)
                        var other = _r.Next(3) == 0 ? v : Piece();
                        fact = $"({e} == {Q(other)}) == {(v == other ? "true" : "false")}";
                        break;
                    }
                    case 2: fact = $"{e}.IndexOf({C(c)}) == {v.IndexOf(c)}"; break;
                    case 3: fact = $"{e}.LastIndexOf({C(c)}) == {v.LastIndexOf(c)}"; break;
                    case 4: fact = $"{e}.Contains({C(c)}) == {(v.Contains(c) ? "true" : "false")}"; break;
                    case 5: fact = $"{e}.StartsWith({C(c)}) == {(v.StartsWith(c) ? "true" : "false")}"; break;
                    case 6: fact = $"{e}.EndsWith({C(c)}) == {(v.EndsWith(c) ? "true" : "false")}"; break;
                    case 7:
                    {
                        var other = Piece();
                        fact = $"{e}.StartsWith({Q(other)}, StringComparison.Ordinal) == {(v.StartsWith(other, StringComparison.Ordinal) ? "true" : "false")}";
                        break;
                    }
                    case 8 when v.Length > 1 && v.Any(x => x != v[0]):
                    {
                        // a foreach: each iteration has its own character, so "always the first" is false
                        var type = _r.Next(2) == 0 ? "char" : "int";
                        return new Check
                        {
                            Requires = requires,
                            Template = $"var e = {e}; foreach ({type} ch in e) {{ ⟨A⟩ }}",
                            True = "ch == e[Spec.Index(ch)]",
                            False = $"ch == {C(v[0])}",
                        };
                    }
                    default:
                        if (v.Length == 0) goto case 0;
                        int at = _r.Next(v.Length);
                        fact = $"{e}[{at}] == {C(v[at])}";
                        break;
                }
                return new Check { Requires = requires, True = fact, False = $"!({fact})" };
            }
        }

        private static (int from, int to) Seeds()
        {
            var s = Environment.GetEnvironmentVariable("CSVERIFY_FUZZ_SEEDS");
            if (s != null && s.Split("..") is { Length: 2 } parts) return (int.Parse(parts[0]), int.Parse(parts[1]));
            return (1, 3);
        }

        [Fact]
        public void KnownAnswers_TheFactVerifies_ItsNegationDoesNot()
        {
            const int PerSeed = 40;
            int facts = 0, verified = 0, planted = 0, rejected = 0;
            var problems = new List<string>();
            var unproved = new List<string>();
            var (from, to) = Seeds();
            for (int seed = from; seed <= to; seed++)
            {
                var gen = new Generator(seed);
                var checks = Enumerable.Range(0, PerSeed).Select(_ => gen.Next()).ToList();
                var sb = new StringBuilder("#nullable enable\nusing System; using CsVerify;\npublic static class S {\n");
                string Method(string name, Check c, string assertion) =>
                    $"static void {name}(string p, string q) {{ Spec.Requires({c.Requires}); {c.Template.Replace("⟨A⟩", $"Spec.Assert({assertion});")} }}\n";
                for (int i = 0; i < checks.Count; i++)
                {
                    sb.Append(Method($"K{i}T", checks[i], checks[i].True));
                    sb.Append(Method($"K{i}F", checks[i], checks[i].False));
                }
                sb.Append("}\n");
                var result = Engine.VerifySources(new[] { ($"strings{seed}.cs", sb.ToString()) }, new VerifierOptions { CheckOverflow = true, TimeoutMs = 2000 });
                Assert.True(result.CompilationErrors.Count == 0, string.Join("\n", result.CompilationErrors.Take(5)));
                bool Verified(string name) => result.Methods.First(r => r.Name == "S." + name).Verified;
                foreach (var r in result.Methods)
                    foreach (var d in r.Diagnostics.Where(d => d.Id == "CSV1999"))
                        problems.Add($"seed {seed}, {r.Name}: internal error: {d.Message}");
                for (int i = 0; i < checks.Count; i++)
                {
                    var c = checks[i];
                    facts++;
                    planted++;
                    if (Verified($"K{i}T")) verified++;
                    else unproved.Add($"seed {seed}, K{i}: {c.Requires}: {c.Template.Replace("⟨A⟩", c.True)}");
                    if (!Verified($"K{i}F")) rejected++;
                    else problems.Add($"seed {seed}, K{i}: verified the false {c.Requires}: {c.Template.Replace("⟨A⟩", c.False)}");
                }
            }
            _out.WriteLine($"{verified} of {facts} facts verified; {rejected} of {planted} false ones rejected; {problems.Count} problem(s)");
            foreach (var u in unproved.Take(10)) _out.WriteLine("not proved: " + u);
            Assert.True(problems.Count == 0, string.Join("\n", problems.Take(10)));
            // (with everything pinned, the verifier decides these: a fact it can't prove means a model too weak, or wrong)
            Assert.True(verified * 10 >= facts * 9, $"only {verified} of {facts} facts verified:\n" + string.Join("\n", unproved.Take(10)));
        }
    }
}
