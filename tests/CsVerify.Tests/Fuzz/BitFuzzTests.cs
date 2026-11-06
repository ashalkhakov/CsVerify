using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.Text;
using CsVerify.Verifier;
using Xunit;
using Xunit.Abstractions;

namespace CsVerify.Tests.Fuzz
{
    /// <summary>
    /// Bitwise operators with known answers: random expressions over parameters pinned to constants (the compiler cannot
    /// fold those), with the answer worked out here by C#'s own operators. A fact must verify and its negation must not.
    /// CSVERIFY_FUZZ_SEEDS=from..to runs more.
    /// </summary>
    public class BitFuzzTests
    {
        private readonly ITestOutputHelper _out;
        public BitFuzzTests(ITestOutputHelper output) { _out = output; }

        /// <summary>An integer type: how to write its values, and its operators.</summary>
        private sealed class Kind
        {
            public string Name, Suffix;
            public Func<long, object> Make;
            public Func<object, object, string, object> Op;
            public Func<object, int, string, object> Shift;
            public Func<object, object> Not;
        }

        private static readonly Kind[] Kinds =
        {
            new Kind
            {
                Name = "int", Suffix = "", Make = v => unchecked((int)v),
                Op = (a, b, o) => o == "&" ? (int)a & (int)b : o == "|" ? (int)a | (int)b : (int)a ^ (int)b,
                Shift = (a, n, o) => o == "<<" ? (int)a << n : o == ">>" ? (int)a >> n : (int)a >>> n,
                Not = a => ~(int)a,
            },
            new Kind
            {
                Name = "uint", Suffix = "u", Make = v => unchecked((uint)v),
                Op = (a, b, o) => o == "&" ? (uint)a & (uint)b : o == "|" ? (uint)a | (uint)b : (uint)a ^ (uint)b,
                Shift = (a, n, o) => o == "<<" ? (uint)a << n : o == ">>" ? (uint)a >> n : (uint)a >>> n,
                Not = a => ~(uint)a,
            },
            new Kind
            {
                Name = "long", Suffix = "L", Make = v => v,
                Op = (a, b, o) => o == "&" ? (long)a & (long)b : o == "|" ? (long)a | (long)b : (long)a ^ (long)b,
                Shift = (a, n, o) => o == "<<" ? (long)a << n : o == ">>" ? (long)a >> n : (long)a >>> n,
                Not = a => ~(long)a,
            },
            new Kind
            {
                Name = "ulong", Suffix = "UL", Make = v => unchecked((ulong)v),
                Op = (a, b, o) => o == "&" ? (ulong)a & (ulong)b : o == "|" ? (ulong)a | (ulong)b : (ulong)a ^ (ulong)b,
                Shift = (a, n, o) => o == "<<" ? (ulong)a << n : o == ">>" ? (ulong)a >> n : (ulong)a >>> n,
                Not = a => ~(ulong)a,
            },
        };

        private static string Lit(object v, Kind k)
        {
            var s = v.ToString();
            return s.StartsWith("-") ? $"({s}{k.Suffix})" : s + k.Suffix;
        }

        private sealed class Check { public string Parameters, Requires, True, False; }

        private sealed class Generator
        {
            private readonly Random _r;
            private Kind _k;
            private object _p, _q;
            private int _n;
            public Generator(int seed) { _r = new Random(seed); }

            private long Interesting()
            {
                switch (_r.Next(6))
                {
                    case 0: return _r.Next(0, 16);
                    case 1: return _r.Next(0, 256);
                    case 2: return -_r.Next(1, 256);
                    case 3: return 1L << _r.Next(63);
                    case 4: return (1L << _r.Next(1, 63)) - 1;
                    default: return _r.NextInt64(long.MinValue, long.MaxValue);
                }
            }

            private (string text, object value) Expr(int depth)
            {
                if (depth <= 0 || _r.Next(4) == 0)
                    switch (_r.Next(3))
                    {
                        case 0: return ("p", _p);
                        case 1: return ("q", _q);
                        default: { var v = _k.Make(Interesting()); return (Lit(v, _k), v); }
                    }
                var a = Expr(depth - 1);
                switch (_r.Next(5))
                {
                    case 0: return ($"(~{a.text})", _k.Not(a.value));
                    case 1:
                    case 2:
                    {
                        var o = new[] { "<<", ">>", ">>>" }[_r.Next(3)];
                        if (_r.Next(4) == 0) return ($"({a.text} {o} n)", _k.Shift(a.value, _n, o));
                        // (counts past the width and negative ones too: they are taken modulo the width)
                        int count = _r.Next(5) == 0 ? _r.Next(-70, 70) : _r.Next(0, 16);
                        return ($"({a.text} {o} {(count < 0 ? $"({count})" : count.ToString())})", _k.Shift(a.value, count, o));
                    }
                    default:
                    {
                        var o = new[] { "&", "|", "^" }[_r.Next(3)];
                        var b = Expr(depth - 1);
                        return ($"({a.text} {o} {b.text})", _k.Op(a.value, b.value, o));
                    }
                }
            }

            public Check Next()
            {
                _k = Kinds[_r.Next(Kinds.Length)];
                _p = _k.Make(Interesting());
                _q = _k.Make(Interesting());
                _n = _r.Next(-5, 70);
                var (text, value) = Expr(3);
                var fact = $"{text} == {Lit(value, _k)}";
                return new Check
                {
                    Parameters = $"{_k.Name} p, {_k.Name} q, int n",
                    Requires = $"p == {Lit(_p, _k)} && q == {Lit(_q, _k)} && n == {(_n < 0 ? $"({_n})" : _n.ToString())}",
                    True = fact,
                    False = $"!({fact})",
                };
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
            int facts = 0, verified = 0, rejected = 0;
            var problems = new List<string>();
            var unproved = new List<string>();
            var (from, to) = Seeds();
            for (int seed = from; seed <= to; seed++)
            {
                var gen = new Generator(seed);
                var checks = Enumerable.Range(0, PerSeed).Select(_ => gen.Next()).ToList();
                var sb = new StringBuilder("#nullable enable\nusing System; using CsVerify;\npublic static class S {\n");
                for (int i = 0; i < checks.Count; i++)
                {
                    var c = checks[i];
                    sb.Append($"static void K{i}T({c.Parameters}) {{ Spec.Requires({c.Requires}); Spec.Assert({c.True}); }}\n");
                    sb.Append($"static void K{i}F({c.Parameters}) {{ Spec.Requires({c.Requires}); Spec.Assert({c.False}); }}\n");
                }
                sb.Append("}\n");
                var result = Engine.VerifySources(new[] { ($"bits{seed}.cs", sb.ToString()) }, new VerifierOptions { CheckOverflow = true, TimeoutMs = 2000 });
                Assert.True(result.CompilationErrors.Count == 0, string.Join("\n", result.CompilationErrors.Take(5)));
                bool Verified(string name) => result.Methods.First(r => r.Name == "S." + name).Verified;
                foreach (var r in result.Methods)
                    foreach (var d in r.Diagnostics.Where(d => d.Id == "CSV1999"))
                        problems.Add($"seed {seed}, {r.Name}: internal error: {d.Message}");
                for (int i = 0; i < checks.Count; i++)
                {
                    var c = checks[i];
                    facts++;
                    if (Verified($"K{i}T")) verified++;
                    else unproved.Add($"seed {seed}, K{i}: {c.Parameters}: {c.Requires}: {c.True}");
                    if (!Verified($"K{i}F")) rejected++;
                    else problems.Add($"seed {seed}, K{i}: verified the false {c.Parameters}: {c.Requires}: {c.False}");
                }
            }
            _out.WriteLine($"{verified} of {facts} facts verified; {rejected} of {facts} false ones rejected; {problems.Count} problem(s)");
            foreach (var u in unproved.Take(10)) _out.WriteLine("not proved: " + u);
            Assert.True(problems.Count == 0, string.Join("\n", problems.Take(10)));
            Assert.True(verified * 10 >= facts * 9, $"only {verified} of {facts} facts verified:\n" + string.Join("\n", unproved.Take(10)));
        }
    }
}
