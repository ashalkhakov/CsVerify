using System.IO;
using System.Linq;
using CsVerify.Verifier;
using Xunit;

namespace CsVerify.Tests
{
    /// <summary>
    /// The Boogie engine (docs/boogie.md): on every method it verifies, it reports what CsVerify's own engine does (each
    /// diagnostic's id and line), and what it doesn't translate is verified as always.
    /// </summary>
    public class BoogieEngineTests
    {
        // (written for these tests: one of each construct the translation covers, and a bug of each kind it checks)
        private const string Corpus = @"
public static class A
{
    public static int Abs(int x) { Spec.Requires(x > int.MinValue); Spec.Ensures<int>(r => r >= 0 && (r == x || r == -x)); if (x < 0) return -x; return x; }
    public static int Sum(int n)
    {
        Spec.Requires(0 <= n && n <= 1000);
        Spec.Ensures<int>(r => r == n * (n + 1) / 2);
        int s = 0, i = 0;
        while (i < n) { Spec.Invariant(0 <= i && i <= n && s == i * (i + 1) / 2); i++; s += i; }
        return s;
    }
    public static long Wide(int x) { Spec.Ensures<long>(r => r == 2L * x); long y = x; return y + y; }
    public static int Twice(int x) { Spec.Requires(x > -1000 && x < 1000); Spec.Ensures<int>(r => r == 2 * x); return x + x; }
    public static int UseAbs(int y) { Spec.Ensures<int>(r => r >= 0); return Abs(y); }
    public static int UseAbsSafely(int y) { Spec.Ensures<int>(r => r >= 0); return y == int.MinValue ? 0 : Abs(y); }
    public static bool Between(int a, int b, int c) { Spec.Ensures<bool>(r => r == (a <= b && b <= c)); return a <= b && b <= c; }
    public static int Checked(int x) { Spec.Ensures<int>(r => r == x + 1); return checked(x + 1); }
    public static int Truncates(int a) { Spec.Requires(a == -7); Spec.Ensures<int>(r => r == -3); return a / 2; }
    public static int Remainder(int a) { Spec.Requires(a == -7); Spec.Ensures<int>(r => r == -1); return a % 2; }
    public static int Overflows(int x) => x + 1;
    public static int Div(int a, int b) => a / b;
    public static void Assertion(int x) { Spec.Requires(x > 3); Spec.Assert(x > 4); }
    public static int BadInv(int n) { Spec.Requires(n >= 0 && n < 100); int i = 0; while (i < n) { Spec.Invariant(i < n); i++; } return i; }
    public static int BadPost(int x) { Spec.Ensures<int>(r => r > x); return x; }
    public static int Elsewhere(string s) { Spec.Requires(s.Length > 0); return s.Length; }
    public static void Fill(int[] a, int v) { Spec.Ensures(Spec.Forall(0, a.Length, k => a[k] == v)); for (int i = 0; i < a.Length; i++) { Spec.Invariant(0 <= i && i <= a.Length && Spec.Forall(0, i, k => a[k] == v)); a[i] = v; } }
    public static int First(int[] a) { Spec.Requires(a.Length > 0); return a[0]; }
    public static int FirstBad(int[] a) => a[0];
    public static int KeepsOwn(int[] a) { Spec.Requires(a.Length > 0); var b = new int[1]; b[0] = 5; Fill(a, 3); Spec.Assert(b[0] == 5); return b[0]; }
    public static void WfBad(int[] a) { Spec.Requires(a[0] > 0); }
    public static int Wraps(int x) { Spec.Ensures<int>(r => x != int.MaxValue || r == int.MinValue); return unchecked(x + 1); }
    public static int Read(int[] a, int i) { Spec.Requires(0 <= i && i < a.Length); Spec.Ensures<int>(r => r == a[i]); return a[i]; }
    public static void CallNull() { int[]? n = null; First(n!); }
    public static int[] Make(int n) { Spec.Requires(n >= 0); Spec.Ensures<int[]>(r => r.Length == n); return new int[n]; }
    public static int Digit(char c) { Spec.Requires('0' <= c && c <= '9'); Spec.Ensures<int>(r => 0 <= r && r <= 9); return c - '0'; }
    public static byte Low(int x) => (byte)x;
    public static byte LowChecked(int x) { Spec.Ensures<byte>(r => r == x); return checked((byte)x); }
    public static byte LowWraps(int x) { Spec.Requires(x == 257); Spec.Ensures<byte>(r => r == 1); return unchecked((byte)x); }
    public static uint TwiceU(uint u) => u * 2;
    public static short Neg(short s) { Spec.Ensures<short>(r => r == -s); return (short)-s; }
    [Pure] public static int Max(int a, int b) => a > b ? a : b;
    [GhostFunction] public static int Fact(int n) { Spec.Requires(n >= 0); Spec.Decreases(n); return n == 0 ? 1 : n * Fact(n - 1); }
    public static int UseMax(int x) { Spec.Ensures<int>(r => r == Max(x, 0)); return x > 0 ? x : 0; }
    public static void UnfoldsOnce() { Spec.Assert(Fact(3) == 6); }
    public static void OutsideTheDomain() { Spec.Assert(Fact(-1) == 1); }
    [GhostFunction] public static int Up(int n) { Spec.Decreases(n); return n <= 0 ? 0 : Up(n + 1); }
    [Pure] public static int NoMeasure(int n) => n <= 0 ? 0 : NoMeasure(n - 1);
    public static int CountDown(int n) { Spec.Requires(n >= 0); int i = n; while (i > 0) { Spec.Decreases(i); i--; } return i; }
    public static int Stuck(int n) { Spec.Requires(n >= 0); int i = n; while (i > 0) { Spec.Decreases(i); if (n > 5) i--; } return i; }
    public static bool Has(int[] a, int v) { Spec.Ensures<bool>(r => !r || Spec.Exists(0, a.Length, k => a[k] == v)); for (int i = 0; i < a.Length; i++) { Spec.Invariant(0 <= i && i <= a.Length); if (a[i] == v) return true; } return false; }
}";

        private static (VerificationResult csverify, VerificationResult boogie) Both(System.Func<VerifierOptions, VerificationResult> run)
        {
            var c = run(new VerifierOptions());
            var b = run(new VerifierOptions { Engine = "boogie" });
            return (c, b);
        }

        private static string[] Reported(MethodResult m) =>
            m.Diagnostics.Where(d => d.IsError).Select(d => d.Id + "@" + d.Line).OrderBy(x => x).ToArray();

        /// <summary>Each method Boogie verified reports what CsVerify's engine reports for it.</summary>
        private static int Agree(VerificationResult csverify, VerificationResult boogie)
        {
            int byBoogie = 0;
            foreach (var m in boogie.Methods.Where(m => m.Engine == "boogie"))
            {
                byBoogie++;
                var other = csverify.Methods.Single(x => x.Name == m.Name);
                Assert.True(Reported(other).SequenceEqual(Reported(m)),
                    $"{m.Name}: CsVerify's engine reports [{string.Join(", ", Reported(other))}], Boogie [{string.Join(", ", Reported(m))}]\n" +
                    string.Join("\n", m.Diagnostics.Concat(other.Diagnostics)));
            }
            return byBoogie;
        }

        [Fact]
        public void Corpus_BothEnginesReportTheSame()
        {
            var (c, b) = Both(o => Engine.VerifySources(new[] { ("Test.cs", Harness.Usings + Corpus) }, o));
            Assert.Equal(40, Agree(c, b));
            foreach (var bug in new[] { "UseAbs", "Overflows", "Div", "Assertion", "BadInv", "BadPost", "FirstBad", "KeepsOwn", "WfBad", "CallNull",
                                        "Low", "TwiceU", "Neg", "UnfoldsOnce", "OutsideTheDomain", "Up", "NoMeasure", "Stuck" })
                Assert.False(b["A." + bug].Verified, bug);
            foreach (var good in new[] { "Abs", "Sum", "Wide", "Twice", "UseAbsSafely", "Between", "Checked", "Truncates", "Remainder", "Fill", "First", "Wraps", "Read", "Make", "Has",
                                         "Digit", "LowChecked", "LowWraps", "Max", "Fact", "UseMax", "CountDown" })
                Assert.True(b["A." + good].Verified, good);
        }

        [Fact]
        public void WhatIsntTranslated_IsVerifiedAsAlways()
        {
            var r = Engine.VerifySources(new[] { ("Test.cs", Harness.Usings + Corpus) }, new VerifierOptions { Engine = "boogie" });
            Assert.Equal("csverify", r["A.Elsewhere"].Engine);
            Assert.True(r["A.Elsewhere"].Verified);
        }

        [Fact]
        public void Samples_BothEnginesReportTheSame()
        {
            foreach (var dir in new[] { "Good", "Buggy" })
            {
                var files = Directory.GetFiles(Path.Combine(Harness.RepoRoot(), "samples", dir), "*.cs");
                // (Boogie's methods, then those alone by CsVerify's engine)
                var b = Engine.VerifyFiles(files, new VerifierOptions { Engine = "boogie-only" });
                var only = new VerifierOptions();
                only.Only.AddRange(b.Methods.Select(m => m.Name));
                var c = Engine.VerifyFiles(files, only);
                Assert.True(Agree(c, b) > 0, dir + ": no method went to Boogie");
            }
        }
    }
}
