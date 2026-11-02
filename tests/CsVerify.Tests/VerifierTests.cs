using System.IO;
using System.Linq;
using CsVerify.Verifier;
using Xunit;

namespace CsVerify.Tests
{
    /// <summary>Each feature has a proved case and a refuted case.</summary>
    public class VerifierTests
    {
        private static string[] Errors(string method, string source, bool overflow = false) =>
            Harness.Verify("public static class C { " + source + " }", overflow).Errors(method);

        // ---- arithmetic and booleans -------------------------------------------------------------------------

        [Fact]
        public void Arithmetic_Proved() => Assert.Empty(Errors("M",
            "static int M(int x, int y) { Spec.Requires(x >= 0 && y >= 0); Spec.Ensures<int>(r => r >= x && r >= y); return x + y; }"));

        [Fact]
        public void Arithmetic_Refuted() => Assert.Equal(new[] { "CSV1002" }, Errors("M",
            "static int M(int x, int y) { Spec.Ensures<int>(r => r >= x); return x + y; }"));

        [Fact]
        public void Booleans_AndBranches() => Assert.Empty(Errors("M",
            "static bool M(bool a, bool b) { Spec.Ensures<bool>(r => r == (a && !b)); if (b) return false; return a; }"));

        [Fact]
        public void DivisionTruncatesTowardZero() => Assert.Empty(Errors("M",
            "static int M() { Spec.Ensures<int>(r => r == -3); int x = -7; int y = 2; Spec.Assert(x % y == -1); return x / y; }"));

        [Fact]
        public void DivisionByZero_Refuted() => Assert.Equal(new[] { "CSV1009" }, Errors("M",
            "static int M(int x, int y) => x / y;"));

        [Fact]
        public void Overflow_OnlyWithFlag()
        {
            const string src = "static int M(int x) => x + 1;";
            Assert.Empty(Errors("M", src));
            Assert.Equal(new[] { "CSV1010" }, Errors("M", src, overflow: true));
            Assert.Empty(Errors("M", "static int M(int x) { Spec.Requires(x < int.MaxValue); return x + 1; }", overflow: true));
        }

        // ---- arrays and spans --------------------------------------------------------------------------------

        [Fact]
        public void ArrayBounds_Proved() => Assert.Empty(Errors("M",
            "static int M(int[] a, int i) { Spec.Requires(0 <= i && i < a.Length); return a[i]; }"));

        [Fact]
        public void ArrayBounds_Refuted() => Assert.Equal(new[] { "CSV1003" }, Errors("M",
            "static int M(int[] a, int i) { Spec.Requires(i < a.Length); return a[i]; }"));

        [Fact]
        public void ArrayWrite_ThenRead() => Assert.Empty(Errors("M",
            "static int M(int[] a) { Spec.Requires(a.Length > 2); Spec.Ensures<int>(r => r == 5); a[1] = 5; a[2] = 6; return a[1]; }"));

        [Fact]
        public void NewArray_HasLength() => Assert.Empty(Errors("M",
            "static int[] M(int n) { Spec.Requires(n > 0); Spec.Ensures<int[]>(r => r.Length == n && r[0] == 0); return new int[n]; }"));

        [Fact]
        public void SpanLength_AndIndex()
        {
            Assert.Empty(Errors("M", "static int M(Span<int> s) { Spec.Requires(s.Length > 0); return s[s.Length - 1]; }"));
            Assert.Equal(new[] { "CSV1003" }, Errors("M", "static int M(ReadOnlySpan<int> s) => s[0];"));
        }

        [Fact]
        public void Quantifiers() => Assert.Empty(Errors("M",
            "static int M(int[] a) { Spec.Requires(a.Length > 3 && Spec.Forall(0, a.Length, i => a[i] > 0)); Spec.Ensures<int>(r => r > 0); return a[3]; }"));

        // ---- modular calls -----------------------------------------------------------------------------------

        private const string Callee = "static int Half(int x) { Spec.Requires(x >= 0 && x % 2 == 0); Spec.Ensures<int>(r => 2 * r == x); return x / 2; } ";

        [Fact]
        public void CallerUsesCalleeEnsures() => Assert.Empty(Errors("M",
            Callee + "static int M(int y) { Spec.Requires(y >= 0 && y < 1000); Spec.Ensures<int>(r => r == y); return Half(2 * y); }"));

        [Fact]
        public void CalleeRequires_Refuted() => Assert.Equal(new[] { "CSV1001" }, Errors("M",
            Callee + "static int M(int y) { Spec.Requires(y >= 0 && y < 1000); return Half(2 * y + 1); }"));

        [Fact]
        public void EnsuresWithResultAndOld_OnRefParameters()
        {
            const string inc = "static void Inc(ref int x) { Spec.Requires(x < 100); Spec.Ensures(x == Spec.Old(x) + 1); x++; } ";
            Assert.Empty(Errors("Inc", inc));
            Assert.Empty(Errors("M", inc + "static int M() { Spec.Ensures(Spec.Result<int>() == 2); int a = 0; Inc(ref a); Inc(ref a); return a; }"));
            Assert.Equal(new[] { "CSV1002" }, Errors("Bad", "static void Bad(ref int x) { Spec.Ensures(x == Spec.Old(x) + 1); x += 2; }"));
        }

        [Fact]
        public void FrameCondition_ReadOnlyCalleeKeepsArrays() => Assert.Empty(Errors("M",
            "static int Get(int[] a) { Spec.Requires(a.Length > 0); return a[0]; } " +
            "static int M(int[] a) { Spec.Requires(a.Length > 1 && a[1] == 7); Get(a); Spec.Assert(a[1] == 7); return 0; }"));

        [Fact]
        public void FrameCondition_WritingCalleeHavocsArrays() => Assert.Equal(new[] { "CSV1004" }, Errors("M",
            "static void Set(int[] a) { Spec.Requires(a.Length > 1); a[1] = 0; } " +
            "static int M(int[] a) { Spec.Requires(a.Length > 1 && a[1] == 7); Set(a); Spec.Assert(a[1] == 7); return 0; }"));

        // ---- loops -------------------------------------------------------------------------------------------

        private const string CountTo =
            "static int M(int n) { Spec.Requires(n >= 0); Spec.Ensures<int>(r => r == n); int i = 0; " +
            "while (i < n) { Spec.Invariant(INV); Spec.Decreases(DEC); i++; } return i; }";

        [Fact]
        public void LoopInvariant_Proved() =>
            Assert.Empty(Errors("M", CountTo.Replace("INV", "0 <= i && i <= n").Replace("DEC", "n - i")));

        [Fact]
        public void LoopInvariant_NotOnEntry() => Assert.Equal(new[] { "CSV1005" }, Errors("M",
            CountTo.Replace("INV", "1 <= i && i <= n").Replace("DEC", "n - i")));

        [Fact]
        public void LoopInvariant_NotMaintained() => Assert.Equal(new[] { "CSV1006" }, Errors("M",
            "static int M(int n) { Spec.Requires(n >= 0); int i = 0; while (i < n) { Spec.Invariant(i <= n && i % 2 == 0); i++; } return i; }"));

        [Fact]
        public void LoopInvariant_TooWeakForPostcondition() => Assert.Equal(new[] { "CSV1002" }, Errors("M",
            CountTo.Replace("INV", "0 <= i").Replace("DEC", "n - i")));

        [Fact]
        public void LoopMeasure_Refuted() => Assert.Equal(new[] { "CSV1007" }, Errors("M",
            CountTo.Replace("INV", "0 <= i && i <= n").Replace("DEC", "i")));

        [Fact]
        public void ForLoop_WithArray() => Assert.Empty(Errors("M",
            "static void M(int[] a) { Spec.Ensures(Spec.Forall(0, a.Length, k => a[k] == 1)); " +
            "for (int i = 0; i < a.Length; i++) { Spec.Invariant(0 <= i && i <= a.Length && Spec.Forall(0, i, k => a[k] == 1)); a[i] = 1; } }"));

        // ---- recursion, ghosts, lemmas, trusted ----------------------------------------------------------------

        [Fact]
        public void RecursionTermination_Proved() => Assert.Empty(Errors("F",
            "static int F(int n) { Spec.Requires(n >= 0); Spec.Decreases(n); return n == 0 ? 0 : F(n - 1); }"));

        [Fact]
        public void RecursionTermination_Refuted() => Assert.Equal(new[] { "CSV1008" }, Errors("F",
            "static int F(int n) { Spec.Requires(n >= 0); Spec.Decreases(n); return n == 0 ? 0 : F(n + 1); }"));

        [Fact]
        public void GhostParameters_AreStaticIndices()
        {
            const string last = "static int Last(int[] a, Ghost<int> n) { Spec.Requires(n.Value > 0 && a.Length == n.Value); return a[n.Value - 1]; } ";
            Assert.Empty(Errors("Last", last));
            Assert.Empty(Errors("M", last + "static int M() => Last(new int[4], Ghost.Of(4));"));
            Assert.Equal(new[] { "CSV1001" }, Errors("M", last + "static int M() => Last(new int[4], Ghost.Of(5));"));
        }

        private const string Tri =
            "[Pure] static int Tri(int n) { Spec.Requires(n >= 0); Spec.Decreases(n); return n == 0 ? 0 : n + Tri(n - 1); } " +
            "[Lemma, Conditional(\"CSVERIFY_SPEC\")] static void TriFormula(int n) { Spec.Requires(n >= 0); Spec.Ensures(2 * Tri(n) == n * (n + 1)); Spec.Decreases(n); if (n > 0) TriFormula(n - 1); } ";

        [Fact]
        public void Lemma_ProvedByInduction() => Assert.Empty(Errors("TriFormula", Tri));

        [Fact]
        public void Lemma_WrongStatement_Refuted() => Assert.Equal(new[] { "CSV1002" }, Errors("L",
            Tri + "[Lemma, Conditional(\"CSVERIFY_SPEC\")] static void L(int n) { Spec.Requires(n >= 0); Spec.Ensures(Tri(n) == n * n); Spec.Decreases(n); if (n > 0) L(n - 1); }"));

        [Fact]
        public void LemmaCall_AddsItsPostcondition()
        {
            Assert.Empty(Errors("M", Tri + "static void M(int n) { Spec.Requires(n >= 2); TriFormula(n); Spec.Assert(2 * Tri(n) == n * (n + 1)); }"));
            Assert.Equal(new[] { "CSV1004" }, Errors("M", Tri + "static void M(int n) { Spec.Requires(n >= 2); Spec.Assert(2 * Tri(n) == n * (n + 1)); }"));
        }

        [Fact]
        public void Trusted_BodyIsSkipped_ContractIsUsed()
        {
            var r = Harness.Verify("public static class C { [Trusted] static int Five() { Spec.Ensures<int>(x => x == 5); return 4; } " +
                                   "static int M() { Spec.Ensures<int>(x => x == 5); return Five(); } }");
            Assert.Null(r["Five"]);
            Assert.Empty(r.Errors("M"));
        }

        // ---- views -------------------------------------------------------------------------------------------

        [Fact]
        public void Views_AddressesMatch() => Assert.Empty(Errors("M",
            "static int M() { Spec.Ensures<int>(r => r == 8); var p = Mem.Alloc(7, out var v); Mem.Write(ref v, p, Mem.Read(in v, p) + 1); int x = Mem.Read(in v, p); Mem.Free(v, p); return x; }"));

        // One report: after a failed obligation the verifier assumes it, so the second wrong use is not reported again.
        [Fact]
        public void Views_WrongPointer_Refuted() => Assert.Equal(new[] { "CSV1001" }, Errors("M",
            "static void M() { var p = Mem.Alloc(1, out var vp); var q = Mem.Alloc(2, out var vq); Mem.Read(in vp, q); Mem.Free(vp, q); Mem.Free(vq, q); }"));

        [Fact]
        public void Views_ValueFlowsThroughGhost() => Assert.Equal(new[] { "CSV1004" }, Errors("M",
            "static void M() { var p = Mem.Alloc(1, out var v); Mem.Write(ref v, p, 2); Spec.Assert(v.Value.Value == 1); Mem.Free(v, p); }"));

        // ---- the samples ---------------------------------------------------------------------------------------

        private static VerificationResult VerifySamples(string dir)
        {
            var root = Path.Combine(Harness.RepoRoot(), "samples", dir);
            var sep = Path.DirectorySeparatorChar;
            var files = Directory.EnumerateFiles(root, "*.cs", SearchOption.AllDirectories)
                .Where(f => !f.Contains($"{sep}obj{sep}") && !f.Contains($"{sep}bin{sep}"));
            return Engine.VerifyFiles(files, new VerifierOptions());
        }

        [Fact]
        public void GoodSamples_AllVerify()
        {
            var r = VerifySamples("Good");
            Assert.True(r.Success, string.Join("\n", r.Diagnostics));
            Assert.Empty(r.Diagnostics);
            Assert.True(r.Methods.Count >= 13);
        }

        [Fact]
        public void BuggySamples_AreFlagged()
        {
            var r = VerifySamples("Buggy");
            Assert.Equal(new[] { "CSV1003" }, r.Errors("SumOffByOne"));
            Assert.Equal(new[] { "CSV1002" }, r.Errors("First"));
            Assert.Equal(new[] { "CSV1001" }, r.Errors("Average"));
            Assert.Equal(new[] { "CSV1005", "CSV1006" }, r.Errors("CountUp"));
            Assert.Equal(new[] { "CSV1008" }, r.Errors("Loop"));
            Assert.Equal(new[] { "CSV1004" }, r.Errors("TriWithoutLemma"));
            Assert.Equal(new[] { "CSV1001" }, r.Errors("WrongPointer"));
        }
    }
}
