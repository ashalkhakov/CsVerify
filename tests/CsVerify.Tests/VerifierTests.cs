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
        public void Old_InLoopInvariant_SeesEntryHeap_AndCurrentLocals()
        {
            const string body = "{ Spec.Ensures(Spec.Forall(0, a.Length, k => a[k] == Spec.Old(a[k]) + 1)); int n = a.Length; " +
                "for (int i = 0; i < n; i++) { Spec.Invariant(0 <= i && i <= n && n == a.Length); " +
                "Spec.Invariant(Spec.Forall(0, i, k => a[k] == Spec.Old(a[k]) + 1)); Spec.Invariant(Spec.Forall(i, n, k => a[k] == Spec.Old(a[k]))); " +
                "Spec.Decreases(n - i); a[i] = a[i] + STEP; } }";
            Assert.Empty(Errors("Inc", "static void Inc(int[] a) " + body.Replace("STEP", "1")));
            Assert.Equal(new[] { "CSV1006" }, Errors("Inc", "static void Inc(int[] a) " + body.Replace("STEP", "2")));
        }

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

        private const string Ack =
            "static int A(int m, int n) { Spec.Requires(m >= 0 && n >= 0); Spec.Ensures<int>(r => r > n); Spec.Decreases(MEASURE); " +
            "if (m == 0) return n + 1; if (n == 0) return A(m - 1, 1); return A(m - 1, A(m, n - 1)); }";

        [Fact]
        public void LexicographicMeasure_Proved() => Assert.Empty(Errors("A", Ack.Replace("MEASURE", "m, n")));

        [Fact]
        public void LexicographicMeasure_Refuted()
        {
            Assert.Equal(new[] { "CSV1008" }, Errors("A", Ack.Replace("MEASURE", "m")));
            Assert.Equal(new[] { "CSV1008", "CSV1008" }, Errors("A", Ack.Replace("MEASURE", "n, m")));
        }

        [Fact]
        public void LexicographicLoopMeasure()
        {
            const string loop = "static void M(int a, int b) { Spec.Requires(a >= 0 && b >= 0); " +
                "while (a > 0) { Spec.Invariant(a >= 0 && b >= 0); Spec.Decreases(a, b); if (b > 0) b--; else { a--; b = 100; } STEP } }";
            Assert.Empty(Errors("M", loop.Replace("STEP", "")));
            Assert.Equal(new[] { "CSV1007" }, Errors("M", loop.Replace("STEP", "if (a == 1) b = 5;")));
        }

        private const string EvenOdd =
            "static bool Even(int n) { Spec.Requires(n >= 0); Spec.Decreases(EVEN); if (n == 0) return true; return Odd(n - 1); } " +
            "static bool Odd(int n) { Spec.Requires(n >= 0); Spec.Decreases(ODD); return !Even(n); }";

        [Fact]
        public void MutualRecursion_Proved()
        {
            var r = Harness.Verify("public static class C { " + EvenOdd.Replace("EVEN", "2 * n").Replace("ODD", "2 * n + 1") + " }");
            Assert.Empty(r.Diagnostics);
        }

        [Fact]
        public void MutualRecursion_Refuted()
        {
            var r = Harness.Verify("public static class C { " + EvenOdd.Replace("EVEN", "n").Replace("ODD", "n") + " }");
            Assert.Empty(r.Errors("Even"));
            Assert.Equal(new[] { "CSV1008" }, r.Errors("Odd"));
        }

        [Fact]
        public void MutualRecursion_MeasuresMustHaveTheSameShape()
        {
            var r = Harness.Verify("public static class C { " + EvenOdd.Replace("EVEN", "n, 0").Replace("ODD", "n") + " }");
            Assert.Equal(new[] { "CSV1008" }, r.Errors("Even"));
            Assert.Equal(new[] { "CSV1008" }, r.Errors("Odd"));
        }

        [Fact]
        public void MutualRecursion_WithoutMeasure_IsAWarning()
        {
            var r = Harness.Verify("public static class C { static int F(int n) => n <= 0 ? 0 : G(n - 1); static int G(int n) => F(n); }");
            Assert.Contains(r["F"].Diagnostics, d => !d.IsError && d.Message.Contains("mutually recursive"));
            Assert.True(r.Success);
        }

        [Fact]
        public void TupleResults()
        {
            const string minMax = "static (int lo, int hi) M(int x, int y) { Spec.Ensures<(int lo, int hi)>(r => r.lo == Math.Min(x, y) && r.Item2 == Math.Max(x, y)); " +
                "return x <= y ? (x, y) : (y, x); }";
            Assert.Empty(Errors("M", minMax));
            Assert.Equal(new[] { "CSV1002" }, Errors("M", minMax.Replace("(y, x)", "(x, y)")));
            Assert.Empty(Errors("U", minMax + " static int U() { Spec.Ensures<int>(r => r == 2); var t = M(5, 3); return t.lo - 1; }"));
            const string use = " static int D() { Spec.Ensures<int>(r => r == 2); var (a, b) = M(5, 3); (int c, _) = M(b, a); return c - 1 + EXTRA; }";
            Assert.Empty(Errors("D", minMax + use.Replace("EXTRA", "0")));
            Assert.Equal(new[] { "CSV1002" }, Errors("D", minMax + use.Replace("EXTRA", "b - a")));
        }

        private const string SumDef = "[Pure] static int Sum(int[] a, int s, int t) { Spec.Requires(0 <= s && s <= t && t <= a.Length); " +
            "Spec.Decreases(t - s); return s == t ? 0 : Sum(a, s, t - 1) + a[t - 1]; } ";

        [Fact]
        public void PureDefinitions_UnfoldInsideQuantifiers()
        {
            // needs Sum(a, b, n + 1) = Sum(a, b, n) + a[n] for the bound b, and Sum(a, n, n) = 0 from the hypothesis
            Assert.Empty(Errors("Step", SumDef + "static void Step(int[] a, int n, int c) { " +
                "Spec.Requires(0 <= n && n < a.Length && 0 <= c && c <= n); Spec.Requires(Spec.Forall(0, n + 1, b => Sum(a, b, n) <= Sum(a, c, n))); " +
                "Spec.Ensures(Spec.Forall(0, n + 1, b => Sum(a, b, n + 1) <= Sum(a, c, n) + a[n])); }"));
        }

        [Fact]
        public void PureDefinitions_InsideQuantifiers_DoNotProveFalseClaims()
        {
            Assert.Equal(new[] { "CSV1002" }, Errors("Bad", SumDef + "static void Bad(int[] a) { Spec.Requires(a.Length > 0); " +
                "Spec.Ensures(Spec.Forall(0, a.Length, b => Sum(a, b, a.Length) == 0)); }"));
            // an assumed quantifier cannot hide a definition: Sum(a, n, n) is 0 whatever the hypothesis says
            Assert.Equal(new[] { "CSV1002" }, Errors("Bad", SumDef + "static void Bad(int[] a, int n) { Spec.Requires(0 <= n && n <= a.Length); " +
                "Spec.Requires(Spec.Forall(0, n + 1, b => Sum(a, b, n) < 0)); Spec.Ensures(false); }"));
        }

        [Fact]
        public void TakeOut_AndPutBack()
        {
            const string inc = "static void Inc(ref ArrayView<int> v, Ptr<int> p, int i) { " +
                "Spec.Requires(v.Addr == p.Addr && 0 <= i && i < v.Length.Value); " +
                "Spec.Ensures(v.Addr == Spec.Old(v).Addr && v.Length == Spec.Old(v).Length && v.Elems == Spec.Old(v).Elems.Update(i, Ghost.Of(7))); " +
                "Mem.TakeOut(v, Ghost.Of(i), out var c, out var h); Mem.Write(ref c, p.Offset(OFF), 7); Mem.PutBack(c, h, out v); }";
            Assert.Empty(Errors("Inc", inc.Replace("OFF", "i")));
            Assert.Equal(new[] { "CSV1001" }, Errors("Inc", inc.Replace("OFF", "0")));
        }

        [Fact]
        public void GhostParameters_AreStaticIndices()
        {
            const string last = "static int Last(int[] a, Ghost<int> n) { Spec.Requires(n.Value > 0 && a.Length == n.Value); return a[a.Length - 1]; } ";
            Assert.Empty(Errors("Last", last));
            Assert.Empty(Errors("M", last + "static int M() => Last(new int[4], Ghost.Of(4));"));
            Assert.Equal(new[] { "CSV1001" }, Errors("M", last + "static int M() => Last(new int[4], Ghost.Of(5));"));
        }

        private const string Tri =
            "[Pure] static int Tri(int n) { Spec.Requires(n >= 0); Spec.Decreases(n); return n == 0 ? 0 : n + Tri(n - 1); } " +
            "[Lemma, Conditional(\"CSVERIFY_SPEC\")] static void TriFormula(int n) { Spec.Requires(n >= 0); Spec.Ensures(2 * Tri(n) == n * (n + 1)); Spec.Decreases(n); if (n > 0) TriFormula(n - 1); } ";

        [Fact]
        public void PureFunction_WithStatements_IsDefined()
        {
            // ifs, returns and local declarations define the function as well as a single expression does
            const string clamp = "[Pure] static int Clamp(int x, int lo) { int m = lo; if (x < m) return m; if (x > 100) { return 100; } return x; } ";
            Assert.Empty(Errors("M", clamp + "static void M() { Spec.Assert(Clamp(-5, 0) == 0 && Clamp(7, 0) == 7 && Clamp(500, 0) == 100); }"));
            Assert.Equal(new[] { "CSV1004" }, Errors("M", clamp + "static void M() { Spec.Assert(Clamp(7, 0) == 8); }"));
            // a body with anything else (here a loop) gives no definition: the function is known by its contract only
            Assert.Equal(new[] { "CSV1004" }, Errors("M", "[Pure] static int Z(int n) { int k = 0; while (k < n) { Spec.Invariant(k <= n || n < 0); k++; } return 0; } " +
                "static void M() { Spec.Assert(Z(3) == 0); }"));
        }

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

        // ---- array views -------------------------------------------------------------------------------------

        private const string ViewParams = "ref ArrayView<int> v, Ptr<int> p, int n";
        private const string ViewPre = "Spec.Requires(v.Addr == p.Addr && v.Length.Value == n && n >= 2); ";

        [Fact]
        public void ArrayView_SplitOffsetJoin_Proved() => Assert.Empty(Errors("M",
            "static void M(" + ViewParams + ") { " + ViewPre +
            "Spec.Ensures(v.Addr == Spec.Old(v).Addr && v.Length == Spec.Old(v).Length && v.Elems == Spec.Old(v).Elems.Update(1, Ghost.Of(5))); " +
            "Mem.Split(v, Ghost.Of(1), out var l, out var r); Mem.Set(ref r, p.Offset(1), 0, 5); Mem.Join(l, r, out v); }"));

        [Fact]
        public void ArrayView_WrongOffset_Refuted() => Assert.Equal(new[] { "CSV1001" }, Errors("M",
            "static void M(" + ViewParams + ") { " + ViewPre +
            "Mem.Split(v, Ghost.Of(1), out var l, out var r); Mem.Set(ref r, p.Offset(2), 0, 5); Mem.Join(l, r, out v); }"));

        [Fact]
        public void ArrayView_WrongContents_Refuted() => Assert.Equal(new[] { "CSV1002" }, Errors("M",
            "static void M(" + ViewParams + ") { " + ViewPre +
            "Spec.Ensures(v.Elems == Spec.Old(v).Elems.Update(0, Ghost.Of(5))); " +
            "Mem.Split(v, Ghost.Of(1), out var l, out var r); Mem.Set(ref r, p.Offset(1), 0, 5); Mem.Join(l, r, out v); }"));

        [Fact]
        public void ArrayView_JoinNeedsAdjacentHalves() => Assert.Equal(new[] { "CSV1001" }, Errors("M",
            "static void M(" + ViewParams + ") { " + ViewPre +
            "Mem.Split(v, Ghost.Of(1), out var l, out var r); Mem.Join(r, l, out v); }"));

        [Fact]
        public void ArrayView_GetBounds()
        {
            Assert.Empty(Errors("M", "static int M(in ArrayView<int> v, Ptr<int> p, int n) { Spec.Requires(v.Addr == p.Addr && v.Length.Value == n && n > 0); return Mem.Get(in v, p, n - 1); }"));
            Assert.Equal(new[] { "CSV1001" }, Errors("M", "static int M(in ArrayView<int> v, Ptr<int> p, int n) { Spec.Requires(v.Addr == p.Addr && v.Length.Value == n); return Mem.Get(in v, p, n); }"));
        }

        [Fact]
        public void ArrayView_FreeNeedsWholeArray() => Assert.Contains("CSV1001", Errors("M", // also a linearity error: l is used after it was freed
            "static void M() { var p = Mem.AllocArray(4, 0, out var v, out var gc); Mem.Split(v, Ghost.Of(2), out var l, out var r); Mem.FreeArray(gc, l, p); Mem.Join(l, r, out v); }"));

        [Fact]
        public void GhostFunction_IsUnfolded() => Assert.Empty(Errors("M",
            "[GhostFunction] static bool AllZero(Seq<int> s, int n) => Spec.Forall(0, n, j => s[j].Value == 0); " +
            "static int M() { Spec.Ensures<int>(r => r == 0); var p = Mem.AllocArray(3, 0, out var v, out var gc); Spec.Assert(AllZero(v.Elems, 3)); " +
            "int x = Mem.Get(in v, p, 2); Mem.FreeArray(gc, v, p); return x; }"));

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
            Assert.True(r.Methods.Count >= 16);
        }

        [Fact]
        public void BuggySamples_AreFlagged()
        {
            var r = VerifySamples("Buggy");
            Assert.Equal(new[] { "CSV1003" }, r.Errors("SumOffByOne"));
            Assert.Equal(new[] { "CSV1002", "CSV1012" }, r.Errors("First"));
            Assert.Equal(new[] { "CSV1001" }, r.Errors("Average"));
            Assert.Equal(new[] { "CSV1005", "CSV1006" }, r.Errors("CountUp"));
            Assert.Equal(new[] { "CSV1008" }, r.Errors("Loop"));
            Assert.Equal(new[] { "CSV1004" }, r.Errors("TriWithoutLemma"));
            Assert.Equal(new[] { "CSV1001" }, r.Errors("WrongPointer"));
            Assert.Equal(new[] { "CSV1001" }, r.Errors("WrongOffset"));
            Assert.Equal(new[] { "CSV1001" }, r.Errors("OnePastEnd"));
            Assert.Equal(new[] { "CSV1005" }, r.Errors("FibWrongStart"));
            Assert.Equal(new[] { "CSV1003" }, r.Errors("ReverseOffByOne"));
            Assert.Equal(new[] { "CSV1002", "CSV1002" }, r.Errors("FastPowWithoutLemma"));
            Assert.Equal(new[] { "CSV1008" }, r.Errors("McCarthyWrongMeasure"));
            Assert.Equal(new[] { "CSV1006", "CSV1007" }, r.Errors("DutchFlagStuck"));
            Assert.Equal(new[] { "CSV1008" }, r.Errors("AckermannSingleMeasure"));
            Assert.Equal(new[] { "CSV1008" }, r.Errors("Odd"));
            Assert.Equal(new[] { "CSV1001" }, r.Errors("IncrementWrongCell"));
            Assert.Equal(new[] { "CSV1003" }, r.Errors("MatGetWrongStride"));
            Assert.Equal(new[] { "CSV1006" }, r.Errors("KadaneForgetsRestart"));
            Assert.Equal(new[] { "CSV1006" }, r.Errors("CubesWrongStep"));
            Assert.Equal(new[] { "CSV1002" }, r.Errors("SumOfCubesWithoutLemma"));
            Assert.Equal(new[] { "CSV1011" }, r.Errors("Circular"));
            Assert.Equal(new[] { "CSV1011" }, r.Errors("Inconsistent"));
            Assert.Equal(new[] { "CSV0013" }, r.Errors("Meddling"));
            Assert.Equal(new[] { "CSV0007" }, r.Errors("Aliased"));
            Assert.Equal(new[] { "CSV1013" }, r.Errors("Unchecked"));
            Assert.Equal(new[] { "CSV1014" }, r.Errors("Forgiven"));
            Assert.Equal(new[] { "CSV1014" }, r.Errors("Broken"));
            Assert.Equal(new[] { "CSV1013" }, r.Errors("FreshArray"));
            Assert.Equal(new[] { "CSV1012" }, r.Errors("SpecTooEarly"));
            Assert.Equal(new[] { "CSV1011" }, r.Errors("Key"));
            Assert.Equal(new[] { "CSV1008" }, r.Errors("DataBugs.Size"));
            Assert.Equal(new[] { "CSV1002" }, r.Errors("DataBugs.FoldPreservesEval"));
            Assert.Equal(new[] { "CSV1006" }, r.Errors("DataBugs.Factorial"));
            Assert.Equal(new[] { "CSV1015" }, r.Errors("Backwards"));
            Assert.Equal(new[] { "CSV1004" }, r.Errors("SameObject"));
            Assert.Equal(new[] { "CSV1001", "CSV1001" }, r.Errors("InsertNoRotation"));
            Assert.Equal(new[] { "CSV1015" }, r.Errors("RotRSingleOnly"));
            Assert.Equal(new[] { "CSV1001" }, r.Errors("BalanceLRecolorWrong"));
            Assert.Equal(new[] { "CSV1015" }, r.Errors("Spend"));
            Assert.Equal(new[] { "CSV1016" }, r.Errors("Steal"));
            Assert.Equal(new[] { "CSV1016" }, r.Errors("Forge"));
            Assert.Equal(new[] { "CSV1002" }, r.Errors("OwnedBugs.Peek"));
            Assert.Equal(new[] { "CSV1016" }, r.Errors("AfterDrop"));
            Assert.Equal(new[] { "CSV1017" }, r.Errors("Positive"));
            Assert.Equal(new[] { "CSV1017" }, r.Errors("Sneaky"));
            Assert.Equal(new[] { "CSV1004" }, r.Errors("Independent"));
            Assert.Equal(new[] { "CSV1015" }, r.Errors("Reading.Positive"));
            Assert.Equal(new[] { "CSV1015" }, r.Errors("AppendSmaller"));
            Assert.Equal(new[] { "CSV1016" }, r.Errors("Reach"));
            Assert.Equal(new[] { "CSV1016" }, r.Errors("Bypass"));
            Assert.Equal(new[] { "CSV1016" }, r.Errors("Cycle"));
            // read shares (ShareBugs.cs)
            Assert.Equal(new[] { "CSV1016" }, r.Errors("WriteWhileShared"));
            Assert.Equal(new[] { "CSV1016" }, r.Errors("LendWhileShared"));
            Assert.Equal(new[] { "CSV1016" }, r.Errors("WriteThroughShare"));
            Assert.Equal(new[] { "CSV1016" }, r.Errors("WrongJoin"));
            Assert.Equal(new[] { "CSV1015" }, r.Errors("LendBroken"));
            Assert.Equal(new[] { "CSV1004" }, r.Errors("ShareBugs.Distinct"));
            // predicates (PredicateBugs.cs)
            Assert.Equal(new[] { "CSV1016" }, r.Errors("Unframed"));
            Assert.Equal(new[] { "CSV1016" }, r.Errors("WriteFolded"));
            Assert.Equal(new[] { "CSV1019" }, r.Errors("FoldWrong"));
            Assert.Equal(new[] { "CSV1016" }, r.Errors("UnfoldMissing"));
            Assert.Equal(new[] { "CSV1016" }, r.Errors("UseUp"));
            Assert.Equal(new[] { "CSV1016" }, r.Errors("KeepLent"));
            // array cells (ArrayPermissionBugs.cs)
            Assert.Equal(new[] { "CSV1016" }, r.Errors("ExchangeSame"));
            Assert.Equal(new[] { "CSV1016" }, r.Errors("PastTheEnd"));
            Assert.Equal(new[] { "CSV1016" }, r.Errors("CallsUnframed"));
            // ATS ports (AtsPortBugs.cs)
            Assert.Equal(new[] { "CSV1019" }, r.Errors("ConcatOneWay"));
            Assert.Equal(new[] { "CSV1001" }, r.Errors("UnconsEmpty"));
            Assert.Equal(new[] { "CSV1016" }, r.Errors("InsertTwice"));
            Assert.Equal(new[] { "CSV1006" }, r.Errors("PopSmallerChild"));
            Assert.Equal(new[] { "CSV1002" }, r.Errors("GrowWithoutCopy"));
            Assert.Equal(new[] { "CSV1019" }, r.Errors("DanglingTwin"));
            Assert.Equal(new[] { "CSV1019" }, r.Errors("SetAnyChar"));
            Assert.Equal(new[] { "CSV1016" }, r.Errors("InsertDropsRest"));
            Assert.Equal(new[] { "CSV1019" }, r.Errors("ShrinkBelowCount"));
            Assert.Equal(new[] { "CSV1002" }, r.Errors("Lemma3AsStated"));
            Assert.Equal(new[] { "CSV1008" }, r.Errors("SplitWithoutFallback"));
            Assert.Equal(new[] { "CSV1019" }, r.Errors("InsertWithoutFind"));
            Assert.Equal(new[] { "CSV1004" }, r.Errors("TreeOwnershipBugs.Stale"));
            Assert.Equal(new[] { "CSV1003" }, r.Errors("Ring.Insert"));
            Assert.Equal(new[] { "CSV1015" }, r.Errors("Clear1"));
            Assert.Equal(new[] { "CSV1015" }, r.Errors("AddLeft"));
            Assert.Equal(new[] { "CSV1006" }, r.Errors("LowerBoundWrong"));
            Assert.Equal(new[] { "CSV1002" }, r.Errors("FindLast"));
            Assert.Equal(new[] { "CSV1006" }, r.Errors("CopyOverlapping"));
            Assert.Equal(new[] { "CSV1006" }, r.Errors("SelectionSortCopies"));
            Assert.Equal(new[] { "CSV1018" }, r.Errors("PickyPurse.TrySpend"));
            Assert.Equal(new[] { "CSV1002" }, r.Errors("LyingPurse.Add"));
            Assert.Equal(new[] { "CSV1002", "CSV1017" }, r.Errors("LeakyPurse.Add"));
            Assert.Equal(new[] { "CSV1001" }, r.Errors("Overdrawn..ctor"));
            Assert.Equal(new[] { "CSV1015" }, r.Errors("Tile..ctor"));
            Assert.Equal(new[] { "CSV1015" }, r.Errors("Registered..ctor"));
            Assert.Equal(new[] { "CSV1011" }, r.Errors("FundsOf"));
        }
    }

    /// <summary>Where the verifier cannot model something soundly it fails (CSV1901); proofs must terminate (CSV1011).</summary>
    public class SoundnessTests
    {
        private static string[] Errors(string method, string source) =>
            Harness.Verify("public static class C { " + source + " }").Errors(method);

        private const string LemmaAttrs = "[Lemma, Conditional(\"CSVERIFY_SPEC\")] ";

        [Fact]
        public void NonTerminatingLemma_DoesNotProveFalse()
        {
            Assert.Equal(new[] { "CSV1011" }, Errors("L", LemmaAttrs + "static void L(int n) { Spec.Ensures(false); L(n); }"));
            Assert.Equal(new[] { "CSV1011" }, Errors("L", LemmaAttrs + "static void L(int n) { Spec.Ensures(false); while (true) { } }"));
            Assert.Contains("CSV1011", Errors("L", LemmaAttrs + "static void L(int n) { Spec.Ensures(false); throw new System.Exception(); }"));
        }

        [Fact]
        public void NonTerminatingDefinition_IsReported() =>
            Assert.Equal(new[] { "CSV1011" }, Errors("F", "[Pure] static int F(int x) => F(x) + 1;"));

        [Fact]
        public void NormalCode_IsPartialCorrectness() =>
            Assert.Empty(Errors("M", "static int M(int n) { Spec.Ensures<int>(r => r == 0); while (true) { } }"));

        [Fact]
        public void UnmodeledControlFlow_FailsVerification()
        {
            Assert.Contains("CSV1901", Errors("M", "static int M(int[] a) { int s = 0; foreach (var x in a) s += x; return s; }"));
            Assert.Contains("CSV1901", Errors("M", "static int M(int x) { again: x++; if (x < 3) goto again; return x; }"));
        }

        [Fact]
        public void UnmodeledState_FailsVerification()
        {
            // a library type's computed property: its value may change in ways the verifier does not track, so each
            // read in code is a value of its own (fields of source classes are modeled: see HeapTests), and a
            // specification cannot mention it
            const string list = "System.Collections.Generic.List<int>";
            Assert.Empty(Harness.Verify("public static class C { public static int M(" + list + " l) => l.Count; }").Errors("M"));
            Assert.Equal(new[] { "CSV1004" }, Harness.Verify("public static class C { public static void M(" + list + " l) { int a = l.Count, b = l.Count; Spec.Assert(a == b); } }").Errors("M"));
            Assert.Contains("CSV1901", Harness.Verify("public static class C { public static int M(" + list + " l) { Spec.Ensures((int r) => r == l.Count); return l.Count; } }").Errors("M"));
            // as the library declares it: Console.Out is not null
            Assert.Empty(Harness.Verify("public static class C { public static void M() { System.Console.Out.Write(1); } }").Errors("M"));
            Assert.Empty(Harness.Verify("public class C { public int P { get; } public int M() => P; }").Errors("M"));
        }

        [Fact]
        public void AssignmentsOfInitializedObjects_AreWritten()
        {
            // the flow graph captures the target of x = new C { ... } before the value: the write must still happen
            const string sym = "public sealed class Sym { public int K; public Sym? Next; } ";
            Assert.Equal(new[] { "CSV1004" }, Harness.Verify(sym + "public static class C { static void M() { Sym? s = null; s = new Sym { K = 1 }; Spec.Assert(s == null); } }").Errors("M"));
            Assert.Equal(new[] { "CSV1004" }, Harness.Verify(sym + "public static class C { static void M(Sym c) { var old = c.Next; c.Next = new Sym { K = 1 }; Spec.Assert(c.Next == old); } }").Errors("M"));
            Assert.Equal(new[] { "CSV1004" }, Harness.Verify(sym + "public static class C { static void M(int[] a) { Spec.Requires(a.Length > 0); a[0] = 5; a[0] = new Sym { K = 1 }.K; Spec.Assert(a[0] == 5); } }").Errors("M"));
            Assert.Empty(Harness.Verify(sym + "public static class C { static int M(Sym? s) { if (s == null) s = new Sym { K = 1 }; return s.K; } }").Errors("M"));
        }

        [Fact]
        public void HeapAliases_FailVerification()
        {
            Assert.Contains("CSV1901", Errors("M", "static void M(int[] a) { Spec.Requires(a.Length > 0); ref int x = ref a[0]; x = 1; }"));
            Assert.Equal(new[] { "CSV1901" }, Errors("M", "static void Set(ref int x) { x = 1; } static void M(int[] a) { Spec.Requires(a.Length > 0); Set(ref a[0]); }"));
        }

        [Fact]
        public void SpanWrites_MayChangeAnyArray() => Assert.Equal(new[] { "CSV1004" }, Errors("M",
            "static void M(int[] a, System.Span<int> s) { Spec.Requires(a.Length > 0 && s.Length > 0); a[0] = 1; s[0] = 2; Spec.Assert(a[0] == 1); }"));

        [Fact]
        public void Constructors_MayWriteArrays()
        {
            var r = Harness.Verify("public class B { public B(int[] a) { a[0] = 5; } } " +
                "public static class C { public static void M(int[] a) { Spec.Requires(a.Length > 0); a[0] = 1; new B(a); Spec.Assert(a[0] == 1); } }");
            Assert.Equal(new[] { "CSV1004" }, r.Errors("M"));
        }
    }

    /// <summary>Specifications must mean something: indexes in bounds, pure functions within their preconditions (CSV1012).</summary>
    public class WellDefinednessTests
    {
        private static string[] Errors(string method, string source) =>
            Harness.Verify("public static class C { " + source + " }").Errors(method);

        private static string[] Requires(string condition) => Errors("M", "static void M(int[] a, int x) { Spec.Requires(" + condition + "); }");

        [Fact]
        public void Indexing_IsGuardedByShortCircuitOperators()
        {
            Assert.Equal(new[] { "CSV1012" }, Requires("a[0] > 0"));
            Assert.Empty(Requires("a.Length > 0 && a[0] > 0"));
            Assert.Empty(Requires("a.Length == 0 || a[0] > 0"));
            Assert.Empty(Requires("(a.Length > 0 ? a[0] : 1) > 0"));
            Assert.Equal(new[] { "CSV1012" }, Requires("a[0] > 0 && a.Length > 0")); // the guard comes too late
        }

        [Fact]
        public void EarlierPreconditions_GuardLaterOnes() =>
            Assert.Empty(Errors("M", "static void M(int[] a) { Spec.Requires(a.Length > 2); Spec.Requires(a[2] > 0); }"));

        [Fact]
        public void QuantifierRanges_AreGuards()
        {
            Assert.Empty(Requires("Spec.Forall(0, a.Length, i => a[i] > 0)"));
            Assert.Equal(new[] { "CSV1012" }, Requires("Spec.Forall(0, a.Length + 1, i => a[i] > 0)"));
            Assert.Empty(Requires("Spec.Forall(0, a.Length, i => Spec.Forall(i + 1, a.Length, j => a[i] <= a[j]))"));
            Assert.Equal(new[] { "CSV1012" }, Requires("Spec.Exists(0, a.Length, i => a[i + 1] == x)"));
        }

        [Fact]
        public void DivisionInSpecifications()
        {
            Assert.Equal(new[] { "CSV1012" }, Requires("100 / x > 1"));
            Assert.Empty(Requires("x != 0 && 100 / x > 1"));
        }

        private const string Sum = "[Pure] static int Sum(int[] a, int n) { Spec.Requires(0 <= n && n <= a.Length); Spec.Decreases(n); " +
                                   "return n == 0 ? 0 : Sum(a, n - 1) + a[n - 1]; } ";

        [Fact]
        public void PureFunctions_AreUsedWithinTheirPreconditions()
        {
            Assert.Empty(Errors("M", Sum + "static int M(int[] a) { Spec.Ensures<int>(r => r == Sum(a, a.Length)); return Sum(a, a.Length); }"));
            Assert.Equal(new[] { "CSV1012" }, Errors("M", Sum + "static void M(int[] a) { Spec.Ensures(Sum(a, a.Length + 1) >= 0 || true); }"));
            Assert.Empty(Errors("M", Sum + "static void M(int[] a, int n) { Spec.Requires(n < 0 || n > a.Length || Sum(a, n) >= 0); }"));
        }

        [Fact]
        public void InvariantsAndAssertions_AreChecked()
        {
            Assert.Equal(new[] { "CSV1012" }, Errors("M", "static void M(int[] a) { for (int i = 0; i < a.Length; i++) { Spec.Invariant(a[i] >= 0 || true); } }"));
            Assert.Empty(Errors("M", "static void M(int[] a) { for (int i = 0; i < a.Length; i++) { Spec.Invariant(0 <= i && i <= a.Length); Spec.Invariant(i == a.Length || a[i] >= 0 || true); } }"));
            Assert.Equal(new[] { "CSV1012" }, Errors("M", "static void M(int[] a) { Spec.Assert(a[0] >= 0 || true); }"));
        }

        [Fact]
        public void CalleeSpecifications_AreTheCalleesConcern()
        {
            var r = Harness.Verify("public static class C { static void Bad(int[] a) { Spec.Requires(a[0] == 0 || true); } static void M() { Bad(new int[0]); } }");
            Assert.Equal(new[] { "CSV1012" }, r.Errors("Bad"));
            Assert.Empty(r.Errors("M"));
        }

        [Fact]
        public void GhostFunctionBodies_CheckBoundsForEveryValue()
        {
            const string pos = "[GhostFunction] static bool Pos(int[] a, int n) { REQ return Spec.Forall(0, n, i => a[i] > 0); }";
            Assert.Equal(new[] { "CSV1003" }, Errors("Pos", pos.Replace("REQ", "")));
            Assert.Empty(Errors("Pos", pos.Replace("REQ", "Spec.Requires(n <= a.Length);")));
        }
    }
    /// <summary>
    /// Null references: every dereference must be proved non-null, and non-nullable reference types (in an enabled
    /// nullable context) are contracts: callers prove arguments, callees prove results.
    /// </summary>
    public class NullTests
    {
        private static string[] Errors(string method, string source) =>
            Harness.Verify("using System.Diagnostics.CodeAnalysis; public static class C { " + source + " }").Errors(method);

        [Fact]
        public void NullableReference_MustBeCheckedBeforeUse()
        {
            Assert.Equal(new[] { "CSV1013" }, Errors("M", "static int M(int[]? a) => a.Length;"));
            Assert.Equal(new[] { "CSV1013" }, Errors("M", "static int M(int[]? a) { Spec.Requires(a == null || a.Length > 0); return a[0]; }"));
            Assert.Equal(new[] { "CSV1013" }, Errors("M", "static string M(string? s) => s.Substring(1);"));
            Assert.Empty(Errors("M", "static int M(int[]? a) { if (a == null) return 0; return a.Length; }"));
            Assert.Empty(Errors("M", "static int M(string? s) { if (s is null) return 0; return s.Length; }"));
            Assert.Empty(Errors("M", "static int M(string? s) => s is not null ? s.Length : 0;"));
            Assert.Empty(Errors("M", "static int M(string? s) => s is { } ? s.Length : 0;"));
            Assert.Empty(Errors("M", "static int M(string? s) => s != null && s.Length > 0 ? 1 : 0;"));
        }

        [Fact]
        public void ConditionalAccessAndCoalescing_AreGuards()
        {
            Assert.Empty(Errors("M", "static string? M(string? s) => s?.Trim();"));
            Assert.Empty(Errors("M", "static int M(string? s) => (s ?? \"none\").Length;"));
            Assert.Empty(Errors("M", "static int M(int[]? a) { int[] b = a ?? new int[3]; return b.Length; }"));
        }

        [Fact]
        public void NonNullableParameter_IsAPrecondition()
        {
            const string callee = "static int Len(int[] a) => a.Length; ";
            Assert.Empty(Errors("Len", callee));
            Assert.Equal(new[] { "CSV1014" }, Errors("M", callee + "static int M(int[]? b) => Len(b);"));
            Assert.Empty(Errors("M", callee + "static int M(int[]? b) => b == null ? 0 : Len(b);"));
            Assert.Equal(new[] { "CSV1014" }, Errors("M", callee + "static int M() => Len(null!);")); // ! proves nothing
            Assert.Empty(Errors("M", callee + "static int M() => Len(new int[2]);"));
        }

        [Fact]
        public void NonNullableResult_IsAPostcondition()
        {
            Assert.Equal(new[] { "CSV1014" }, Errors("M", "static string M(bool c) { if (c) return \"x\"; return null!; }"));
            Assert.Empty(Errors("M", "static string M(bool c) { if (c) return \"x\"; return \"\"; }"));
            Assert.Equal(new[] { "CSV1014" }, Errors("M", "static void M(out string s) { s = null!; }"));
            // callers rely on it, for results and out parameters
            Assert.Empty(Errors("Use", "static string Get() => \"abc\"; static int Use() => Get().Length;"));
            Assert.Empty(Errors("Use", "static void Get(out int[] a) { a = new int[1]; } static int Use() { Get(out var a); return a.Length; }"));
            Assert.Equal(new[] { "CSV1013" }, Errors("Use", "static string? Get() => null; static int Use() => Get().Length;"));
        }

        [Fact]
        public void Specifications_MustNotDereferenceNull()
        {
            Assert.Equal(new[] { "CSV1012" }, Errors("M", "static void M(int[]? a) { Spec.Requires(a.Length > 0); }"));
            Assert.Empty(Errors("M", "static int M(int[]? a) { Spec.Requires(a != null && a.Length > 0); return a[0]; }"));
            Assert.Empty(Errors("M", "static void M(string? s) { Spec.Requires((s ?? \"\").Length < 10); }"));
            Assert.Empty(Errors("M", "[Pure] static string Self(this string s) => s; static void M(string? s) { Spec.Requires(s?.Self() == s); }"));
            // a postcondition is checked on each return path, with that path's result
            const string ens = "static int[]? M(int n) { Spec.Requires(n >= 0); Spec.Ensures((int[]? r) => r.Length == n); return RET; }";
            Assert.Empty(Errors("M", ens.Replace("RET", "new int[n]")));
            Assert.Equal(new[] { "CSV1002", "CSV1012" }, Errors("M", ens.Replace("RET", "null")));
        }

        [Fact]
        public void NonNullableFields_AreNeverNullOnceBuilt()
        {
            static string[] Of(string method, string source) => Harness.Verify(source).Errors(method);
            // writes prove it, reads assume it
            const string node = "public sealed class Node { public string Name; public Node? Next; public Node(string n) { Name = n; } } ";
            Assert.Empty(Of("Node..ctor", node));
            Assert.Empty(Of("M", node + "public static class C { static int M(Node n) => n.Name.Length; }"));
            Assert.Equal(new[] { "CSV1013" }, Of("M", node + "public static class C { static Node? M(Node n) => n.Next.Next; }"));
            Assert.Equal(new[] { "CSV1014" }, Of("M", node + "public static class C { static void M(Node n, string? s) { n.Name = s!; } }"));
            Assert.Empty(Of("M", node + "public static class C { static void M(Node n, string? s) { if (s != null) n.Name = s; } }"));
            // a constructor must set them
            Assert.Equal(new[] { "CSV1014" }, Of("Node..ctor", "public sealed class Node { public string Name; public Node(bool b) { if (b) Name = \"x\"; } }"));
            Assert.Equal(new[] { "CSV1014" }, Of("Node..ctor", "public sealed class Node { public string Name = null!; public Node() { } }"));
            Assert.Empty(Of("Node..ctor", "public sealed class Node { public string Name = \"\"; public Node() { } }"));
            // ... except required ones, which every object initializer sets
            const string req = "public sealed class R { public required string Name; public int K; } ";
            Assert.Empty(Of("M", req + "public static class C { static int M() { var r = new R { Name = \"ab\" }; return r.Name.Length; } }"));
            Assert.Equal(new[] { "CSV1014" }, Of("M", req + "public static class C { static R M(string? s) => new R { Name = s! }; }"));
            // and this may not escape before they are set
            Assert.Equal(new[] { "CSV1015" }, Of("Node..ctor", "public sealed class Node { public string Name; public Node() { C.Use(this); Name = \"\"; } } " +
                "public static class C { public static int Use(Node n) => n.Name.Length; }"));
            // a static field starting with an object stays one
            const string st = "public static class S { public static string Text = \"\"; public static string? Maybe; ";
            Assert.Empty(Of("M", st + "static int M() => Text.Length; }"));
            Assert.Equal(new[] { "CSV1013" }, Of("M", st + "static int M() => Maybe.Length; }"));
            Assert.Equal(new[] { "CSV1014" }, Of("M", st + "static void M() { Text = Maybe!; } }"));
        }

        [Fact]
        public void NonNullableLocals_StayNotNullThroughLoops()
        {
            const string node = "public sealed class Node { public Node? Next; } ";
            Assert.Empty(Harness.Verify(node + "public static class C { static Node M(Node n) { Node p = n; while (p.Next != null) p = p.Next; return p; } }").Errors("M"));
            Assert.Equal(new[] { "CSV1014" }, Harness.Verify(node + "public static class C { static void M(Node n) { Node p = n; p = n.Next!; } }").Errors("M"));
            Assert.Equal(new[] { "CSV1013" }, Harness.Verify(node + "public static class C { static int M(Node n) { var p = n.Next; while (p != null) p = p.Next; return p.GetHashCode(); } }").Errors("M"));
        }

        [Fact]
        public void LibraryNullness_IsKnown()
        {
            // a concatenation is never null; a static readonly field made with an object is not; TryGetValue's out
            // value is not null when it returns true
            Assert.Empty(Errors("M", "static int M(string a) => (a + \"x\").Length;"));
            Assert.Empty(Errors("M", "static readonly int[] T = new int[4]; static int M() => T.Length;"));
            Assert.Empty(Errors("M", "static int M(System.Collections.Generic.Dictionary<int, string> d) => d.TryGetValue(1, out var s) ? s.Length : 0;"));
            Assert.Equal(new[] { "CSV1013" }, Errors("M", "static int M(System.Collections.Generic.Dictionary<int, string> d) => d.TryGetValue(1, out var s) ? 0 : s.Length;"));
            // a method group made a delegate is not null; a list of strings holds strings
            Assert.Empty(Errors("M", "static int Cmp(int a, int b) => 0; static void M(int[] a) { System.Array.Sort(a, Cmp); }"));
            Assert.Empty(Errors("M", "static int M(System.Collections.Generic.List<string> l) { Spec.Requires(l != null); return l.Count > 0 ? l[0].Length : 0; }"));
            Assert.Equal(new[] { "CSV1013" }, Errors("M", "static int M(System.Collections.Generic.List<string?> l) => l.Count > 0 ? l[0].Length : 0;"));
        }

        [Fact]
        public void ArrayElements_AreMaybeNull()
        {
            // C# lets string[] hold nulls (new string[n] is all nulls): only a specification says otherwise
            const string m = "static int M(string[] a) { Spec.Requires(a.Length > 0); REQ return a[0].Length; }";
            Assert.Equal(new[] { "CSV1013" }, Errors("M", m.Replace("REQ", "")));
            Assert.Empty(Errors("M", m.Replace("REQ", "Spec.Requires(Spec.Forall(0, a.Length, i => a[i] != null));")));
            Assert.Equal(new[] { "CSV1013" }, Errors("M", "static int M() { var a = new string[1]; return a[0].Length; }"));
        }

        [Fact]
        public void ObliviousTypes_AreMaybeNull() =>
            Assert.Equal(new[] { "CSV1013" }, Errors("M", "\n#nullable disable\n static int M(int[] a) => a.Length;\n#nullable restore\n"));

        [Fact]
        public void LibraryNullabilityAttributes_AreTrusted()
        {
            Assert.Empty(Errors("M", "static int M(string? s) { if (string.IsNullOrEmpty(s)) return 0; return s.Length; }"));
            Assert.Empty(Errors("M", "static int M(string? s) { ArgumentNullException.ThrowIfNull(s); return s.Length; }"));
            Assert.Empty(Errors("M", "static int M(string s) => s.Trim().Length;")); // Trim returns string, not string?
        }
    }
}
