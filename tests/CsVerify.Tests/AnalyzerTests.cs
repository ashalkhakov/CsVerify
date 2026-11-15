using System.IO;
using System.Linq;
using System.Reflection;
using Microsoft.CodeAnalysis;
using Xunit;

namespace CsVerify.Tests
{
    public class LinearityTests
    {
        private static string[] Body(string body, string parameters = "") =>
            Harness.Analyze("static class C { static void M(" + parameters + ") { " + body + " } }");

        [Fact]
        public void AllocReadFree_IsClean() =>
            Assert.Empty(Body("var p = Mem.Alloc(1, out var v); int x = Mem.Read(in v, p); Mem.Write(ref v, p, 2); Mem.Free(v, p);"));

        [Fact]
        public void NeverConsumed_Leaks() =>
            Assert.Equal(new[] { "CSV0001" }, Body("var p = Mem.Alloc(1, out var v);"));

        [Fact]
        public void ConsumedOnOnePathOnly_Leaks() =>
            Assert.Equal(new[] { "CSV0001" }, Body("var p = Mem.Alloc(1, out var v); if (b) Mem.Free(v, p);", "bool b"));

        [Fact]
        public void ConsumedOnBothPaths_IsClean() =>
            Assert.Empty(Body("var p = Mem.Alloc(1, out var v); if (b) Mem.Free(v, p); else Mem.Free(v, p);", "bool b"));

        [Fact]
        public void DoubleConsume_IsReported() =>
            Assert.Equal(new[] { "CSV0002" }, Body("var p = Mem.Alloc(1, out var v); Mem.Free(v, p); Mem.Free(v, p);"));

        [Fact]
        public void BorrowAfterConsume_IsReported() =>
            Assert.Equal(new[] { "CSV0002" }, Body("var p = Mem.Alloc(1, out var v); Mem.Free(v, p); Mem.Read(in v, p);"));

        // (a ?: among a call's arguments has the flow graph capture the earlier ones first, ref ones too)
        [Fact]
        public void LentBeforeAConditionalArgument_IsStillABorrow() =>
            Assert.Empty(Body("var p = Mem.Alloc(1, out var v); Mem.Write(ref v, p, b ? 0 : 1); Mem.Free(v, p);", "bool b"));

        [Fact]
        public void MovedBeforeAConditionalArgument_IsStillAMove() =>
            Assert.Equal(new[] { "CSV0002" }, Body("var p = Mem.Alloc(1, out var v); Mem.Free(v, b ? p : p); Mem.Free(v, p);", "bool b"));

        [Fact]
        public void ConsumeInLoop_IsReported() =>
            Assert.Contains("CSV0002", Body("var p = Mem.Alloc(1, out var v); for (int i = 0; i < 2; i++) Mem.Free(v, p);"));

        [Fact]
        public void Move_TransfersOwnership()
        {
            Assert.Empty(Body("var p = Mem.Alloc(1, out var v); var w = v; Mem.Free(w, p);"));
            Assert.Equal(new[] { "CSV0002" }, Body("var p = Mem.Alloc(1, out var v); var w = v; Mem.Free(w, p); Mem.Free(v, p);"));
        }

        [Fact]
        public void ParameterByValue_MustBeConsumed()
        {
            Assert.Equal(new[] { "CSV0001" }, Body("", "PointsTo<int> v, Ptr<int> p"));
            Assert.Empty(Body("Mem.Free(v, p);", "PointsTo<int> v, Ptr<int> p"));
        }

        [Fact]
        public void Returning_Consumes() =>
            Assert.Empty(Harness.Analyze("static class C { static PointsTo<int> M(Ptr<int> p) { Mem.Alloc(1, out var v); return v; } }"));

        [Fact]
        public void RefParameter_IsBorrowed_AndMustBeGivenBack()
        {
            Assert.Empty(Body("Mem.Write(ref v, p, 3);", "ref PointsTo<int> v, Ptr<int> p"));
            Assert.Equal(new[] { "CSV0001" }, Body("Mem.Free(v, p);", "ref PointsTo<int> v, Ptr<int> p"));
        }

        [Fact]
        public void InParameter_CannotBeConsumed() =>
            Assert.Equal(new[] { "CSV0005" }, Body("Mem.Free(v, p);", "in PointsTo<int> v, Ptr<int> p"));

        private const string ViewParams = "ref ArrayView<int> v, Ptr<int> p";

        [Fact]
        public void ArrayView_SplitAndJoinedBack_IsClean() => Assert.Empty(Body(
            "Mem.Split(v, Ghost.Of(1), out var l, out var r); Mem.Set(ref r, p.Offset(1), 0, 5); Mem.Join(l, r, out v);", ViewParams));

        [Fact]
        public void ArrayView_NotJoinedBack_LeaksBothHalves() => Assert.Equal(new[] { "CSV0001", "CSV0001", "CSV0001" }, Body(
            "Mem.Split(v, Ghost.Of(1), out var l, out var r);", ViewParams));

        [Fact]
        public void ArrayView_HalfUsedAfterJoin_IsReported() => Assert.Equal(new[] { "CSV0002" }, Body(
            "Mem.Split(v, Ghost.Of(1), out var l, out var r); Mem.Join(l, r, out v); Mem.Set(ref l, p, 0, 1);", ViewParams));

        [Fact]
        public void TakeOut_MustBePutBack()
        {
            Assert.Empty(Body("Mem.TakeOut(v, Ghost.Of(0), out var c, out var h); Mem.Write(ref c, p, 1); Mem.PutBack(c, h, out v);", ViewParams));
            Assert.Equal(new[] { "CSV0001", "CSV0001", "CSV0001" }, Body("Mem.TakeOut(v, Ghost.Of(0), out var c, out var h);", ViewParams));
        }

        [Fact]
        public void FreeArray_ConsumesViewAndToken() =>
            Assert.Empty(Body("var p = Mem.AllocArray(4, 0, out var v, out var gc); Mem.Set(ref v, p, 3, 1); Mem.FreeArray(gc, v, p);"));

        [Fact]
        public void LambdaCapture_IsReported() =>
            Assert.Contains("CSV0003", Body("var p = Mem.Alloc(1, out var v); Func<int> f = () => Mem.Read(in v, p); Mem.Free(v, p);"));

        [Fact]
        public void Boxing_IsReported() =>
            Assert.Contains("CSV0004", Body("var p = Mem.Alloc(1, out var v); object o = v;"));

        [Fact]
        public void FieldInNonLinearType_IsReported()
        {
            Assert.Equal(new[] { "CSV0004" }, Harness.Analyze("class Holder { PointsTo<int> view; }"));
            Assert.Empty(Harness.Analyze("[Linear] struct Pair { PointsTo<int> a; PointsTo<int> b; }"));
        }

        [Fact]
        public void Forging_IsReported_OutsideTrusted()
        {
            Assert.Contains("CSV0006", Body("var v = default(PointsTo<int>); Mem.Free(v, p);", "Ptr<int> p"));
            Assert.Empty(Harness.Analyze("static class C { [Trusted] static void M(Ptr<int> p) { var v = default(PointsTo<int>); Mem.Free(v, p); } }"));
        }

        [Fact]
        public void UsesInsideSpecifications_AreGhost() =>
            Assert.Empty(Body("var p = Mem.Alloc(1, out var v); Spec.Assert(v.Addr == p.Addr); Mem.Free(v, p); Spec.Assert(v.Addr == p.Addr);"));

        [Fact]
        public void UserDefinedLinearType_IsTracked() =>
            Assert.Equal(new[] { "CSV0001" }, Harness.Analyze(
                "[Linear] struct Token { } static class C { [Trusted] static Token Make() => default; " +
                "static void M() { var t = Make(); } }"));
    }

    public class GhostTests
    {
        [Fact]
        public void GhostValue_InsideSpec_IsClean() =>
            Assert.Empty(Harness.Analyze("static class C { static int M(int[] a, Ghost<int> n) { Spec.Requires(a.Length == n.Value); return a.Length; } }"));

        [Fact]
        public void GhostValue_AtRunTime_IsReported() =>
            Assert.Equal(new[] { "CSV0010" }, Harness.Analyze("static class C { static int M(Ghost<int> n) => n.Value; }"));

        [Fact]
        public void GhostValue_InLemmaBodyAndArguments_IsClean() =>
            Assert.Empty(Harness.Analyze(
                "static class C { [Lemma, Conditional(\"CSVERIFY_SPEC\")] static void L(int n) { int m = Ghost.Of(n).Value; } " +
                "static void M(Ghost<int> g) { L(g.Value); } }"));

        [Fact]
        public void Lemma_MustBeVoid() =>
            Assert.Equal(new[] { "CSV0011" }, Harness.Analyze("static class C { [Lemma] static int L() => 0; }"));

        [Fact]
        public void Lemma_MustBeConditional()
        {
            Assert.Equal(new[] { "CSV0011" }, Harness.Analyze("static class C { [Lemma] static void L() { } }"));
            Assert.Empty(Harness.Analyze("static class C { [Lemma, Conditional(\"CSVERIFY_SPEC\")] static void L() { } }"));
        }

        [Fact]
        public void ResultOnlyInEnsures_OldAlsoInInvariantsAndAssertions()
        {
            Assert.Empty(Harness.Analyze("static class C { static int M(int x) { Spec.Ensures(Spec.Result<int>() > Spec.Old(x)); return x + 1; } }"));
            Assert.Empty(Harness.Analyze("static class C { static void M(int x) { while (x > 0) { Spec.Invariant(x <= Spec.Old(x)); x--; } Spec.Assert(Spec.Old(x) >= x); } }"));
            Assert.Equal(new[] { "CSV0012" }, Harness.Analyze("static class C { static void M(int x) { Spec.Requires(Spec.Old(x) == x); } }"));
            Assert.Equal(new[] { "CSV0012" }, Harness.Analyze("static class C { static void M(int x) { Spec.Assert(Spec.Result<int>() == x); } }"));
        }

        [Fact]
        public void GhostFunction_BodyIsGhost_ButCallsAreSpecOnly()
        {
            const string fn = "[GhostFunction] static bool AllZero(Seq<int> s, int n) => Spec.Forall(0, n, j => s[j].Value == 0); ";
            Assert.Empty(Harness.Analyze("static class C { " + fn + "static void M(ref ArrayView<int> v) { Spec.Requires(AllZero(v.Elems, 2)); } }"));
            Assert.Equal(new[] { "CSV0010" }, Harness.Analyze("static class C { " + fn + "static bool M(ArrayView<int> v) { var b = AllZero(v.Elems, 2); Mem.LengthIsNatural(in v); return b; } }")
                .Where(id => id != "CSV0001").ToArray());
        }

        [Fact]
        public void SeqOperations_AtRunTime_AreReported() =>
            Assert.Equal(new[] { "CSV0010", "CSV0010" }, Harness.Analyze("static class C { static void M(Seq<int> s) { var t = s.Drop(1); var x = s[0]; } }"));

        [Fact]
        public void Quantifier_AtRunTime_IsReported()
        {
            Assert.Empty(Harness.Analyze("static class C { static void M(int[] a) { Spec.Assert(Spec.Forall(0, a.Length, i => a[i] >= 0)); } }"));
            Assert.Equal(new[] { "CSV0010" }, Harness.Analyze("static class C { static bool M(int[] a) => Spec.Forall(0, a.Length, i => a[i] >= 0); }"));
        }
    }

    public class ErasureTests
    {
        /// <summary>Without CSVERIFY_SPEC the compiler removes Spec calls and their arguments: specs cost nothing.</summary>
        [Fact]
        public void SpecCalls_AndTheirArguments_AreErased()
        {
            var source = @"public static class C {
                public static int Calls;
                static bool Count() { Calls++; return false; }
                [Lemma, Conditional(""CSVERIFY_SPEC"")] static void L(int n) { Calls++; }
                public static int M(int x) {
                    Spec.Requires(Count()); Spec.Ensures<int>(r => Count()); Spec.Assert(Count()); L(x);
                    var p = Mem.Alloc(x, out var v); int y = Mem.Read(in v, p); Mem.Free(v, p);
                    return y; } }";
            var compilation = Harness.Compile(source);
            using var ms = new MemoryStream();
            var emit = compilation.Emit(ms);
            Assert.True(emit.Success, string.Join("\n", emit.Diagnostics));
            var asm = Assembly.Load(ms.ToArray());
            var c = asm.GetType("C");
            Assert.Equal(7, c.GetMethod("M").Invoke(null, new object[] { 7 }));
            Assert.Equal(0, c.GetField("Calls").GetValue(null));
        }

        /// <summary>Views and ghosts carry no data: an empty struct, the CLR's minimum of one byte.</summary>
        [Fact]
        public void ViewTokens_CarryNoData()
        {
            Assert.Equal(1, System.Runtime.CompilerServices.Unsafe.SizeOf<PointsTo<long>>());
            Assert.Equal(1, System.Runtime.CompilerServices.Unsafe.SizeOf<Ghost<long>>());
            Assert.Empty(typeof(PointsTo<long>).GetFields(BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic));
        }
    }
}

namespace CsVerify.Tests
{
    /// <summary>Proofs and specifications have no side effects (CSV0013); one linear value is one argument (CSV0007).</summary>
    public class PurityTests
    {
        private const string LemmaAttrs = "[Lemma, Conditional(\"CSVERIFY_SPEC\")] ";

        [Fact]
        public void ProofScratchSpace_IsAllowed() => Assert.Empty(Harness.Analyze(
            "static class C { " + LemmaAttrs + "static void L(int n) { int k = 0; while (k < n) { Spec.Decreases(n - k); k++; } n = 0; } " +
            "[Pure] static int F(int[] a, int i) { int j = i; j++; return Math.Max(a.Length, j); } }"));

        [Fact]
        public void LemmaWritingTheHeap_IsReported() => Assert.Equal(new[] { "CSV0013" }, Harness.Analyze(
            "static class C { " + LemmaAttrs + "static void L(int[] a) { a[0] = 1; } }"));

        [Fact]
        public void PureCallingImpureCode_IsReported() => Assert.Equal(new[] { "CSV0013" }, Harness.Analyze(
            "static class C { static int G() => 1; [Pure] static int F() => G(); }"));

        [Fact]
        public void PureAllocating_IsReported() => Assert.Equal(new[] { "CSV0013" }, Harness.Analyze(
            "static class C { [Pure] static int[] F() => new int[1]; }"));

        [Fact]
        public void SideEffectInSpecification_IsReported() => Assert.Equal(new[] { "CSV0013" }, Harness.Analyze(
            "static class C { static void M(int x) { Spec.Assert(x++ > 0); } }"));

        [Fact]
        public void ProofSignatures()
        {
            Assert.Equal(new[] { "CSV0013" }, Harness.Analyze("static class C { [Pure] static int F(ref int x) => x; }"));
            // a [Pure] query may be virtual (overrides honour its contract), but its overrides must be [Pure] too;
            // a lemma or ghost function is one fixed proof or definition
            Assert.Empty(Harness.Analyze("class C { [Pure] public virtual int F(int x) => x; }"));
            // an override of a [Pure] query is [Pure] itself: its body may have no side effects
            Assert.Equal(new[] { "CSV0013" }, Harness.Analyze("class C { [Pure] public virtual int F(int x) => x; } class D : C { int _n; public override int F(int x) { _n = x; return x; } }"));
            Assert.Equal(new[] { "CSV0013" }, Harness.Analyze("class C { [GhostFunction] public virtual int F(int x) => x; }"));
        }

        [Fact]
        public void LinearValue_PassedTwice_IsReported()
        {
            const string swap = "static void Swap(ref PointsTo<int> a, ref PointsTo<int> b, Ptr<int> p, Ptr<int> q) { } " +
                                "static int Peek(in PointsTo<int> a, in PointsTo<int> b, Ptr<int> p) => 0; ";
            Assert.Equal(new[] { "CSV0007" }, Harness.Analyze("static class C { " + swap +
                "static void M() { var p = Mem.Alloc(1, out var v); Swap(ref v, ref v, p, p); Mem.Free(v, p); } }"));
            Assert.Empty(Harness.Analyze("static class C { " + swap +
                "static void M() { var p = Mem.Alloc(1, out var v); Peek(in v, in v, p); Mem.Free(v, p); } }"));
        }
    }
}
