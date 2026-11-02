using System;
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
        public void RefParameter_IsBorrowed()
        {
            Assert.Empty(Body("Mem.Write(ref v, p, 3);", "ref PointsTo<int> v, Ptr<int> p"));
            Assert.Equal(new[] { "CSV0005" }, Body("Mem.Free(v, p);", "ref PointsTo<int> v, Ptr<int> p"));
        }

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
        public void ResultAndOld_OnlyInEnsures()
        {
            Assert.Empty(Harness.Analyze("static class C { static int M(int x) { Spec.Ensures(Spec.Result<int>() > Spec.Old(x)); return x + 1; } }"));
            Assert.Equal(new[] { "CSV0012" }, Harness.Analyze("static class C { static void M(int x) { Spec.Assert(Spec.Old(x) == x); } }"));
        }

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
