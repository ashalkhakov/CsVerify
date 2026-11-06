using System;
using System.Linq;
using System.Text;
using Xunit;

namespace CsVerify.Tests
{
    /// <summary>Bitwise operators and shifts, what a method's array writes leave alone, and the samples against .NET.</summary>
    public class BitTests
    {
        private const string Rejected = "CSV1004";

        private static string[] Errors(string body) =>
            Harness.Verify("using CsVerify; using System; public static class C { " + body + " }").Errors("M");

        [Theory]
        [InlineData("int", "(x & 255) >= 0 && (x & 255) <= 255")]
        [InlineData("int", "(x | 1) != 0")]
        [InlineData("int", "(x >> 1) * 2 + (x & 1) == x")]
        [InlineData("long", "(x >> 40) * 1099511627776L + (x & 1099511627775L) == x")]
        [InlineData("uint", "(x >> 31) <= 1u")]
        [InlineData("int", "(~x) == -x - 1")]
        [InlineData("uint", "(~x) == 4294967295u - x")]
        [InlineData("int", "(x >>> 31) == (x < 0 ? 1 : 0)")]
        [InlineData("int", "(x ^ 0) == x")]
        [InlineData("int", "(x ^ -1) == ~x")]
        [InlineData("int", "(x & -1) == x")]
        [InlineData("int", "(x << 32) == x")]
        [InlineData("int", "(x >> 33) == (x >> 1)")]
        public void Facts_Hold(string type, string fact) => Assert.Empty(Errors($"static void M({type} x) {{ Spec.Assert({fact}); }}"));

        [Theory]
        [InlineData("int", "(x >> 1) >= 0")]         // (negative stays negative)
        [InlineData("int", "(x >>> 1) == (x >> 1)")]  // (not for negative values)
        [InlineData("int", "(x << 1) == x * 2 && x > 100000")]
        [InlineData("int", "(x & 255) == x")]
        [InlineData("int", "(x | 1) == x + 1")]
        [InlineData("int", "(x ^ 1) == x + 1")]
        [InlineData("uint", "(~x) == 0u")]
        public void WrongFacts_AreRejected(string type, string fact) => Assert.Equal(new[] { Rejected }, Errors($"static void M({type} x) {{ Spec.Assert({fact}); }}"));

        [Fact]
        public void Shifts_DoNotOverflow_EvenChecked() => Assert.Empty(Errors("static int M(int x) { return checked(x << 8); }"));

        [Fact]
        public void Packing_ComesApartAgain() => Assert.Empty(Errors(
            "static void M(byte a, byte b) { int n = (a << 8) | b; Spec.Assert((n >> 8) == a && (n & 255) == b); }"));

        [Fact]
        public void Packing_WrongHalf_IsRejected() => Assert.Equal(new[] { Rejected }, Errors(
            "static void M(byte a, byte b) { int n = (a << 8) | b; Spec.Assert((n >> 8) == b); }"));

        [Fact]
        public void Masks_DecideARange() => Assert.Empty(Errors(
            "static void M(byte b) { if ((b & 0xE0) == 0xC0) Spec.Assert(0xC0 <= b && b <= 0xDF); }"));

        [Theory]
        [InlineData("byte", "c &= 15; Spec.Assert(c <= 15);")]
        [InlineData("sbyte", "c &= 15; Spec.Assert(0 <= c && c <= 15);")]
        [InlineData("short", "c |= 1; Spec.Assert(c != 0);")]
        [InlineData("ushort", "c ^= 0; Spec.Assert(c == a);")]
        public void Compound_OfSmallTypes(string type, string body) => Assert.Empty(Errors($"static void M({type} a) {{ {type} c = a; {body} }}"));

        [Fact]
        public void Narrowing_AMask_IsProved() => Assert.Empty(Errors("static byte M(int x) { return (byte)(x & 255); }"));

        [Fact]
        public void Narrowing_TooWideAMask_IsReported() => Assert.Equal(new[] { "CSV1010" }, Errors("static byte M(int x) { return (byte)(x & 511); }"));

        [Fact]
        public void TwoUnknowns_Bit_By_Bit() => Assert.Empty(Errors(
            "static void M(int x, int y) { Spec.Requires(x == 12 && y == 10); Spec.Assert((x & y) == 8 && (x | y) == 14 && (x ^ y) == 6); }"));

        [Fact]
        public void TwoUnknowns_NotAnythingGoes() => Assert.Equal(new[] { Rejected }, Errors(
            "static void M(int x, int y) { Spec.Assert((x & y) == x); }"));

        [Fact]
        public void UnderAQuantifier() => Assert.Empty(Errors(
            "static void M(int[] a) { Spec.Requires(Spec.Forall(0, a.Length, i => (a[i] & 1) == 0)); if (a.Length > 0) Spec.Assert(a[0] % 2 == 0); }"));

        [Fact]
        public void Lifted() => Assert.Empty(Errors("static void M(int? x) { int? y = x & 3; if (y != null) Spec.Assert(y.Value <= 3); }"));

        // ---- what a call's array writes leave alone ---------------------------------------------------------------

        private const string Keeps = "static void M(int[] a) { Spec.Requires(a.Length > 0 && a[0] == 7); F(a); Spec.Assert(a[0] == 7); }";

        [Fact]
        public void Call_WritingOnlyItsOwnNewArray_LeavesOthersAlone() => Assert.Empty(Errors(
            Keeps + "static int[] F(int[] x) { var t = new int[1]; t[0] = 1; return t; }"));

        [Fact]
        public void Call_WritingItsParameter_ForgetsTheArray() => Assert.Equal(new[] { Rejected }, Errors(
            Keeps + "static int[] F(int[] x) { x[0] = 1; return x; }"));

        [Fact]
        public void Call_ReassigningTheLocal_ForgetsTheArray() => Assert.Equal(new[] { Rejected }, Errors(
            Keeps + "static int[] F(int[] x) { var t = new int[1]; t = x; t[0] = 1; return t; }"));

        [Fact]
        public void Call_ThroughAnAlias_ForgetsTheArray() => Assert.Equal(new[] { Rejected }, Errors(
            Keeps + "static int[] F(int[] x) { var t = x; t[0] = 1; return t; }"));

        [Fact]
        public void Call_RefToTheLocal_ForgetsTheArray() => Assert.Equal(new[] { Rejected }, Errors(
            Keeps + "static int[] F(int[] x) { var t = new int[1]; G(ref t, x); t[0] = 1; return t; } static void G(ref int[] t, int[] x) { t = x; }"));

        // (the callee may write without an element access on the left: each of these changes a[0])
        [Theory]
        [InlineData("static void F(int[] x) { Spec.Requires(x.Length > 1); ref int r = ref x[0]; r = 1; }")]
        [InlineData("static void F(int[] x) { Spec.Requires(x.Length > 1); ref int r = ref x[0]; r++; }")]
        [InlineData("static void G(ref int v) { v = 1; } static void F(int[] x) { Spec.Requires(x.Length > 1); ref int r = ref x[0]; G(ref r); }")]
        [InlineData("static void F(int[] x) { Spec.Requires(x.Length > 1); ref int r = ref (x.Length > 5 ? ref x[1] : ref x[0]); r = 1; }")]
        [InlineData("static void F(int[] x) { Spec.Requires(x.Length > 1); (x[0], x[1]) = (1, 2); }")]
        [InlineData("static void F(int[] x) { Spec.Requires(x.Length > 1); int k; (k, (x[0], x[1])) = (0, (1, 2)); }")]
        [InlineData("static void F(int[] x) { Spec.Requires(x.Length > 1); foreach (var (p, q) in new[] { (1, 2) }) { (x[0], x[1]) = (p, q); } }")]
        public void Call_WritingWithoutAnElementOnTheLeft_ForgetsTheArray(string callee) => Assert.Contains(Rejected, Errors(
            "static void M(int[] a) { Spec.Requires(a.Length > 1 && a[0] == 7); F(a); Spec.Assert(a[0] == 7); } " + callee));

        [Fact]
        public void Call_ThroughARefToAStructElement_ForgetsTheArray() => Assert.Contains(Rejected, Errors(
            "struct S { public int V; } static void M(S[] a) { Spec.Requires(a.Length > 0); int b = a[0].V; F(a); Spec.Assert(a[0].V == b); } " +
            "static void F(S[] x) { Spec.Requires(x.Length > 0); ref S r = ref x[0]; r.V = b0; } const int b0 = 1;"));

        [Fact]
        public void Call_ReturningARef_ForgetsTheArray()
        {
            var errors = Harness.Verify("using CsVerify; public static class C { static void M(int[] a) { Spec.Requires(a.Length > 0 && a[0] == 7); W(a); Spec.Assert(a[0] == 7); } " +
                "static ref int Slot(int[] x) { Spec.Requires(x.Length > 0); return ref x[0]; } static void W(int[] x) { Spec.Requires(x.Length > 0); Slot(x) = 1; } }").Errors("M");
            Assert.Contains(Rejected, errors);
        }

        // (the callee's new arrays, however they are held: a[0] stays)
        [Theory]
        [InlineData("var t = new int[1]; var u = t; u[0] = 1; return u;")]
        [InlineData("int[] t; t = new int[1]; t[0] = 1; return t;")]
        [InlineData("var t = new int[1]; var u = new int[1]; var v = x.Length > 3 ? t : u; v[0] = 1; return v;")]
        [InlineData("var t = new int[1]; var u = t; t = u; t[0] = 1; return t;")]
        [InlineData("var t = new int[1]; t = new int[2]; t[0] = 1; return t;")]
        [InlineData("var t = new int[1]; var u = (t); (u)[0] = 1; return u;")]
        [InlineData("var t = new int[1]; ref int r = ref t[0]; r = 1; return t;")]
        [InlineData("var t = new[] { 1, 2 }; (t[0], t[1]) = (3, 4); return t;")]
        public void Call_WritingOnlyNewArrays_LeavesOthersAlone(string body) => Assert.Empty(Errors(
            Keeps + "static int[] F(int[] x) { " + body + " }"));

        // (an alias that isn't one: x gets in)
        [Theory]
        [InlineData("var t = new int[1]; var u = t; u = x; t = u; t[0] = 1; return t;")]
        [InlineData("var t = new int[1]; var u = x.Length > 3 ? t : x; u[0] = 1; return u;")]
        [InlineData("var t = new int[1]; var u = t; (t, u) = (x, t); u[0] = 1; t[0] = 1; return t;")]
        [InlineData("int[] t; int[] u = new int[1]; t = u; u = x; t[0] = 1; u[0] = 1; return t;")]
        [InlineData("var t = new int[1]; t ??= x; var u = x; u[0] = 1; return t;")]
        [InlineData("var t = new int[1]; Func<int[]> g = () => x; var u = g(); u[0] = 1; return u;")]
        [InlineData("var t = new int[1]; int[] u = t; ref int[] r = ref u; r = x; u[0] = 1; return u;")]
        [InlineData("var u = Id(x); u[0] = 1; return u;")]
        [InlineData("var u = (int[])x; u[0] = 1; return u;")]
        [InlineData("int[][] j = { x }; var u = j[0]; u[0] = 1; return u;")]
        [InlineData("var t = new int[1]; var u = t; u = Id(x); u[0] = 1; return u;")]
        public void Call_AnAliasThatMayHoldTheParameter_ForgetsTheArray(string body) => Assert.Contains(Rejected, Errors(
            Keeps + "static int[] Id(int[] y) { return y; } static int[] F(int[] x) { " + body + " }"));

        // (a local function's array is not its own: the method around it holds it, and may read it after the call)
        [Fact]
        public void LocalFunction_WritingACapturedNewArray_IsAWrite() => Assert.Equal(new[] { Rejected }, Errors(
            "static void M() { var t = new int[1]; void L() { t[0] = 1; } L(); Spec.Assert(t[0] == 0); }"));

        [Fact]
        public void LocalFunction_WritingACapturedReassignedArray_IsAWrite() => Assert.Equal(new[] { Rejected }, Errors(
            "static void M(int[] x) { Spec.Requires(x.Length > 0 && x[0] == 7); var t = new int[1]; t = x; void L() { t[0] = 1; } L(); Spec.Assert(x[0] == 7); }"));

        [Fact]
        public void LocalFunction_WritingItsOwnNewArray_LeavesOthersAlone() => Assert.Empty(Errors(
            "static void M(int[] x) { Spec.Requires(x.Length > 0 && x[0] == 7); void L() { var t = new int[1]; t[0] = 1; } L(); Spec.Assert(x[0] == 7); }"));

        [Fact]
        public void Loop_AFramedCall_KeepsWhatTheInvariantSays() => Assert.Empty(Errors(FillIt +
            "static void M(int[] a, int[] b) { Spec.Requires(a.Length > 0 && b.Length > 0 && a != b && a[0] == 7); for (int i = 0; i < 2; i++) { Spec.Invariant(a[0] == 7); Fill(b); } Spec.Assert(a[0] == 7); }"));

        [Fact]
        public void Loop_AFramedCall_WrongInvariantIsRejected() => Assert.NotEmpty(Errors(FillIt +
            "static void M(int[] a) { Spec.Requires(a.Length > 0 && a[0] == 7); for (int i = 0; i < 2; i++) { Spec.Invariant(a[0] == 7); Fill(a); } }"));

        [Fact]
        public void Fresh_AResultIsAnotherArray() => Assert.Empty(Errors(
            "static int[] N() { Spec.Ensures<int[]>(r => Spec.Fresh(r)); return new int[1]; } " +
            "static void M(int[] a) { var r = N(); var s = N(); var t = new int[1]; Spec.Assert(r != a && r != s && t != r && t != a); }"));

        [Fact]
        public void WithoutFresh_AResultMayBeAnyArray() => Assert.Equal(new[] { Rejected }, Errors(
            "static int[] N() { return new int[1]; } static void M(int[] a) { var r = N(); Spec.Assert(r != a); }"));

        [Fact]
        public void Fresh_AWriteToIt_ThroughAnAlias_LeavesOthersAlone() => Assert.Empty(Errors(
            "static int[] N() { Spec.Ensures<int[]>(r => Spec.Fresh(r) && r.Length == 1); return new int[1]; } " +
            "static void M(int[] a) { Spec.Requires(a.Length > 0 && a[0] == 7); var r = N(); var s = r; s[0] = 1; Spec.Assert(a[0] == 7 && r[0] == 1); }"));

        // ---- Spec.Modifies, for arrays -----------------------------------------------------------------------------

        private const string FillIt = "static void Fill(int[] x) { Spec.Requires(x.Length > 0); Spec.Modifies(ObjSet.Of(x)); x[0] = 1; } ";

        [Fact]
        public void Modifies_TheCallChangesOnlyTheFrame() => Assert.Empty(Errors(FillIt +
            "static void M(int[] a, int[] b) { Spec.Requires(a.Length > 0 && b.Length > 0 && a != b && a[0] == 7); Fill(b); Spec.Assert(a[0] == 7); }"));

        [Fact]
        public void Modifies_TheFrameItselfIsForgotten() => Assert.Equal(new[] { Rejected }, Errors(FillIt +
            "static void M(int[] a) { Spec.Requires(a.Length > 0 && a[0] == 7); Fill(a); Spec.Assert(a[0] == 7); }"));

        [Fact]
        public void Modifies_APossibleAliasIsForgotten() => Assert.Equal(new[] { Rejected }, Errors(FillIt +
            "static void M(int[] a, int[] b) { Spec.Requires(a.Length > 0 && b.Length > 0 && a[0] == 7); Fill(b); Spec.Assert(a[0] == 7); }"));

        [Fact]
        public void Modifies_AHelperFillingANewArray() => Assert.Empty(Errors(FillIt +
            "static int[] N() { Spec.Modifies(ObjSet.Empty); var t = new int[1]; Fill(t); return t; } " +
            "static void M(int[] a) { Spec.Requires(a.Length > 0 && a[0] == 7); N(); Spec.Assert(a[0] == 7); }"));

        [Fact]
        public void Modifies_AnotherArrayKeepsItsContentsThroughFrames() => Assert.Empty(Errors(FillIt +
            "static void Twice(int[] x, int[] y) { Spec.Requires(x.Length > 0 && y.Length > 0); Spec.Modifies(ObjSet.Of(x).Add(y)); Fill(x); Fill(y); } " +
            "static void M(int[] a, int[] b, int[] c) { Spec.Requires(a.Length > 0 && b.Length > 0 && c.Length > 0 && a != b && a != c && a[0] == 7); Twice(b, c); Spec.Assert(a[0] == 7); }"));

        // (each writes x, which its frame leaves out: all reported where the write is)
        [Theory]
        [InlineData("x[0] = 1;")]
        [InlineData("x[0]++;")]
        [InlineData("ref int r = ref x[0]; r = 1;")]
        [InlineData("(x[0], x[0]) = (1, 2);")]
        [InlineData("var u = x; u[0] = 1;")]
        [InlineData("G(ref x[0]);")]
        [InlineData("Span<int> s = x; s[0] = 1;")]
        [InlineData("x.AsSpan().Fill(1);")]
        [InlineData("new int[1].AsSpan().CopyTo(x.AsSpan());")]
        [InlineData("Array.Fill(x, 1);")]
        [InlineData("Fill(x);")]
        [InlineData("H(x);")]
        [InlineData("Action a = () => { x[0] = 1; }; a();")]
        [InlineData("void L() { x[0] = 1; } L();")]
        public void Modifies_AWriteOutsideTheFrame_IsReported(string body) => Assert.Contains("CSV1017",
            Harness.Verify("using CsVerify; using System; public static class C { " + FillIt +
                "static void G(ref int v) { v = 1; } static void H(int[] y) { Spec.Requires(y.Length > 0); y[0] = 1; } " +
                "static void M(int[] x) { Spec.Requires(x.Length > 0); Spec.Modifies(ObjSet.Empty); " + body + " } }").Errors("M"));

        [Theory]
        [InlineData("x[0] = 1;")]
        [InlineData("ref int r = ref x[0]; r = 1;")]
        [InlineData("x.AsSpan().Fill(1);")]
        [InlineData("Array.Fill(x, 1);")]
        [InlineData("Fill(x);")]
        [InlineData("var t = new int[1]; t[0] = 1;")]
        public void Modifies_AWriteInsideTheFrame_IsFine(string body) => Assert.Empty(Errors(FillIt +
            "static void M(int[] x) { Spec.Requires(x.Length > 0); Spec.Modifies(ObjSet.Of(x)); " + body + " }"));

        [Fact]
        public void Modifies_ANewArrayFromAFreshCall_MayBeWritten() => Assert.Empty(Errors(
            "static int[] N() { Spec.Ensures<int[]>(r => Spec.Fresh(r) && r.Length == 1); return new int[1]; } " +
            "static void M() { Spec.Modifies(ObjSet.Empty); var t = N(); t[0] = 1; }"));

        [Fact]
        public void Modifies_AResultNotKnownFresh_MayNotBeWritten() => Assert.Contains("CSV1017", Errors(
            "static int[] N(int[] x) { Spec.Ensures<int[]>(r => r.Length == x.Length); return x; } " +
            "static void M(int[] x) { Spec.Requires(x.Length > 0); Spec.Modifies(ObjSet.Empty); var t = N(x); t[0] = 1; }"));

        [Fact]
        public void Modifies_AnArrayInAField_IsNamedByTheArray() => Assert.Contains("CSV1017", Errors(
            "class B { public int[] A = new int[1]; } static void M(B o) { Spec.Requires(o.A.Length > 0); Spec.Modifies(ObjSet.Of(o)); o.A[0] = 1; }"));

        [Fact]
        public void Modifies_ThroughAnOverride_TheBaseFrameHolds() => Assert.Contains("CSV1017",
            Harness.Verify("using CsVerify; public class B { public virtual void F(int[] x) { Spec.Requires(x.Length > 0); Spec.Modifies(ObjSet.Empty); } } " +
                "public class D : B { public override void F(int[] x) { x[0] = 1; } }").Errors("D.F"));

        [Fact]
        public void Call_ReturningADelegateThatWritesLater_ForgetsTheArray() => Assert.Contains(Rejected, Errors(
            "static void M() { Action act; var r = F(out act); Spec.Assume(r[0] == 0); act(); Spec.Assert(r[0] == 0); } " +
            "static int[] F(out Action w) { var t = new int[1]; w = () => { t[0] = 1; }; t[0] = 0; return t; }"));

        // ---- the samples, run against .NET ------------------------------------------------------------------------

        [Fact]
        public void Base64Sample_AgreesWithConvert()
        {
            var r = new Random(1);
            for (int n = 0; n < 300; n++)
            {
                var bytes = new byte[r.Next(0, 40)];
                r.NextBytes(bytes);
                var text = Samples.Good.Base64.Encode(bytes);
                Assert.Equal(Convert.ToBase64String(bytes), new string(text));
                Assert.Equal(bytes, Samples.Good.Base64.Decode(text));
            }
        }

        [Theory]
        [InlineData("Zg=")]    // (not a multiple of four)
        [InlineData("Zh==")]   // (unused bits set: not canonical)
        [InlineData("Zm9=")]   // (likewise)
        [InlineData("Z!==")]   // (not an alphabet character)
        [InlineData("====")]
        public void Base64Sample_RefusesWhatIsNotCanonical(string text) => Assert.Null(Samples.Good.Base64.Decode(text.ToCharArray()));

        [Fact]
        public void Utf8Sample_AgreesWithEncoding()
        {
            foreach (int cp in Enumerable.Range(0, 0x110000).Where(c => c < 0xD800 || c > 0xDFFF).Where((_, i) => i % 97 == 0).Concat(new[] { 0, 0x7F, 0x80, 0x7FF, 0x800, 0xD7FF, 0xE000, 0xFFFF, 0x10000, 0x10FFFF }))
            {
                var bytes = Samples.Good.Utf8.Encode(cp);
                Assert.Equal(Encoding.UTF8.GetBytes(char.ConvertFromUtf32(cp)), bytes);
                Assert.Equal(cp, Samples.Good.Utf8.Decode(bytes, 0));
            }
        }

        [Theory]
        [InlineData(0xC0, 0x80)]             // (overlong)
        [InlineData(0xC1, 0xBF)]             // (overlong)
        [InlineData(0xE0, 0x80, 0x80)]       // (overlong)
        [InlineData(0xED, 0xA0, 0x80)]       // (a surrogate)
        [InlineData(0xF0, 0x80, 0x80, 0x80)] // (overlong)
        [InlineData(0xF4, 0x90, 0x80, 0x80)] // (past the last code point)
        [InlineData(0x80)]                   // (a stray continuation)
        [InlineData(0xC2)]                   // (truncated)
        [InlineData(0xFF)]
        public void Utf8Sample_RefusesWhatTheStandardDoes(params int[] bytes) =>
            Assert.Equal(-1, Samples.Good.Utf8.Decode(bytes.Select(b => (byte)b).ToArray(), 0));
    }
}
