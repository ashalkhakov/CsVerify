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
