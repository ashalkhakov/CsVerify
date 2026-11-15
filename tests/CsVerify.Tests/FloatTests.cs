using Xunit;

namespace CsVerify.Tests
{
    /// <summary>float and double as IEEE 754: what verifies is true of the program as it runs.</summary>
    public class FloatTests
    {
        [Fact]
        public void Floats_AreIeeeNotReals()
        {
            var r = Harness.Verify(@"public static class C {
    static void Facts() {
        Spec.Assert(0.1 + 0.2 != 0.3);
        Spec.Assert(1.0 / 0.0 == double.PositiveInfinity);
        double nan = 0.0 / 0.0;
        Spec.Assert(nan != nan && double.IsNaN(nan));
        Spec.Assert(-0.0 == 0.0 && double.IsNaN(System.Math.Max(1.0, nan))); }
    static void Successor(double x) { Spec.Assert(x + 1.0 > x); }
    static void Reflexive(double x) { Spec.Assert(x == x); }
    static void ReflexiveIfNumber(double x) { Spec.Requires(!double.IsNaN(x)); Spec.Assert(x == x); }
}");
            Assert.Empty(r.Errors("Facts"));
            Assert.Equal(new[] { "CSV1004" }, r.Errors("Successor"));
            Assert.Equal(new[] { "CSV1004" }, r.Errors("Reflexive"));
            Assert.Empty(r.Errors("ReflexiveIfNumber"));
        }

        [Fact]
        public void Floats_LiveInFieldsAndArrays()
        {
            var r = Harness.Verify(@"public sealed class P { public float X; }
public static class C {
    static float Low(float[] xs, P p) {
        Spec.Requires(xs.Length > 0 && !float.IsNaN(xs[0]) && !float.IsNaN(p.X));
        Spec.Ensures((float r) => r <= p.X && r <= xs[0]);
        return System.MathF.Min(p.X, xs[0]); }
    static double Zero() { Spec.Ensures((double r) => r == 0.0); var a = new double[2]; return a[1]; }
}");
            Assert.Empty(r.Errors("Low"));
            Assert.Empty(r.Errors("Zero"));
        }

        [Fact]
        public void CastsToIntegers_MustFit()
        {
            var r = Harness.Verify(@"public static class C {
    static int Any(double d) => (int)d;
    static int InRange(double d) { Spec.Requires(0 <= d && d < 100); Spec.Ensures((int r) => 0 <= r && r < 100); return (int)d; }
    static int Checked(double d) { Spec.Ensures((int r) => r >= 0 || r < 0); return checked((int)d); }
}");
            Assert.Equal(new[] { "CSV1010" }, r.Errors("Any"));
            Assert.Empty(r.Errors("InRange"));
            Assert.Empty(r.Errors("Checked"));
        }

        [Fact]
        public void CastsToIntegers_InSpecifications_MustFitToo()
        {
            // a cast that does not fit has no value: in a specification it must be shown to fit, as a divisor is
            var r = Harness.Verify(@"public static class C {
    static void Unguarded(double d) { Spec.Assert((int)d >= int.MinValue); }
    static void Guarded(double d) { Spec.Assert(!(0 <= d && d < 100) || (int)d < 100); }
    static void ByTernary(double d) { Spec.Assert((d >= 0 && d <= 10 ? (int)d : 0) <= 10); }
    static void InEnsures(double d) { Spec.Requires(0 <= d && d < 5); Spec.Ensures((int)d < 5); }
    static void Big(double d) { Spec.Requires(d == 1e300); Spec.Assert((int)d != 0 || true); }
}");
            Assert.Equal(new[] { "CSV1012" }, r.Errors("Unguarded"));
            Assert.Empty(r.Errors("Guarded"));
            Assert.Empty(r.Errors("ByTernary"));
            Assert.Empty(r.Errors("InEnsures"));
            Assert.Equal(new[] { "CSV1012" }, r.Errors("Big"));
        }
    
        [Fact]
        public void MonotonicityLemmas_ProveWhatBitBlastingCannotQuickly()
        {
            var r = Harness.Verify(@"public static class C {
    static float Scaled(float lo, float hi, float s) {
        Spec.Requires(lo <= hi && s >= 0 && float.IsFinite(lo) && float.IsFinite(hi) && float.IsFinite(s));
        Spec.Ensures((float r) => lo * s <= r);
        Ieee.MulMonotone(lo, hi, s);
        return hi * s; }
    static void Needs(float x, float z) {
        Spec.Requires(z >= 0 && float.IsFinite(z));
        Ieee.MulMonotone(x, x, z); }
}");
            Assert.Empty(r.Errors("Scaled"));
            Assert.Equal(new[] { "CSV1001" }, r.Errors("Needs")); // x may be infinite (an infinity times 0 is NaN)
        }

        [Fact]
        public void Remainder_IsFmod()
        {
            var r = Harness.Verify(@"public static class C {
    static void Exact() { double a = 7.5 % 2.0; Spec.Assert(a == 1.5); double b = -7.5 % 2.0; Spec.Assert(b == -1.5);
        double c = 7.0 % -2.0; Spec.Assert(c == 1.0); float d = 5.5f % 1.0f; Spec.Assert(d == 0.5f); Spec.Assert(double.IsNaN(1.0 % 0.0)); }
    static void Wrong() { double a = -7.5 % 2.0; Spec.Assert(a == 0.5); }
}");
            Assert.Empty(r.Errors("Exact"));
            Assert.Equal(new[] { "CSV1004" }, r.Errors("Wrong")); // IEEE's remainder would be 0.5; C#'s keeps x's sign
        }
}
}
