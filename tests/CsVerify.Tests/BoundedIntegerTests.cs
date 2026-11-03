using Xunit;

namespace CsVerify.Tests
{
    /// <summary>
    /// Bounded integers (the default): run-time arithmetic is C#'s. Overflow is reported unless it throws (checked)
    /// or wraps on purpose (unchecked); specifications and ghost code are mathematical.
    /// </summary>
    public class BoundedIntegerTests
    {
        private static string[] Errors(string method, string source, bool overflow = true) =>
            Harness.Verify("public static class C { " + source + " }", overflow).Errors(method);

        [Fact]
        public void SilentOverflow_IsReported()
        {
            Assert.Equal(new[] { "CSV1010" }, Errors("M", "static int M(int x) => x + 1;"));
            Assert.Empty(Errors("M", "static int M(int x) { Spec.Requires(x < int.MaxValue); return x + 1; }"));
            Assert.Equal(new[] { "CSV1010" }, Errors("M", "static int M(long l) => (int)l;"));
            // MinValue / -1 and Math.Abs(MinValue) throw in .NET: ordinary code goes on only if they did not, a
            // [Pure] function may not throw
            Assert.Empty(Errors("M", "static int M(int x, int y) { Spec.Requires(y != 0); return x / y; }"));
            Assert.Equal(new[] { "CSV1010" }, Errors("P", "[Pure] static int P(int x, int y) { Spec.Requires(y != 0); return x / y; }"));
            Assert.Empty(Errors("M", "static int M(int x) => System.Math.Abs(x);"));
            Assert.Equal(new[] { "CSV1010" }, Errors("P", "[Pure] static int P(int x) => System.Math.Abs(x);"));
        }

        [Fact]
        public void Checked_Throws_SoCodeGoesOnOnlyWithoutOverflow()
        {
            Assert.Empty(Errors("M", "static int M(int x) { int y = checked(x + 1); Spec.Assert(y > x); return y; }"));
            Assert.Empty(Errors("M", "static int M(long l) { int i = checked((int)l); Spec.Assert(i == l); return i; }"));
            // a [Pure] function must not throw, so there checked is no excuse
            Assert.Equal(new[] { "CSV1010" }, Errors("P", "[Pure] static int P(int x) => checked(x + 1);"));
        }

        [Fact]
        public void Unchecked_WrapsAround_Exactly()
        {
            Assert.Empty(Errors("M", "static int M() { int x = int.MaxValue; int y = unchecked(x + 1); Spec.Assert(y == int.MinValue); return y; }"));
            Assert.Equal(new[] { "CSV1004" }, Errors("M", "static int M(int x) { int y = unchecked(x + 1); Spec.Assert(y > x); return y; }"));
            Assert.Empty(Errors("M", "static int M() { int i = unchecked((int)4294967297L); Spec.Assert(i == 1); return i; }"));
        }

        [Fact]
        public void SpecificationsAndGhostCode_AreMathematical()
        {
            Assert.Empty(Errors("M", "static void M(int x) { Spec.Requires(x > 0); Spec.Assert(x + x > x); var g = Ghost.Of(x * x * x); Spec.Assert(g.Value > 0); }"));
            Assert.Empty(Errors("G", "[GhostFunction] static int G(int n) { Spec.Requires(n >= 0); Spec.Decreases(n); return n == 0 ? 0 : n * n + G(n - 1); }"));
        }

        [Fact]
        public void ReadsFromMemory_AreInRange() =>
            // an int field or element holds an int, so subtracting what is known smaller cannot overflow
            Assert.Empty(Errors("M", "static int M(int[] a) { Spec.Requires(a.Length > 0 && a[0] >= 0); return a[0] - 1 + 1; }"));

        [Fact]
        public void NoOverflowOption_MakesIntegersMathematical() =>
            Assert.Empty(Errors("M", "static int M(int x) => x + 1;", overflow: false));
    }
}
