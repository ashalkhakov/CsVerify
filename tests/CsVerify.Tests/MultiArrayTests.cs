using Xunit;

namespace CsVerify.Tests
{
    /// <summary>Rectangular arrays (int[,], int[,,]): a length per dimension, and cells told apart by all their indices.</summary>
    public class MultiArrayTests
    {
        private static string[] Errors(string method, string source, bool overflow = false) =>
            Harness.Verify("public static class C { " + source + " }", overflow).Errors(method);

        private const string Zero =
            "static void M(int[,] m) { Spec.Ensures(Spec.Forall(0, m.GetLength(0), i => Spec.Forall(0, m.GetLength(1), j => m[i, j] == 0))); " +
            "for (int i = 0; i < m.GetLength(0); i++) { " +
            "Spec.Invariant(0 <= i && i <= m.GetLength(0) && Spec.Forall(0, i, p => Spec.Forall(0, m.GetLength(1), q => m[p, q] == 0))); " +
            "for (int j = 0; j < m.GetLength(1); j++) { " +
            "Spec.Invariant(0 <= j && j <= m.GetLength(1) && Spec.Forall(0, i, p => Spec.Forall(0, m.GetLength(1), q => m[p, q] == 0)) && INNER); " +
            "m[i, j] = 0; } } }";

        [Fact]
        public void Matrix_ZeroFill_Proved() => Assert.Empty(Errors("M", Zero.Replace("INNER", "Spec.Forall(0, j, q => m[i, q] == 0)")));

        [Fact]
        public void Matrix_ZeroFill_InvariantTooWeak() => Assert.Equal(new[] { "CSV1006" }, Errors("M", Zero.Replace("INNER", "true")));

        [Fact]
        public void Matrix_IndexOutOfRange() => Assert.Equal(new[] { "CSV1003" }, Errors("M", "static int M(int[,] m) { return m[0, 0]; }"));

        [Fact]
        public void Matrix_IndexInRange() => Assert.Empty(Errors("M",
            "static int M(int[,] m) { Spec.Requires(m.GetLength(0) > 1 && m.GetLength(1) > 2); return m[1, 2]; }"));

        private const string TwoCells =
            "static void M(int[,] m) { Spec.Requires(m.GetLength(0) > 1 && m.GetLength(1) > 1); m[0, 1] = 5; m[1, 0] = 7; Spec.Assert(m[0, 1] == EXPECTED); }";

        [Fact]
        public void Matrix_CellsAreDistinct() => Assert.Empty(Errors("M", TwoCells.Replace("EXPECTED", "5")));

        [Fact]
        public void Matrix_CellsAreDistinct_Refuted() => Assert.Equal(new[] { "CSV1004" }, Errors("M", TwoCells.Replace("EXPECTED", "7")));

        [Fact]
        public void NewMatrix_LengthsAndInitializer() => Assert.Empty(Errors("M",
            "static int M() { Spec.Ensures<int>(r => r == 4); var m = new int[2, 3]; Spec.Assert(m.Length == 6 && m.GetLength(0) == 2 && m.GetLength(1) == 3 && m[1, 2] == 0); " +
            "var k = new int[,] { { 1, 2 }, { 3, 4 } }; Spec.Assert(k[0, 1] == 2 && k[1, 0] == 3); return k[1, 1]; }"));

        [Fact]
        public void NewMatrix_IndexOutOfRange() => Assert.Equal(new[] { "CSV1003" }, Errors("M",
            "static int M() { var m = new int[2, 3]; return m[2, 0]; }"));

        [Fact]
        public void NewMatrix_NegativeSize() => Assert.Equal(new[] { "CSV1003" }, Errors("M",
            "static int[,] M(int n) { return new int[2, n]; }"));

        [Fact]
        public void GetLength_DimensionOutOfRange()
        {
            Assert.Equal(new[] { "CSV1003" }, Errors("M", "static int M(int[,] m) { return m.GetLength(2); }"));
            Assert.Empty(Errors("M", "static int M(int[] a) { Spec.Ensures<int>(r => r == a.Length); return a.GetLength(0); }"));
        }

        [Fact]
        public void ThreeDimensions() => Assert.Empty(Errors("M",
            "static void M(int[,,] c) { Spec.Requires(c.GetLength(0) == 2 && c.GetLength(1) == 2 && c.GetLength(2) == 2); " +
            "c[0, 1, 1] = 3; c[1, 0, 1] = 4; c[1, 1, 0] = 5; Spec.Assert(c[0, 1, 1] == 3 && c[1, 0, 1] == 4); }"));

        [Fact]
        public void Matrix_CalleeWritesAreSeen() => Assert.Equal(new[] { "CSV1004" }, Errors("M",
            "static void Set(int[,] m) { Spec.Requires(m.GetLength(0) > 0 && m.GetLength(1) > 0); m[0, 0] = 1; } " +
            "static void M(int[,] m) { Spec.Requires(m.GetLength(0) > 0 && m.GetLength(1) > 0); m[0, 0] = 0; Set(m); Spec.Assert(m[0, 0] == 0); }"));
    }
}
