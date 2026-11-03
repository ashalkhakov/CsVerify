using Xunit;

namespace CsVerify.Tests
{
    /// <summary>Multisets: Spec.Multiset(a, n), and what array writes do to it.</summary>
    public class MultisetTests
    {
        private static string[] Errors(string method, string source) =>
            Harness.Verify("public static class C { " + source + " }").Errors(method);

        [Fact]
        public void Swapping_KeepsTheMultiset_WithoutALemma()
        {
            const string swap = "static void M(int[] a, int i, int j) { Spec.Requires(0 <= i && i < a.Length && 0 <= j && j < a.Length); " +
                                "Spec.Ensures(Spec.Multiset(a, a.Length) == Spec.Old(Spec.Multiset(a, a.Length))); BODY }";
            Assert.Empty(Errors("M", swap.Replace("BODY", "int t = a[i]; a[i] = a[j]; a[j] = t;")));
            Assert.Equal(new[] { "CSV1002" }, Errors("M", swap.Replace("BODY", "a[i] = a[j];")));
        }

        [Fact]
        public void WritesOutsideThePrefix_DoNotChangeIt() =>
            Assert.Empty(Errors("M", @"static void M(int[] a, int n) {
                Spec.Requires(0 <= n && n < a.Length);
                var before = Ghost.Of(Spec.Multiset(a, n).Count(0));
                a[n] = 42;
                Spec.Assert(Spec.Multiset(a, n).Count(0) == before.Value); }"));

        [Fact]
        public void ConcreteArrays_AreCountedExactly() =>
            Assert.Empty(Errors("M", @"static void M() {
                var a = new[] { 2, 7, 2 };
                Spec.Assert(Spec.Multiset(a, 3).Count(2) == 2 && Spec.Multiset(a, 3).Count(5) == 0);
                Spec.Assert(Spec.Multiset(a, 3) == Bag.Of(7).Add(2).Add(2)); }"));

        [Fact]
        public void Multiset_IsWellDefinedOnlyWithinTheArray() =>
            Assert.Equal(new[] { "CSV1012" }, Errors("M", "static void M(int[] a) { Spec.Requires(Spec.Multiset(a, a.Length + 1).Count(0) == 0); }"));
    }
}
