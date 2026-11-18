using Xunit;

namespace CsVerify.Tests
{
    /// <summary>
    /// A type parameter's Equals, GetHashCode and CompareTo keep to their laws, as every implementation must: Equals an
    /// equivalence, GetHashCode the same of equal values, CompareTo a total order. Of an integer or a bool, they are
    /// its value's.
    /// </summary>
    public class GenericLawTests
    {
        private const string Laws = @"using System.Collections.Generic;
public static class Laws
{
    public static bool Same<T>(T a, T b) { Spec.Ensures<bool>(r => r == EqualityComparer<T>.Default.Equals(b, a)); return EqualityComparer<T>.Default.Equals(a, b); }
    public static bool Objects<T>(T a, T b) { Spec.Ensures<bool>(r => r == Equals(b, a)); return Equals(a, b); }
    public static bool NotNull<T>(T a, T b) where T : notnull { Spec.Ensures<bool>(r => r == b.Equals(a)); return a.Equals(b); }
    public static bool Equatable<T>(T a, T b) where T : IEquatable<T> { Spec.Ensures<bool>(r => r == EqualityComparer<T>.Default.Equals(b, a)); return a.Equals(b); }
    public static int Hash<T>(T a, T b) where T : notnull { Spec.Requires(a.Equals(b)); Spec.Ensures<int>(h => h == b.GetHashCode()); return a.GetHashCode(); }
    public static T Max<T>(T a, T b) where T : IComparable<T> { Spec.Ensures<T>(m => m.CompareTo(a) >= 0 && m.CompareTo(b) >= 0); return a.CompareTo(b) >= 0 ? a : b; }
    public static T Max3<T>(T a, T b, T c) where T : IComparable<T> { Spec.Ensures<T>(m => m.CompareTo(a) >= 0 && m.CompareTo(c) >= 0); return Max(Max(a, b), c); }
    public static int Compare<T>(T a, T b) { Spec.Ensures<int>(r => (r < 0) == (Comparer<T>.Default.Compare(b, a) > 0)); return Comparer<T>.Default.Compare(a, b); }
    public static void Transitive<T>(T a, T b, T c) { Spec.Requires(EqualityComparer<T>.Default.Equals(a, b) && EqualityComparer<T>.Default.Equals(b, c)); Spec.Assert(EqualityComparer<T>.Default.Equals(a, c)); }
    public static void Ints() { var x = Same(1, 2); var y = Same(3, 3); Spec.Assert(!x && y); }
    public static void IntMax() { var m = Max(1, 5); Spec.Assert(m >= 5); }
    public static void Strings(string s) { var x = Same(s, s); Spec.Assert(x); }
    public static void WrongEqual<T>(T a, T b) { Spec.Assert(EqualityComparer<T>.Default.Equals(a, b)); }
    public static void WrongHash<T>(T a, T b) where T : notnull { Spec.Assert(a.Equals(b) == (a.GetHashCode() == b.GetHashCode())); }
    public static void WrongOrder<T>(T a, T b) where T : IComparable<T> { Spec.Assert((a.CompareTo(b) == 0) == a.Equals(b)); }
    public static void WrongStrings(string s, string t) { var x = Same(s, t); Spec.Assert(x); }
    public static void WrongInts() { var x = Same(1, 2); Spec.Assert(x); }
}";

        [Fact]
        public void ATypeParametersEqualityAndOrder_KeepToTheirLaws()
        {
            var r = Harness.Verify(Laws);
            foreach (var ok in new[] { "Same", "Objects", "NotNull", "Equatable", "Hash", "Max", "Max3", "Compare", "Transitive", "Ints", "IntMax", "Strings" })
            {
                Assert.True(r.Errors(ok).Length == 0, r.Explain(ok));
            }
            foreach (var wrong in new[] { "WrongEqual", "WrongHash", "WrongOrder", "WrongStrings", "WrongInts" })
            {
                Assert.Equal(new[] { "CSV1004" }, r.Errors(wrong));
            }
        }
    }
}
