using Xunit;

namespace CsVerify.Tests
{
    /// <summary>
    /// Lambdas and local functions verified as units of their own, and eager LINQ (and List's predicate methods) with
    /// pure lambdas inlined.
    /// </summary>
    public class LambdaTests
    {
        [Fact]
        public void Lambdas_AreVerified_AsUnitsOfTheirOwn()
        {
            var r = Harness.Verify(@"
#nullable enable
public static class P
{
    public static Func<int, int> Index(int[] a) => i => a[i];
    public static Func<int, int> Guarded(int[] a) => i => i >= 0 && i < a.Length ? a[i] : 0;
    public static Func<string, int> Length() => s => s.Length;
    public static Func<string?, int> MaybeNull() => s => s.Length;
    // (specifications' lambdas are ghost: not code to verify)
    public static bool Ghost(int[] a) { Spec.Ensures<bool>(r => r || !Spec.Forall(0, a.Length, i => a[i] > 0)); return true; }
}");
            Assert.Equal(new[] { "CSV1003" }, r.Errors("P.Index.<lambda:6>"));
            Assert.Empty(r.Errors("P.Guarded.<lambda:7>"));
            Assert.Empty(r.Errors("P.Length.<lambda:8>"));
            Assert.Equal(new[] { "CSV1013" }, r.Errors("P.MaybeNull.<lambda:9>"));
            Assert.DoesNotContain(r.Methods, m => m.Name.StartsWith("P.Ghost."));
        }

        [Fact]
        public void LocalFunctions_HaveContracts_ThatNameWhatTheyCapture()
        {
            var r = Harness.Verify(@"
public static class P
{
    public static int Local(int[] a)
    {
        int Get(int i) { Spec.Requires(0 <= i && i < a.Length); return a[i]; }
        return a.Length > 0 ? Get(0) : 0;
    }
    public static int Unchecked(int[] a) { int Get(int i) => a[i]; return Get(0); }
}");
            Assert.Empty(r.Errors("P.Local"));
            Assert.Empty(r.Errors("P.Local.Get"));
            Assert.Equal(new[] { "CSV1003" }, r.Errors("P.Unchecked.Get"));
        }

        [Fact]
        public void EagerLinq_WithPureLambdas()
        {
            var r = Harness.Verify(@"
using System.Collections.Generic;
using System.Linq;
public static class P
{
    public static bool AnyPos(int[] a) { Spec.Requires(a.Length == 2 && a[1] == 5); Spec.Ensures<bool>(r => r); return a.Any(x => x > 0); }
    public static bool AllPos(List<int> l) { Spec.Requires(l.Count == 2 && l[0] == 1 && l[1] == 2); Spec.Ensures<bool>(r => r); return l.All(x => x > 0); }
    public static bool NotAll(List<int> l) { Spec.Requires(l.Count == 2 && l[0] == 1 && l[1] == -2); Spec.Ensures<bool>(r => !r); return l.All(x => x > 0); }
    public static int First(int[] a) { Spec.Requires(a.Length == 3 && a[0] == 1 && a[1] == 7 && a[2] == 9); Spec.Ensures<int>(r => r == 7); return a.First(x => x > 5); }
    public static int Last(IReadOnlyList<int> xs) { Spec.Requires(xs.Count == 2 && xs[1] == 4); Spec.Ensures<int>(r => r == 4); return xs.Last(); }
    public static int Count(int[] a) { Spec.Ensures<int>(r => r == a.Length); return a.Count(); }
    public static int CountP(int[] a) { Spec.Requires(a.Length == 2 && a[0] > 0 && a[1] > 0); Spec.Ensures<int>(r => r == 2); return a.Count(x => x > 0); }
    public static bool Has(List<string> l) { Spec.Requires(l.Count == 1 && l[0] == ""a""); Spec.Ensures<bool>(r => r); return l.Contains(""a""); }
    public static List<int> Copy(int[] a) { Spec.Requires(a.Length == 2 && a[0] == 3); var l = a.ToList(); Spec.Assert(l.Count == 2 && l[0] == 3); return l; }
    public static int[] Arr(List<int> l) { Spec.Requires(l.Count == 1 && l[0] == 8); var a = l.ToArray(); Spec.Assert(a.Length == 1 && a[0] == 8); return a; }
    public static int Find(List<int> l) { Spec.Requires(l.Count == 2 && l[0] == 1 && l[1] == 6); Spec.Ensures<int>(r => r == 6); return l.Find(x => x > 5); }
    public static int FindIndex(List<int> l) { Spec.Requires(l.Count == 2 && l[0] == 1 && l[1] == 6); Spec.Ensures<int>(r => r == 1); return l.FindIndex(x => x > 5); }
    public static bool Captured(int[] a, int k) { Spec.Requires(a.Length == 1 && a[0] == k); Spec.Ensures<bool>(r => r); return a.Any(x => x == k); }
    public static int Empty(List<int> l) => l.First();
    public static int NoneMatch(int[] a) { Spec.Requires(a.Length == 1 && a[0] == 0); return a.First(x => x > 0); }
}", overflow: false);
            foreach (var m in new[] { "AnyPos", "AllPos", "NotAll", "First", "Last", "Count", "CountP", "Has", "Copy", "Arr", "Find", "FindIndex", "Captured" })
                Assert.Empty(r.Errors("P." + m));
            Assert.Equal(new[] { "CSV1001" }, r.Errors("P.Empty"));
            Assert.Equal(new[] { "CSV1001" }, r.Errors("P.NoneMatch"));
        }

        [Fact]
        public void ImpureLambdas_LeaveTheCallALibraryCall()
        {
            var r = Harness.Verify(@"
using System.Collections.Generic;
using System.Linq;
public static class P
{
    // the lambda writes: not inlined, so nothing is known of the result
    public static bool Counting(int[] a) { Spec.Requires(a.Length == 1 && a[0] == 5); Spec.Ensures<bool>(r => r); int n = 0; return a.Any(x => { n++; return x > 0; }); }
}", overflow: false);
            Assert.Equal(new[] { "CSV1002" }, r.Errors("P.Counting"));
        }
    }
}
