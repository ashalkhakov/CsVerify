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
        public void LazyLinq_IsReadWhenItIsEnumerated()
        {
            var r = Harness.Verify(@"
using System.Collections.Generic;
using System.Linq;
public static class P
{
    public static int Doubled(int[] a) { Spec.Requires(a.Length == 2 && a[1] == 4); Spec.Ensures<int>(r => r == 8); return a.Select(x => x * 2).Last(); }
    public static int WhereFirst(int[] a) { Spec.Requires(a.Length == 3 && a[0] == 1 && a[1] == 6 && a[2] == 7); Spec.Ensures<int>(r => r == 6); return a.Where(x => x > 5).First(); }
    public static int WhereCount(int[] a) { Spec.Requires(a.Length == 3 && a[0] == 1 && a[1] == 6 && a[2] == 7); Spec.Ensures<int>(r => r == 2); return a.Where(x => x > 5).Count(); }
    public static bool WhereAll(int[] a) { Spec.Ensures<bool>(r => r); return a.Where(x => x > 5).All(x => x > 0); }
    public static List<int> Chain(List<int> l)
    {
        Spec.Requires(l.Count == 2 && l[0] == 3 && l[1] == 9);
        var r = l.Where(x => x > 4).Select(x => x + 1).ToList();
        Spec.Assert(r.Count == 1 && r[0] == 10);
        return r;
    }
    // a view reads its source when it is enumerated: it sees the 5 added after it was made
    public static int Later(List<int> l) { Spec.Requires(l.Count == 0); Spec.Modifies(ObjSet.Of(l)); var q = l.Select(x => x); l.Add(5); return q.First(); }
    public static int Take(int[] a) { Spec.Requires(a.Length == 5); Spec.Ensures<int>(r => r == 2); return a.Take(2).Count(); }
    public static int Skip(int[] a) { Spec.Requires(a.Length == 3 && a[2] == 7); Spec.Ensures<int>(r => r == 7); return a.Skip(2).First(); }
    public static int Each(int[] a) { int s = 0; foreach (var x in a.Where(y => y > 5)) { Spec.Assert(x > 5); s = x; } return s; }
    public static int Mapped(List<int> l) { int s = 0; foreach (var x in l.Select(y => y * 0)) { Spec.Assert(x == 0); s = x; } return s; }
    public static int Empty(int[] a) => a.Where(x => x > 100).First();
    public static int TooStrong(int[] a) { int s = 0; foreach (var x in a.Where(y => y > 5)) { Spec.Assert(x > 6); s = x; } return s; }
}", overflow: false);
            foreach (var m in new[] { "Doubled", "WhereFirst", "WhereCount", "WhereAll", "Chain", "Later", "Take", "Skip", "Each", "Mapped" })
                Assert.Empty(r.Errors("P." + m));
            Assert.Equal(new[] { "CSV1001" }, r.Errors("P.Empty"));
            Assert.Equal(new[] { "CSV1004" }, r.Errors("P.TooStrong"));
        }

        [Fact]
        public void Aggregates_SumMinMax_AndAnExactCount()
        {
            var r = Harness.Verify(@"
using System.Collections.Generic;
using System.Linq;
public static class P
{
    public static int Sum(int[] a) { Spec.Requires(a.Length == 3 && a[0] == 1 && a[1] == 2 && a[2] == 3); Spec.Ensures<int>(r => r == 6); return a.Sum(); }
    public static int SumOf(List<int> l) { Spec.Requires(l.Count == 2 && l[0] == 4 && l[1] == 5); Spec.Ensures<int>(r => r == 18); return l.Sum(x => x * 2); }
    public static int Min(int[] a) { Spec.Requires(a.Length == 3 && a[0] == 4 && a[1] == -1 && a[2] == 9); Spec.Ensures<int>(r => r == -1); return a.Min(); }
    public static int Max(int[] a) { Spec.Requires(a.Length > 0); Spec.Ensures<int>(r => Spec.Forall(0, a.Length, i => a[i] <= r)); return a.Max(); }
    public static int MaxOf(int[] a) { Spec.Requires(a.Length == 2 && a[0] == 3 && a[1] == 1); Spec.Ensures<int>(r => r == 2); return a.Max(x => x - 1); }
    public static int CountP(int[] a) { Spec.Requires(a.Length == 4 && a[0] == 1 && a[1] == -6 && a[2] == 7 && a[3] == 0); Spec.Ensures<int>(r => r == 2); return a.Count(x => x > 0); }
    public static int SumBounded(int[] a) { Spec.Requires(a.Length == 2 && 0 <= a[0] && a[0] < 10 && 0 <= a[1] && a[1] < 10); return a.Sum(); }
    public static int Overflows(int[] a) => a.Sum();
    public static int EmptyMin(List<int> l) => l.Min();
}");
            foreach (var m in new[] { "Sum", "SumOf", "Min", "Max", "MaxOf", "CountP", "SumBounded" })
                Assert.True(r.Errors("P." + m).Length == 0, r.Explain("P." + m));
            Assert.Equal(new[] { "CSV1001" }, r.Errors("P.Overflows"));
            Assert.Equal(new[] { "CSV1001" }, r.Errors("P.EmptyMin"));
        }

        [Fact]
        public void Views_DistinctOrderBySelectManyGroupBy_AndSelectWithAnIndex()
        {
            var r = Harness.Verify(@"
#nullable enable
using System.Collections.Generic;
using System.Linq;
public sealed class Box { public List<int> Items = new List<int>(); }
public static class P
{
    public static int Indexed(int[] a) { Spec.Requires(a.Length == 3); Spec.Ensures<int>(r => r == a[2] + 2); return a.Select((x, i) => x + i).Last(); }
    public static int Distinct(int[] a) { Spec.Requires(a.Length == 4 && a[0] == 1 && a[1] == 2 && a[2] == 1 && a[3] == 3); Spec.Ensures<int>(r => r == 3); return a.Distinct().Count(); }
    public static int DistinctLast(List<int> l) { Spec.Requires(l.Count == 3 && l[0] == 5 && l[1] == 5 && l[2] == 5); Spec.Ensures<int>(r => r == 5); return l.Distinct().Last(); }
    public static int Smallest(int[] a) { Spec.Requires(a.Length == 3 && a[0] == 4 && a[1] == 2 && a[2] == 9); Spec.Ensures<int>(r => r == 2); return a.OrderBy(x => x).First(); }
    public static int Largest(int[] a) { Spec.Requires(a.Length == 3 && a[0] == 4 && a[1] == 2 && a[2] == 9); Spec.Ensures<int>(r => r == 9); return a.OrderByDescending(x => x).First(); }
    public static int Sorted(int[] a)
    {
        int s = 0;
        foreach (var x in a.OrderBy(y => y)) { s = x; }
        return a.OrderBy(y => y).Count() - a.Length;
    }
    public static int Flat(List<Box> boxes)
    {
        Spec.Requires(boxes.Count == 2 && boxes[0] != null && boxes[1] != null && boxes[0] != boxes[1] && boxes[0].Items.Count == 1 && boxes[1].Items.Count == 2 && boxes[1].Items[1] == 7);
        Spec.Ensures<int>(r => r == 7);
        return boxes.SelectMany(b => b.Items).Last();
    }
    public static int FlatCount(List<Box> boxes)
    {
        Spec.Requires(boxes.Count == 2 && boxes[0] != null && boxes[1] != null && boxes[0] != boxes[1] && boxes[0].Items.Count == 1 && boxes[1].Items.Count == 2);
        Spec.Ensures<int>(r => r == 3);
        return boxes.SelectMany(b => b.Items).Count();
    }
    public static int Groups(int[] a) { Spec.Requires(a.Length == 4 && a[0] == 1 && a[1] == 2 && a[2] == 1 && a[3] == 4); Spec.Ensures<int>(r => r == 3); return a.GroupBy(x => x % 2 == 0 ? x : 1).Count(); }
    public static int FirstKey(int[] a) { Spec.Requires(a.Length == 2 && a[0] == 6 && a[1] == 3); Spec.Ensures<int>(r => r == 6); return a.GroupBy(x => x).First().Key; }
    public static int Members(int[] a)
    {
        int s = 0;
        foreach (var g in a.GroupBy(x => x % 3))
            foreach (var x in g) { Spec.Assert(x % 3 == g.Key); s = x; }
        return s;
    }
    public static int Keys(int[] a) { Spec.Requires(a.Length == 3 && a[0] == 2 && a[1] == 2 && a[2] == 5); Spec.Ensures<int>(r => r == 5); return a.GroupBy(x => x).Select(g => g.Key).Last(); }
    public static int GroupSize(int[] a) { Spec.Requires(a.Length == 3 && a[0] == 2 && a[1] == 2 && a[2] == 5); Spec.Ensures<int>(r => r == 2); return a.GroupBy(x => x).First().Count(); }
    public static int WrongGroup(int[] a)
    {
        int s = 0;
        foreach (var g in a.GroupBy(x => x % 3))
            foreach (var x in g) { Spec.Assert(x % 3 == 0); s = x; }
        return s;
    }
    public static int EmptyOrdered(List<int> l) => l.OrderBy(x => x).First();
    public static int WrongSort(int[] a) { Spec.Requires(a.Length == 2 && a[0] == 1 && a[1] == 2); Spec.Ensures<int>(r => r == 1); return a.OrderByDescending(x => x).First(); }
}", overflow: false);
            foreach (var m in new[] { "Indexed", "Distinct", "DistinctLast", "Smallest", "Largest", "Sorted", "Flat", "FlatCount", "Groups", "FirstKey", "Members", "Keys", "GroupSize" })
                Assert.True(r.Errors("P." + m).Length == 0, r.Explain("P." + m));
            Assert.Equal(new[] { "CSV1001" }, r.Errors("P.EmptyOrdered"));
            Assert.Equal(new[] { "CSV1002" }, r.Errors("P.WrongSort"));
            Assert.Equal(new[] { "CSV1004" }, r.Errors("P.WrongGroup"));
        }

        [Fact]
        public void Views_ZipJoinThenBy()
        {
            var r = Harness.Verify(@"
#nullable enable
using System.Collections.Generic;
using System.Linq;
public static class P
{
    public static int Zip(int[] a, List<int> b) { Spec.Requires(a.Length == 3 && b.Count == 2 && a[1] == 4 && b[1] == 5); Spec.Ensures<int>(r => r == 9); return a.Zip(b, (x, y) => x + y).Last(); }
    public static int ZipShorter(int[] a, int[] b) { Spec.Requires(a.Length == 3 && b.Length == 5); Spec.Ensures<int>(r => r == 3); return a.Zip(b, (x, y) => x).Count(); }
    public static int Join(int[] ids, int[] owners)
    {
        Spec.Requires(ids.Length == 2 && ids[0] == 1 && ids[1] == 2 && owners.Length == 3 && owners[0] == 2 && owners[1] == 3 && owners[2] == 2);
        Spec.Ensures<int>(r => r == 2);
        return ids.Join(owners, i => i, o => o, (i, o) => i).Count();
    }
    public static int JoinFirst(int[] ids, int[] owners)
    {
        Spec.Requires(ids.Length == 2 && ids[0] == 1 && ids[1] == 2 && owners.Length == 2 && owners[0] == 2 && owners[1] == 1);
        Spec.Ensures<int>(r => r == 10 + 1);
        return ids.Join(owners, i => i, o => o, (i, o) => 10 * i + o / o).First();
    }
    public static void Matches(int[] ids, int[] owners)
    {
        foreach (var p in ids.Join(owners, i => i % 4, o => o % 4, (i, o) => i - o)) Spec.Assert(p % 4 == 0);
    }
    public static int ThenBy(int[] a)
    {
        Spec.Requires(a.Length == 3 && a[0] == 21 && a[1] == 12 && a[2] == 11);
        Spec.Ensures<int>(r => r == 11);
        return a.OrderBy(x => x % 10).ThenBy(x => x).First();
    }
    public static int ThenDown(int[] a)
    {
        Spec.Requires(a.Length == 3 && a[0] == 21 && a[1] == 12 && a[2] == 11);
        Spec.Ensures<int>(r => r == 21);
        return a.OrderBy(x => x % 10).ThenByDescending(x => x).First();
    }
    public static int WrongZip(int[] a, int[] b) { Spec.Requires(a.Length == 3 && b.Length == 5); Spec.Ensures<int>(r => r == 5); return a.Zip(b, (x, y) => y).Count(); }
    public static int WrongJoin(int[] ids, int[] owners) { Spec.Requires(ids.Length == 2 && owners.Length == 2); Spec.Ensures<int>(r => r == 2); return ids.Join(owners, i => i, o => o, (i, o) => i).Count(); }
    public static int WrongThen(int[] a)
    {
        Spec.Requires(a.Length == 3 && a[0] == 21 && a[1] == 12 && a[2] == 11);
        Spec.Ensures<int>(r => r == 11);
        return a.OrderBy(x => x % 10).ThenByDescending(x => x).First();
    }
}", overflow: false);
            foreach (var m in new[] { "Zip", "ZipShorter", "Join", "JoinFirst", "Matches", "ThenBy", "ThenDown" })
                Assert.True(r.Errors("P." + m).Length == 0, r.Explain("P." + m));
            foreach (var m in new[] { "WrongZip", "WrongJoin", "WrongThen" })
                Assert.Equal(new[] { "CSV1002" }, r.Errors("P." + m));
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
