using System.Linq;
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
        public void Aggregates_FloatingPoint_Average_Aggregate_Long()
        {
            var r = Harness.Verify(@"
#nullable enable
using System.Linq;
public static class P
{
    public static double Sum(double[] a) { Spec.Requires(a.Length == 2 && a[0] == 1.5 && a[1] == 2.0); Spec.Ensures<double>(r => r == 3.5); return a.Sum(); }
    // rounded at each step, as .NET adds them: 0.1 + 0.2 is not 0.3
    public static double Rounded(double[] a) { Spec.Requires(a.Length == 2 && a[0] == 0.1 && a[1] == 0.2); Spec.Ensures<double>(r => r != 0.3); return a.Sum(); }
    public static double MinNaN(double[] a) { Spec.Requires(a.Length == 2 && a[0] == 1.5 && double.IsNaN(a[1])); Spec.Ensures<double>(r => double.IsNaN(r)); return a.Min(); }
    public static double MaxSkipsNaN(double[] a) { Spec.Requires(a.Length == 2 && a[0] == 1.5 && double.IsNaN(a[1])); Spec.Ensures<double>(r => r == 1.5); return a.Max(); }
    public static double Average(int[] a) { Spec.Requires(a.Length == 2 && a[0] == 1 && a[1] == 2); Spec.Ensures<double>(r => r == 1.5); return a.Average(); }
    public static double AverageD(double[] a) { Spec.Requires(a.Length == 2 && a[0] == 1.0 && a[1] == 2.0); Spec.Ensures<double>(r => r == 1.5); return a.Average(); }
    public static int Aggregate(int[] a) { Spec.Requires(a.Length == 3 && a[0] == 1 && a[1] == 2 && a[2] == 3); Spec.Ensures<int>(r => r == 6); return a.Aggregate((x, y) => x + y); }
    public static int Seeded(int[] a) { Spec.Requires(a.Length == 2 && a[0] == 1 && a[1] == 2); Spec.Ensures<int>(r => r == 13); return a.Aggregate(10, (x, y) => x + y); }
    public static long Long(long[] a) { Spec.Requires(a.Length == 2 && a[0] == 1 && a[1] == 2); Spec.Ensures<long>(r => r == 3); return a.Sum(); }
    public static long Counted(int[] a) { Spec.Requires(a.Length == 3); Spec.Ensures<long>(r => r == 3); return a.LongCount(); }
    // an empty sequence has no average, nor an aggregate; a long sum may overflow
    public static double Empty(double[] a) => a.Average();
    public static int NoSeed(int[] a) => a.Aggregate((x, y) => x);
    public static long Overflow(long[] a) => a.Sum();
    public static double WrongMax(double[] a) { Spec.Requires(a.Length == 2 && a[0] == 1.5 && double.IsNaN(a[1])); Spec.Ensures<double>(r => double.IsNaN(r)); return a.Max(); }
}", overflow: false);
            foreach (var m in new[] { "Sum", "Rounded", "MinNaN", "MaxSkipsNaN", "Average", "AverageD", "Aggregate", "Seeded", "Long", "Counted" })
                Assert.True(r.Errors("P." + m).Length == 0, r.Explain("P." + m));
            foreach (var m in new[] { "Empty", "NoSeed", "Overflow" })
                Assert.Equal(new[] { "CSV1001" }, r.Errors("P." + m));
            Assert.Equal(new[] { "CSV1002" }, r.Errors("P.WrongMax"));
        }

        [Fact]
        public void Views_ConcatReverse_ResultSelectors_GroupJoin_Tuples()
        {
            var r = Harness.Verify(@"
#nullable enable
using System.Linq;
public static class P
{
    public static int Reverse(int[] a) { Spec.Requires(a.Length == 3 && a[0] == 1 && a[2] == 9); Spec.Ensures<int>(r => r == 9); return a.Reverse().First(); }
    public static int Concat(int[] a, int[] b) { Spec.Requires(a.Length == 1 && b.Length == 2 && b[1] == 4); Spec.Ensures<int>(r => r == 4); return a.Concat(b).Last(); }
    public static int Pairs(int[] a, int[] b) { Spec.Requires(a.Length == 2 && b.Length == 3); Spec.Ensures<int>(r => r == 6); return a.SelectMany(x => b, (x, y) => x + y).Count(); }
    public static int Zip(int[] a, int[] b) { Spec.Requires(a.Length == 2 && b.Length == 2 && a[1] == 5 && b[1] == 6); Spec.Ensures<int>(r => r == 11); var t = a.Zip(b).Last(); return t.First + t.Second; }
    public static int Elements(int[] a) { Spec.Requires(a.Length == 2 && a[0] == 4 && a[1] == 4); Spec.Ensures<int>(r => r == 8); return a.GroupBy(x => x, x => x * 2).First().First(); }
    public static int Sizes(int[] a) { Spec.Requires(a.Length == 2 && a[0] == 4 && a[1] == 4); Spec.Ensures<int>(r => r == 2); return a.GroupBy(x => x, (k, g) => g.Count()).First(); }
    public static int Matches(int[] a, int[] b) { Spec.Requires(a.Length == 1 && b.Length == 2 && a[0] == 1 && b[0] == 1 && b[1] == 2); Spec.Ensures<int>(r => r == 1); return a.GroupJoin(b, x => x, y => y, (x, ys) => ys.Count()).First(); }
    // by a tuple, and by an anonymous object: equal when their parts are
    public static int ByTuple(int[] a) { Spec.Requires(a.Length == 3 && a[0] == 1 && a[1] == 3 && a[2] == 5); Spec.Ensures<int>(r => r == 2); return a.GroupBy(x => (x % 2, x > 2)).Count(); }
    public static int ByObject(int[] a) { Spec.Requires(a.Length == 3 && a[0] == 1 && a[1] == 3 && a[2] == 5); Spec.Ensures<int>(r => r == 2); return a.Select(x => new { odd = x % 2, big = x > 2 }).Distinct().Count(); }
    // (a tuple made in a lambda is a value of its element, not one for all of them)
    public static int WrongByTuple(int[] a) { Spec.Requires(a.Length == 3 && a[0] == 1 && a[1] == 3 && a[2] == 5); Spec.Ensures<int>(r => r == 3); return a.GroupBy(x => (x % 2, x > 2)).Count(); }
    public static int WrongReverse(int[] a) { Spec.Requires(a.Length == 3 && a[0] == 1 && a[2] == 9); Spec.Ensures<int>(r => r == 1); return a.Reverse().First(); }
    public static int WrongSizes(int[] a) { Spec.Requires(a.Length == 3 && a[0] == 4 && a[1] == 4 && a[2] == 5); Spec.Ensures<int>(r => r == 3); return a.GroupBy(x => x, (k, g) => g.Count()).First(); }
}", overflow: false);
            foreach (var m in new[] { "Reverse", "Concat", "Pairs", "Zip", "Elements", "Sizes", "Matches", "ByTuple", "ByObject" })
                Assert.True(r.Errors("P." + m).Length == 0, r.Explain("P." + m));
            foreach (var m in new[] { "WrongByTuple", "WrongReverse", "WrongSizes" })
                Assert.Equal(new[] { "CSV1002" }, r.Errors("P." + m));
        }

        [Fact]
        public void QuerySyntax_FromLetJoinGroupInto()
        {
            var r = Harness.Verify(@"
#nullable enable
using System.Linq;
public static class P
{
    public static int Select(int[] a) { Spec.Requires(a.Length == 2); Spec.Ensures<int>(r => r == 2); return (from x in a select x + 1).Count(); }
    public static int TwoFroms(int[] a, int[] b) { Spec.Requires(a.Length == 2 && b.Length == 3); Spec.Ensures<int>(r => r == 6); return (from x in a from y in b select x + y).Count(); }
    public static int Let(int[] a) { Spec.Requires(a.Length == 2 && a[0] == 3 && a[1] == 1); Spec.Ensures<int>(r => r == 1); return (from x in a let y = x * 2 where y > 4 select y).Count(); }
    public static int Join(int[] a, int[] b) { Spec.Requires(a.Length == 1 && b.Length == 2 && a[0] == 2 && b[0] == 2 && b[1] == 5); Spec.Ensures<int>(r => r == 1); return (from x in a join y in b on x equals y select x + y).Count(); }
    public static int JoinInto(int[] a, int[] b)
    {
        Spec.Requires(a.Length == 1 && b.Length == 3 && a[0] == 2 && b[0] == 2 && b[1] == 5 && b[2] == 2);
        Spec.Ensures<int>(r => r == 2);
        return (from x in a join y in b on x equals y into ys select ys.Count()).First();
    }
    public static int GroupInto(int[] a)
    {
        Spec.Requires(a.Length == 3 && a[0] == 1 && a[1] == 4 && a[2] == 1);
        Spec.Ensures<int>(r => r == 2);
        return (from x in a group x by x into g select new { g.Key, n = g.Count() }).First().n;
    }
    public static int WrongLet(int[] a) { Spec.Requires(a.Length == 2 && a[0] == 3 && a[1] == 1); Spec.Ensures<int>(r => r == 2); return (from x in a let y = x * 2 where y > 4 select y).Count(); }
}", overflow: false);
            foreach (var m in new[] { "Select", "TwoFroms", "Let", "Join", "JoinInto", "GroupInto" })
                // (it and its clauses' lambdas, each a unit of its own)
                Assert.True(r.Methods.Where(x => x.Name == "P." + m || x.Name.StartsWith("P." + m + ".")).All(x => !x.Diagnostics.Any(d => d.IsError)),
                            string.Join("\n", r.Methods.Where(x => x.Name.StartsWith("P." + m)).Select(x => r.Explain(x.Name))));
            Assert.Equal(new[] { "CSV1002" }, r.Errors("P.WrongLet"));
        }

        [Fact]
        public void SetOperations_Single_While_By_AndTheRest()
        {
            var r = Harness.Verify(@"#nullable enable
using System.Collections.Generic;
using System.Linq;
public static class P
{
    public static int Append(int[] a) { Spec.Requires(a.Length == 2); Spec.Ensures<int>(r => r == 7); return a.Append(7).Last(); }
    public static int Prepend(int[] a) { Spec.Requires(a.Length == 2); Spec.Ensures<int>(r => r == 7); return a.Prepend(7).First(); }
    public static int Default(int[] a) { Spec.Requires(a.Length == 0); Spec.Ensures<int>(r => r == 1); return a.DefaultIfEmpty().Count(); }
    public static int TakeW(int[] a) { Spec.Requires(a.Length == 3 && a[0] == 1 && a[1] == 2 && a[2] == -1); Spec.Ensures<int>(r => r == 2); return a.TakeWhile(x => x > 0).Count(); }
    public static int SkipW(int[] a) { Spec.Requires(a.Length == 3 && a[0] == 1 && a[1] == -2 && a[2] == 3); Spec.Ensures<int>(r => r == -2); return a.SkipWhile(x => x > 0).First(); }
    public static int Single(int[] a) { Spec.Requires(a.Length == 1 && a[0] == 4); Spec.Ensures<int>(r => r == 4); return a.Single(); }
    public static int SingleBad(int[] a) => a.Single();
    public static int SingleP(int[] a) { Spec.Requires(a.Length == 2 && a[0] == 4 && a[1] == -1); Spec.Ensures<int>(r => r == 4); return a.Single(x => x > 0); }
    public static int Union(int[] a, int[] b) { Spec.Requires(a.Length == 2 && b.Length == 1 && a[0] == 1 && a[1] == 2 && b[0] == 2); Spec.Ensures<int>(r => r == 2); return a.Union(b).Count(); }
    public static int Inter(int[] a, int[] b) { Spec.Requires(a.Length == 2 && b.Length == 1 && a[0] == 1 && a[1] == 2 && b[0] == 2); Spec.Ensures<int>(r => r == 1); return a.Intersect(b).Count(); }
    public static int Except(int[] a, int[] b) { Spec.Requires(a.Length == 2 && b.Length == 1 && a[0] == 1 && a[1] == 2 && b[0] == 2); Spec.Ensures<int>(r => r == 1); return a.Except(b).First(); }
    public static int DistBy(int[] a) { Spec.Requires(a.Length == 3 && a[0] == 1 && a[1] == 3 && a[2] == 4); Spec.Ensures<int>(r => r == 2); return a.DistinctBy(x => x % 2).Count(); }
    public static int MinBy(int[] a) { Spec.Requires(a.Length == 3 && a[0] == 5 && a[1] == 3 && a[2] == 4); Spec.Ensures<int>(r => r == 3); return a.MinBy(x => x); }
    public static int MaxBy(int[] a) { Spec.Requires(a.Length == 3 && a[0] == 5 && a[1] == 3 && a[2] == 4); Spec.Ensures<int>(r => r == 5); return a.MaxBy(x => x); }
    public static int WhereI(int[] a) { Spec.Requires(a.Length == 4); Spec.Ensures<int>(r => r == 2); return a.Where((x, i) => i % 2 == 0).Count(); }
    public static int TakeL(int[] a) { Spec.Requires(a.Length == 4 && a[3] == 9); Spec.Ensures<int>(r => r == 9); return a.TakeLast(2).Last(); }
    public static int SkipL(int[] a) { Spec.Requires(a.Length == 4); Spec.Ensures<int>(r => r == 1); return a.SkipLast(3).Count(); }
    // (Lists: on arrays, with using System, SequenceEqual is MemoryExtensions' over spans)
    public static bool SeqEq(List<int> a, List<int> b) { Spec.Requires(a.Count == 2 && b.Count == 2 && a[0] == b[0] && a[1] == b[1]); Spec.Ensures<bool>(r => r); return a.SequenceEqual(b); }
    public static int Idx(int[] a) { Spec.Requires(a.Length == 3); Spec.Ensures<int>(r => r == 2); return a.Index().Last().Index; }
    public static Dictionary<int, int> Dict(int[] a) { Spec.Requires(a.Length == 2 && a[0] == 1 && a[1] == 2); return a.ToDictionary(x => x); }
    public static Dictionary<int, int> DictBad(int[] a) => a.ToDictionary(x => x);
}
", overflow: false);
            foreach (var m in new[] { "Append", "Prepend", "Default", "TakeW", "SkipW", "Single", "SingleP", "Union", "Inter", "Except", "DistBy", "MinBy", "MaxBy", "WhereI", "TakeL", "SkipL", "SeqEq", "Idx", "Dict" })
                Assert.True(r.Errors("P." + m).Length == 0, r.Explain("P." + m));
            // none or more than one; a repeated key
            Assert.Equal(new[] { "CSV1001" }, r.Errors("P.SingleBad"));
            Assert.Equal(new[] { "CSV1001" }, r.Errors("P.DictBad"));
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
