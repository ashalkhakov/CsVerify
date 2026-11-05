#nullable enable
namespace Samples.Linq
{
    using System.Collections.Generic;
    using System.Linq;
    using CsVerify;

    public sealed class Basket
    {
        public List<int> Items = new List<int>();
    }

    /// <summary>The bugs the LINQ models catch (Samples/Good/Linq.cs has the fixed versions).</summary>
    public static class LinqBugs
    {
        // Sum checks its additions: two large readings overflow (CSV1001, it would throw OverflowException)
        public static int Total(int[] readings) => readings.Sum();

        // Max of no scores throws (CSV1001)
        public static int Best(List<int> scores) => scores.Max();

        // First of a filter that may match nothing throws (CSV1001)
        public static int FirstFailing(int[] scores) => scores.Where(s => s < 50).First();

        // descending order puts the largest first, not the smallest (CSV1002)
        public static int Lowest(int[] scores)
        {
            Spec.Requires(scores.Length == 2 && scores[0] == 40 && scores[1] == 90);
            Spec.Ensures<int>(r => r == 40);
            return scores.OrderByDescending(s => s).First();
        }

        // repeated scores are dropped: there may be fewer distinct ones (CSV1002)
        public static int Distinct(int[] scores)
        {
            Spec.Ensures<int>(r => r == scores.Length);
            return scores.Distinct().Count();
        }

        // a group's members share its key (x % 10), not equal it (CSV1004)
        public static void Groups(int[] scores)
        {
            foreach (var g in scores.GroupBy(s => s % 10))
                foreach (var s in g)
                    Spec.Assert(s == g.Key);
        }

        // every basket may be empty: then there is no first item (CSV1001)
        public static int FirstItem(List<Basket> baskets)
        {
            Spec.Requires(baskets.Count > 0);
            return baskets.SelectMany(b => b.Items).First();
        }

        // Zip stops at the shorter: b may have fewer readings (CSV1002)
        public static int Pairs(int[] a, int[] b)
        {
            Spec.Ensures<int>(r => r == a.Length);
            return a.Zip(b, (x, y) => x == y).Count();
        }

        // no basket may match the customer: then the join is empty (CSV1001)
        public static int FirstMatch(int[] customers, int[] owners) => customers.Join(owners, c => c, o => o, (c, o) => c).First();

        // ThenByDescending puts 21 before 11 within the ones (CSV1002)
        public static int Smallest(int[] a)
        {
            Spec.Requires(a.Length == 3 && a[0] == 21 && a[1] == 12 && a[2] == 11);
            Spec.Ensures<int>(r => r == 11);
            return a.OrderBy(x => x % 10).ThenByDescending(x => x).First();
        }

        // there may be no readings, and an empty sequence has no mean (CSV1001)
        public static double Mean(double[] readings) => readings.Average();

        // selects the score, not the curved one (CSV1002)
        public static int[] Curved(int[] scores)
        {
            Spec.Requires(Spec.Forall(0, scores.Length, i => 0 <= scores[i] && scores[i] <= 100));
            Spec.Ensures<int[]>(r => Spec.Forall(0, r.Length, i => 75 <= r[i]));
            return (from s in scores let b = s / 2 + 50 where b >= 75 select s).ToArray();
        }

        // two anonymous objects with equal parts are equal by Equals, but == compares references (CSV1004)
        public static void Same(int x)
        {
            var a = new { x };
            var b = new { x };
            Spec.Assert(a == b);
        }
    }
}
