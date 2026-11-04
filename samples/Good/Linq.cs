#nullable enable
namespace Samples.Linq
{
    using System.Collections.Generic;
    using System.Linq;
    using CsVerify;

    public sealed class Order
    {
        public int Customer;
        public List<int> Items = new List<int>();
    }

    /// <summary>
    /// LINQ over Lists and arrays (docs/library-contracts.md, "LINQ" and "Lazy LINQ"): pure lambdas are inlined, and a
    /// query is read when it is enumerated, so what it gives can be specified like any other result.
    /// </summary>
    public static class LinqSamples
    {
        // the scores at or above the bar: no more of them than there were, and every one at or above it
        public static List<int> Passing(int[] scores, int bar)
        {
            Spec.Ensures<List<int>>(r => r.Count <= scores.Length);
            Spec.Ensures<List<int>>(r => Spec.Forall(0, r.Count, i => r[i] >= bar));
            return scores.Where(s => s >= bar).ToList();
        }

        // the best score: no score is above it, and some score is it
        public static int Best(int[] scores)
        {
            Spec.Requires(scores.Length > 0);
            Spec.Ensures<int>(r => Spec.Forall(0, scores.Length, i => scores[i] <= r));
            Spec.Ensures<int>(r => Spec.Exists(0, scores.Length, i => scores[i] == r));
            return scores.Max();
        }

        // a total that cannot overflow: three readings of at most 1000 each
        public static int Total(int[] readings)
        {
            Spec.Requires(readings.Length == 3 && Spec.Forall(0, 3, i => 0 <= readings[i] && readings[i] <= 1000));
            Spec.Ensures<int>(r => r == readings[0] + readings[1] + readings[2]);
            return readings.Sum();
        }

        // how many scores are above the bar, exactly
        public static int Above(int[] scores)
        {
            Spec.Requires(scores.Length == 4 && scores[0] == 70 && scores[1] == 40 && scores[2] == 90 && scores[3] == 50);
            Spec.Ensures<int>(r => r == 2);
            return scores.Count(s => s > 60);
        }

        // the lowest score, through a sort: one of the scores
        public static int Lowest(List<int> scores)
        {
            Spec.Requires(scores.Count > 0);
            Spec.Ensures<int>(r => Spec.Exists(0, scores.Count, i => scores[i] == r));
            return scores.OrderBy(s => s).First();
        }

        // the sorted scores: in order, and as many as there were
        public static int[] Sorted(int[] scores)
        {
            Spec.Ensures<int[]>(r => r.Length == scores.Length);
            Spec.Ensures<int[]>(r => Spec.Forall(0, r.Length - 1, i => r[i] <= r[i + 1]));
            return scores.OrderBy(s => s).ToArray();
        }

        // there are no more distinct customers than orders
        public static int Customers(List<Order> orders)
        {
            Spec.Ensures<int>(r => 0 <= r && r <= orders.Count);
            return orders.Select(o => o.Customer).Distinct().Count();
        }

        // each customer's orders, grouped: every order in a group is that customer's
        public static int Busiest(List<Order> orders)
        {
            // (a List's elements are not known to be non-null from its type: the List could have been filled through
            // code that ignored nullable warnings)
            Spec.Requires(Spec.Forall(0, orders.Count, i => orders[i] != null));
            int best = 0;
            foreach (var g in orders.GroupBy(o => o.Customer))
            {
                int n = 0;
                foreach (var o in g)
                {
                    Spec.Assert(o.Customer == g.Key);
                    if (n < int.MaxValue) n++;
                }
                if (n > best) best = n;
            }
            return best;
        }

        // the first item of all the orders' items is the first order's first item
        public static int FirstItem(List<Order> orders)
        {
            Spec.Requires(orders.Count > 0 && orders[0] != null && orders[0].Items.Count > 0);
            Spec.Ensures<int>(r => r == orders[0].Items[0]);
            return orders.SelectMany(o => o.Items).First();
        }

        // the even-numbered positions' values, by index
        public static int LastEven(int[] a)
        {
            Spec.Requires(a.Length == 3);
            Spec.Ensures<int>(r => r == a[2]);
            return a.Select((x, i) => i % 2 == 0 ? x : 0).Last();
        }

        // two readings agree where every pair of them does
        public static bool Agree(int[] a, int[] b)
        {
            Spec.Requires(a.Length == b.Length);
            Spec.Ensures<bool>(r => r == Spec.Forall(0, a.Length, i => a[i] == b[i]));
            return a.Zip(b, (x, y) => x == y).All(same => same);
        }

        // each order joined to its customer is that customer's
        public static bool Matched(int[] customers, List<Order> orders)
        {
            Spec.Requires(Spec.Forall(0, orders.Count, i => orders[i] != null));
            Spec.Ensures<bool>(r => r);
            return customers.Join(orders, c => c, o => o.Customer, (c, o) => c == o.Customer).All(ok => ok);
        }

        // by tens, then by value within the same ten: in that order
        public static int[] ByTens(int[] a)
        {
            Spec.Requires(Spec.Forall(0, a.Length, i => 0 <= a[i]));
            Spec.Ensures<int[]>(r => r.Length == a.Length);
            Spec.Ensures<int[]>(r => Spec.Forall(0, r.Length - 1, i => r[i] / 10 < r[i + 1] / 10 || r[i] / 10 == r[i + 1] / 10 && r[i] <= r[i + 1]));
            return a.OrderBy(x => x / 10).ThenBy(x => x).ToArray();
        }
    }
}
