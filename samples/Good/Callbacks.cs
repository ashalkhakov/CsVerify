// Written for this repository, to show callbacks with specifications: what a Func accepts and gives (Spec.Pre,
// Spec.Post), what it may change (Spec.ChangesNothing) and read (Spec.ReadsOf), and a delegate type with a contract.
using System;
using System.Threading;
using System.Threading.Tasks;
using CsVerify;

namespace CallbacksSample
{
    public sealed class Order
    {
        public int Amount;
        public int Quantity;
    }

    /// <summary>What an order costs for a quantity: at most 100 a unit.</summary>
    public delegate int Pricing(int quantity);

    [ContractClassFor(typeof(Pricing))]
    internal abstract class PricingContract
    {
        public int Invoke(int quantity)
        {
            Spec.Requires(0 <= quantity && quantity <= 1000);
            Spec.Ensures<int>(r => 0 <= r && r <= 100 * quantity);
            return default;
        }
    }

    public static class Prices
    {
        public static readonly Pricing Flat = q => 100 * q;
        public static readonly Pricing Bulk = q => q > 100 ? 90 * q : 100 * q;

        /// <summary>A quote with a fixed fee: any pricing keeps it within bounds.</summary>
        public static int Quote(Pricing price, int quantity)
        {
            Spec.Requires(0 <= quantity && quantity <= 1000);
            Spec.Ensures<int>(r => 5 <= r && r <= 100005);
            return price(quantity) + 5;
        }

        /// <summary>Each element of a through f: what f gives for it, element by element.</summary>
        public static int[] Map(int[] a, Func<int, int> f)
        {
            Spec.Requires(Spec.Forall(0, a.Length, i => Spec.Pre(f, a[i])) && Spec.ChangesNothing(f));
            Spec.Ensures<int[]>(r => r.Length == a.Length && Spec.Forall(0, a.Length, i => Spec.Post(f, a[i], r[i])));
            var r = new int[a.Length];
            for (int k = 0; k < a.Length; k++)
            {
                Spec.Invariant(0 <= k && k <= a.Length && r.Length == a.Length);
                Spec.Invariant(Spec.Forall(0, k, i => Spec.Post(f, a[i], r[i])));
                Spec.Invariant(Spec.Forall(0, a.Length, i => Spec.Pre(f, a[i])));
                r[k] = f(a[k]);
            }
            return r;
        }

        public static void Halve(int[] a)
        {
            Spec.Requires(a.Length > 0);
            var half = Map(a, x => x / 2);
            Spec.Assert(half[0] == a[0] / 2);
        }

        /// <summary>
        /// The prices less a discount, which mustn't change the prices: without Spec.ChangesNothing, a call of it could
        /// have, and the bounds the sum needs would be lost.
        /// </summary>
        public static int Total(int[] prices, Func<int, int> discount)
        {
            Spec.Requires(prices.Length <= 1000 && Spec.Forall(0, prices.Length, i => 0 <= prices[i] && prices[i] <= 1000));
            Spec.Requires(Spec.Total(discount) && Spec.ChangesNothing(discount));
            int sum = 0;
            for (int k = 0; k < prices.Length; k++)
            {
                Spec.Invariant(0 <= k && k <= prices.Length && 0 <= sum && sum <= 1000 * k);
                Spec.Invariant(Spec.Forall(0, prices.Length, i => 0 <= prices[i] && prices[i] <= 1000));
                int d = discount(prices[k]);
                if (d < 0) d = 0;
                if (d > prices[k]) d = prices[k];
                sum += prices[k] - d;
            }
            return sum;
        }
    }

    public static class Approvals
    {
        /// <summary>
        /// Checks an order by a rule that may read the order, but only it: recording the check in the audit order
        /// (another one) leaves what the rule accepts as it was.
        /// </summary>
        public static bool Approve(Order order, Order audit, Func<Order, bool> rule)
        {
            Spec.Requires(order != audit);
            Spec.Requires(Spec.Pre(rule, order) && Spec.ReadsOf(rule, order).IsSubsetOf(ObjSet.Of(order)));
            audit.Quantity = audit.Quantity < 1000 ? audit.Quantity + 1 : 0;
            return rule(order);
        }

        public static bool ApproveLarge(Order order, Order audit)
        {
            Spec.Requires(order != audit);
            order.Quantity = 4;
            order.Amount = 100;
            // the rule divides by the quantity: it says so, and what it reads
            return Approve(order, audit, o => { Spec.Reads(ObjSet.Of(o)); Spec.Requires(o.Quantity > 0); return o.Amount / o.Quantity > 10; });
        }
    }

    public static class Retries
    {
        /// <summary>Tries up to a number of times; the last failure is the caller's.</summary>
        public static async Task<T> RetryAsync<T>(Func<CancellationToken, Task<T>> attempt, int times, CancellationToken ct)
        {
            Spec.Requires(Spec.Total(attempt) && 1 <= times && times <= 10);
            for (int k = 1; k < times; k++)
            {
                Spec.Invariant(1 <= k && k <= times);
                try { return await attempt(ct); }
                catch (TimeoutException) { await Task.Delay(10 * k, ct); }
            }
            return await attempt(ct);
        }
    }
}
