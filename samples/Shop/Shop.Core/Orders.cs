using CsVerify;

namespace Shop.Core;

/// <summary>Orders: what CsVerify proves of each method is in its specification.</summary>
public static class Orders
{
    /// <summary>The first amount over the limit, or -1: every one before it is within the limit.</summary>
    public static int FirstOver(int[] amounts, int limit)
    {
        Spec.Ensures<int>(r => -1 <= r && r < amounts.Length);
        Spec.Ensures<int>(r => r < 0 || amounts[r] > limit);
        Spec.Ensures<int>(r => r >= 0 || Spec.Forall(0, amounts.Length, i => amounts[i] <= limit));
        for (int i = 0; i < amounts.Length; i++)
        {
            Spec.Invariant(0 <= i && i <= amounts.Length && Spec.Forall(0, i, j => amounts[j] <= limit));
            if (amounts[i] > limit) return i;
        }
        return -1;
    }

    /// <summary>The sum of the amounts, in a long: it cannot overflow.</summary>
    public static long Total(int[] amounts)
    {
        Spec.Ensures<long>(r => -2147483648L * amounts.Length <= r && r <= 2147483647L * amounts.Length);
        long sum = 0;
        for (int i = 0; i < amounts.Length; i++)
        {
            Spec.Invariant(0 <= i && i <= amounts.Length && -2147483648L * i <= sum && sum <= 2147483647L * i);
            sum += amounts[i];
        }
        return sum;
    }

    /// <summary>A member's discount: a tenth of a total of 100 or more, never more than the total.</summary>
    public static int Discount(int total, bool member)
    {
        Spec.Requires(total >= 0);
        Spec.Ensures<int>(r => 0 <= r && r <= total);
        if (member && total >= 100) return total / 10;
        return 0;
    }

    /// <summary>
    /// The last amount, of n: n is a ghost (a static index, as in ATS), there for the proof only. Erasure removes it,
    /// from this signature and from every call.
    /// </summary>
    public static int Last(int[] amounts, Ghost<int> n)
    {
        Spec.Requires(n.Value == amounts.Length && n.Value > 0);
        Spec.Ensures<int>(r => r == amounts[n.Value - 1]);
        return amounts[amounts.Length - 1];
    }

    /// <summary>Whether an order can ship.</summary>
    public static bool CanShip(bool paid, bool inStock, bool blocked) => paid && inStock && !blocked;
}
