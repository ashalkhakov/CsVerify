using CsVerify;

namespace Samples.Buggy
{
    [Owned]
    public sealed class Bead
    {
        public int Val;
        public Bead? Next;
    }

    public static class PredicateBugs
    {
        [Predicate]
        public static bool Chain(Bead? from, Bead? to, int n) =>
            n == 0 ? from == to : n > 0 && from != null && Spec.Acc(from) && Chain(from.Next, to, n - 1);

        // BUG: reads a field it has no Spec.Acc for: what it says could change while folded (CSV1016)
        [Predicate]
        public static bool Unframed(Bead? at) => at != null && at.Val > 0;

        // BUG: writes a node folded into the chain (CSV1016)
        public static void WriteFolded(Bead a, int n)
        {
            Spec.Requires(n > 0 && Chain(a, null, n));
            a.Val = 0;
        }

        // BUG: an empty chain must start where it ends (CSV1019)
        public static void FoldWrong(Bead? a, Bead? b)
        {
            Spec.Fold(Chain(a, b, 0));
        }

        // BUG: unfolds a chain it does not hold (CSV1016)
        public static void UnfoldMissing(Bead? a, int n)
        {
            Spec.Requires(n >= 0);
            Spec.Unfold(Chain(a, null, n));
        }

        public static void Consume(Bead? a, int n)
        {
            Spec.Requires(n >= 0 && Chain(a, null, n));
        }

        // BUG: each round gives away the chain held outside the loop (CSV1016)
        public static void UseUp(Bead? a, int n, int times)
        {
            Spec.Requires(n >= 0 && times >= 0 && Chain(a, null, n));
            for (int i = 0; i < times; i++)
            {
                Spec.Invariant(0 <= i && i <= times);
                Consume(a, n);
            }
        }

        // BUG: the node is lent to this method (its tree is its caller's): it cannot be folded away (CSV1016)
        public static void KeepLent(Bead c)
        {
            Spec.Modifies(Own.Tree(c));
            Spec.Fold(Chain(c.Next, c.Next, 0));
            Spec.Fold(Chain(c, c.Next, 1));
        }
    }
}
