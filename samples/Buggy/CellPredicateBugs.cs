using CsVerify;

namespace Samples.Buggy
{
    [Owned]
    public sealed class Tray
    {
        public int[] Slots;
    }

    public static class CellPredicateBugs
    {
        [Predicate]
        public static bool Held(Tray t) => Spec.Acc(t) && t.Slots != null && Spec.Acc(t.Slots);

        // BUG: reads a cell it has no permission to: it could change while folded (CSV1016)
        [Predicate]
        public static bool FirstPositive(Tray t) => Spec.Acc(t) && t.Slots != null && t.Slots.Length > 0 && t.Slots[0] > 0;

        // BUG: writes a cell folded into the tray's predicate (CSV1016)
        public static void WriteFoldedCell(Tray t)
        {
            Spec.Requires(Held(t));
            Spec.Unfold(Held(t));
            var slots = t.Slots;
            Spec.Fold(Held(t));
            if (slots.Length > 0) slots[0] = 1;
        }
    }
}
