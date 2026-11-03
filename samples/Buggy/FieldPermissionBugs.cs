using CsVerify;

namespace Samples.Buggy
{
    [Owned]
    public sealed class Knob
    {
        public int Turn;
        public int Push;
    }

    [Owned]
    public sealed class Dimmer
    {
        public int Level;
        [Invariant, Pure] public bool Valid() => Level >= 0;
    }

    public static class FieldPermissionBugs
    {
        // BUG: holds Turn, writes Push (CSV1016)
        public static void WrongField(Knob k)
        {
            Spec.Requires(Spec.Acc(k, nameof(Knob.Turn)));
            Spec.Ensures(Spec.Acc(k, nameof(Knob.Turn)));
            k.Push = 1;
        }

        public static void TakeTurn(Knob k)
        {
            Spec.Requires(Spec.Acc(k, nameof(Knob.Turn)));
        }

        // BUG: a field given away for good: the view is not whole (CSV1016)
        public static void Incomplete(Knob k, ref Own<Knob> view)
        {
            Spec.Requires(view.Obj.Value == k);
            TakeTurn(k);
            Keep(ref view);
        }

        public static void Keep(ref Own<Knob> view) { }

        // BUG: different fields: these may be one knob (CSV1004)
        public static void MaybeSame(Knob a, Knob b)
        {
            Spec.Requires(Spec.Acc(a, nameof(Knob.Turn)) && Spec.Acc(b, nameof(Knob.Push)));
            Spec.Assert(a != b);
        }

        // BUG: a class with an invariant has no single-field permissions (CSV1016)
        public static void Invariant(Dimmer d)
        {
            Spec.Requires(Spec.Acc(d, nameof(Dimmer.Level)));
        }
    }
}
