using CsVerify;

namespace Samples.Buggy
{
    public sealed class Slot
    {
        public int Val;
        public Slot(int v) { Spec.Ensures(Val == v); Val = v; }
    }

    public sealed class Holder
    {
        public Slot? S;
        public Ghost<ObjSet> Repr;

        [GhostFunction]
        public bool Valid()
        {
            Spec.Reads(Repr.Value.Add(this));
            return Repr.Value.Contains(this) && S != null && Repr.Value.Contains(S);
        }

        // BUG: reads the slot's value, which Spec.Reads does not cover (CSV1017)
        [GhostFunction]
        public bool Positive()
        {
            Spec.Reads(ObjSet.Of(this));
            return S != null && S.Val > 0;
        }

        // BUG: promises nothing about freshness, so clients cannot tell two holders apart (see Independent)
        public Holder()
        {
            Spec.Ensures(Valid());
            S = new Slot(0);
            Repr = Ghost.Of(ObjSet.Of(this).Add(S));
        }

        public void Bump()
        {
            Spec.Requires(Valid());
            Spec.Modifies(Repr.Value);
            Spec.Ensures(Valid() && Repr.Value == Spec.Old(Repr.Value));
            S!.Val = checked(S!.Val + 1);
        }
    }

    public static class FrameBugs
    {
        // BUG: writes a slot outside its Spec.Modifies frame (CSV1017)
        public static void Sneaky(Holder h, Slot other)
        {
            Spec.Requires(h.Valid());
            Spec.Modifies(ObjSet.Of(other));
            h.S!.Val = 1;
        }

        // BUG: without Spec.Fresh the two representations may overlap, so b may have changed (CSV1004)
        public static void Independent()
        {
            var a = new Holder();
            var b = new Holder();
            int before = b.S!.Val;
            a.Bump();
            Spec.Assert(b.S!.Val == before);
        }
    }
}
