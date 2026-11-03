using CsVerify;

namespace Samples.Buggy
{
    [Owned]
    public sealed class Dial
    {
        public int Pos;

        [Invariant, Pure] public bool Valid() => Pos >= 0;

        public Dial() { Pos = 0; }
    }

    public static class ShareBugs
    {
        public static int Look(Shared<Dial> s, Dial d)
        {
            Spec.Requires(s.Obj.Value == d);
            int p = d.Pos;
            Own.Drop(s);
            return p;
        }

        public static void Turn(ref Own<Dial> v, Dial d)
        {
            Spec.Requires(v.Obj.Value == d);
            d.Pos = 1;
        }

        // BUG: a share is out for good, so the view is no longer whole: it cannot write (CSV1016)
        public static void WriteWhileShared(ref Own<Dial> v, Dial d)
        {
            Spec.Requires(v.Obj.Value == d);
            Own.Share(ref v, out var s);
            Look(s, d);
            d.Pos = 2;
        }

        // BUG: nor can it be handed to code that may write (CSV1016)
        public static void LendWhileShared(ref Own<Dial> v, Dial d)
        {
            Spec.Requires(v.Obj.Value == d);
            Own.Share(ref v, out var s);
            Own.Drop(s);
            Turn(ref v, d);
        }

        // BUG: a share holder writes (CSV1016)
        public static void WriteThroughShare(Shared<Dial> s, Dial d)
        {
            Spec.Requires(s.Obj.Value == d);
            d.Pos = 3;
            Own.Drop(s);
        }

        // BUG: joins a share of some other dial (CSV1016)
        public static void WrongJoin(ref Own<Dial> v, Shared<Dial> other)
        {
            Own.Unshare(ref v, other);
        }

        public static int Peek(in Own<Dial> v, Dial d)
        {
            Spec.Requires(v.Obj.Value == d);
            Spec.Ensures((int r) => r >= 0);
            return d.Pos;
        }

        // BUG: lends the view read-only while its invariant is broken: the reader relies on it (CSV1015)
        public static void LendBroken(ref Own<Dial> v, Dial d)
        {
            Spec.Requires(v.Obj.Value == d);
            d.Pos = -1;
            Peek(in v, d);
            d.Pos = 0;
        }

        // BUG: two views lent read-only may be the same one (CSV1004)
        public static void Distinct(in Own<Dial> a, in Own<Dial> b)
        {
            Spec.Assert(a.Obj.Value != b.Obj.Value);
        }
    }
}
