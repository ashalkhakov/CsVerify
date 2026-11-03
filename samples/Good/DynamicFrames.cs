using CsVerify;

namespace Samples
{
    // Dafny-style dynamic frames (the Dafny tutorial's Valid()/Repr idiom), for ordinary mutable classes: each Pair
    // keeps a ghost set of the objects it is made of, a ghost Valid() that reads only them, and methods that may
    // change only them. Two pairs built separately have disjoint representations, so updating one leaves the
    // other, and its Valid(), as it was.
    /// <summary>A mutable cell.</summary>
    public sealed class Cell
    {
        public int Val;
        public Cell(int v) { Spec.Ensures(Val == v); Val = v; }
    }
    /// <summary>Two distinct cells, owned through a ghost representation set.</summary>
    public sealed class Pair
    {
        public Cell? A, B;
        public Ghost<ObjSet> Repr;

        [GhostFunction] public bool Valid()
        {
            Spec.Reads(Repr.Value.Add(this));
            return Repr.Value.Contains(this) && A != null && B != null && A != B && Repr.Value.Contains(A) && Repr.Value.Contains(B);
        }

        public Pair()
        {
            Spec.Ensures(Valid() && A!.Val == 0 && B!.Val == 0 && Spec.Fresh(Repr.Value));
            A = new Cell(0);
            B = new Cell(0);
            Repr = Ghost.Of(ObjSet.Of(this).Add(A).Add(B));
        }

        public void IncA()
        {
            Spec.Requires(Valid() && A!.Val < int.MaxValue);
            Spec.Modifies(Repr.Value);
            Spec.Ensures(Valid() && Repr.Value == Spec.Old(Repr.Value) && A!.Val == Spec.Old(A!.Val) + 1 && B!.Val == Spec.Old(B!.Val));
            A!.Val++;
        }

        public void Swap()
        {
            Spec.Requires(Valid());
            Spec.Modifies(Repr.Value);
            Spec.Ensures(Valid() && Repr.Value == Spec.Old(Repr.Value) && A == Spec.Old(B) && B == Spec.Old(A));
            var t = A; A = B; B = t;
        }
    }

    public static class DynamicFrames
    {
        public static int Demo()
        {
            var p = new Pair();
            var q = new Pair();
            p.IncA();
            p.Swap();
            Spec.Assert(q.Valid() && q.A!.Val == 0 && p.B!.Val == 1);
            return p.A!.Val + 10 * p.B!.Val + 100 * q.A!.Val;
        }
    }
}
