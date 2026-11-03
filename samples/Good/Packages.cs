using CsVerify;

namespace Samples
{
    // Packages of views: a [Linear] positional readonly record struct holds views (and anything else) together,
    // as ATS's viewtypes pair a view with its pointer. Building one hands its views over (their invariants hold),
    // deconstructing it gives them back; a call that gets a package may change only the objects whose views are in it.

    /// <summary>A counter that never goes negative.</summary>
    [Owned]
    public sealed class Tally
    {
        public int Count;

        [Invariant, Pure] public bool Valid() => Count >= 0;

        public Tally()
        {
            Spec.Ensures(Count == 0);
            Count = 0;
        }
    }

    /// <summary>A tally and its view, travelling together (ATS: <c>(tally @ l | ptr l)</c>).</summary>
    [Linear]
    public readonly record struct OwnedTally(Own<Tally> View, Tally Obj)
    {
        /// <summary>The view is of the object: proved where a package is built, known wherever it is taken apart.</summary>
        [Invariant, GhostFunction] public bool Valid() => View.Obj.Value == Obj;
    }

    public static class Packages
    {
        /// <summary>A new tally, packed.</summary>
        public static OwnedTally Make()
        {
            Spec.Ensures((OwnedTally r) => r.Obj.Count == 0);
            var t = Own.New(new Tally(), out var view);
            return new OwnedTally(view, t);
        }

        /// <summary>Counts once: unpack, write, pack again.</summary>
        public static void Tick(ref OwnedTally tally)
        {
            Spec.Requires(tally.Obj.Count < int.MaxValue);
            Spec.Ensures(tally.Obj.Count == Spec.Old(tally.Obj.Count) + 1);
            var (view, t) = tally;
            t.Count = checked(t.Count + 1);
            tally = new OwnedTally(view, t);
        }

        /// <summary>Two packages and a view in hand: ticking one changes neither the other nor the object in hand.</summary>
        public static int Demo(Tally mine, ref Own<Tally> mineView)
        {
            Spec.Requires(mineView.Obj.Value == mine && mine.Count == 0);
            Spec.Ensures((int r) => r == 2 && mine.Count == 1);
            mine.Count = 1;
            var a = Make();
            var b = Make();
            Tick(ref a);
            Tick(ref b);
            Spec.Assert(mine.Count == 1);
            var (av, at) = a;
            var (bv, bt) = b;
            Spec.Assert(at.Count == 1 && bt.Count == 1 && at != bt); // two views: two tallies
            int r = at.Count + bt.Count;
            Own.Drop(av);
            Own.Drop(bv);
            return r;
        }
    }
}
