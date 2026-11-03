using CsVerify;

namespace Samples.Buggy
{
    [Owned]
    public sealed class Gem
    {
        public int Carat;

        [Invariant, Pure] public bool Valid() => Carat >= 0;

        public Gem()
        {
            Spec.Ensures(Carat == 0);
            Carat = 0;
        }
    }

    [Linear]
    public readonly record struct GemBox(Own<Gem> View, Gem Obj)
    {
        [Invariant, GhostFunction] public bool Valid() => View.Obj.Value == Obj;
    }

    public static class PackageBugs
    {
        public static void Polish(ref GemBox box)
        {
            var (view, gem) = box;
            gem.Carat = 5;
            box = new GemBox(view, gem);
        }

        // BUG: a call that gets the package may change the gem in it (CSV1004)
        public static void StaleRead(ref GemBox box)
        {
            var (view, gem) = box;
            int before = gem.Carat;
            box = new GemBox(view, gem);
            Polish(ref box);
            Spec.Assert(gem.Carat == before);
        }

        // BUG: packs a gem whose invariant is broken (CSV1015)
        public static void PackBroken(Gem gem, ref Own<Gem> view)
        {
            Spec.Requires(view.Obj.Value == gem);
            gem.Carat = -1;
            var box = new GemBox(view, gem);
            var (back, g) = box;
            g.Carat = 0;
            view = back;
        }

        // BUG: the view is in the package, not in hand (CSV1016)
        public static void WriteThroughBox(ref GemBox box)
        {
            box.Obj.Carat = 3;
        }

        // BUG: packs a view with some other object: the package's invariant fails (CSV1015)
        public static GemBox Mismatch(Gem other)
        {
            var gem = Own.New(new Gem(), out var view);
            return new GemBox(view, other);
        }
    }
}
