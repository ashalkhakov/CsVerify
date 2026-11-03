using CsVerify;

namespace Samples.Buggy
{
    [Owned]
    public sealed class Wallet
    {
        public int Cash;

        [Invariant, Pure] public bool Valid() => Cash >= 0;

        // BUG: can leave the wallet negative, breaking the invariant it must give back (CSV1015)
        public void Spend(int amount)
        {
            Spec.Requires(amount >= 0);
            Cash -= amount;
        }
    }

    public static class OwnedBugs
    {
        // BUG: writes a wallet without its view (CSV1016)
        public static void Steal(Wallet w) { w.Cash = 0; }

        // BUG: a second view of an existing wallet would break uniqueness (CSV1016)
        public static void Forge(Wallet w)
        {
            Own.New(w, out var v);
            Own.Drop(v);
        }

        // BUG: without the view, nothing says the invariant holds right now (CSV1002)
        public static int Peek(Wallet w)
        {
            Spec.Ensures((int r) => r >= 0);
            return w.Cash;
        }

        // BUG: written after the view was given up (CSV1016)
        public static void AfterDrop()
        {
            var w = Own.New(new Wallet(), out var v);
            Own.Drop(v);
            w.Cash = 5;
        }
    }
}
