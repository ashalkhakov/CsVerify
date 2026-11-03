using CsVerify;

namespace Samples
{
    // Read shares of owned objects (counting permissions, the fractional permissions of ATS's early prototype):
    // the view keeps writing rights only while every share it split off is back. A share can be passed around
    // freely, two of them may name one object, and whoever holds one knows nobody writes the object meanwhile.

    /// <summary>A range that never inverts.</summary>
    [Owned]
    public sealed class Gauge
    {
        public int Lo, Hi;

        [Invariant, Pure] public bool Valid() => Lo <= Hi;

        public Gauge(int lo, int hi)
        {
            Spec.Requires(lo <= hi);
            Spec.Ensures(Lo == lo && Hi == hi);
            Lo = lo;
            Hi = hi;
        }

        public void Widen(int by)
        {
            Spec.Requires(0 <= by && by <= 1000 && Hi <= 1000000);
            Spec.Ensures(Hi == Spec.Old(Hi) + by && Lo == Spec.Old(Lo));
            Hi += by;
        }
    }

    public static class Shares
    {
        /// <summary>A reader with a share: the invariant holds, though it cannot write.</summary>
        public static bool Contains(in Shared<Gauge> s, Gauge g, int x)
        {
            Spec.Requires(s.Obj.Value == g);
            Spec.Ensures((bool r) => r == (g.Lo <= x && x <= g.Hi));
            return g.Lo <= x && x <= g.Hi;
        }

        /// <summary>Two shares, perhaps of one gauge (two views could never be): does a's range lie within b's?</summary>
        public static bool Within(in Shared<Gauge> a, Gauge x, in Shared<Gauge> b, Gauge y)
        {
            Spec.Requires(a.Obj.Value == x && b.Obj.Value == y);
            Spec.Ensures((bool r) => r == (y.Lo <= x.Lo && x.Hi <= y.Hi));
            return y.Lo <= x.Lo && x.Hi <= y.Hi;
        }

        /// <summary>Shares out, reads; all back, a write; the reads saw a gauge nobody changed.</summary>
        public static bool Demo()
        {
            Spec.Ensures((bool r) => r);
            var g = Own.New(new Gauge(1, 5), out var v);
            Own.Share(ref v, out var s1);
            Own.Share(ref v, out var s2);
            bool same = Within(in s1, g, in s2, g);      // a gauge lies within itself
            bool three = Contains(in s1, g, 3);
            Own.Unshare(ref v, s1);
            Own.Unshare(ref v, s2);
            g.Widen(5);                                  // whole again: it may write
            bool ten = Contains2(ref v, g, 10);
            Own.Drop(v);
            return same && three && ten;
        }

        /// <summary>Lends a share for one call, from a view passed by reference.</summary>
        private static bool Contains2(ref Own<Gauge> v, Gauge g, int x)
        {
            Spec.Requires(v.Obj.Value == g);
            Spec.Ensures((bool r) => r == (g.Lo <= x && x <= g.Hi) && g.Lo == Spec.Old(g.Lo) && g.Hi == Spec.Old(g.Hi));
            Own.Share(ref v, out var s);
            bool r = Contains(in s, g, x);
            Own.Unshare(ref v, s);
            return r;
        }
    }
}
