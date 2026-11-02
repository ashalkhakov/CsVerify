using CsVerify;

namespace Samples
{
    /// <summary>
    /// Array views, ATS-style: an ArrayView&lt;T&gt; is array_v(T, n, l). Split hands the two halves of an array to
    /// different code (each with its own pointer, l and l + i); Join gives the whole back. The linearity analyzer
    /// checks that a borrowed view is whole again on return, the verifier checks addresses, lengths and contents.
    /// </summary>
    public static class ArrayViews
    {
        /// <summary>A specification-only predicate (ATS static function): s[0..n) are all x.</summary>
        [GhostFunction]
        public static bool AllEqual(Seq<int> s, int n, int x) => Spec.Forall(0, n, j => s[j].Value == x);

        /// <summary>Fills the n cells of the view with x, divide and conquer.</summary>
        public static void Fill(ref ArrayView<int> view, Ptr<int> p, int n, int x)
        {
            Spec.Requires(view.Addr == p.Addr && view.Length.Value == n);
            Spec.Ensures(view.Addr == Spec.Old(view).Addr && view.Length == Spec.Old(view).Length);
            Spec.Ensures(AllEqual(view.Elems, n, x));
            Spec.Decreases(n);
            Mem.LengthIsNatural(in view);                                  // n : nat
            if (n == 0) return;
            if (n == 1) { Mem.Set(ref view, p, 0, x); return; }
            int mid = n / 2;
            Mem.Split(view, Ghost.Of(mid), out var left, out var right);   // array_v(n, l) -> array_v(mid, l) * array_v(n-mid, l+mid)
            Fill(ref left, p, mid, x);
            Fill(ref right, p.Offset(mid), n - mid, x);                   // pointer arithmetic: l + mid
            Mem.Join(left, right, out view);                               // and back
        }

        /// <summary>Swaps the first and last cells: two disjoint views, each read and written through its own pointer.</summary>
        public static void SwapEnds(ref ArrayView<int> view, Ptr<int> p, int n)
        {
            Spec.Requires(view.Addr == p.Addr && view.Length.Value == n && n >= 2);
            Spec.Ensures(view.Addr == Spec.Old(view).Addr && view.Length == Spec.Old(view).Length);
            Spec.Ensures(view.Elems == Spec.Old(view).Elems.Update(0, Spec.Old(view).Elems[n - 1]).Update(n - 1, Spec.Old(view).Elems[0]));
            Mem.Split(view, Ghost.Of(n - 1), out var front, out var last);
            Ptr<int> q = p.Offset(n - 1);
            int a = Mem.Get(in front, p, 0);
            int b = Mem.Get(in last, q, 0);
            Mem.Set(ref front, p, 0, b);
            Mem.Set(ref last, q, 0, a);
            Mem.Join(front, last, out view);
        }

        public static int Demo()
        {
            Spec.Ensures<int>(r => r == 9 + 7);   // first = old last = 9, middle untouched = 7
            Ptr<int> p = Mem.AllocArray(10, 0, out ArrayView<int> view, out FreeGc<int> gc);
            Fill(ref view, p, 10, 7);
            Mem.Set(ref view, p, 9, 9);
            SwapEnds(ref view, p, 10);
            int first = Mem.Get(in view, p, 0);
            int middle = Mem.Get(in view, p, 5);
            Mem.FreeArray(gc, view, p);                                    // needs the whole view back and the gc token
            return first + middle;
        }
    }
}
