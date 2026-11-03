using System;
using CsVerify;

namespace Samples
{
    /// <summary>
    /// Array programs from the DML/ATS line of work, rewritten in C#: the dot product from Xi and Pfenning,
    /// "Eliminating Array Bound Checking Through Dependent Types" (PLDI 1998), where the whole point is that every
    /// subscript is proved in bounds; an array copy over linear array views (ATS's array_v); insertion sort, a
    /// staple of the ATS tutorials and of Dafny's.
    /// </summary>
    public static class AtsArrays
    {
        /// <summary>
        /// DML: <c>fun dotprod (v1, v2) = ... where dotprod &lt;| {n:nat} int array(n) * int array(n) -&gt; int</c>.
        /// The index n is the shared length; no subscript needs a run-time check.
        /// </summary>
        public static int DotProd(int[] v1, int[] v2)
        {
            Spec.Requires(v1.Length == v2.Length);
            int sum = 0;
            for (int i = 0; i < v1.Length; i++)
            {
                Spec.Invariant(0 <= i && i <= v1.Length);
                Spec.Decreases(v1.Length - i);
                sum += v1[i] * v2[i];
            }
            return sum;
        }

        /// <summary>A specification-only predicate: the first n cells of two views agree.</summary>
        [GhostFunction]
        public static bool SamePrefix(Seq<int> s, Seq<int> t, int n) => Spec.Forall(0, n, j => s[j].Value == t[j].Value);

        /// <summary>
        /// ATS's array copy over views: <c>(!array_v(a, n, l1), !array_v(a, n, l2) | ptr l1, ptr l2, int n)</c>.
        /// Both views are borrowed; the source comes back unchanged, the destination equal to it.
        /// </summary>
        public static void Copy(ref ArrayView<int> dst, in ArrayView<int> src, Ptr<int> pd, Ptr<int> ps, int n)
        {
            Spec.Requires(dst.Addr == pd.Addr && src.Addr == ps.Addr);
            Spec.Requires(dst.Length.Value == n && src.Length.Value == n);
            Spec.Ensures(dst.Addr == Spec.Old(dst).Addr && dst.Length == Spec.Old(dst).Length);
            Spec.Ensures(SamePrefix(dst.Elems, src.Elems, n));
            Mem.LengthIsNatural(in dst);                                   // n : nat
            for (int i = 0; i < n; i++)
            {
                Spec.Invariant(0 <= i && i <= n);
                Spec.Invariant(dst.Addr == pd.Addr && dst.Length.Value == n);
                Spec.Invariant(SamePrefix(dst.Elems, src.Elems, i));
                Spec.Decreases(n - i);
                Mem.Set(ref dst, pd, i, Mem.Get(in src, ps, i));
            }
        }

        public static int CopyDemo()
        {
            Spec.Ensures<int>(r => r == 5);
            var ps = Mem.AllocArray(3, 5, out ArrayView<int> src, out FreeGc<int> gs);
            var pd = Mem.AllocArray(3, 0, out ArrayView<int> dst, out FreeGc<int> gd);
            Copy(ref dst, in src, pd, ps, 3);
            int r = Mem.Get(in dst, pd, 2);
            Mem.FreeArray(gs, src, ps);
            Mem.FreeArray(gd, dst, pd);
            return r;
        }

        /// <summary>
        /// Insertion sort, proved to sort. That the result is a permutation of the input is not stated: CsVerify
        /// has no multisets (ATS proves it with a dataprop over lists, Dafny with <c>multiset</c>).
        /// </summary>
        public static void InsertionSort(int[] a)
        {
            Spec.Ensures(Spec.Forall(0, a.Length, k => Spec.Forall(k + 1, a.Length, l => a[k] <= a[l])));
            for (int i = 1; i < a.Length; i++)
            {
                Spec.Invariant(1 <= i && i <= Math.Max(a.Length, 1));
                Spec.Invariant(Spec.Forall(0, i, k => Spec.Forall(k + 1, i, l => a[k] <= a[l])));
                Spec.Decreases(a.Length - i);
                int x = a[i];
                int j = i;
                while (j > 0 && a[j - 1] > x)
                {
                    // a[0..i] is sorted except for the hole at j, and everything after the hole exceeds x
                    Spec.Invariant(0 <= j && j <= i && i < a.Length);
                    Spec.Invariant(Spec.Forall(0, i + 1, k => Spec.Forall(k + 1, i + 1, l => k == j || l == j || a[k] <= a[l])));
                    Spec.Invariant(Spec.Forall(j + 1, i + 1, k => x < a[k]));
                    Spec.Invariant(j == i || (j > 0 ? a[j - 1] <= a[j + 1] : true));
                    Spec.Decreases(j);
                    a[j] = a[j - 1];
                    j--;
                }
                a[j] = x;
            }
        }
    }
}
