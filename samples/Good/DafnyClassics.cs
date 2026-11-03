using System;
using System.Diagnostics;
using CsVerify;

namespace Samples
{
    /// <summary>
    /// Standard Dafny teaching examples (the Dafny tutorial and "Getting Started with Dafny", Leino's examples),
    /// re-expressed in C#. Dafny's <c>requires</c>/<c>ensures</c>/<c>invariant</c>/<c>decreases</c> map one to one;
    /// <c>forall k :: lo &lt;= k &lt; hi ==&gt; P</c> is <c>Spec.Forall(lo, hi, k =&gt; P)</c>; <c>function</c> is [Pure],
    /// <c>lemma</c> is [Lemma].
    /// </summary>
    public static class DafnyClassics
    {
        /// <summary>Index of a maximum element (Dafny tutorial, FindMax).</summary>
        public static int FindMax(int[] a)
        {
            Spec.Requires(a.Length > 0);
            Spec.Ensures<int>(r => 0 <= r && r < a.Length);
            Spec.Ensures<int>(r => Spec.Forall(0, a.Length, k => a[k] <= a[r]));
            int best = 0;
            for (int i = 1; i < a.Length; i++)
            {
                Spec.Invariant(1 <= i && i <= a.Length);
                Spec.Invariant(0 <= best && best < a.Length);
                Spec.Invariant(Spec.Forall(0, i, k => a[k] <= a[best]));
                Spec.Decreases(a.Length - i);
                if (a[i] > a[best]) best = i;
            }
            return best;
        }

        /// <summary>Linear search (Dafny tutorial, Find): the first index holding key, or -1 if there is none.</summary>
        public static int Find(int[] a, int key)
        {
            Spec.Ensures<int>(r => -1 <= r && r < a.Length);
            Spec.Ensures<int>(r => r < 0 || a[r] == key);
            Spec.Ensures<int>(r => r >= 0 || Spec.Forall(0, a.Length, k => a[k] != key));
            Spec.Ensures<int>(r => r < 0 || Spec.Forall(0, r, k => a[k] != key));
            for (int i = 0; i < a.Length; i++)
            {
                Spec.Invariant(0 <= i && i <= a.Length);
                Spec.Invariant(Spec.Forall(0, i, k => a[k] != key));
                Spec.Decreases(a.Length - i);
                if (a[i] == key) return i;
            }
            return -1;
        }

        /// <summary>Reverses an array in place: the postcondition relates every cell to the old contents.</summary>
        public static void Reverse(int[] a)
        {
            Spec.Ensures(Spec.Forall(0, a.Length, k => a[k] == Spec.Old(a[a.Length - 1 - k])));
            int n = a.Length;
            for (int i = 0; i < n / 2; i++)
            {
                Spec.Invariant(0 <= i && i <= n / 2 && n == a.Length);
                Spec.Invariant(Spec.Forall(0, i, k => a[k] == Spec.Old(a[n - 1 - k]) && a[n - 1 - k] == Spec.Old(a[k])));
                Spec.Invariant(Spec.Forall(i, n - i, k => a[k] == Spec.Old(a[k])));
                Spec.Decreases(n / 2 - i);
                int t = a[i];
                a[i] = a[n - 1 - i];
                a[n - 1 - i] = t;
            }
        }

        /// <summary>Integer square root by linear search: r*r &lt;= n &lt; (r+1)*(r+1).</summary>
        public static int Sqrt(int n)
        {
            Spec.Requires(n >= 0);
            Spec.Ensures<int>(r => r >= 0 && r * r <= n && n < (r + 1) * (r + 1));
            int r = 0;
            while (checked((long)(r + 1) * (r + 1)) <= n)
            {
                Spec.Invariant(r >= 0 && r * r <= n);
                Spec.Decreases(n - r * r);
                r = r + 1;
            }
            return r;
        }

        // ---- fast exponentiation, with an inductive lemma ------------------------------------------------------

        [GhostFunction]
        public static int Pow(int b, int e)
        {
            Spec.Requires(e >= 0);
            Spec.Decreases(e);
            return e == 0 ? 1 : b * Pow(b, e - 1);
        }

        /// <summary>b^(m+n) = b^m * b^n, by induction on m.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void PowAdd(int b, int m, int n)
        {
            Spec.Requires(m >= 0 && n >= 0);
            Spec.Ensures(Pow(b, m + n) == Pow(b, m) * Pow(b, n));
            Spec.Decreases(m);
            if (m > 0) PowAdd(b, m - 1, n);
        }

        /// <summary>Exponentiation by squaring, recursive: halves the exponent, the lemma justifies squaring.</summary>
        public static int FastPow(int b, int e)
        {
            Spec.Requires(e >= 0);
            Spec.Ensures<int>(r => r == Pow(b, e));
            Spec.Decreases(e);
            if (e == 0) return 1;
            int h = FastPow(b, e / 2);
            PowAdd(b, e / 2, e / 2);
            if (e % 2 == 0) return checked(h * h);
            PowAdd(b, 1, e - 1);
            return checked(b * h * h);
        }

        // ---- Dutch national flag, bounds and colours (no permutation) ----------------------------------------

        /// <summary>
        /// Dijkstra's Dutch national flag over colours 0, 1, 2 (Dafny's DutchFlag): afterwards the array is
        /// 0s, then 1s, then 2s. The original also proves the result a permutation of the input (Dafny's
        /// <c>multiset(a[..]) == old(multiset(a[..]))</c>); CsVerify has no multisets, so that part is left out.
        /// </summary>
        public static void DutchFlag(int[] a)
        {
            Spec.Requires(Spec.Forall(0, a.Length, k => 0 <= a[k] && a[k] <= 2));
            Spec.Ensures(Spec.Forall(0, a.Length, k => 0 <= a[k] && a[k] <= 2));
            Spec.Ensures(Spec.Forall(0, a.Length, i => Spec.Forall(i, a.Length, j => a[i] <= a[j])));
            int lo = 0, mid = 0, hi = a.Length;
            while (mid < hi)
            {
                Spec.Invariant(0 <= lo && lo <= mid && mid <= hi && hi <= a.Length);
                Spec.Invariant(Spec.Forall(0, a.Length, k => 0 <= a[k] && a[k] <= 2));
                Spec.Invariant(Spec.Forall(0, lo, k => a[k] == 0));
                Spec.Invariant(Spec.Forall(lo, mid, k => a[k] == 1));
                Spec.Invariant(Spec.Forall(hi, a.Length, k => a[k] == 2));
                Spec.Decreases(hi - mid);
                if (a[mid] == 0)
                {
                    int t = a[lo]; a[lo] = a[mid]; a[mid] = t;
                    lo++; mid++;
                }
                else if (a[mid] == 1)
                {
                    mid++;
                }
                else
                {
                    hi--;
                    int t = a[mid]; a[mid] = a[hi]; a[hi] = t;
                }
            }
        }
        // ---- McCarthy's 91 function (INT2PROGINATS, Dafny's McCarthy91 and KatzManna) --------------------------

        /// <summary>
        /// Nested recursion: the outer call's argument is the inner call's result, so termination needs the inner
        /// call's postcondition. ATS: <c>fun f91 {i:int} .&lt;max(101-i, 0)&gt;. (x: int i): [j:int | ...] int j</c>.
        /// </summary>
        public static int McCarthy91(int n)
        {
            Spec.Ensures<int>(r => r == (n <= 100 ? 91 : n - 10));
            Spec.Decreases(101 - n);
            if (n > 100) return n - 10;
            return McCarthy91(McCarthy91(n + 11));
        }

        // ---- FindZero (Dafny's dafny1/FindZero.dfy) ------------------------------------------------------------

        /// <summary>
        /// In an array of naturals that drops by at most one per step, a[j] &gt; 0 means none of the next a[j]
        /// cells can be zero. Proved with a loop inside the lemma.
        /// </summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void Skipping(int[] a, int j)
        {
            Spec.Requires(Spec.Forall(0, a.Length, i => 0 <= a[i]));
            Spec.Requires(Spec.Forall(1, a.Length, i => a[i - 1] - 1 <= a[i]));
            Spec.Requires(0 <= j && j < a.Length);
            Spec.Ensures(Spec.Forall(j, Math.Min(j + a[j], a.Length), k => a[k] != 0));
            int k = j;
            while (k < j + a[j] && k < a.Length)
            {
                Spec.Invariant(j <= k && k <= a.Length);
                Spec.Invariant(k == a.Length || a[k] >= a[j] - (k - j));
                Spec.Invariant(Spec.Forall(j, k, i => a[i] != 0));
                Spec.Decreases(a.Length - k);
                k++;
            }
        }

        /// <summary>Searches for a zero, jumping a[i] cells at a time instead of one.</summary>
        public static int FindZero(int[] a)
        {
            Spec.Requires(Spec.Forall(0, a.Length, i => 0 <= a[i]));
            Spec.Requires(Spec.Forall(1, a.Length, i => a[i - 1] - 1 <= a[i]));
            Spec.Ensures<int>(r => r < 0 || (r < a.Length && a[r] == 0));
            Spec.Ensures<int>(r => r >= 0 || Spec.Forall(0, a.Length, k => a[k] != 0));
            int index = 0;
            while (index < a.Length)
            {
                Spec.Invariant(0 <= index);
                Spec.Invariant(Spec.Forall(0, Math.Min(index, a.Length), k => a[k] != 0));
                Spec.Decreases(a.Length - index);
                if (a[index] == 0) return index;
                Skipping(a, index);
                index = checked(index + a[index]);
            }
            return -1;
        }
    }
}
