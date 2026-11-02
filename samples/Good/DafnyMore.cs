using System.Diagnostics;
using CsVerify;

namespace Samples
{
    /// <summary>
    /// More programs from Dafny's test suite (dafny1/Cubes.dfy, dafny1/SumOfCubes.dfy, dafny2/Classics.dfy,
    /// dafny2/SegmentSum.dfy), rewritten in C# over int arrays.
    /// </summary>
    public static class DafnyMore
    {
        // ---- maximum segment sum (Kadane) ---------------------------------------------------------------------

        /// <summary>a[s] + ... + a[t-1].</summary>
        [Pure]
        public static int Sum(int[] a, int s, int t)
        {
            Spec.Requires(0 <= s && s <= t && t <= a.Length);
            Spec.Decreases(t - s);
            return s == t ? 0 : Sum(a, s, t - 1) + a[t - 1];
        }

        /// <summary>
        /// Kadane's algorithm: a segment a[k..m) of maximum sum, in one pass, keeping the best segment so far and the
        /// best segment ending at n. Dafny's <c>returns (k: int, m: int)</c> is a C# tuple.
        /// </summary>
        public static (int k, int m) MaxSegSum(int[] a)
        {
            Spec.Ensures<(int k, int m)>(r => 0 <= r.k && r.k <= r.m && r.m <= a.Length);
            Spec.Ensures<(int k, int m)>(r => Spec.Forall(0, a.Length + 1, p => Spec.Forall(p, a.Length + 1, q => Sum(a, p, q) <= Sum(a, r.k, r.m))));
            int k = 0, m = 0, s = 0;  // best segment so far: a[k..m), s = its sum
            int c = 0, t = 0;         // best segment ending at n: a[c..n), t = its sum
            for (int n = 0; n < a.Length; )
            {
                Spec.Invariant(n <= a.Length && 0 <= c && c <= n && t == Sum(a, c, n));
                Spec.Invariant(Spec.Forall(0, n + 1, b => Sum(a, b, n) <= Sum(a, c, n)));
                Spec.Invariant(0 <= k && k <= m && m <= n && s == Sum(a, k, m));
                Spec.Invariant(Spec.Forall(0, n + 1, p => Spec.Forall(p, n + 1, q => Sum(a, p, q) <= Sum(a, k, m))));
                Spec.Decreases(a.Length - n);
                t = t + a[n];
                n = n + 1;
                if (t < 0) { c = n; t = 0; }
                else if (s < t) { k = c; m = n; s = t; }
            }
            return (k, m);
        }

        // ---- cubes by addition --------------------------------------------------------------------------------

        /// <summary>Fills a[i] = i³ using additions only: finite differences of n³ are 3n² + 3n + 1, then 6n + 6, then 6.</summary>
        public static void Cubes(int[] a)
        {
            Spec.Ensures(Spec.Forall(0, a.Length, i => a[i] == i * i * i));
            int c = 0, k = 1, m = 6;
            for (int n = 0; n < a.Length; n++)
            {
                Spec.Invariant(0 <= n && n <= a.Length);
                Spec.Invariant(Spec.Forall(0, n, i => a[i] == i * i * i));
                Spec.Invariant(c == n * n * n && k == 3 * n * n + 3 * n + 1 && m == 6 * n + 6);
                Spec.Decreases(a.Length - n);
                a[n] = c;
                c = c + k;
                k = k + m;
                m = m + 6;
            }
        }

        // ---- sum of cubes is the square of the sum ------------------------------------------------------------

        /// <summary>0 + 1 + ... + (n-1).</summary>
        [Pure]
        public static int Gauss(int n)
        {
            Spec.Requires(n >= 0);
            Spec.Decreases(n);
            return n == 0 ? 0 : Gauss(n - 1) + (n - 1);
        }

        /// <summary>0³ + 1³ + ... + (n-1)³.</summary>
        [Pure]
        public static int SumCubes(int n)
        {
            Spec.Requires(n >= 0);
            Spec.Decreases(n);
            return n == 0 ? 0 : SumCubes(n - 1) + (n - 1) * (n - 1) * (n - 1);
        }

        [Lemma, Conditional(Spec.Symbol)]
        public static void GaussFormula(int n)
        {
            Spec.Requires(n >= 0);
            Spec.Ensures(2 * Gauss(n) == n * (n - 1));
            Spec.Decreases(n);
            if (n > 0) GaussFormula(n - 1);
        }

        /// <summary>
        /// Nicomachus: Σ i³ = (Σ i)². Step: adding n³ to G² gives (G + n)² because 2 G n = n²(n - 1), by Gauss.
        /// </summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void Nicomachus(int n)
        {
            Spec.Requires(n >= 0);
            Spec.Ensures(SumCubes(n) == Gauss(n) * Gauss(n));
            Spec.Decreases(n);
            if (n > 0)
            {
                Nicomachus(n - 1);
                GaussFormula(n - 1);
            }
        }

        /// <summary>Computes Σ i³ for i &lt; n with a loop and returns it squared-sum style, proved by the lemma.</summary>
        public static int SumOfCubes(int n)
        {
            Spec.Requires(0 <= n && n <= 100);
            Spec.Ensures<int>(r => r == Gauss(n) * Gauss(n));
            int sum = 0;
            for (int i = 0; i < n; i++)
            {
                Spec.Invariant(0 <= i && i <= n && sum == SumCubes(i));
                Spec.Decreases(n - i);
                sum += i * i * i;
            }
            Nicomachus(n);
            return sum;
        }

        // ---- factorial with additions only (Classics.dfy) -----------------------------------------------------

        [Pure]
        public static int Factorial(int n)
        {
            Spec.Requires(n >= 0);
            Spec.Decreases(n);
            return n == 0 ? 1 : n * Factorial(n - 1);
        }

        /// <summary>Multiplication by r + 1 done as r + 1 additions of the previous factorial.</summary>
        public static int AdditiveFactorial(int n)
        {
            Spec.Requires(0 <= n && n <= 12);
            Spec.Ensures<int>(u => u == Factorial(n));
            int u = 1;
            for (int r = 0; r < n; r++)
            {
                Spec.Invariant(0 <= r && r <= n && u == Factorial(r));
                Spec.Decreases(n - r);
                int v = u;
                for (int s = 1; s <= r; s++)
                {
                    Spec.Invariant(1 <= s && s <= r + 1 && u == s * Factorial(r));
                    Spec.Decreases(r + 1 - s);
                    u = u + v;
                }
            }
            return u;
        }
    }
}
