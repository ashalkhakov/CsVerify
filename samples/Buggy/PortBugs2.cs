using System.Diagnostics;
using CsVerify;

namespace Samples.Buggy
{
    /// <summary>The second batch of ports (AtsMatrixAndTakeOut.cs, DafnyMore.cs), each with one planted bug.</summary>
    public static class PortBugs2
    {
        // CSV1001: the cell taken out is l + i, but it is written through l + i + 1.
        public static void IncrementWrongCell(ref ArrayView<int> view, Ptr<int> p, int i)
        {
            Spec.Requires(view.Addr == p.Addr && 0 <= i && i + 1 < view.Length.Value);
            Mem.TakeOut(view, Ghost.Of(i), out PointsTo<int> cell, out ArrayHole<int> rest);
            Ptr<int> q = p.Offset(checked(i + 1));
            Mem.Write(ref cell, q, 0);
            Mem.PutBack(cell, rest, out view);
        }

        // CSV1003: row-major order strides by the number of columns n, not rows m (out of range when m > n).
        public static int MatGetWrongStride(int[] a, int m, int n, int i, int j)
        {
            Spec.Requires(a.Length == m * n);
            Spec.Requires(0 <= i && i < m && 0 <= j && j < n);
            return a[checked(i * m + j)];
        }

        [GhostFunction]
        public static int Sum(int[] a, int s, int t)
        {
            Spec.Requires(0 <= s && s <= t && t <= a.Length);
            Spec.Decreases(t - s);
            return s == t ? 0 : Sum(a, s, t - 1) + a[t - 1];
        }

        // CSV1006: when the running sum goes negative, Kadane restarts the segment at n; this resets the sum only.
        public static (int k, int m) KadaneForgetsRestart(int[] a)
        {
            Spec.Ensures<(int k, int m)>(r => 0 <= r.k && r.k <= r.m && r.m <= a.Length);
            int k = 0, m = 0, s = 0;
            int c = 0, t = 0;
            for (int n = 0; n < a.Length; )
            {
                Spec.Invariant(n <= a.Length && 0 <= c && c <= n && t == Sum(a, c, n));
                Spec.Invariant(0 <= k && k <= m && m <= n && s == Sum(a, k, m));
                Spec.Decreases(a.Length - n);
                t = checked(t + a[n]);
                n = n + 1;
                if (t < 0) { t = 0; }
                else if (s < t) { k = c; m = n; s = t; }
            }
            return (k, m);
        }

        // CSV1006: the second difference of n³ is 6n + 6; stepping it by 5 breaks the invariant.
        public static void CubesWrongStep(int[] a)
        {
            int c = 0, k = 1, m = 6;
            for (int n = 0; n < a.Length; n++)
            {
                Spec.Invariant(0 <= n && n <= a.Length);
                Spec.Invariant(c == n * n * n && k == 3 * n * n + 3 * n + 1 && m == 6 * n + 6);
                Spec.Decreases(a.Length - n);
                a[n] = c;
                checked
                {
                    c = c + k;
                    k = k + m;
                    m = m + 5;
                }
            }
        }

        [GhostFunction]
        public static int Gauss(int n)
        {
            Spec.Requires(n >= 0);
            Spec.Decreases(n);
            return n == 0 ? 0 : Gauss(n - 1) + (n - 1);
        }

        [GhostFunction]
        public static int SumCubes(int n)
        {
            Spec.Requires(n >= 0);
            Spec.Decreases(n);
            return n == 0 ? 0 : SumCubes(n - 1) + (n - 1) * (n - 1) * (n - 1);
        }

        // CSV1002: true (Nicomachus), but only by induction; without the lemma call the postcondition is not proved.
        public static int SumOfCubesWithoutLemma(int n)
        {
            Spec.Requires(0 <= n && n <= 100);
            Spec.Ensures<int>(r => r == Gauss(n) * Gauss(n));
            int sum = 0;
            for (int i = 0; i < n; i++)
            {
                Spec.Invariant(0 <= i && i <= n && sum == SumCubes(i));
                Spec.Decreases(n - i);
                sum = checked(sum + i * i * i);
            }
            return sum;
        }
    }
}
