using CsVerify;

namespace Samples.Buggy
{
    /// <summary>The ported ATS and Dafny samples (samples/Good/AtsIntro.cs, DafnyClassics.cs), each with one planted bug.</summary>
    public static class PortBugs
    {
        [Pure]
        public static int Fib(int n)
        {
            Spec.Requires(n >= 0);
            Spec.Decreases(n);
            return n < 2 ? n : Fib(n - 1) + Fib(n - 2);
        }

        // CSV1005: the accumulators start at FIB(1), FIB(2) instead of FIB(0), FIB(1).
        public static int FibWrongStart(int n)
        {
            Spec.Requires(n >= 0);
            Spec.Ensures<int>(r => r == Fib(n));
            int a = 1, b = 1;
            for (int i = 0; i < n; i++)
            {
                Spec.Invariant(0 <= i && i <= n);
                Spec.Invariant(a == Fib(i) && b == Fib(i + 1));
                Spec.Decreases(n - i);
                int c = a + b;
                a = b;
                b = c;
            }
            return a;
        }

        // CSV1003: mirrors index i to n - i instead of n - 1 - i, so the first swap reads a[n].
        public static void ReverseOffByOne(int[] a)
        {
            int n = a.Length;
            for (int i = 0; i < n / 2; i++)
            {
                Spec.Invariant(0 <= i && i <= n / 2 && n == a.Length);
                Spec.Decreases(n / 2 - i);
                int t = a[i];
                a[i] = a[n - i];
                a[n - i] = t;
            }
        }

        [Pure]
        public static int Pow(int b, int e)
        {
            Spec.Requires(e >= 0);
            Spec.Decreases(e);
            return e == 0 ? 1 : b * Pow(b, e - 1);
        }

        // CSV1002: squaring without the PowAdd lemma: true, but Z3 cannot see b^(2k) = b^k * b^k by itself.
        public static int FastPowWithoutLemma(int b, int e)
        {
            Spec.Requires(e >= 0);
            Spec.Ensures<int>(r => r == Pow(b, e));
            Spec.Decreases(e);
            if (e == 0) return 1;
            int h = FastPowWithoutLemma(b, e / 2);
            if (e % 2 == 0) return h * h;
            return b * h * h;
        }

        // CSV1008: f91 with the wrong termination metric (n instead of 101 - n).
        public static int McCarthyWrongMeasure(int n)
        {
            Spec.Ensures<int>(r => r == (n <= 100 ? 91 : n - 10));
            Spec.Decreases(n);
            if (n > 100) return n - 10;
            return McCarthyWrongMeasure(McCarthyWrongMeasure(n + 11));
        }

        // CSV1006 + CSV1007: the Dutch flag that forgets mid++ after swapping a 0 into place: lo overtakes mid, and
        // the loop can spin on the same cell without the measure going down.
        public static void DutchFlagStuck(int[] a)
        {
            Spec.Requires(Spec.Forall(0, a.Length, k => 0 <= a[k] && a[k] <= 2));
            int lo = 0, mid = 0, hi = a.Length;
            while (mid < hi)
            {
                Spec.Invariant(0 <= lo && lo <= mid && mid <= hi && hi <= a.Length);
                Spec.Decreases(hi - mid);
                if (a[mid] == 0)
                {
                    int t = a[lo]; a[lo] = a[mid]; a[mid] = t;
                    lo++;
                }
                else if (a[mid] == 1) mid++;
                else { hi--; int t = a[mid]; a[mid] = a[hi]; a[hi] = t; }
            }
        }
    }
}
