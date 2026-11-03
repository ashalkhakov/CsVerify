using CsVerify;

namespace Samples.Buggy
{
    /// <summary>Each method here has a bug the verifier or the analyzers report. See README "Diagnostics".</summary>
    public static class Bugs
    {
        // CSV1003: off by one, i <= a.Length reads one past the end.
        public static int SumOffByOne(int[] a)
        {
            int sum = 0;
            for (int i = 0; i <= a.Length; i++)
            {
                Spec.Invariant(0 <= i && i <= a.Length + 1);
                sum = checked(sum + a[i]);
            }
            return sum;
        }

        // CSV1002 + CSV1012: the postcondition promises more than the code does, and for an empty array a[0] in it
        // means nothing at all.
        public static int First(int[] a)
        {
            Spec.Ensures<int>(r => r == a[0]);
            return a.Length > 0 ? a[0] : 0;
        }

        public static int Div(int x, int y)
        {
            Spec.Requires(y != 0);
            return x / y;
        }

        // CSV1001: the callee's precondition y != 0 is not established.
        public static int Average(int total, int count) => Div(total, count);

        // CSV1006: the invariant is not maintained (i grows past n).
        public static int CountUp(int n)
        {
            Spec.Requires(n >= 0);
            int i = 0;
            while (i < n)
            {
                Spec.Invariant(i < n);
                i++;
            }
            return i;
        }

        // CSV1008: the recursion's measure does not decrease.
        public static int Loop(int n)
        {
            Spec.Requires(n >= 0);
            Spec.Decreases(n);
            if (n == 0) return 0;
            return Loop(n);
        }

        // CSV1004: without the lemma call the fact is not known.
        public static int TriWithoutLemma(int n)
        {
            Spec.Requires(n >= 2);
            Spec.Assert(2 * Samples.Buggy.Math.Tri(n) == n * (n + 1));
            return n;
        }

        // CSV1001: reading through a pointer the view is not about (view.Addr != q.Addr).
        public static int WrongPointer()
        {
            var p = Mem.Alloc(1, out var vp);
            var q = Mem.Alloc(2, out var vq);
            int x = Mem.Read(in vp, q);
            Mem.Free(vp, p);
            Mem.Free(vq, q);
            return x;
        }
    }

    public static class Math
    {
        [GhostFunction]
        public static int Tri(int n)
        {
            Spec.Requires(n >= 0);
            Spec.Decreases(n);
            return n == 0 ? 0 : n + Tri(n - 1);
        }
    }
}
