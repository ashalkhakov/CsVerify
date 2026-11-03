using CsVerify;

namespace Samples
{
    // Permissions to array cells (Viper's quantified permissions over a range): a method whose contract says
    // Spec.Acc(a, from, to) writes only those cells, so a call to it changes only them (and arrays it makes).
    // Methods without array permissions are as before: their array writes are not checked, and a call to one that
    // writes arrays forgets them all.
    public static class ArrayPermissions
    {
        /// <summary>Sets a[from..to) to v.</summary>
        public static void FillRange(int[] a, int from, int to, int v)
        {
            Spec.Requires(0 <= from && from <= to && to <= a.Length && Spec.Acc(a, from, to));
            Spec.Ensures(Spec.Acc(a, from, to) && Spec.Forall(from, to, i => a[i] == v));
            for (int i = from; i < to; i++)
            {
                Spec.Invariant(from <= i && i <= to && Spec.Forall(from, i, j => a[j] == v));
                a[i] = v;
            }
        }

        /// <summary>Two cells, one permission each: they are different cells.</summary>
        public static void SwapCells(int[] a, int i, int j)
        {
            Spec.Requires(0 <= i && i < a.Length && 0 <= j && j < a.Length && Spec.Acc(a, i, i + 1) && Spec.Acc(a, j, j + 1));
            Spec.Ensures(Spec.Acc(a, i, i + 1) && Spec.Acc(a, j, j + 1) && a[i] == Spec.Old(a[j]) && a[j] == Spec.Old(a[i]));
            Spec.Assert(i != j);
            int t = a[i];
            a[i] = a[j];
            a[j] = t;
        }

        /// <summary>A new array: all of it is the caller's.</summary>
        public static int[] Filled(int n, int v)
        {
            Spec.Requires(n >= 0);
            Spec.Ensures((int[] r) => Spec.Acc(r) && Spec.Fresh(r) && r.Length == n && Spec.Forall(0, n, i => r[i] == v));
            var r = new int[n];
            FillRange(r, 0, n, v);
            return r;
        }

        /// <summary>
        /// Two halves filled separately: the second fill keeps the first half, and the other array is untouched
        /// (this method has no array permissions of its own: it holds every cell, and gives the callees theirs).
        /// </summary>
        public static void Halves(int[] a, int[] other)
        {
            Spec.Requires(a.Length == 10 && other.Length == 10 && a != other);
            Spec.Ensures(a[0] == 1 && a[9] == 2 && other[3] == Spec.Old(other[3]));
            FillRange(a, 0, 5, 1);
            FillRange(a, 5, 10, 2);
        }

        public static int Demo()
        {
            Spec.Ensures((int r) => r == 10);
            var a = Filled(10, 0);
            var b = Filled(10, 7);
            Halves(a, b);
            SwapCells(a, 0, 9);
            return a[0] + a[9] + b[3]; // 2 + 1 + 7: the swap changed a's two cells, nothing of b
        }
    }
}
