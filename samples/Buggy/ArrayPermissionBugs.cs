using CsVerify;

namespace Samples.Buggy
{
    public static class ArrayPermissionBugs
    {
        public static void Exchange(int[] a, int i, int j)
        {
            Spec.Requires(0 <= i && i < a.Length && 0 <= j && j < a.Length && Spec.Acc(a, i, i + 1) && Spec.Acc(a, j, j + 1));
            Spec.Ensures(Spec.Acc(a, i, i + 1) && Spec.Acc(a, j, j + 1));
            int t = a[i];
            a[i] = a[j];
            a[j] = t;
        }

        // BUG: one cell given twice (CSV1016)
        public static void ExchangeSame(int[] a)
        {
            Spec.Requires(a.Length > 2);
            Exchange(a, 1, 1);
        }

        // BUG: writes a cell outside its permission (CSV1016)
        public static void PastTheEnd(int[] a)
        {
            Spec.Requires(a.Length > 2 && Spec.Acc(a, 0, 1));
            a[1] = 0;
        }

        public static void Unframed(int[] a)
        {
            Spec.Requires(a.Length > 0);
            a[0] = 1;
        }

        // BUG: calls a method that may write any array, so its own frame cannot be kept (CSV1016)
        public static void CallsUnframed(int[] a)
        {
            Spec.Requires(a.Length > 0 && Spec.Acc(a));
            Spec.Ensures(Spec.Acc(a));
            Unframed(a);
        }
    }
}
