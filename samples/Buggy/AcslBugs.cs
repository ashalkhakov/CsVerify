using CsVerify;

namespace Samples.Buggy
{
    public static class AcslBugs
    {
        [GhostFunction]
        public static bool Increasing(int[] a, int n)
        {
            Spec.Requires(0 <= n && n <= a.Length);
            return Spec.Forall(0, n, i => Spec.Forall(i, n, j => a[i] <= a[j]));
        }

        // BUG: compares with <= instead of <, so this is upper_bound under lower_bound's contract (CSV1006)
        public static int LowerBoundWrong(int[] a, int n, int v)
        {
            Spec.Requires(0 <= n && n <= a.Length && Increasing(a, n));
            Spec.Ensures((int r) => 0 <= r && r <= n && Spec.Forall(0, r, i => a[i] < v) && Spec.Forall(r, n, i => v <= a[i]));
            int left = 0, right = n;
            while (left < right)
            {
                Spec.Invariant(0 <= left && left <= right && right <= n);
                Spec.Invariant(Spec.Forall(0, left, i => a[i] < v) && Spec.Forall(right, n, i => v <= a[i]));
                Spec.Decreases(right - left);
                int middle = left + (right - left) / 2;
                if (a[middle] <= v) left = middle + 1; else right = middle;
            }
            return left;
        }

        // BUG: keeps searching after a match, so it finds the last v, not the first (CSV1002)
        public static int FindLast(int[] a, int n, int v)
        {
            Spec.Requires(0 <= n && n <= a.Length);
            Spec.Ensures((int r) => 0 <= r && r <= n && Spec.Forall(0, r, i => a[i] != v) && (r == n || a[r] == v));
            int found = n;
            for (int i = 0; i < n; i++)
            {
                Spec.Invariant(0 <= i && i <= n && (found == n || 0 <= found && found < i && a[found] == v));
                if (a[i] == v) found = i;
            }
            return found;
        }

        // BUG: copies into the destination, but the contract says the ranges may overlap: nothing then says a is unchanged (CSV1002)
        public static void CopyOverlapping(int[] a, int n, int[] b)
        {
            Spec.Requires(0 <= n && n <= a.Length && n <= b.Length);
            Spec.Ensures(Spec.Forall(0, n, i => b[i] == Spec.Old(a[i])));
            for (int i = 0; i < n; i++)
            {
                Spec.Invariant(0 <= i && i <= n && Spec.Forall(0, i, k => b[k] == Spec.Old(a[k])));
                b[i] = a[i];
            }
        }
    
        // BUG: copies the minimum over a[i] instead of swapping: sorted, but an element is lost (CSV1006)
        public static void SelectionSortCopies(int[] a)
        {
            Spec.Ensures(Spec.Multiset(a, a.Length) == Spec.Old(Spec.Multiset(a, a.Length)));
            int n = a.Length;
            for (int i = 0; i < n; i++)
            {
                Spec.Invariant(0 <= i && i <= n && Spec.Multiset(a, n) == Spec.Old(Spec.Multiset(a, n)));
                int sel = i;
                for (int j = i + 1; j < n; j++)
                {
                    Spec.Invariant(i < j && j <= n && i <= sel && sel < j);
                    if (a[j] < a[sel]) sel = j;
                }
                a[i] = a[sel];
            }
        }
}
}
