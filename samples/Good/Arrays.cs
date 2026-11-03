using CsVerify;

namespace Samples
{
    public static class Arrays
    {
        /// <summary>Sum of a[0..n), a mathematical (ghost) definition: every a[i] is proved in bounds.</summary>
        [GhostFunction]
        public static int SumTo(int[] a, int n)
        {
            Spec.Requires(0 <= n && n <= a.Length);
            Spec.Decreases(n);
            return n == 0 ? 0 : SumTo(a, n - 1) + a[n - 1];
        }

        public static int Sum(int[] a)
        {
            Spec.Ensures<int>(r => r == SumTo(a, a.Length));
            int sum = 0;
            for (int i = 0; i < a.Length; i++)
            {
                Spec.Invariant(0 <= i && i <= a.Length);
                Spec.Invariant(sum == SumTo(a, i));
                Spec.Decreases(a.Length - i);
                sum = checked(sum + a[i]); // throws if the sum leaves int, so a return means it did not
            }
            return sum;
        }

        /// <summary>Classic binary search over a sorted array, with the full functional specification.</summary>
        public static int BinarySearch(int[] a, int key)
        {
            Spec.Requires(Spec.Forall(0, a.Length, i => Spec.Forall(i, a.Length, j => a[i] <= a[j])));
            Spec.Ensures<int>(r => -1 <= r && r < a.Length);
            Spec.Ensures<int>(r => r < 0 || a[r] == key);
            Spec.Ensures<int>(r => r >= 0 || Spec.Forall(0, a.Length, i => a[i] != key));
            int lo = 0, hi = a.Length;
            while (lo < hi)
            {
                Spec.Invariant(0 <= lo && lo <= hi && hi <= a.Length);
                Spec.Invariant(Spec.Forall(0, lo, i => a[i] < key));
                Spec.Invariant(Spec.Forall(hi, a.Length, i => a[i] > key));
                Spec.Decreases(hi - lo);
                int mid = lo + (hi - lo) / 2;
                if (a[mid] < key) lo = mid + 1;
                else if (a[mid] > key) hi = mid;
                else return mid;
            }
            return -1;
        }

        /// <summary>Returns a copy of a with x appended; the length postcondition is ATS's array(a, n+1).</summary>
        public static int[] Append(int[] a, int x)
        {
            Spec.Requires(a.Length < int.MaxValue);
            Spec.Ensures<int[]>(r => r.Length == a.Length + 1);
            Spec.Ensures<int[]>(r => r[a.Length] == x && Spec.Forall(0, a.Length, j => r[j] == a[j]));
            var result = new int[a.Length + 1];
            for (int i = 0; i < a.Length; i++)
            {
                Spec.Invariant(0 <= i && i <= a.Length);
                Spec.Invariant(Spec.Forall(0, i, j => result[j] == a[j]));
                result[i] = a[i];
            }
            result[a.Length] = x;
            return result;
        }

        /// <summary>A static index as a ghost parameter: ATS's {n:nat} (A: arrayref(int, n), n: int n).</summary>
        public static int Last(int[] a, Ghost<int> n)
        {
            Spec.Requires(n.Value > 0 && a.Length == n.Value);
            Spec.Ensures<int>(r => r == a[n.Value - 1]);
            return a[a.Length - 1];
        }

        public static int LastOfThree()
        {
            var a = new[] { 1, 2, 3 };
            int last = Last(a, Ghost.Of(3));
            Spec.Assert(last == 3);
            return last;
        }
    }
}
