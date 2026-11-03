using CsVerify;

namespace Samples
{
    /// <summary>
    /// Ports from "ACSL by Example" (Fraunhofer FOKUS, MIT licence): C++ standard algorithms specified in ACSL and
    /// verified with Frama-C/WP, rewritten in C# with the ACSL contracts carried over. The translation:
    /// <c>\valid_read(a + (0..n-1))</c> is <c>n &lt;= a.Length</c>; <c>behavior</c>s are case-split postconditions;
    /// <c>assigns</c> is the inferred frame plus explicit "unchanged" postconditions (<c>Unchanged{Old,Here}</c>);
    /// <c>\separated</c> is <c>a != b</c>; logic functions (<c>Count</c>, <c>Accumulate</c>) are recursive [Pure]
    /// definitions. Integers are mathematical here (run csverify --overflow for ACSL's bounds); permutation
    /// the sorting chapter's MultisetReorder is Spec.Multiset(a, n) == Spec.Old(Spec.Multiset(a, n)).
    /// </summary>
    public static class AcslByExample
    {
        // ------------------------------------------------------------------------------- logic

        /// <summary>Increasing(a, n): a[0..n) is sorted.</summary>
        [GhostFunction]
        public static bool Increasing(int[] a, int n)
        {
            Spec.Requires(0 <= n && n <= a.Length);
            return Spec.Forall(0, n, i => Spec.Forall(i, n, j => a[i] <= a[j]));
        }

        /// <summary>The logic function Count(a, n, v): occurrences of v in a[0..n).</summary>
        [Pure]
        public static int Count(int[] a, int n, int v)
        {
            Spec.Requires(0 <= n && n <= a.Length);
            Spec.Decreases(n);
            Spec.Ensures((int r) => 0 <= r && r <= n);
            return n == 0 ? 0 : Count(a, n - 1, v) + (a[n - 1] == v ? 1 : 0);
        }

        /// <summary>The logic function Accumulate(a, n, init): init + a[0] + ... + a[n-1].</summary>
        [Pure]
        public static int Accumulate(int[] a, int n, int init)
        {
            Spec.Requires(0 <= n && n <= a.Length);
            Spec.Decreases(n);
            return n == 0 ? init : Accumulate(a, n - 1, init) + a[n - 1];
        }

        // ------------------------------------------------------------------------------- non-mutating

        /// <summary>find: behaviors some (the first index holding v) and none (n).</summary>
        public static int Find(int[] a, int n, int v)
        {
            Spec.Requires(0 <= n && n <= a.Length);
            Spec.Ensures((int r) => 0 <= r && r <= n && Spec.Forall(0, r, i => a[i] != v));
            Spec.Ensures((int r) => r == n || a[r] == v);
            for (int i = 0; i < n; i++)
            {
                Spec.Invariant(0 <= i && i <= n && Spec.Forall(0, i, k => a[k] != v));
                if (a[i] == v) return i;
            }
            return n;
        }

        /// <summary>mismatch: the first index where a and b differ, or n.</summary>
        public static int Mismatch(int[] a, int[] b, int n)
        {
            Spec.Requires(0 <= n && n <= a.Length && n <= b.Length);
            Spec.Ensures((int r) => 0 <= r && r <= n && Spec.Forall(0, r, i => a[i] == b[i]) && (r == n || a[r] != b[r]));
            for (int i = 0; i < n; i++)
            {
                Spec.Invariant(0 <= i && i <= n && Spec.Forall(0, i, k => a[k] == b[k]));
                if (a[i] != b[i]) return i;
            }
            return n;
        }

        /// <summary>equal: a[0..n) and b[0..n) agree, via mismatch.</summary>
        public static bool Equal(int[] a, int[] b, int n)
        {
            Spec.Requires(0 <= n && n <= a.Length && n <= b.Length);
            Spec.Ensures((bool r) => r == Spec.Forall(0, n, i => a[i] == b[i]));
            return Mismatch(a, b, n) == n;
        }

        /// <summary>adjacent_find: the first i with a[i] == a[i+1], or n.</summary>
        public static int AdjacentFind(int[] a, int n)
        {
            Spec.Requires(0 <= n && n <= a.Length);
            Spec.Ensures((int r) => 0 <= r && r <= n && Spec.Forall(0, r, i => i + 1 >= n || a[i] != a[i + 1]));
            Spec.Ensures((int r) => r == n || r + 1 < n && a[r] == a[r + 1]);
            Spec.Ensures((int r) => r < n || Spec.Forall(0, n - 1, i => a[i] != a[i + 1]));
            if (n <= 1) return n;
            for (int i = 0; i + 1 < n; i++)
            {
                Spec.Invariant(0 <= i && i + 1 <= n && Spec.Forall(0, i, k => a[k] != a[k + 1]));
                if (a[i] == a[i + 1]) return i;
            }
            return n;
        }

        /// <summary>count: the number of elements equal to v, as the logic function Count says.</summary>
        public static int CountOf(int[] a, int n, int v)
        {
            Spec.Requires(0 <= n && n <= a.Length);
            Spec.Ensures((int r) => r == Count(a, n, v) && 0 <= r && r <= n);
            int counted = 0;
            for (int i = 0; i < n; i++)
            {
                Spec.Invariant(0 <= i && i <= n && counted == Count(a, i, v));
                if (a[i] == v) counted++;
            }
            return counted;
        }

        // ------------------------------------------------------------------------------- min and max

        /// <summary>max_element: the first index of a largest element (0 when n is 0).</summary>
        public static int MaxElement(int[] a, int n)
        {
            Spec.Requires(0 <= n && n <= a.Length);
            Spec.Ensures((int r) => n == 0 ? r == 0 :
                0 <= r && r < n && Spec.Forall(0, n, i => a[i] <= a[r]) && Spec.Forall(0, r, i => a[i] < a[r]));
            if (n == 0) return 0;
            int max = 0;
            for (int i = 1; i < n; i++)
            {
                Spec.Invariant(1 <= i && i <= n && 0 <= max && max < i);
                Spec.Invariant(Spec.Forall(0, i, k => a[k] <= a[max]) && Spec.Forall(0, max, k => a[k] < a[max]));
                if (a[max] < a[i]) max = i;
            }
            return max;
        }

        /// <summary>clamp: v limited to [lo, hi].</summary>
        public static int Clamp(int v, int lo, int hi)
        {
            Spec.Requires(lo <= hi);
            Spec.Ensures((int r) => lo <= r && r <= hi && (v < lo ? r == lo : v > hi ? r == hi : r == v));
            return v < lo ? lo : hi < v ? hi : v;
        }

        // ------------------------------------------------------------------------------- binary search

        /// <summary>lower_bound: everything before the result is less than v, everything from it on is not.</summary>
        public static int LowerBound(int[] a, int n, int v)
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
                if (a[middle] < v) left = middle + 1; else right = middle;
            }
            return left;
        }

        /// <summary>upper_bound: everything before the result is at most v, everything from it on is greater.</summary>
        public static int UpperBound(int[] a, int n, int v)
        {
            Spec.Requires(0 <= n && n <= a.Length && Increasing(a, n));
            Spec.Ensures((int r) => 0 <= r && r <= n && Spec.Forall(0, r, i => a[i] <= v) && Spec.Forall(r, n, i => v < a[i]));
            int left = 0, right = n;
            while (left < right)
            {
                Spec.Invariant(0 <= left && left <= right && right <= n);
                Spec.Invariant(Spec.Forall(0, left, i => a[i] <= v) && Spec.Forall(right, n, i => v < a[i]));
                Spec.Decreases(right - left);
                int middle = left + (right - left) / 2;
                if (a[middle] <= v) left = middle + 1; else right = middle;
            }
            return left;
        }

        /// <summary>binary_search: is v in the sorted a[0..n)? Via lower_bound, as in the book.</summary>
        public static bool BinarySearch(int[] a, int n, int v)
        {
            Spec.Requires(0 <= n && n <= a.Length && Increasing(a, n));
            Spec.Ensures((bool r) => r == Spec.Exists(0, n, i => a[i] == v));
            int lb = LowerBound(a, n, v);
            return lb < n && a[lb] == v;
        }

        // ------------------------------------------------------------------------------- mutating

        /// <summary>fill: a[0..n) all become v; assigns a[0..n-1] (the rest is unchanged).</summary>
        public static void Fill(int[] a, int n, int v)
        {
            Spec.Requires(0 <= n && n <= a.Length);
            Spec.Ensures(Spec.Forall(0, n, i => a[i] == v) && Spec.Forall(n, a.Length, i => a[i] == Spec.Old(a[i])));
            for (int i = 0; i < n; i++)
            {
                Spec.Invariant(0 <= i && i <= n && Spec.Forall(0, i, k => a[k] == v) && Spec.Forall(n, a.Length, k => a[k] == Spec.Old(a[k])));
                a[i] = v;
            }
        }

        /// <summary>copy: b[0..n) becomes a[0..n); a is unchanged (\separated: different arrays).</summary>
        public static void Copy(int[] a, int n, int[] b)
        {
            Spec.Requires(0 <= n && n <= a.Length && n <= b.Length && a != b);
            Spec.Ensures(Spec.Forall(0, n, i => b[i] == a[i]) && Spec.Forall(0, a.Length, i => a[i] == Spec.Old(a[i])));
            for (int i = 0; i < n; i++)
            {
                Spec.Invariant(0 <= i && i <= n && Spec.Forall(0, i, k => b[k] == a[k]) && Spec.Forall(0, a.Length, k => a[k] == Spec.Old(a[k])));
                b[i] = a[i];
            }
        }

        /// <summary>swap_ranges: a[0..n) and b[0..n) exchange contents.</summary>
        public static void SwapRanges(int[] a, int n, int[] b)
        {
            Spec.Requires(0 <= n && n <= a.Length && n <= b.Length && a != b);
            Spec.Ensures(Spec.Forall(0, n, i => a[i] == Spec.Old(b[i]) && b[i] == Spec.Old(a[i])));
            for (int i = 0; i < n; i++)
            {
                Spec.Invariant(0 <= i && i <= n);
                Spec.Invariant(Spec.Forall(0, i, k => a[k] == Spec.Old(b[k]) && b[k] == Spec.Old(a[k])));
                Spec.Invariant(Spec.Forall(i, n, k => a[k] == Spec.Old(a[k]) && b[k] == Spec.Old(b[k])));
                int t = a[i];
                a[i] = b[i];
                b[i] = t;
            }
        }

        /// <summary>replace: every v becomes w, everything else stays.</summary>
        public static void Replace(int[] a, int n, int v, int w)
        {
            Spec.Requires(0 <= n && n <= a.Length);
            Spec.Ensures(Spec.Forall(0, n, i => Spec.Old(a[i]) == v ? a[i] == w : a[i] == Spec.Old(a[i])));
            for (int i = 0; i < n; i++)
            {
                Spec.Invariant(0 <= i && i <= n);
                Spec.Invariant(Spec.Forall(0, i, k => Spec.Old(a[k]) == v ? a[k] == w : a[k] == Spec.Old(a[k])));
                Spec.Invariant(Spec.Forall(i, n, k => a[k] == Spec.Old(a[k])));
                if (a[i] == v) a[i] = w;
            }
        }

        /// <summary>remove_copy: the elements of a other than v go to the front of b, in order of position.</summary>
        public static int RemoveCopy(int[] a, int n, int[] b, int v)
        {
            Spec.Requires(0 <= n && n <= a.Length && n <= b.Length && a != b);
            Spec.Ensures((int r) => 0 <= r && r <= n && Spec.Forall(0, r, i => b[i] != v));
            Spec.Ensures((int r) => r == n - Count(a, n, v));
            Spec.Ensures(Spec.Forall(0, a.Length, i => a[i] == Spec.Old(a[i])));
            Spec.Ensures((int r) => Spec.Forall(r, n, i => b[i] == Spec.Old(b[i])));
            int j = 0;
            for (int i = 0; i < n; i++)
            {
                Spec.Invariant(0 <= i && i <= n && 0 <= j && j <= i && j == i - Count(a, i, v));
                Spec.Invariant(Spec.Forall(0, j, k => b[k] != v) && Spec.Forall(j, n, k => b[k] == Spec.Old(b[k])));
                Spec.Invariant(Spec.Forall(0, a.Length, k => a[k] == Spec.Old(a[k])));
                if (a[i] != v)
                {
                    b[j] = a[i];
                    j++;
                }
            }
            return j;
        }

        /// <summary>reverse: a[i] gets the old a[n-1-i].</summary>
        public static void Reverse(int[] a, int n)
        {
            Spec.Requires(0 <= n && n <= a.Length);
            Spec.Ensures(Spec.Forall(0, n, i => a[i] == Spec.Old(a[n - 1 - i])));
            for (int i = 0; i < n / 2; i++)
            {
                Spec.Invariant(0 <= i && i <= n / 2);
                Spec.Invariant(Spec.Forall(0, i, k => a[k] == Spec.Old(a[n - 1 - k]) && a[n - 1 - k] == Spec.Old(a[k])));
                Spec.Invariant(Spec.Forall(i, n - i, k => a[k] == Spec.Old(a[k])));
                int t = a[i];
                a[i] = a[n - 1 - i];
                a[n - 1 - i] = t;
            }
        }

        // ------------------------------------------------------------------------------- numeric

        /// <summary>iota: a[i] == v + i.</summary>
        public static void Iota(int[] a, int n, int v)
        {
            Spec.Requires(0 <= n && n <= a.Length);
            Spec.Ensures(Spec.Forall(0, n, i => a[i] == v + i));
            for (int i = 0; i < n; i++)
            {
                Spec.Invariant(0 <= i && i <= n && Spec.Forall(0, i, k => a[k] == v + k));
                a[i] = v + i;
            }
        }

        /// <summary>accumulate: init plus the sum of a[0..n), as the logic function Accumulate says.</summary>
        public static int AccumulateOf(int[] a, int n, int init)
        {
            Spec.Requires(0 <= n && n <= a.Length);
            Spec.Ensures((int r) => r == Accumulate(a, n, init));
            int sum = init;
            for (int i = 0; i < n; i++)
            {
                Spec.Invariant(0 <= i && i <= n && sum == Accumulate(a, i, init));
                sum += a[i];
            }
            return sum;
        }

        /// <summary>partial_sum: b[i] is a[0] + ... + a[i]; a is unchanged.</summary>
        public static int PartialSum(int[] a, int n, int[] b)
        {
            Spec.Requires(0 <= n && n <= a.Length && n <= b.Length && a != b);
            Spec.Ensures((int r) => r == n);
            Spec.Ensures(Spec.Forall(0, n, i => b[i] == Accumulate(a, i + 1, 0)));
            Spec.Ensures(Spec.Forall(0, a.Length, i => a[i] == Spec.Old(a[i])));
            int sum = 0;
            for (int i = 0; i < n; i++)
            {
                Spec.Invariant(0 <= i && i <= n && sum == Accumulate(a, i, 0));
                Spec.Invariant(Spec.Forall(0, i, k => b[k] == Accumulate(a, k + 1, 0)));
                Spec.Invariant(Spec.Forall(0, a.Length, k => a[k] == Spec.Old(a[k])));
                sum += a[i];
                b[i] = sum;
            }
            return n;
        }

        /// <summary>is_sorted: does a[0..n) increase?</summary>
        public static bool IsSorted(int[] a, int n)
        {
            Spec.Requires(0 <= n && n <= a.Length);
            Spec.Ensures((bool r) => r == Spec.Forall(0, n - 1, i => a[i] <= a[i + 1]));
            for (int i = 0; i + 1 < n; i++)
            {
                Spec.Invariant(0 <= i && (i == 0 || i < n) && Spec.Forall(0, i, k => a[k] <= a[k + 1]));
                if (a[i] > a[i + 1]) return false;
            }
            return true;
        }

        // ------------------------------------------------------------------------------- sorting (with permutation)

        /// <summary>Exchanges a[i] and a[j]: the multiset of the array is unchanged, with no lemma (the write axioms).</summary>
        private static void Swap(int[] a, int i, int j)
        {
            Spec.Requires(0 <= i && i < a.Length && 0 <= j && j < a.Length);
            Spec.Ensures(a[i] == Spec.Old(a[j]) && a[j] == Spec.Old(a[i]));
            Spec.Ensures(Spec.Forall(0, a.Length, k => k == i || k == j || a[k] == Spec.Old(a[k])));
            Spec.Ensures(Spec.Multiset(a, a.Length) == Spec.Old(Spec.Multiset(a, a.Length)));
            int t = a[i];
            a[i] = a[j];
            a[j] = t;
        }

        /// <summary>selection_sort: MultisetReorder{Old,Here}(a, n) and Increasing(a, n).</summary>
        public static void SelectionSort(int[] a)
        {
            Spec.Ensures(Spec.Multiset(a, a.Length) == Spec.Old(Spec.Multiset(a, a.Length)));
            Spec.Ensures(Increasing(a, a.Length));
            int n = a.Length;
            for (int i = 0; i < n; i++)
            {
                Spec.Invariant(0 <= i && i <= n && Spec.Multiset(a, n) == Spec.Old(Spec.Multiset(a, n)));
                Spec.Invariant(Spec.Forall(0, i, k => Spec.Forall(k, i, l => a[k] <= a[l])));
                Spec.Invariant(Spec.Forall(0, i, k => Spec.Forall(i, n, l => a[k] <= a[l])));
                int sel = i;
                for (int j = i + 1; j < n; j++)
                {
                    Spec.Invariant(i < j && j <= n && i <= sel && sel < j && Spec.Forall(i, j, k => a[sel] <= a[k]));
                    if (a[j] < a[sel]) sel = j;
                }
                Swap(a, i, sel);
            }
        }

        /// <summary>bubble_sort: each pass carries the largest of a[0..i) to the end.</summary>
        public static void BubbleSort(int[] a)
        {
            Spec.Ensures(Spec.Multiset(a, a.Length) == Spec.Old(Spec.Multiset(a, a.Length)));
            Spec.Ensures(Increasing(a, a.Length));
            int n = a.Length;
            for (int i = n; i > 0; i--)
            {
                Spec.Invariant(0 <= i && i <= n && Spec.Multiset(a, n) == Spec.Old(Spec.Multiset(a, n)));
                Spec.Invariant(Spec.Forall(i, n, k => Spec.Forall(k, n, l => a[k] <= a[l])));
                Spec.Invariant(Spec.Forall(0, i, k => Spec.Forall(i, n, l => a[k] <= a[l])));
                for (int j = 0; j + 1 < i; j++)
                {
                    Spec.Invariant(0 <= j && j < i && Spec.Multiset(a, n) == Spec.Old(Spec.Multiset(a, n)));
                    Spec.Invariant(Spec.Forall(0, j, k => a[k] <= a[j]));
                    Spec.Invariant(Spec.Forall(i, n, k => Spec.Forall(k, n, l => a[k] <= a[l])));
                    Spec.Invariant(Spec.Forall(0, i, k => Spec.Forall(i, n, l => a[k] <= a[l])));
                    if (a[j] > a[j + 1]) Swap(a, j, j + 1);
                }
            }
        }

        /// <summary>
        /// insertion_sort, with adjacent swaps (the book's version moves a block with rotate): a[i] sinks into the
        /// sorted prefix.
        /// </summary>
        public static void InsertionSort(int[] a)
        {
            Spec.Ensures(Spec.Multiset(a, a.Length) == Spec.Old(Spec.Multiset(a, a.Length)));
            Spec.Ensures(Increasing(a, a.Length));
            int n = a.Length;
            for (int i = 0; i < n; i++)
            {
                Spec.Invariant(0 <= i && i <= n && Spec.Multiset(a, n) == Spec.Old(Spec.Multiset(a, n)));
                Spec.Invariant(Spec.Forall(0, i, k => Spec.Forall(k, i, l => a[k] <= a[l])));
                int j = i;
                while (j > 0 && a[j - 1] > a[j])
                {
                    // sorted except that a[j] may be smaller than what is before it
                    Spec.Invariant(0 <= j && j <= i && Spec.Multiset(a, n) == Spec.Old(Spec.Multiset(a, n)));
                    Spec.Invariant(Spec.Forall(0, i + 1, k => Spec.Forall(k, i + 1, l => k == j || l == j || a[k] <= a[l])));
                    Spec.Invariant(Spec.Forall(j, i + 1, l => a[j] <= a[l]));
                    Spec.Decreases(j);
                    Swap(a, j - 1, j);
                    j--;
                }
            }
        }

        /// <summary>3 1 2 sorted three ways: 123 123 123.</summary>
        public static int SortDemo()
        {
            var x = new[] { 3, 1, 2 };
            var y = new[] { 3, 1, 2 };
            var z = new[] { 3, 1, 2 };
            SelectionSort(x);
            BubbleSort(y);
            InsertionSort(z);
            return (x[0] * 100 + x[1] * 10 + x[2]) * 1000000 + (y[0] * 100 + y[1] * 10 + y[2]) * 1000 + z[0] * 100 + z[1] * 10 + z[2];
        }

        public static int Demo()
        {
            var a = new[] { 1, 3, 3, 5, 8 };
            var b = new int[5];
            int found = Find(a, 5, 5);                 // 3
            int lb = LowerBound(a, 5, 3);              // 1
            int ub = UpperBound(a, 5, 3);              // 3
            int count = CountOf(a, 5, 3);              // 2
            int kept = RemoveCopy(a, 5, b, 3);         // 3: b = 1 5 8
            PartialSum(a, 5, b);                       // b = 1 4 7 12 20
            return found * 10000 + lb * 1000 + ub * 100 + count * 10 + kept + b[4] * 100000;
        }
    }
}
