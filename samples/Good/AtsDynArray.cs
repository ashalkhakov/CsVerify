using CsVerify;

namespace Samples
{
    // A port of libatsc's dynarray (Hongwei Xi and Artyom Shalkhakov, 2019): a growable array, a buffer with a
    // capacity and a length. The ATS view DYNARRAY(a, m, n, l) = array_v(a, l, n) * array_v(a?, l + n, m - n) *
    // mfree_gc_v(l) * myprop(m, n) becomes a predicate over the header and its buffer's cells. The ATS version tracks
    // the length; here each operation also says what the contents become.

    /// <summary>DYNARRAYNODE: the buffer and the length (the capacity is the buffer's length).</summary>
    [Owned]
    public sealed class DynArray
    {
        public int[] Data;
        public int Len;

        public DynArray(int[] data)
        {
            Spec.Ensures(Len == 0 && Data == data);
            Data = data;
        }
    }

    public static class AtsDynArray
    {
        /// <summary>The largest capacity: doubling it stays an int.</summary>
        public const int MaxCapacity = 0x3FFFFFFF;

        /// <summary>dynarray(a, n): n items in a buffer of capacity m, 0 &lt; m, n &lt;= m (myprop), all of its cells held.</summary>
        [Predicate]
        public static bool Dyn(DynArray d, int n) =>
            d != null && Spec.Acc(d) && d.Data != null && d.Len == n && 0 <= n && n <= d.Data.Length &&
            0 < d.Data.Length && d.Data.Length <= MaxCapacity && Spec.Acc(d.Data);

        /// <summary>
        /// The buffer, seen from outside a held Dyn (Viper's unfolding in a function): specifications speak of the
        /// contents through it.
        /// </summary>
        [Pure]
        public static int[] Buf(DynArray d, int n)
        {
            Spec.Requires(Dyn(d, n));
            Spec.Ensures((int[] r) => r != null && 0 <= n && n <= r.Length && 0 < r.Length && r.Length <= MaxCapacity);
            Spec.Unfold(Dyn(d, n));
            return d.Data;
        }

        /// <summary>dynarray_make_nil.</summary>
        public static DynArray MakeNil(int capacity)
        {
            Spec.Requires(0 < capacity && capacity <= MaxCapacity);
            Spec.Ensures((DynArray r) => Dyn(r, 0) && Buf(r, 0).Length == capacity);
            var buffer = new int[capacity]; // array_ptr_alloc: its cells are in hand here
            var d = Own.New(new DynArray(buffer), out var view);
            Own.ToAcc(view);
            Spec.Fold(Dyn(d, 0));
            return d;
        }

        /// <summary>dynarray_get_size.</summary>
        public static int Size(DynArray d, int n)
        {
            Spec.Requires(Dyn(d, n));
            Spec.Ensures((int r) => r == n && Dyn(d, n));
            Spec.Ensures(Buf(d, n) == Spec.Old(Buf(d, n)) && Spec.Forall(0, n, j => Buf(d, n)[j] == Spec.Old(Buf(d, n)[j])));
            Spec.Unfold(Dyn(d, n));
            int len = d.Len;
            Spec.Fold(Dyn(d, n));
            return len;
        }

        /// <summary>dynarray_get_at_size: A[i].</summary>
        public static int Get(DynArray d, int n, int i)
        {
            Spec.Requires(0 <= i && i < n && Dyn(d, n));
            Spec.Ensures((int r) => r == Buf(d, n)[i] && Dyn(d, n));
            Spec.Ensures(Buf(d, n) == Spec.Old(Buf(d, n)) && Spec.Forall(0, n, j => Buf(d, n)[j] == Spec.Old(Buf(d, n)[j])));
            Spec.Unfold(Dyn(d, n));
            int x = d.Data[i];
            Spec.Fold(Dyn(d, n));
            return x;
        }

        /// <summary>dynarray_set_at_size: A[i] := x, nothing else changes.</summary>
        public static void Set(DynArray d, int n, int i, int x)
        {
            Spec.Requires(0 <= i && i < n && Dyn(d, n));
            Spec.Ensures(Dyn(d, n) && Buf(d, n) == Spec.Old(Buf(d, n)) && Buf(d, n)[i] == x);
            Spec.Ensures(Spec.Forall(0, n, j => j != i ? Buf(d, n)[j] == Spec.Old(Buf(d, n)[j]) : true));
            Spec.Unfold(Dyn(d, n));
            d.Data[i] = x;
            Spec.Fold(Dyn(d, n));
        }

        /// <summary>
        /// recapacitize with dynarray$frealloc: if the capacity is below m1, a new buffer of capacity m1 with the
        /// n items copied into it (the old one is left to the collector, ATS's mfree).
        /// </summary>
        public static void Recapacitize(DynArray d, int n, int m1)
        {
            Spec.Requires(m1 <= MaxCapacity && Dyn(d, n));
            Spec.Ensures(Dyn(d, n) && Buf(d, n).Length >= m1);
            Spec.Ensures(Spec.Forall(0, n, j => Buf(d, n)[j] == Spec.Old(Buf(d, n)[j])));
            Spec.Unfold(Dyn(d, n));
            var old = d.Data;
            if (m1 > old.Length)
            {
                var fresh = new int[m1];
                for (int j = 0; j < n; j++)
                {
                    Spec.Invariant(0 <= j && j <= n && Spec.Forall(0, j, k => fresh[k] == old[k]));
                    fresh[j] = old[j];
                }
                d.Data = fresh;
            }
            Spec.Fold(Dyn(d, n));
        }

        /// <summary>
        /// dynarray_insert_at: before index i. A full buffer grows first ($fgrow: twice the capacity); the items
        /// from i move one cell right (memmove_right), from the end down.
        /// </summary>
        public static void InsertAt(DynArray d, int n, int i, int x)
        {
            Spec.Requires(0 <= i && i <= n && n < MaxCapacity && Dyn(d, n));
            Spec.Ensures(Dyn(d, n + 1) && Buf(d, n + 1)[i] == x);
            Spec.Ensures(Spec.Forall(0, i, j => Buf(d, n + 1)[j] == Spec.Old(Buf(d, n)[j])));
            Spec.Ensures(Spec.Forall(i + 1, n + 1, j => Buf(d, n + 1)[j] == Spec.Old(Buf(d, n)[j - 1])));
            Spec.Unfold(Dyn(d, n));
            int cap = d.Data.Length;
            Spec.Fold(Dyn(d, n));
            if (n == cap) Recapacitize(d, n, cap <= MaxCapacity / 2 ? cap + cap : MaxCapacity);
            Spec.Unfold(Dyn(d, n));
            var a = d.Data;
            for (int k = n; k > i; k--)
            {
                Spec.Invariant(i <= k && k <= n);
                Spec.Invariant(Spec.Forall(0, k, j => a[j] == Spec.Old(Buf(d, n)[j])));
                Spec.Invariant(Spec.Forall(k + 1, n + 1, j => a[j] == Spec.Old(Buf(d, n)[j - 1])));
                a[k] = a[k - 1];
            }
            a[i] = x;
            d.Len = n + 1;
            Spec.Fold(Dyn(d, n + 1));
        }

        /// <summary>dynarray_append: insert after the last.</summary>
        public static void Append(DynArray d, int n, int x)
        {
            Spec.Requires(0 <= n && n < MaxCapacity && Dyn(d, n));
            Spec.Ensures(Dyn(d, n + 1) && Buf(d, n + 1)[n] == x && Spec.Forall(0, n, j => Buf(d, n + 1)[j] == Spec.Old(Buf(d, n)[j])));
            InsertAt(d, n, n, x);
        }

        /// <summary>dynarray_takeout_at: the item at i comes out; the items after it move one cell left.</summary>
        public static int TakeoutAt(DynArray d, int n, int i)
        {
            Spec.Requires(0 <= i && i < n && Dyn(d, n));
            Spec.Ensures((int r) => r == Spec.Old(Buf(d, n)[i]) && Dyn(d, n - 1));
            Spec.Ensures(Spec.Forall(0, i, j => Buf(d, n - 1)[j] == Spec.Old(Buf(d, n)[j])));
            Spec.Ensures(Spec.Forall(i, n - 1, j => Buf(d, n - 1)[j] == Spec.Old(Buf(d, n)[j + 1])));
            Spec.Unfold(Dyn(d, n));
            var a = d.Data;
            int res = a[i];
            for (int k = i; k < n - 1; k++)
            {
                Spec.Invariant(i <= k && k <= n - 1);
                Spec.Invariant(Spec.Forall(0, i, j => a[j] == Spec.Old(Buf(d, n)[j])));
                Spec.Invariant(Spec.Forall(i, k, j => a[j] == Spec.Old(Buf(d, n)[j + 1])));
                Spec.Invariant(Spec.Forall(k, n, j => a[j] == Spec.Old(Buf(d, n)[j])));
                a[k] = a[k + 1];
            }
            d.Len = n - 1;
            Spec.Fold(Dyn(d, n - 1));
            return res;
        }

        /// <summary>dynarray_takeout_last.</summary>
        public static int TakeoutLast(DynArray d, int n)
        {
            Spec.Requires(0 < n && Dyn(d, n));
            Spec.Ensures((int r) => r == Spec.Old(Buf(d, n)[n - 1]) && Dyn(d, n - 1) && Spec.Forall(0, n - 1, j => Buf(d, n - 1)[j] == Spec.Old(Buf(d, n)[j])));
            return TakeoutAt(d, n, n - 1);
        }

        /// <summary>dynarray_reset_capacity: done only if the n items still fit (and the capacity grows).</summary>
        public static bool ResetCapacity(DynArray d, int n, int m1)
        {
            Spec.Requires(1 <= m1 && m1 <= MaxCapacity && Dyn(d, n));
            Spec.Ensures((bool done) => Dyn(d, n) && Spec.Forall(0, n, j => Buf(d, n)[j] == Spec.Old(Buf(d, n)[j])) && (done ? Buf(d, n).Length >= m1 : true));
            if (m1 < n) return false;
            Recapacitize(d, n, m1);
            return true;
        }

        /// <summary>Append 1, 2, 3 into a buffer of one (growing twice), insert 0 in front, take out index 2.</summary>
        public static int Demo()
        {
            Spec.Ensures((int r) => r == 2);
            var d = MakeNil(1);
            Append(d, 0, 1);
            Append(d, 1, 2);
            Append(d, 2, 3);                 // [1, 2, 3]
            InsertAt(d, 3, 0, 0);            // [0, 1, 2, 3]
            int x = TakeoutAt(d, 4, 2);      // 2, leaving [0, 1, 3]
            int last = Get(d, 3, 2), size = Size(d, 3);
            Spec.Assert(last == 3 && size == 3);
            return x;
        }
    }
}
