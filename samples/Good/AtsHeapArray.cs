using CsVerify;

namespace Samples
{
    // A port of tfc's heaparray (Artyom Shalkhakov, after martinkunev's C heap): the binary heap of AtsBinHeap.cs as
    // an object, HEAPNODE(m, n, l) = data, size, count, with the view
    //   heap(T, m, n, l) = array_v(T, l, n) * array_v(T?, l + n, m - n) * mfree_gc_v(l) * myprop(m >= n).
    // Here that view is a predicate over the header and its buffer's cells, and it carries the heap order too, which
    // the ATS version does not state. Push, pop and front unfold it and run the array algorithms of AtsBinHeap.cs
    // (the hole moving up and down), whose proofs are reused; init, isnot_full, resize and term are new.

    /// <summary>HEAPNODE: the buffer (its length is the size m) and the count n.</summary>
    [Owned]
    public sealed class HeapArray
    {
        public int[] Data;
        public int Count;

        public HeapArray(int[] data)
        {
            Spec.Ensures(Data == data && Count == 0);
            Data = data;
        }
    }

    public static class AtsHeapArray
    {
        public const int MaxSize = 0x3FFFFFFE;

        /// <summary>heap(T, m, n, l): n items in a buffer of m (myprop: m >= n), all its cells held, in heap order.</summary>
        [Predicate]
        public static bool Heap(HeapArray h, int n) =>
            h != null && Spec.Acc(h) && h.Data != null && h.Count == n && 0 <= n && n <= h.Data.Length &&
            h.Data.Length <= MaxSize && Spec.Acc(h.Data) && Spec.Forall(1, n, j => h.Data[(j - 1) / 2] >= h.Data[j]);

        /// <summary>The buffer, seen from outside a held heap.</summary>
        [Pure]
        public static int[] Buf(HeapArray h, int n)
        {
            Spec.Requires(Heap(h, n));
            Spec.Ensures((int[] r) => r != null && 0 <= n && n <= r.Length && r.Length <= MaxSize && AtsBinHeap.IsHeap(r, n));
            Spec.Unfold(Heap(h, n));
            return h.Data;
        }

        /// <summary>heap_init: an empty heap of the given size.</summary>
        public static HeapArray Init(int size)
        {
            Spec.Requires(0 < size && size <= MaxSize);
            Spec.Ensures((HeapArray r) => Heap(r, 0) && Buf(r, 0).Length == size);
            var data = new int[size];
            var h = Own.New(new HeapArray(data), out var view);
            Own.ToAcc(view);
            Spec.Assert(AtsBinHeap.IsHeap(data, 0));
            Spec.Fold(Heap(h, 0));
            return h;
        }

        /// <summary>heap_isnot_full: count &lt; size.</summary>
        public static bool IsNotFull(HeapArray h, int n)
        {
            Spec.Requires(Heap(h, n));
            Spec.Ensures((bool r) => Heap(h, n) && r == (n < Buf(h, n).Length));
            Spec.Ensures(Buf(h, n) == Spec.Old(Buf(h, n)) && Spec.Forall(0, n, j => Buf(h, n)[j] == Spec.Old(Buf(h, n)[j])));
            Spec.Unfold(Heap(h, n));
            bool r = h.Count < h.Data.Length;
            Spec.Fold(Heap(h, n));
            return r;
        }

        /// <summary>heap_front: the largest item.</summary>
        public static int Front(HeapArray h, int n)
        {
            Spec.Requires(0 < n && Heap(h, n));
            Spec.Ensures((int r) => Heap(h, n) && r == Buf(h, n)[0] && Spec.Forall(0, n, j => r >= Buf(h, n)[j]));
            Spec.Ensures(Buf(h, n) == Spec.Old(Buf(h, n)) && Spec.Forall(0, n, j => Buf(h, n)[j] == Spec.Old(Buf(h, n)[j])));
            Spec.Unfold(Heap(h, n));
            int r = AtsBinHeap.Front(h.Data, n);
            Spec.Fold(Heap(h, n));
            return r;
        }

        /// <summary>heap_push: needs room (n &lt; m); the item is in the heap afterwards.</summary>
        public static void Push(HeapArray h, int n, int v)
        {
            Spec.Requires(Heap(h, n) && 0 <= n && n < Buf(h, n).Length);
            Spec.Ensures(Heap(h, n + 1) && Spec.Exists(0, n + 1, j => Buf(h, n + 1)[j] == v));
            Spec.Ensures(Buf(h, n + 1).Length == Spec.Old(Buf(h, n).Length));
            Spec.Unfold(Heap(h, n));
            AtsBinHeap.Push(h.Data, n, v);
            h.Count = n + 1;
            Spec.Fold(Heap(h, n + 1));
        }

        /// <summary>heap_pop: the largest item goes.</summary>
        public static int Pop(HeapArray h, int n)
        {
            Spec.Requires(0 < n && Heap(h, n));
            Spec.Ensures((int r) => Heap(h, n - 1) && r == Spec.Old(Buf(h, n)[0]));
            Spec.Ensures(Buf(h, n - 1).Length == Spec.Old(Buf(h, n).Length));
            Spec.Unfold(Heap(h, n));
            int r = AtsBinHeap.Pop(h.Data, n);
            h.Count = n - 1;
            Spec.Fold(Heap(h, n - 1));
            return r;
        }

        /// <summary>heap_resize: a new buffer of the given size (at least the count), the items copied in order.</summary>
        public static void Resize(HeapArray h, int n, int size)
        {
            Spec.Requires(n <= size && size <= MaxSize && Heap(h, n));
            Spec.Ensures(Heap(h, n) && Buf(h, n).Length == size && Spec.Forall(0, n, j => Buf(h, n)[j] == Spec.Old(Buf(h, n)[j])));
            Spec.Unfold(Heap(h, n));
            var old = h.Data;
            var fresh = new int[size];
            for (int j = 0; j < n; j++)
            {
                Spec.Invariant(0 <= j && j <= n && Spec.Forall(0, j, k => fresh[k] == old[k]));
                fresh[j] = old[j]; // array_copy
            }
            Spec.Assert(AtsBinHeap.IsHeap(fresh, n)); // (the same items, so the same order)
            h.Data = fresh;
            Spec.Fold(Heap(h, n));
        }

        /// <summary>heap_term: the heap is given up (ATS frees the buffer; here the collector does).</summary>
        public static void Term(HeapArray h, int n)
        {
            Spec.Requires(Heap(h, n));
            Spec.Unfold(Heap(h, n));
            h.Count = 0;
        }

        /// <summary>Size 2: push 3 and 9, full, resize to 4, push 4 and 7; the front is at least 7 and is what pops.</summary>
        public static bool Demo()
        {
            Spec.Ensures((bool r) => r);
            var h = Init(2);
            Push(h, 0, 3);
            Push(h, 1, 9);
            bool roomy = IsNotFull(h, 2);
            Resize(h, 2, 4);
            Push(h, 2, 4);
            Push(h, 3, 7);
            int front = Front(h, 4);
            int top = Pop(h, 4);
            Term(h, 3);
            return !roomy && top == front && front >= 7;
        }
    }
}
