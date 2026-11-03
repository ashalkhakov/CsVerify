using System.Diagnostics;
using CsVerify;

namespace Samples
{
    // A port of ATS-playground/binheap.dats (Artyom Shalkhakov, after martinkunev's C heap): a binary max-heap in an
    // array, pushing by moving a hole up from the new leaf and popping by moving a hole down from the root. The ATS
    // version proves memory safety, taking the index arithmetic on trust (__trustme); here the cells are framed by
    // Spec.Acc, the arithmetic is checked, and the heap order itself is proved: push and pop keep it, and the root
    // is the maximum.
    public static class AtsBinHeap
    {
        /// <summary>Every node is at least its children: a[(j - 1) / 2] >= a[j] for 0 &lt; j &lt; n.</summary>
        [GhostFunction]
        public static bool IsHeap(int[] a, int n)
        {
            Spec.Requires(0 <= n && n <= a.Length);
            return Spec.Forall(1, n, j => a[(j - 1) / 2] >= a[j]);
        }

        /// <summary>The root is the largest: up the parents from any node.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void RootIsMax(int[] a, int n, int j)
        {
            Spec.Requires(0 <= j && j < n && n <= a.Length && IsHeap(a, n));
            Spec.Ensures(a[0] >= a[j]);
            Spec.Decreases(j);
            if (j > 0)
            {
                Spec.Assert(a[(j - 1) / 2] >= a[j]);
                RootIsMax(a, n, (j - 1) / 2);
            }
        }

        /// <summary>
        /// heap_push: the hole starts at the new leaf; while its parent is smaller than v, the parent moves down
        /// into it and the hole moves up. Around the hole the order is suspended: its children are at most v and
        /// at most its parent.
        /// </summary>
        public static void Push(int[] a, int n, int v)
        {
            Spec.Requires(0 <= n && n < a.Length && Spec.Acc(a) && IsHeap(a, n));
            Spec.Ensures(Spec.Acc(a) && IsHeap(a, n + 1) && Spec.Exists(0, n + 1, j => a[j] == v));
            Spec.Ensures(Spec.Forall(n + 1, a.Length, j => a[j] == Spec.Old(a[j])));
            int hole = n;
            while (hole > 0 && a[(hole - 1) / 2] < v)
            {
                Spec.Invariant(0 <= hole && hole <= n);
                Spec.Invariant(Spec.Forall(1, n + 1, j => j != hole && (j - 1) / 2 != hole ? a[(j - 1) / 2] >= a[j] : true));
                Spec.Invariant(Spec.Forall(1, n + 1, j => (j - 1) / 2 == hole ? a[j] <= v : true));
                Spec.Invariant(hole > 0 ? Spec.Forall(1, n + 1, j => (j - 1) / 2 == hole ? a[(hole - 1) / 2] >= a[j] : true) : true);
                Spec.Invariant(Spec.Forall(n + 1, a.Length, j => a[j] == Spec.Old(a[j])));
                Spec.Decreases(hole);
                int parent = (hole - 1) / 2;
                a[hole] = a[parent];
                hole = parent;
            }
            a[hole] = v;
        }

        /// <summary>
        /// heap_pop: the root goes, the last item is lifted out, and the hole moves down from the root, the larger
        /// child moving up into it, until the last item fits.
        /// </summary>
        public static int Pop(int[] a, int n)
        {
            Spec.Requires(0 < n && n <= a.Length && a.Length < 0x3FFFFFFF && Spec.Acc(a) && IsHeap(a, n));
            Spec.Ensures((int r) => Spec.Acc(a) && IsHeap(a, n - 1) && r == Spec.Old(a[0]));
            int top = a[0];
            int count = n - 1;
            int last = a[count];
            if (count == 0) return top;
            int hole = 0;
            while (true)
            {
                Spec.Invariant(0 <= hole && hole < count);
                Spec.Invariant(Spec.Forall(1, count, j => j != hole && (j - 1) / 2 != hole ? a[(j - 1) / 2] >= a[j] : true));
                Spec.Invariant(hole > 0 ? a[(hole - 1) / 2] >= last : true);
                Spec.Invariant(hole > 0 ? Spec.Forall(1, count, j => (j - 1) / 2 == hole ? a[(hole - 1) / 2] >= a[j] : true) : true);
                Spec.Decreases(count - hole);
                int swap = hole + hole + 1;
                if (swap >= count) break;                            // no children: it fits here
                int other = swap + 1;
                if (other < count && a[other] > a[swap]) swap = other; // the larger child
                if (last >= a[swap]) break;                          // at least its children: it fits here
                a[hole] = a[swap];
                hole = swap;
            }
            a[hole] = last;
            return top;
        }

        /// <summary>heap_front: the largest item.</summary>
        public static int Front(int[] a, int n)
        {
            Spec.Requires(0 < n && n <= a.Length && IsHeap(a, n));
            Spec.Ensures((int r) => r == a[0] && Spec.Forall(0, n, j => r >= a[j]));
            int top = a[0];
            for (int j = 0; j < n; j++)
            {
                Spec.Invariant(0 <= j && j <= n && Spec.Forall(0, j, i => top >= a[i]));
                RootIsMax(a, n, j);
            }
            return top;
        }

        /// <summary>Four pushes: the front is at least the last one pushed; a pop leaves a heap of three.</summary>
        public static bool Demo()
        {
            Spec.Ensures((bool r) => r);
            var a = new int[8];
            Spec.Assert(IsHeap(a, 0));
            Push(a, 0, 3);
            Push(a, 1, 9);
            Push(a, 2, 4);
            Push(a, 3, 7);
            int front = Front(a, 4);
            int top = Pop(a, 4);
            Spec.Assert(IsHeap(a, 3));
            return front >= 7 && top == front;
        }
    }
}
