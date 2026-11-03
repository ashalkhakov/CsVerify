using CsVerify;

namespace Samples
{
    // A port of tfc/src/DATS/queue_sllist2.dats (Hongwei Xi, "Effective ATS: Amortized Queue Implementation"):
    // a queue of n items is a front list and a reversed rear list, f + r = n; inserting conses onto the rear, and
    // taking out, when the front is empty, first reverses the rear into it. The dataviewtype becomes a predicate
    // over the queue object and its two list segments (ListSegments.cs).

    [Owned]
    public sealed class SQueue
    {
        public SNode? Front, Rear;
        public int F, R;

        public SQueue()
        {
            Spec.Ensures(Front == null && Rear == null && F == 0 && R == 0);
        }
    }

    public static class AtsQueue
    {
        /// <summary>queue(a, n) = QUEUE of (sllist(a, f), sllist(a, r)) with f + r = n.</summary>
        [Predicate]
        public static bool Queue(SQueue q, int n) =>
            q != null && Spec.Acc(q) && q.F >= 0 && q.R >= 0 && q.F + q.R == n &&
            ListSegments.Seg(q.Front, null, q.F) && ListSegments.Seg(q.Rear, null, q.R);

        /// <summary>queue_make_nil.</summary>
        public static SQueue MakeNil()
        {
            Spec.Ensures((SQueue r) => Queue(r, 0));
            var q = Own.New(new SQueue(), out var view);
            Own.ToAcc(view);
            Spec.Fold(ListSegments.Seg(q.Front, null, 0));
            Spec.Fold(ListSegments.Seg(q.Rear, null, 0));
            Spec.Fold(Queue(q, 0));
            return q;
        }

        /// <summary>queue_is_empty: both lists are nil.</summary>
        public static bool IsEmpty(SQueue q, int n)
        {
            Spec.Requires(Queue(q, n));
            Spec.Ensures((bool r) => r == (n == 0) && Queue(q, n));
            Spec.Unfold(Queue(q, n));
            Spec.Unfold(ListSegments.Seg(q.Front, null, q.F));
            Spec.Unfold(ListSegments.Seg(q.Rear, null, q.R));
            bool empty = q.Front == null && q.Rear == null;
            Spec.Fold(ListSegments.Seg(q.Front, null, q.F));
            Spec.Fold(ListSegments.Seg(q.Rear, null, q.R));
            Spec.Fold(Queue(q, n));
            return empty;
        }

        /// <summary>queue_insert_atend: cons onto the rear.</summary>
        public static void InsertAtEnd(SQueue q, int n, int x)
        {
            Spec.Requires(n < int.MaxValue && Queue(q, n));
            Spec.Ensures(Queue(q, n + 1));
            Spec.Unfold(Queue(q, n));
            q.Rear = ListSegments.Cons(x, q.Rear, q.R);
            q.R = q.R + 1;
            Spec.Fold(Queue(q, n + 1));
        }

        /// <summary>queue_takeout_atbeg: from the front, after moving the reversed rear there if it is empty.</summary>
        public static int TakeOutAtBeg(SQueue q, int n)
        {
            Spec.Requires(n > 0 && Queue(q, n));
            Spec.Ensures(Queue(q, n - 1));
            Spec.Unfold(Queue(q, n));
            if (q.Front == null)
            {
                Spec.Unfold(ListSegments.Seg(q.Front, null, q.F)); // the front is nil: everything is at the rear
                q.Front = ListSegments.Reverse(q.Rear, q.R);
                q.F = q.R;
                q.Rear = null;
                q.R = 0;
                Spec.Fold(ListSegments.Seg(q.Rear, null, 0));
            }
            Spec.Unfold(ListSegments.Seg(q.Front, null, q.F));
            var first = q.Front!;
            q.Front = first.Next;
            q.F = q.F - 1;
            Spec.Fold(Queue(q, n - 1));
            return first.Val;
        }

        /// <summary>Three in, three out (the third through the reversal): empty again.</summary>
        public static bool Demo()
        {
            Spec.Ensures((bool r) => r);
            var q = MakeNil();
            InsertAtEnd(q, 0, 1);
            InsertAtEnd(q, 1, 2);
            TakeOutAtBeg(q, 2);
            InsertAtEnd(q, 1, 3);
            TakeOutAtBeg(q, 2);
            TakeOutAtBeg(q, 1);
            return IsEmpty(q, 0);
        }
    }
}
