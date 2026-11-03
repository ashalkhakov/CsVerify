using System.Diagnostics;
using CsVerify;

namespace Samples
{
    // A port of ats-miscellanea/dlseg (Artyom Shalkhakov, 2010, after Hongwei Xi's 2004 code): doubly-linked list
    // segments, with a forward view (dlseg_v, peeled from the front) and a backward one (rdlseg_v, peeled from the
    // back). The dataviews are predicates, the proof functions recursive lemmas, and the list functions keep their
    // shapes: the head and tail pointers are ref parameters, the views are in the contracts.

    /// <summary>dlnode(a, prev, next): a node of a doubly-linked list.</summary>
    [Owned]
    public sealed class DlNode
    {
        public int Item;
        public DlNode? Prev;
        public DlNode? Next;

        public DlNode(int item)
        {
            Spec.Ensures(Item == item && Prev == null && Next == null);
            Item = item;
        }
    }

    public static class AtsDlSeg
    {
        // ------------------------------------------------------------------------------------------ views

        /// <summary>
        /// dlseg_v(first, prev, next, last, n): n nodes from first to last; first's Prev is prev, last's Next is
        /// next. Empty: first is next, and prev is last.
        /// </summary>
        [Predicate]
        public static bool DlSeg(DlNode? first, DlNode? prev, DlNode? next, DlNode? last, int n) =>
            n == 0 ? first == next && prev == last
                   : n > 0 && last != null && first != null && Spec.Acc(first) && first.Prev == prev &&
                     DlSeg(first.Next, first, next, last, n - 1);

        /// <summary>rdlseg_v: the same segment, seen from its last node.</summary>
        [Predicate]
        public static bool RDlSeg(DlNode? first, DlNode? prev, DlNode? next, DlNode? last, int n) =>
            n == 0 ? first == next && prev == last
                   : n > 0 && last != null && Spec.Acc(last) && last.Next == next &&
                     RDlSeg(first, prev, last, last.Prev, n - 1);

        // ------------------------------------------------------------------------------------------ proofs

        /// <summary>dlseg_v_append: two forward segments that point at each other make one.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void DlSegAppend(DlNode? f1, DlNode? p, DlNode? f2, DlNode? l1, int n1, DlNode? nx, DlNode? l2, int n2)
        {
            Spec.Requires(n1 >= 0 && n2 >= 0 && l2 != null && DlSeg(f1, p, f2, l1, n1) && DlSeg(f2, l1, nx, l2, n2));
            Spec.Ensures(DlSeg(f1, p, nx, l2, n1 + n2));
            Spec.Decreases(n1);
            Spec.Unfold(DlSeg(f1, p, f2, l1, n1));
            if (n1 > 0)
            {
                DlSegAppend(f1!.Next, f1, f2, l1, n1 - 1, nx, l2, n2);
                Spec.Fold(DlSeg(f1, p, nx, l2, n1 + n2));
            }
        }

        /// <summary>rdlseg_v_append: the same for backward segments, by induction on the second.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void RDlSegAppend(DlNode? f1, DlNode? pL, DlNode? f2, DlNode? l1, int n1, DlNode? nL, DlNode? l2, int n2)
        {
            Spec.Requires(n1 >= 0 && n2 >= 0 && RDlSeg(f1, pL, f2, l1, n1) && RDlSeg(f2, l1, nL, l2, n2));
            Spec.Ensures(RDlSeg(f1, pL, nL, l2, n1 + n2));
            Spec.Decreases(n2);
            Spec.Unfold(RDlSeg(f2, l1, nL, l2, n2));
            if (n2 > 0)
            {
                RDlSegAppend(f1, pL, f2, l1, n1, l2, l2!.Prev, n2 - 1);
                Spec.Fold(RDlSeg(f1, pL, nL, l2, n1 + n2));
            }
        }

        /// <summary>rdlseg_v_of_dlseg_v: a forward view gives the backward view of the same segment.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void BackwardOf(DlNode? first, DlNode? prev, DlNode? next, DlNode? last, int n)
        {
            Spec.Requires(n >= 0 && DlSeg(first, prev, next, last, n));
            Spec.Ensures(RDlSeg(first, prev, next, last, n));
            Spec.Decreases(n);
            Spec.Unfold(DlSeg(first, prev, next, last, n));
            if (n == 0)
            {
                Spec.Fold(RDlSeg(first, prev, next, last, 0));
                return;
            }
            var rest = first!.Next;
            BackwardOf(rest, first, next, last, n - 1);
            // the first node alone, seen from its end: rdlseg_v_some(rdlseg_v_none(), node)
            Spec.Fold(RDlSeg(first, prev, first, first.Prev, 0));
            Spec.Fold(RDlSeg(first, prev, rest, first, 1));
            RDlSegAppend(first, prev, rest, first, 1, next, last, n - 1);
        }

        /// <summary>dlseg_v_of_rdlseg_v: and back.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void ForwardOf(DlNode? first, DlNode? prev, DlNode? next, DlNode? last, int n)
        {
            Spec.Requires(n >= 0 && RDlSeg(first, prev, next, last, n));
            Spec.Ensures(DlSeg(first, prev, next, last, n));
            Spec.Decreases(n);
            Spec.Unfold(RDlSeg(first, prev, next, last, n));
            if (n == 0)
            {
                Spec.Fold(DlSeg(first, prev, next, last, 0));
                return;
            }
            var before = last!.Prev;
            ForwardOf(first, prev, last, before, n - 1);
            // the last node alone: dlseg_v_some(node, dlseg_v_none())
            Spec.Fold(DlSeg(last.Next, last, last.Next, last, 0));
            Spec.Fold(DlSeg(last, before, next, last, 1));
            DlSegAppend(first, prev, last, before, n - 1, next, last, 1);
        }

        // ------------------------------------------------------------------------------------------ lists
        // dllst_v(h, t, n) = dlseg_v(h, null, null, t, n); rdllst_v likewise.

        /// <summary>dllst_cons: a free node goes in front.</summary>
        public static void Cons(ref DlNode? head, ref DlNode? tail, int n, DlNode e)
        {
            Spec.Requires(n >= 0 && DlSeg(head, null, null, tail, n) && Spec.Acc(e));
            Spec.Ensures(DlSeg(head, null, null, tail, n + 1) && head == e);
            Spec.Unfold(DlSeg(head, null, null, tail, n));
            if (head == null)
            {
                e.Next = null;
                e.Prev = null;
                tail = e;
                Spec.Fold(DlSeg(e.Next, e, null, e, 0));
            }
            else
            {
                e.Next = head;
                e.Prev = null;
                head.Prev = e;
                Spec.Fold(DlSeg(head, e, null, tail, n));
            }
            Spec.Fold(DlSeg(e, null, null, tail, n + 1));
            head = e;
        }

        /// <summary>dllst_uncons: the first node comes out, free.</summary>
        public static DlNode Uncons(ref DlNode? head, ref DlNode? tail, int n)
        {
            Spec.Requires(n > 0 && DlSeg(head, null, null, tail, n));
            Spec.Ensures(DlSeg(head, null, null, tail, n - 1) && Spec.Acc(Spec.Result<DlNode>()) && Spec.Result<DlNode>() == Spec.Old(head));
            Spec.Unfold(DlSeg(head, null, null, tail, n));
            var first = head!;
            var next = first.Next;
            Spec.Unfold(DlSeg(next, first, null, tail, n - 1));
            if (next == null)
            {
                head = null;
                tail = null;
                Spec.Fold(DlSeg(head, null, null, tail, 0));
            }
            else
            {
                next.Prev = null;
                head = next;
                Spec.Fold(DlSeg(head, null, null, tail, n - 1));
            }
            return first;
        }

        /// <summary>dllst_snoc: a free node goes at the end (through the backward view).</summary>
        public static void Snoc(ref DlNode? head, ref DlNode? tail, int n, DlNode e)
        {
            Spec.Requires(n >= 0 && RDlSeg(head, null, null, tail, n) && Spec.Acc(e));
            Spec.Ensures(RDlSeg(head, null, null, tail, n + 1) && tail == e);
            Spec.Unfold(RDlSeg(head, null, null, tail, n));
            if (tail == null)
            {
                e.Prev = null;
                e.Next = null;
                head = e;
                Spec.Fold(RDlSeg(e, null, e, e.Prev, 0));
            }
            else
            {
                e.Prev = tail;
                e.Next = null;
                tail.Next = e;
                Spec.Fold(RDlSeg(head, null, e, tail, n));
            }
            Spec.Fold(RDlSeg(head, null, null, e, n + 1));
            tail = e;
        }

        /// <summary>dllst_length, walking forward: the part walked is a segment from the head up to the cursor.</summary>
        public static int Length(DlNode? head, DlNode? tail, int n)
        {
            Spec.Requires(n >= 0 && DlSeg(head, null, null, tail, n));
            Spec.Ensures((int r) => r == n && DlSeg(head, null, null, tail, n));
            DlNode? cur = head, before = null;
            int k = 0;
            Spec.Fold(DlSeg(head, null, cur, before, 0));
            while (cur != null)
            {
                Spec.Invariant(0 <= k && k <= n && DlSeg(head, null, cur, before, k) && DlSeg(cur, before, null, tail, n - k));
                Spec.Unfold(DlSeg(cur, before, null, tail, n - k));
                var next = cur.Next;
                Spec.Fold(DlSeg(next, cur, next, cur, 0));
                Spec.Fold(DlSeg(cur, before, next, cur, 1));
                DlSegAppend(head, null, cur, before, k, next, cur, 1);
                before = cur;
                cur = next;
                k++;
            }
            Spec.Unfold(DlSeg(cur, before, null, tail, n - k)); // empty: k is n, and the cursor's left is the tail
            return k;
        }

        /// <summary>
        /// dllst_concat: the first list's last node (reached through its backward view) and the second's first
        /// node are linked, and the two segments appended.
        /// </summary>
        public static void Concat(ref DlNode? h1, ref DlNode? t1, int n1, DlNode? h2, DlNode? t2, int n2)
        {
            Spec.Requires(n1 >= 0 && n2 >= 0 && DlSeg(h1, null, null, t1, n1) && DlSeg(h2, null, null, t2, n2));
            Spec.Ensures(DlSeg(h1, null, null, t1, n1 + n2));
            if (h1 == null)
            {
                Spec.Unfold(DlSeg(h1, null, null, t1, n1));
                h1 = h2;
                t1 = t2;
                return;
            }
            if (h2 == null)
            {
                Spec.Unfold(DlSeg(h2, null, null, t2, n2));
                return;
            }
            BackwardOf(h1, null, null, t1, n1);
            Spec.Unfold(RDlSeg(h1, null, null, t1, n1));
            Spec.Unfold(DlSeg(h2, null, null, t2, n2));
            var last = t1!;
            last.Next = h2;
            h2.Prev = last;
            Spec.Fold(RDlSeg(h1, null, h2, last, n1));
            ForwardOf(h1, null, h2, last, n1);
            Spec.Fold(DlSeg(h2, last, null, t2, n2));
            DlSegAppend(h1, null, h2, last, n1, null, t2, n2);
            t1 = t2;
        }

        // ------------------------------------------------------------------------------------------ zipper
        // dllst_v_zipper(lh, lf, lt, n1, n2): a focused node (the cursor), the n1 nodes before it as a backward
        // segment, the n2 after it as a forward one.

        [Predicate]
        public static bool Zipper(DlNode? head, DlNode? cursor, DlNode? tail, int n1, int n2) =>
            cursor != null && Spec.Acc(cursor) &&
            RDlSeg(head, null, cursor, cursor.Prev, n1) && DlSeg(cursor.Next, cursor, null, tail, n2);

        /// <summary>dlzipper_make_first: the cursor on the first node.</summary>
        public static void ZipFirst(DlNode? head, DlNode? tail, int n)
        {
            Spec.Requires(n > 0 && DlSeg(head, null, null, tail, n));
            Spec.Ensures(Zipper(head, head, tail, 0, n - 1));
            Spec.Unfold(DlSeg(head, null, null, tail, n));
            Spec.Fold(RDlSeg(head, null, head, head!.Prev, 0));
            Spec.Fold(Zipper(head, head, tail, 0, n - 1));
        }

        /// <summary>dlzipper_move_right.</summary>
        public static void MoveRight(DlNode? head, ref DlNode cursor, DlNode? tail, int n1, int n2)
        {
            Spec.Requires(n1 >= 0 && n2 > 0 && Zipper(head, cursor, tail, n1, n2));
            Spec.Ensures(Zipper(head, cursor, tail, n1 + 1, n2 - 1) && cursor.Prev == Spec.Old(cursor));
            Spec.Unfold(Zipper(head, cursor, tail, n1, n2));
            var next = cursor.Next!;
            Spec.Unfold(DlSeg(next, cursor, null, tail, n2));
            Spec.Fold(RDlSeg(head, null, next, cursor, n1 + 1));
            Spec.Fold(Zipper(head, next, tail, n1 + 1, n2 - 1));
            cursor = next;
        }

        /// <summary>dlzipper_move_left.</summary>
        public static void MoveLeft(DlNode? head, ref DlNode cursor, DlNode? tail, int n1, int n2)
        {
            Spec.Requires(n1 > 0 && n2 >= 0 && n2 < int.MaxValue && Zipper(head, cursor, tail, n1, n2));
            Spec.Ensures(Zipper(head, cursor, tail, n1 - 1, n2 + 1));
            Spec.Unfold(Zipper(head, cursor, tail, n1, n2));
            var prev = cursor.Prev!;
            Spec.Unfold(RDlSeg(head, null, cursor, prev, n1));
            Spec.Unfold(DlSeg(cursor.Next, cursor, null, tail, n2)); // (to see the tail is a node)
            Spec.Fold(DlSeg(cursor.Next, cursor, null, tail, n2));
            Spec.Fold(DlSeg(cursor, prev, null, tail, n2 + 1));
            Spec.Fold(Zipper(head, prev, tail, n1 - 1, n2 + 1));
            cursor = prev;
        }

        /// <summary>dlzipper_takeout, to write: the item under the cursor.</summary>
        public static void SetFocus(DlNode? head, DlNode cursor, DlNode? tail, int n1, int n2, int item)
        {
            Spec.Requires(Zipper(head, cursor, tail, n1, n2));
            Spec.Ensures(Zipper(head, cursor, tail, n1, n2) && cursor.Item == item);
            Spec.Unfold(Zipper(head, cursor, tail, n1, n2));
            cursor.Item = item;
            Spec.Fold(Zipper(head, cursor, tail, n1, n2));
        }

        /// <summary>dllst_v_of_zipper_v: the whole list again.</summary>
        public static void Unzip(DlNode? head, DlNode cursor, DlNode? tail, int n1, int n2)
        {
            Spec.Requires(n1 >= 0 && n2 >= 0 && n2 < int.MaxValue && Zipper(head, cursor, tail, n1, n2));
            Spec.Ensures(DlSeg(head, null, null, tail, n1 + n2 + 1));
            Spec.Unfold(Zipper(head, cursor, tail, n1, n2));
            var before = cursor.Prev;
            ForwardOf(head, null, cursor, before, n1);
            Spec.Unfold(DlSeg(cursor.Next, cursor, null, tail, n2)); // (to see the tail is a node)
            Spec.Fold(DlSeg(cursor.Next, cursor, null, tail, n2));
            Spec.Fold(DlSeg(cursor, before, null, tail, n2 + 1));
            DlSegAppend(head, null, cursor, before, n1, null, tail, n2 + 1);
        }

        // ------------------------------------------------------------------------------------------ test

        private static DlNode Fresh(int item)
        {
            Spec.Ensures((DlNode r) => Spec.Acc(r));
            var node = Own.New(new DlNode(item), out var view);
            Own.ToAcc(view);
            return node;
        }

        /// <summary>A zipper walk: to the third node, write it, one back, and the list again.</summary>
        public static int ZipperDemo()
        {
            Spec.Ensures((int r) => r == 3);
            DlNode? h = null, t = null;
            Spec.Fold(DlSeg(h, null, null, t, 0));
            Cons(ref h, ref t, 0, Fresh(3));
            Cons(ref h, ref t, 1, Fresh(2));
            Cons(ref h, ref t, 2, Fresh(1));
            ZipFirst(h, t, 3);
            DlNode c = h!;
            MoveRight(h, ref c, t, 0, 2);
            MoveRight(h, ref c, t, 1, 1);
            SetFocus(h, c, t, 2, 0, 30);
            MoveLeft(h, ref c, t, 2, 0);
            Unzip(h, c, t, 1, 1);
            return Length(h, t, 3);
        }

        /// <summary>dlseg_test: build [3, 1, 2] and [4], concatenate, take the first off, count.</summary>
        public static int Demo()
        {
            Spec.Ensures((int r) => r == 3);
            DlNode? h = null, t = null; // dllst_make_empty
            Spec.Fold(DlSeg(h, null, null, t, 0));
            Cons(ref h, ref t, 0, Fresh(1));
            Cons(ref h, ref t, 1, Fresh(3));
            BackwardOf(h, null, null, t, 2);
            Snoc(ref h, ref t, 2, Fresh(2));
            ForwardOf(h, null, null, t, 3);
            DlNode? h2 = null, t2 = null;
            Spec.Fold(DlSeg(h2, null, null, t2, 0));
            Cons(ref h2, ref t2, 0, Fresh(4));
            Concat(ref h, ref t, 3, h2, t2, 1);
            var first = Uncons(ref h, ref t, 4);
            return Length(h, t, 3);
        }
    }
}
