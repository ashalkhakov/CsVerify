using CsVerify;

namespace Samples
{
    // A port of ats-miscellanea/hacks/circlist.dats (Artyom Shalkhakov, 2011): a circular singly-linked list is a
    // head node and a segment from the head's successor back round to the head,
    //   cslist_v(n, l) = node @ l * slseg_v(n - 1, l.next, l),
    // over the list segments of ListSegments.cs. printcirc's walk, which frees the nodes as it prints them, counts
    // them here and lets their permissions go.
    public static class AtsCircList
    {
        /// <summary>cslist_v(a, n, l).</summary>
        [Predicate]
        public static bool CList(SNode? head, int n) =>
            n == 0 ? head == null
                   : n > 0 && head != null && Spec.Acc(head) && ListSegments.Seg(head.Next, head, n - 1);

        /// <summary>cslist_make_sing: a node pointing at itself.</summary>
        public static void MakeSingle(SNode node)
        {
            Spec.Requires(Spec.Acc(node));
            Spec.Ensures(CList(node, 1));
            node.Next = node;
            Spec.Fold(ListSegments.Seg(node.Next, node, 0));
            Spec.Fold(CList(node, 1));
        }

        /// <summary>cslist_insert_after: a free node goes right after the head.</summary>
        public static void InsertAfter(SNode head, int n, SNode node)
        {
            Spec.Requires(n > 0 && CList(head, n) && Spec.Acc(node));
            Spec.Ensures(CList(head, n + 1));
            Spec.Unfold(CList(head, n));
            node.Next = head.Next;
            head.Next = node;
            Spec.Fold(ListSegments.Seg(node, head, n));
            Spec.Fold(CList(head, n + 1));
        }

        /// <summary>
        /// printcirc: once round the list, from the head's successor until the head comes back. The nodes walked
        /// past are let go (ATS frees them); the head's permission stays in hand, so the segment left when the
        /// head comes round again is empty.
        /// </summary>
        public static int CountRound(SNode head, int n)
        {
            Spec.Requires(n > 0 && CList(head, n));
            Spec.Ensures((int r) => r == n);
            Spec.Unfold(CList(head, n));
            SNode? cur = head.Next;
            int k = 1;
            while (cur != head)
            {
                Spec.Invariant(1 <= k && k <= n && Spec.Acc(head) && ListSegments.Seg(cur, head, n - k));
                Spec.Unfold(ListSegments.Seg(cur, head, n - k));
                cur = cur!.Next;
                k++;
            }
            Spec.Unfold(ListSegments.Seg(cur, head, n - k)); // back at the head: nothing left, k is n
            return k;
        }

        private static SNode Node(int val)
        {
            Spec.Ensures((SNode r) => Spec.Acc(r));
            var node = Own.New(new SNode(val, null), out var view);
            Own.ToAcc(view);
            return node;
        }

        /// <summary>main: 10, then 15 after it, round once.</summary>
        public static int Demo()
        {
            Spec.Ensures((int r) => r == 2);
            var first = Node(10);
            MakeSingle(first);
            InsertAfter(first, 1, Node(15));
            return CountRound(first, 2);
        }
    }
}
