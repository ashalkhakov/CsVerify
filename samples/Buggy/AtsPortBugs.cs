using CsVerify;

namespace Samples.Buggy
{
    // Mistakes in the style of the ATS ports (Good/AtsDlSeg.cs, AtsCircList.cs, AtsQueue.cs), with small copies
    // of their views.

    [Owned]
    public sealed class Dn
    {
        public int Item;
        public Dn? Prev, Next;
    }

    [Owned]
    public sealed class Sn
    {
        public int Item;
        public Sn? Next;
    }

    public static class AtsPortBugs
    {
        [Predicate]
        public static bool Dl(Dn? first, Dn? prev, Dn? next, Dn? last, int n) =>
            n == 0 ? first == next && prev == last
                   : n > 0 && last != null && first != null && Spec.Acc(first) && first.Prev == prev && Dl(first.Next, first, next, last, n - 1);

        [Predicate]
        public static bool Sl(Sn? from, Sn? to, int n) =>
            n == 0 ? from == to : n > 0 && from != null && Spec.Acc(from) && Sl(from.Next, to, n - 1);

        /// <summary>cslist_v: a head and the segment back round to it.</summary>
        [Predicate]
        public static bool Circ(Sn? head, int n) =>
            n == 0 ? head == null : n > 0 && head != null && Spec.Acc(head) && Sl(head.Next, head, n - 1);

        // BUG: links the first list's last node forward to the second's head, but not the head back, so the
        // second segment cannot be seen as following it (first.Prev == prev fails: CSV1019)
        public static void ConcatOneWay(Dn t1, Dn h2, Dn? t2, int n2)
        {
            Spec.Requires(n2 > 0 && Spec.Acc(t1) && Dl(h2, null, null, t2, n2));
            Spec.Unfold(Dl(h2, null, null, t2, n2));
            t1.Next = h2;
            Spec.Fold(Dl(h2, t1, null, t2, n2));
        }

        public static void Uncons(ref Dn? head, ref Dn? tail, int n)
        {
            Spec.Requires(n > 0 && Dl(head, null, null, tail, n));
        }

        // BUG: takes the first node of an empty list (CSV1001)
        public static void UnconsEmpty()
        {
            Dn? h = null, t = null;
            Spec.Fold(Dl(h, null, null, t, 0));
            Uncons(ref h, ref t, 0);
        }

        public static void InsertAfter(Sn head, int n, Sn node)
        {
            Spec.Requires(n > 0 && Circ(head, n) && Spec.Acc(node));
            Spec.Ensures(Circ(head, n + 1));
            Spec.Unfold(Circ(head, n));
            node.Next = head.Next;
            head.Next = node;
            Spec.Fold(Sl(node, head, n));
            Spec.Fold(Circ(head, n + 1));
        }

        // BUG: inserts the same node twice: its permission went into the list the first time (CSV1016)
        public static void InsertTwice(Sn head, int n, Sn node)
        {
            Spec.Requires(n > 0 && n < 1000 && Circ(head, n) && Spec.Acc(node));
            InsertAfter(head, n, node);
            InsertAfter(head, n + 1, node);
        }
    }
}
