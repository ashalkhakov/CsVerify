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

    [Owned]
    public sealed class Vec
    {
        public int[] Data;
        public int Len;

        public Vec(int[] data)
        {
            Spec.Ensures(Data == data && Len == 0);
            Data = data;
        }
    }

    [Owned]
    public sealed class Rgn
    {
        public int[] Twin;

        public Rgn(int[] twin)
        {
            Spec.Ensures(Twin == twin);
            Twin = twin;
        }
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

        [GhostFunction]
        public static bool Heap(int[] a, int n)
        {
            Spec.Requires(0 <= n && n <= a.Length);
            return Spec.Forall(1, n, j => a[(j - 1) / 2] >= a[j]);
        }

        // BUG: binheap's pop, moving the smaller child up into the hole: the larger one ends up below it (CSV1006)
        public static int PopSmallerChild(int[] a, int n)
        {
            Spec.Requires(0 < n && n <= a.Length && a.Length < 0x3FFFFFFF && Spec.Acc(a) && Heap(a, n));
            Spec.Ensures((int r) => Spec.Acc(a));
            int top = a[0];
            int count = n - 1;
            int last = a[count];
            if (count == 0) return top;
            int hole = 0;
            while (true)
            {
                Spec.Invariant(0 <= hole && hole < count);
                Spec.Invariant(Spec.Forall(1, count, j => j != hole && (j - 1) / 2 != hole ? a[(j - 1) / 2] >= a[j] : true));
                Spec.Invariant(hole > 0 ? Spec.Forall(1, count, j => (j - 1) / 2 == hole ? a[(hole - 1) / 2] >= a[j] : true) : true);
                Spec.Decreases(count - hole);
                int swap = hole + hole + 1;
                if (swap >= count) break;
                int other = swap + 1;
                if (other < count && a[other] < a[swap]) swap = other;
                if (last >= a[swap]) break;
                a[hole] = a[swap];
                hole = swap;
            }
            a[hole] = last;
            return top;
        }

        [Predicate]
        public static bool Grows(Vec d, int n) =>
            d != null && Spec.Acc(d) && d.Data != null && d.Len == n && 0 <= n && n <= d.Data.Length && Spec.Acc(d.Data);

        [Pure]
        public static int[] Items(Vec d, int n)
        {
            Spec.Requires(Grows(d, n));
            Spec.Ensures((int[] r) => r != null && 0 <= n && n <= r.Length);
            Spec.Unfold(Grows(d, n));
            return d.Data;
        }

        // BUG: dynarray's recapacitize without the copy (frealloc's memcpy): the items are lost (CSV1002)
        public static void GrowWithoutCopy(Vec d, int n, int m1)
        {
            Spec.Requires(n < m1 && Grows(d, n));
            Spec.Ensures(Grows(d, n) && Spec.Forall(0, n, j => Items(d, n)[j] == Spec.Old(Items(d, n)[j])));
            Spec.Unfold(Grows(d, n));
            d.Data = new int[m1];
            Spec.Fold(Grows(d, n));
        }

        /// <summary>half-edge-mesh's region: every twin is a half-edge of it, or none.</summary>
        [Predicate]
        public static bool Region(Rgn r) =>
            r != null && Spec.Acc(r) && r.Twin != null && Spec.Acc(r.Twin) &&
            Spec.Forall(0, r.Twin.Length, h => -1 <= r.Twin[h] && r.Twin[h] < r.Twin.Length);

        // BUG: a twin one past the last half-edge, a dangling region pointer: the region cannot be folded (CSV1019)
        public static void DanglingTwin(Rgn r)
        {
            Spec.Requires(Region(r));
            Spec.Ensures(Region(r));
            Spec.Unfold(Region(r));
            if (r.Twin.Length > 0) r.Twin[0] = r.Twin.Length;
            Spec.Fold(Region(r));
        }

        /// <summary>strbuf_v: n non-NUL chars and a NUL after them.</summary>
        [Predicate]
        public static bool Cstr(char[] buf, int n) =>
            buf != null && 0 <= n && n < buf.Length && Spec.Acc(buf) && Spec.Forall(0, n, i => buf[i] != '\0') && buf[n] == '\0';

        // BUG: strbuf_set_char_at without its c1har (non-NUL) argument: a NUL inside cuts the string short, and its
        // length is no longer n (CSV1019)
        public static void SetAnyChar(char[] buf, int n, int i, char c)
        {
            Spec.Requires(0 <= i && i < n && Cstr(buf, n));
            Spec.Ensures(Cstr(buf, n));
            Spec.Unfold(Cstr(buf, n));
            buf[i] = c;
            Spec.Fold(Cstr(buf, n));
        }

        // BUG: slist_insert_before's aux, linking v in but not the rest of the list after it: the nodes after the
        // place are lost, and the list is one node short of n + 2 (CSV1016: their segment is not there to fold)
        public static void InsertDropsRest(Sn v, Sn hd, Sn? rest, int n)
        {
            Spec.Requires(n >= 0 && Spec.Acc(v) && Spec.Acc(hd) && hd.Next == rest && Sl(rest, null, n));
            Spec.Ensures(Sl(hd, null, n + 2));
            hd.Next = v;
            v.Next = null;
            Spec.Fold(Sl(v.Next, null, 0));
            Spec.Fold(Sl(v, null, 1));
            Spec.Fold(Sl(hd, null, n + 2));
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
