using System.Diagnostics;
using CsVerify;

namespace Samples
{
    // A port of libatsc's slist (Artyom Shalkhakov): an intrusive singly-linked list, slseg_v(a, n, la, lz) built of
    // node views, slist_v(a, n, l) = slseg_v(a, n, l, null). The template hooks ($work, $pred) are fixed functions
    // here, and the recursive aux functions stay recursive.
    //
    // slist_search_takeout duplicates the found node's view with a __trustme: the list keeps it and the caller gets
    // a@l as well. Here the takeout is honest: the list comes back split around the node (the segment before it, the
    // node, the rest), and the lemma Restore puts it back together.

    /// <summary>A user node: a key, and the next-pointer slist_node_get_next/set_next read and write.</summary>
    [Owned]
    public sealed class SlNode
    {
        public int Key;
        public SlNode? Next;

        public SlNode(int key)
        {
            Spec.Ensures(Key == key && Next == null);
            Key = key;
        }
    }

    public static class AtsSList
    {
        /// <summary>slseg_v(a, n, la, lz).</summary>
        [Predicate]
        public static bool Seg(SlNode? from, SlNode? to, int n) =>
            n == 0 ? from == to : n > 0 && from != null && Spec.Acc(from) && Seg(from.Next, to, n - 1);

        /// <summary>A segment, then a node: a segment one longer (slseg_v_cons, at the far end).</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void Extend(SlNode? from, SlNode last, int n)
        {
            Spec.Requires(n >= 0 && Seg(from, last, n) && Spec.Acc(last));
            Spec.Ensures(Seg(from, last.Next, n + 1));
            Spec.Decreases(n);
            Spec.Unfold(Seg(from, last, n));
            if (n == 0)
            {
                Spec.Fold(Seg(last.Next, last.Next, 0));
                Spec.Fold(Seg(from, last.Next, 1));
            }
            else
            {
                Extend(from!.Next, last, n - 1);
                Spec.Fold(Seg(from, last.Next, n + 1));
            }
        }

        /// <summary>Two segments end to end make one.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void Append(SlNode? a, SlNode? b, int n1, SlNode? c, int n2)
        {
            Spec.Requires(n1 >= 0 && n2 >= 0 && Seg(a, b, n1) && Seg(b, c, n2));
            Spec.Ensures(Seg(a, c, n1 + n2));
            Spec.Decreases(n1);
            Spec.Unfold(Seg(a, b, n1));
            if (n1 > 0)
            {
                Append(a!.Next, b, n1 - 1, c, n2);
                Spec.Fold(Seg(a, c, n1 + n2));
            }
        }

        /// <summary>The inverse of a takeout: the segment before the node, the node, the rest, as one list.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void Restore(SlNode? head, SlNode node, int k, int n)
        {
            Spec.Requires(0 <= k && k < n && Seg(head, node, k) && Spec.Acc(node) && Seg(node.Next, null, n - k - 1));
            Spec.Ensures(Seg(head, null, n));
            Spec.Fold(Seg(node, null, n - k));
            Append(head, node, k, null, n - k);
        }

        // ------------------------------------------------------------------------------------------ the list

        /// <summary>slist_cons: a node goes in front.</summary>
        public static SlNode Cons(SlNode v, SlNode? list, int n)
        {
            Spec.Requires(n >= 0 && Spec.Acc(v) && Seg(list, null, n));
            Spec.Ensures((SlNode r) => r == v && Seg(r, null, n + 1));
            v.Next = list;
            Spec.Fold(Seg(v, null, n + 1));
            return v;
        }

        /// <summary>slist_foreach, with $work adding one to each key.</summary>
        public static void Foreach(SlNode? p, int n)
        {
            Spec.Requires(n >= 0 && Seg(p, null, n));
            Spec.Ensures(Seg(p, null, n));
            Spec.Decreases(n);
            Spec.Unfold(Seg(p, null, n));
            if (p != null)
            {
                p.Key = unchecked(p.Key + 1); // ($work)
                Foreach(p.Next, n - 1);
                Spec.Fold(Seg(p, null, n));
            }
            else Spec.Fold(Seg(p, null, n));
        }

        /// <summary>slist_iforeach, with $work labelling each node with its index; returns how many there were.</summary>
        public static int Iforeach(SlNode? p, int i, int n)
        {
            Spec.Requires(n >= 0 && 0 <= i && i <= int.MaxValue - n && Seg(p, null, n));
            Spec.Ensures((int r) => r == i + n && Seg(p, null, n));
            Spec.Decreases(n);
            Spec.Unfold(Seg(p, null, n));
            if (p == null)
            {
                Spec.Fold(Seg(p, null, n));
                return i;
            }
            p.Key = i; // ($work)
            int r = Iforeach(p.Next, i + 1, n - 1);
            Spec.Fold(Seg(p, null, n));
            return r;
        }

        /// <summary>slist_all, with $pred "the key is positive".</summary>
        public static bool All(SlNode? p, int n)
        {
            Spec.Requires(n >= 0 && Seg(p, null, n));
            Spec.Ensures(Seg(p, null, n));
            Spec.Decreases(n);
            Spec.Unfold(Seg(p, null, n));
            if (p == null)
            {
                Spec.Fold(Seg(p, null, n));
                return true;
            }
            bool res = p.Key > 0 && All(p.Next, n - 1);
            Spec.Fold(Seg(p, null, n));
            return res;
        }

        /// <summary>
        /// slist_search_takeout, with $pred "the key is k": the k-th node of the list (counting from 0) is the first
        /// with that key, and comes out of the list: what the caller holds is the segment before it, the node and the
        /// rest. Or null, and the list as it was.
        /// </summary>
        public static (SlNode? node, int k) SearchTakeout(SlNode? head, int n, int key)
        {
            Spec.Requires(n >= 0 && Seg(head, null, n));
            Spec.Ensures<(SlNode? node, int k)>(t => t.node == null
                ? t.k == n && Seg(head, null, n)
                : 0 <= t.k && t.k < n && t.node.Key == key && Seg(head, t.node, t.k) && Spec.Acc(t.node) && Seg(t.node.Next, null, n - t.k - 1));
            SlNode? p = head;
            int k = 0;
            Spec.Fold(Seg(head, p, 0));
            while (p != null)
            {
                Spec.Invariant(0 <= k && k <= n && Seg(head, p, k) && Seg(p, null, n - k));
                Spec.Unfold(Seg(p, null, n - k));
                if (p.Key == key) return (p, k); // ($pred)
                var next = p.Next;
                Extend(head, p, k);
                p = next;
                k++;
            }
            Spec.Unfold(Seg(p, null, n - k)); // the end: k is n
            return (null, k);
        }

        /// <summary>
        /// slist_insert_before, with $pred "the key is at least v's": v goes before the first such node, or at the
        /// end. aux keeps the node before the place (pf_hd) in hand, as in ATS.
        /// </summary>
        public static SlNode InsertBefore(SlNode v, SlNode? head, int n)
        {
            Spec.Requires(n >= 0 && Spec.Acc(v) && Seg(head, null, n));
            Spec.Ensures((SlNode r) => Seg(r, null, n + 1));
            Spec.Unfold(Seg(head, null, n));
            if (head == null)
            {
                v.Next = null;
                Spec.Fold(Seg(v.Next, null, 0));
                Spec.Fold(Seg(v, null, 1));
                return v;
            }
            if (head.Key >= v.Key)
            {
                Spec.Fold(Seg(head, null, n));
                v.Next = head;
                Spec.Fold(Seg(v, null, n + 1));
                return v;
            }
            InsertAfter(v, head, head.Next, n - 1);
            return head;
        }

        /// <summary>insert_before's aux: hd (in hand) is before the place, rest is the list after it.</summary>
        private static void InsertAfter(SlNode v, SlNode hd, SlNode? rest, int n)
        {
            Spec.Requires(n >= 0 && Spec.Acc(v) && Spec.Acc(hd) && hd.Next == rest && Seg(rest, null, n));
            Spec.Ensures(Seg(hd, null, n + 2));
            Spec.Decreases(n);
            Spec.Unfold(Seg(rest, null, n));
            if (rest == null || rest.Key >= v.Key)
            {
                Spec.Fold(Seg(rest, null, n));
                hd.Next = v;
                v.Next = rest;
                Spec.Fold(Seg(v, null, n + 1));
                Spec.Fold(Seg(hd, null, n + 2));
                return;
            }
            InsertAfter(v, rest, rest.Next, n - 1);
            Spec.Fold(Seg(hd, null, n + 2));
        }

        // ------------------------------------------------------------------------------------------ test

        private static SlNode Node(int key)
        {
            Spec.Ensures((SlNode r) => Spec.Acc(r) && r.Key == key);
            var node = Own.New(new SlNode(key), out var view);
            Own.ToAcc(view);
            return node;
        }

        /// <summary>TEST/slist.dats: build 1, 3, 5; insert 4 in order; take a node out and put it back; count.</summary>
        public static int Demo()
        {
            Spec.Ensures((int r) => r == 4);
            SlNode? list = null;
            Spec.Fold(Seg(list, null, 0));
            list = Cons(Node(5), list, 0);
            list = Cons(Node(3), list, 1);
            list = Cons(Node(1), list, 2);
            list = InsertBefore(Node(4), list, 3);
            Foreach(list, 4);
            var (found, k) = SearchTakeout(list, 4, 4);
            if (found != null)
            {
                found.Key = 40; // the caller holds the node: it may write it
                Restore(list, found, k, 4);
            }
            bool positive = All(list, 4);
            return Iforeach(list, 0, 4);
        }
    }
}
