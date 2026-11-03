using System.Diagnostics;
using CsVerify;

namespace Samples
{
    // ATS's singly-linked list segments (slseg_v, from "Programming with Views and Viewtypes") as a predicate over
    // permissions, Viper style: Seg(from, to, n) holds the n nodes from 'from' up to (not including) 'to'. Its
    // footprint is folded into it; Spec.Unfold takes one node out, Spec.Fold puts it back.

    /// <summary>A list node. Its Next is a plain reference: the predicate, not the node, says what it owns.</summary>
    [Owned]
    public sealed class SNode
    {
        public int Val;
        public SNode? Next;

        public SNode(int val, SNode? next)
        {
            Spec.Ensures(Val == val && Next == next);
            Val = val;
            Next = next;
        }
    }

    public static class ListSegments
    {
        /// <summary>slseg_v(from, to, n): empty if n is 0 (and from is to), else a node and the segment after it.</summary>
        [Predicate]
        public static bool Seg(SNode? from, SNode? to, int n) =>
            n == 0 ? from == to : n > 0 && from != null && Spec.Acc(from) && Seg(from.Next, to, n - 1);

        /// <summary>The sum of a segment's values (a ghost function over the predicate: it reads only its footprint).</summary>
        [GhostFunction]
        public static int Sum(SNode? from, SNode? to, int n)
        {
            Spec.Requires(n >= 0 && Seg(from, to, n));
            Spec.Decreases(n);
            Spec.Unfold(Seg(from, to, n));
            return n == 0 ? 0 : from!.Val + Sum(from.Next, to, n - 1);
        }

        /// <summary>A segment ending at a node, and the node: a segment one longer (ATS: slseg_v_extend).</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void Extend(SNode? from, SNode last, int n)
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

        /// <summary>A new node in front of a list.</summary>
        public static SNode Cons(int val, SNode? list, int n)
        {
            Spec.Requires(n >= 0 && n < int.MaxValue && Seg(list, null, n));
            Spec.Ensures((SNode r) => Seg(r, null, n + 1));
            var node = Own.New(new SNode(val, list), out var view);
            Own.ToAcc(view); // the view's permission, for the predicate
            Spec.Fold(Seg(node, null, n + 1));
            return node;
        }

        /// <summary>A list's length, walking it: the part walked is a segment from the head to the cursor.</summary>
        public static int Length(SNode? list, int n)
        {
            Spec.Requires(n >= 0 && Seg(list, null, n));
            Spec.Ensures((int r) => r == n && Seg(list, null, n));
            SNode? cur = list;
            int k = 0;
            Spec.Fold(Seg(list, list, 0));
            while (cur != null)
            {
                Spec.Invariant(0 <= k && k <= n && Seg(list, cur, k) && Seg(cur, null, n - k));
                Spec.Unfold(Seg(cur, null, n - k));
                Extend(list, cur, k);
                cur = cur.Next;
                k++;
            }
            Spec.Unfold(Seg(cur, null, n - k)); // the rest is empty (k is n), and the walked part, up to null, is the list
            return k;
        }

        /// <summary>Reverses a list in place: the reversed part and the rest are two segments ending at null.</summary>
        public static SNode? Reverse(SNode? list, int n)
        {
            Spec.Requires(n >= 0 && Seg(list, null, n));
            Spec.Ensures((SNode? r) => Seg(r, null, n));
            SNode? done = null;
            SNode? rest = list;
            int k = 0;
            Spec.Fold(Seg(done, null, 0));
            while (rest != null)
            {
                Spec.Invariant(0 <= k && k <= n && Seg(done, null, k) && Seg(rest, null, n - k));
                Spec.Unfold(Seg(rest, null, n - k));
                var next = rest.Next;
                rest.Next = done;
                Spec.Fold(Seg(rest, null, k + 1));
                done = rest;
                rest = next;
                k++;
            }
            Spec.Unfold(Seg(rest, null, n - k));
            return done;
        }

        /// <summary>Adds one to the head's value: the sum goes up by one.</summary>
        public static void BumpHead(SNode? list, int n)
        {
            Spec.Requires(n > 0 && Seg(list, null, n));
            Spec.Ensures(Seg(list, null, n) && Sum(list, null, n) == Spec.Old(Sum(list, null, n)) + 1);
            Spec.Unfold(Seg(list, null, n));
            list!.Val = checked(list.Val + 1);
            Spec.Fold(Seg(list, null, n));
        }

        /// <summary>Two lists: reversing one leaves the other's sum as it was (the frame rule, through the footprints).</summary>
        public static SNode? ReverseOther(SNode? keep, int n, SNode? other, int m)
        {
            Spec.Requires(n >= 0 && m >= 0 && Seg(keep, null, n) && Seg(other, null, m));
            Spec.Ensures((SNode? r) => Seg(keep, null, n) && Seg(r, null, m) && Sum(keep, null, n) == Spec.Old(Sum(keep, null, n)));
            return Reverse(other, m);
        }

        public static int Demo()
        {
            Spec.Ensures((int r) => r == 3);
            SNode? list = null;
            Spec.Fold(Seg(list, null, 0));
            list = Cons(1, list, 0);
            list = Cons(2, list, 1);
            list = Cons(3, list, 2);
            list = Reverse(list, 3);
            return Length(list, 3);
        }
    }
}
