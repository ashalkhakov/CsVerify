using CsVerify;

namespace Samples
{
    /// <summary>
    /// A sorted linked list whose nodes own the rest of the list (ATS-style nested views, an ownership tree). Each
    /// node's invariant reads only itself and the node it owns, which no one can change while it is owned: the
    /// list is sorted because every node is. The ghost Len is the list's length (ATS's index of the list type),
    /// which also measures the recursion.
    /// </summary>
    [Owned]
    public sealed class SortedNode
    {
        public int Val;
        [Owns] public SortedNode? Next;
        public Ghost<int> Len;

        [Invariant, GhostFunction]
        public bool Valid() =>
            Len.Value >= 1 && (Next == null ? Len.Value == 1 : Len.Value == Next.Len.Value + 1) && (Next == null || Val <= Next.Val);

        public SortedNode(int v)
        {
            Spec.Ensures(Val == v && Next == null && Len.Value == 1);
            Val = v;
            Len = Ghost.Of(1);
        }

        /// <summary>Inserts <paramref name="v"/> after this node, keeping the list sorted (unfold, insert, fold).</summary>
        public void InsertAfter(int v)
        {
            Spec.Requires(Val <= v);
            Spec.Decreases(Len.Value);
            Spec.Ensures(Val == Spec.Old(Val) && Len.Value == Spec.Old(Len.Value) + 1);
            if (Next == null)
            {
                var n = Own.New(new SortedNode(v), out var nv);
                Own.Give(ref Next, n, nv);
            }
            else if (v <= Next.Val)
            {
                var rest = Own.Take(ref Next, out var rv);
                var n = Own.New(new SortedNode(v), out var nv);
                Own.Give(ref n.Next, rest, rv);
                n.Len = Ghost.Of(rest.Len.Value + 1);
                Own.Give(ref Next, n, nv);
            }
            else
            {
                var next = Own.Take(ref Next, out var xv);
                next.InsertAfter(v);
                Own.Give(ref Next, next, xv);
            }
            Len = Ghost.Of(Len.Value + 1);
        }

        /// <summary>The values in order, last digit first: a run-time check of what was built.</summary>
        public int Digits()
        {
            Spec.Decreases(Len.Value);
            Spec.Ensures(Val == Spec.Old(Val) && Len.Value == Spec.Old(Len.Value));
            if (Next == null) return Val;
            var next = Own.Take(ref Next, out var nv);
            int rest = next.Digits();
            Own.Give(ref Next, next, nv);
            return Val + 10 * rest;
        }
    }

    public static class OwnedList
    {
        /// <summary>Two lists: inserting into one leaves the other's whole tree as it was.</summary>
        public static void Independent(SortedNode a, ref Own<SortedNode> av, SortedNode b, ref Own<SortedNode> bv)
        {
            Spec.Requires(av.Obj.Value == a && bv.Obj.Value == b && a.Val <= 10);
            var bLen = Ghost.Of(b.Len.Value);
            var bNext = b.Next;
            a.InsertAfter(10);
            Spec.Assert(b.Len.Value == bLen.Value && b.Next == bNext);
        }

        public static int Demo()
        {
            var head = Own.New(new SortedNode(1), out var hv);
            head.InsertAfter(5);
            head.InsertAfter(3);
            head.InsertAfter(4);
            Spec.Assert(head.Val == 1 && head.Len.Value == 4);
            int digits = head.Digits();
            Own.Drop(hv);
            return digits;
        }
    }
}
