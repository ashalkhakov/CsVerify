using CsVerify;

namespace Samples.Buggy
{
    [Owned]
    public sealed class Link
    {
        public int Val;
        [Owns] public Link? Next;

        [Invariant, Pure] public bool Sorted() => Next == null || Val <= Next.Val;

        // BUG: links a smaller node after this one: the list is no longer sorted when this returns (CSV1015)
        public void AppendSmaller()
        {
            Spec.Requires(Next == null);
            var n = Own.New(new Link(), out var nv);
            n.Val = checked(Val - 1);
            Own.Give(ref Next, n, nv);
        }

        /// <summary>Cuts the list after its second node.</summary>
        public void TrimAfterSecond()
        {
            if (Next == null) return;
            var n = Own.Take(ref Next, out var nv);
            if (n.Next != null)
            {
                Own.Take(ref n.Next, out var rv);
                Own.Drop(rv);
            }
            Own.Give(ref Next, n, nv);
        }
    }

    public static class TreeOwnershipBugs
    {
        // BUG: changes a node the list owns without taking it out (CSV1016)
        public static void Reach(Link a, ref Own<Link> av)
        {
            Spec.Requires(av.Obj.Value == a && a.Next != null);
            a.Next.Val = 0;
        }

        // BUG: an [Owns] field set directly, bypassing Own.Give (CSV1016)
        public static void Bypass(Link a, ref Own<Link> av)
        {
            Spec.Requires(av.Obj.Value == a);
            a.Next = null;
        }

        // BUG: a node made to own itself (CSV1016)
        public static void Cycle()
        {
            var a = Own.New(new Link(), out var av);
            Own.Give(ref a.Next, a, av);
        }

        // BUG: what is inside a list may change when the list is handed to a method (CSV1004)
        public static void Stale(Link a, ref Own<Link> av)
        {
            Spec.Requires(av.Obj.Value == a && a.Next != null);
            var inner = a.Next;
            var after = inner.Next;
            a.TrimAfterSecond();
            Spec.Assert(inner.Next == after);
        }
    }
}
