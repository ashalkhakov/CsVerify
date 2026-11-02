using CsVerify;

namespace Samples.Buggy
{
    public static class ArrayViewBugs
    {
        // CSV1001: the right half starts at p + mid, not p + mid + 1.
        public static void WrongOffset(ref ArrayView<int> view, Ptr<int> p, int n)
        {
            Spec.Requires(view.Addr == p.Addr && view.Length.Value == n && n >= 2);
            Mem.Split(view, Ghost.Of(1), out var left, out var right);
            Mem.Set(ref right, p.Offset(2), 0, 5);
            Mem.Join(left, right, out view);
        }

        // CSV0001 (analyzer): the halves are never joined, so the borrowed view is not whole on return,
        // and both halves leak.
        public static void ForgetToJoin(ref ArrayView<int> view, Ptr<int> p)
        {
            Spec.Requires(view.Addr == p.Addr && view.Length.Value >= 1);
            Mem.Split(view, Ghost.Of(1), out var left, out var right);
            Mem.Set(ref left, p, 0, 1);
        }

        // CSV1003-style bug through a view: index n is one past the end (CSV1001 on Get's precondition).
        public static int OnePastEnd(in ArrayView<int> view, Ptr<int> p, int n)
        {
            Spec.Requires(view.Addr == p.Addr && view.Length.Value == n);
            return Mem.Get(in view, p, n);
        }
    }
}
