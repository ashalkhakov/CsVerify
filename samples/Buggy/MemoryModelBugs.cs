using CsVerify;

namespace Samples.Buggy
{
    public static class MemoryModelBugs
    {
        // BUG: empty views hold no cells, so two of them may start at one address (CSV1004)
        public static void EmptyViewsApart(in ArrayView<int> a, in ArrayView<int> b)
        {
            Spec.Assert(a.Addr != b.Addr);
        }

        public static void Poke(ref ArrayView<int> view, Ptr<int> p)
        {
            Spec.Requires(view.Addr == p.Addr && view.Length.Value > 0);
            Spec.Ensures(view.Addr == Spec.Old(view).Addr && view.Length == Spec.Old(view).Length);
            Mem.Set(ref view, p, 0, 1);
        }

        // BUG: the view went to Poke by ref: its contents may have changed (CSV1004)
        public static void Stale(ref ArrayView<int> view, Ptr<int> p)
        {
            Spec.Requires(view.Addr == p.Addr && view.Length.Value > 0);
            int before = Mem.Get(in view, p, 0);
            Poke(ref view, p);
            Spec.Assert(view.Elems[0].Value == before);
        }
    }
}
