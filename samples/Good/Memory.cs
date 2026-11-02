using CsVerify;

namespace Samples
{
    /// <summary>Manual memory with views: PointsTo&lt;T&gt; is ATS's T @ l, and must be freed exactly once.</summary>
    public static class Memory
    {
        public static int Counter()
        {
            Spec.Ensures<int>(r => r == 42);
            Ptr<int> p = Mem.Alloc(41, out PointsTo<int> view);   // view: int @ p.Addr
            int x = Mem.Read(in view, p);                           // borrow the view
            Spec.Assert(x == 41);
            Mem.Write(ref view, p, x + 1);                          // borrow, and update the view's value
            int y = Mem.Read(in view, p);
            Mem.Free(view, p);                                      // consume the view
            return y;
        }

        /// <summary>A function that takes a view and gives it back: ATS's (!int @ l | ptr l) -&gt; void.</summary>
        public static void Increment(ref PointsTo<int> view, Ptr<int> p)
        {
            Spec.Requires(view.Addr == p.Addr && view.Value.Value < 1000);
            Spec.Ensures(view.Addr == Spec.Old(view).Addr && view.Value.Value == Spec.Old(view).Value.Value + 1);
            int v = Mem.Read(in view, p);
            Mem.Write(ref view, p, v + 1);
        }

        public static int Twice()
        {
            Spec.Ensures<int>(r => r == 2);
            var p = Mem.Alloc(0, out var view);
            Increment(ref view, p);
            Increment(ref view, p);
            int r = Mem.Read(in view, p);
            Mem.Free(view, p);
            return r;
        }
    }
}
