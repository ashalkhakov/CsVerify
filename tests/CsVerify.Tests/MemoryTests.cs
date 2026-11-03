using Xunit;

namespace CsVerify.Tests
{
    /// <summary>ATS's manual memory on the cell model: views hold cells, calls change only what they get.</summary>
    public class MemoryTests
    {
        [Fact]
        public void Views_HoldDisjointCells()
        {
            var r = Harness.Verify(@"
public static class C
{
    static void Apart(in ArrayView<int> a, in ArrayView<int> b) {
        Spec.Requires(a.Length.Value > 0 && b.Length.Value > 0);
        Spec.Assert(a.Addr.Value + a.Length.Value <= b.Addr.Value || b.Addr.Value + b.Length.Value <= a.Addr.Value); }
    static void EmptyApart(in ArrayView<int> a, in ArrayView<int> b) { Spec.Assert(a.Addr != b.Addr); }
    static int TwoCells() {
        Spec.Ensures((int r) => r == 4);
        var p = Mem.Alloc(4, out var v); var q = Mem.Alloc(5, out var w);
        Spec.Assert(v.Addr != w.Addr);
        Mem.Write(ref w, q, 6);
        int r = Mem.Read(in v, p);
        Mem.Free(v, p); Mem.Free(w, q);
        return r; }
}");
            // two views in hand are of different cells; writing one cell leaves the others as they were
            Assert.Empty(r.Errors("Apart"));
            Assert.Empty(r.Errors("TwoCells"));
            Assert.Equal(new[] { "CSV1004" }, r.Errors("EmptyApart"));
        }

        [Fact]
        public void Calls_ChangeOnlyTheCellsTheyGet()
        {
            var r = Harness.Verify(@"
public static class C
{
    static void Poke(ref ArrayView<int> view, Ptr<int> p) {
        Spec.Requires(view.Addr == p.Addr && view.Length.Value > 0);
        Spec.Ensures(view.Addr == Spec.Old(view).Addr && view.Length == Spec.Old(view).Length);
        Mem.Set(ref view, p, 0, 1); }
    static void Other(ref ArrayView<int> a, Ptr<int> pa, in ArrayView<int> b, Ptr<int> pb, int[] arr) {
        Spec.Requires(a.Addr == pa.Addr && a.Length.Value > 0 && b.Addr == pb.Addr && b.Length.Value > 0 && arr.Length > 0);
        int x = Mem.Get(in b, pb, 0); int y = arr[0];
        Poke(ref a, pa);
        int x2 = Mem.Get(in b, pb, 0);
        Spec.Assert(x2 == x && arr[0] == y); }
    static void Same(ref ArrayView<int> a, Ptr<int> pa) {
        Spec.Requires(a.Addr == pa.Addr && a.Length.Value > 0);
        int x = Mem.Get(in a, pa, 0);
        Poke(ref a, pa);
        Spec.Assert(a.Elems[0].Value == x); }
}");
            Assert.Empty(r.Errors("Poke"));
            Assert.Empty(r.Errors("Other"));
            Assert.Equal(new[] { "CSV1004" }, r.Errors("Same"));
        }
    }
}
