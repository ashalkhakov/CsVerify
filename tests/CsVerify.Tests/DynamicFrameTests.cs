using Xunit;

namespace CsVerify.Tests
{
    /// <summary>Dafny-style dynamic frames: Valid() and a ghost Repr, Spec.Modifies, Spec.Reads, Spec.Fresh.</summary>
    public class DynamicFrameTests
    {
        private const string Pair = @"
public sealed class Cell
{
    public int Val;
    public Cell(int v) { Spec.Ensures(Val == v); Val = v; }
}
public sealed class Pair
{
    public Cell? A, B;
    public Ghost<ObjSet> Repr;

    [GhostFunction] public bool Valid()
    {
        Spec.Reads(Repr.Value.Add(this));
        return Repr.Value.Contains(this) && A != null && B != null && A != B && Repr.Value.Contains(A) && Repr.Value.Contains(B);
    }

    public Pair()
    {
        Spec.Ensures(Valid() && A!.Val == 0 && B!.Val == 0 && Spec.Fresh(Repr.Value));
        A = new Cell(0);
        B = new Cell(0);
        Repr = Ghost.Of(ObjSet.Of(this).Add(A).Add(B));
    }

    public void IncA()
    {
        Spec.Requires(Valid());
        Spec.Modifies(Repr.Value);
        Spec.Ensures(Valid() && Repr.Value == Spec.Old(Repr.Value) && A!.Val == Spec.Old(A!.Val) + 1 && B!.Val == Spec.Old(B!.Val));
        A!.Val++;
    }

    public void Swap()
    {
        Spec.Requires(Valid());
        Spec.Modifies(Repr.Value);
        Spec.Ensures(Valid() && Repr.Value == Spec.Old(Repr.Value) && A == Spec.Old(B) && B == Spec.Old(A));
        var t = A; A = B; B = t;
    }
}
";

        private static string[] Errors(string method, string body) =>
            Harness.Verify(Pair + "public static class C { " + body + " }").Errors(method);

        [Fact]
        public void TheClass_Verifies()
        {
            var r = Harness.Verify(Pair);
            Assert.Empty(r.Errors("Pair..ctor"));
            Assert.Empty(r.Errors("IncA"));
            Assert.Empty(r.Errors("Swap"));
            Assert.Empty(r.Errors("Valid"));
        }

        [Fact]
        public void DisjointObjects_SurviveEachOthersUpdates() =>
            // fresh representations are disjoint; q's fields and Valid() are untouched by p's methods
            Assert.Empty(Errors("M", @"static void M() {
                var p = new Pair();
                var q = new Pair();
                p.IncA();
                Spec.Assert(q.Valid() && q.A!.Val == 0 && p.A!.Val == 1);
                p.Swap();
                Spec.Assert(q.Valid() && q.A!.Val == 0); }"));

        [Fact]
        public void PossiblySharedObjects_DoNot()
        {
            // q may be p, or share its cells: nothing is known after p changes
            Assert.Equal(new[] { "CSV1004" }, Errors("M", "static void M(Pair p, Pair q) { Spec.Requires(p.Valid() && q.Valid()); p.Swap(); Spec.Assert(q.Valid()); }"));
            Assert.Equal(new[] { "CSV1004" }, Errors("M", "static void M(Pair p, Pair q) { Spec.Requires(p.Valid() && q.Valid()); int v = q.A!.Val; p.IncA(); Spec.Assert(q.A!.Val == v); }"));
            Assert.Empty(Errors("M", @"static void M(Pair p, Pair q) {
                Spec.Requires(p.Valid() && q.Valid() && p.Repr.Value.IsDisjointFrom(q.Repr.Value));
                int v = q.A!.Val; p.IncA(); Spec.Assert(q.A!.Val == v && q.Valid()); }"));
        }

        [Fact]
        public void Modifies_IsChecked()
        {
            Assert.Equal(new[] { "CSV1017" }, Errors("M", "static void M(Pair p, Cell c) { Spec.Requires(p.Valid()); Spec.Modifies(ObjSet.Of(c)); p.A!.Val = 2; }"));
            Assert.Empty(Errors("M", "static void M(Pair p, Cell c) { Spec.Modifies(ObjSet.Of(c)); c.Val = 1; var d = new Cell(3); d.Val = 4; }"));
            // a callee that writes but has no frame cannot be checked; one with a wider frame is not allowed
            Assert.Equal(new[] { "CSV1017" }, Errors("M", "static void Set(Cell c) { c.Val = 0; } static void M(Cell c) { Spec.Modifies(ObjSet.Of(c)); Set(c); }"));
            Assert.Equal(new[] { "CSV1017" }, Errors("M", "static void M(Pair p, Cell c) { Spec.Requires(p.Valid()); Spec.Modifies(ObjSet.Of(c)); p.IncA(); }"));
        }

        [Fact]
        public void Reads_IsChecked() =>
            Assert.Equal(new[] { "CSV1017" }, Harness.Verify(Pair.Replace("public void IncA()",
                "[GhostFunction] public bool Bad() { Spec.Reads(ObjSet.Of(this)); return A != null && A.Val > 0; }\n    public void IncA()")).Errors("Bad"));

        [Fact]
        public void OwnedClasses_UseViewsNotFrames() =>
            Assert.Equal(new[] { "CSV1017" }, Harness.Verify(@"
[Owned] public sealed class Box { public int V; public void Set() { Spec.Modifies(ObjSet.Of(this)); V = 1; } }").Errors("Set"));
    }
}
