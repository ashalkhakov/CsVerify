using System.Linq;
using Xunit;

namespace CsVerify.Tests
{
    /// <summary>ATS-style ownership: [Owned] objects are written only through their linear Own&lt;T&gt; view.</summary>
    public class OwnedTests
    {
        private const string Account = @"
[Owned]
public sealed class Account
{
    public int Balance;
    [Invariant, Pure] public bool Valid() => Balance >= 0;
    public Account(int initial) { Spec.Requires(initial >= 0); Spec.Ensures(Balance == initial); Balance = initial; }
    public void Deposit(int amount) { Spec.Requires(amount >= 0); Spec.Ensures(Balance == Spec.Old(Balance) + amount); Balance += amount; }
    public void Withdraw(int amount) { Spec.Requires(0 <= amount && amount <= Balance); Spec.Ensures(Balance == Spec.Old(Balance) - amount); Balance -= amount; }
}
public interface IAudit { void Record(int amount); }
";

        private static string[] Errors(string method, string body) =>
            Harness.Verify(Account + "public static class C { " + body + " }").Errors(method);

        [Fact]
        public void Writes_NeedTheView()
        {
            Assert.Equal(new[] { "CSV1016" }, Errors("M", "static void M(Account a) { a.Balance = 1; }"));
            Assert.Equal(new[] { "CSV1016" }, Errors("M", "static void M(Account a) { a.Deposit(1); }"));
            Assert.Empty(Errors("M", "static void M(Account a, ref Own<Account> v) { Spec.Requires(v.Obj.Value == a); a.Deposit(1); }"));
            // a read-only borrow does not allow writing
            Assert.Equal(new[] { "CSV1016" }, Errors("M", "static void M(Account a, in Own<Account> v) { Spec.Requires(v.Obj.Value == a); a.Deposit(1); }"));
        }

        [Fact]
        public void Views_AreMadeOnlyForNewObjects()
        {
            Assert.Equal(new[] { "CSV1016" }, Errors("M", "static void M(Account a) { Own.New(a, out var v); Own.Drop(v); }"));
            Assert.Empty(Errors("M", "static int M() { Spec.Ensures((int r) => r == 5); var a = Own.New(new Account(5), out var v); int b = a.Balance; Own.Drop(v); return b; }"));
        }

        [Fact]
        public void TheInvariant_TravelsWithTheView()
        {
            // assumed where the view is received, proved where it is given back
            Assert.Empty(Errors("M", "static int M(Account a, ref Own<Account> v) { Spec.Requires(v.Obj.Value == a); Spec.Ensures((int r) => r >= 0); return a.Balance; }"));
            Assert.Equal(new[] { "CSV1002" }, Errors("M", "static int M(Account a) { Spec.Ensures((int r) => r >= 0); return a.Balance; }"));
            Assert.Equal(new[] { "CSV1015" }, Errors("M", "static void M(Account a, ref Own<Account> v) { Spec.Requires(v.Obj.Value == a); a.Balance = -1; }"));
            // giving the view up for good needs no invariant: nobody can write or rely on the object any more
            Assert.Empty(Errors("M", "static void M() { var a = Own.New(new Account(0), out var v); a.Balance = -1; Own.Drop(v); }"));
        }

        [Fact]
        public void OwnedInvariants_ReadOnlyTheirOwnFields()
        {
            string Check(string cls) => string.Join(",", Harness.Verify("public sealed class Cell { public int Val; }\n" + cls).Errors("V"));
            Assert.Equal("CSV1015", Check("[Owned] public sealed class A { public Cell? Peer; [Invariant, Pure] public bool V() => Peer == null || Peer.Val > 0; }"));
            Assert.Equal("CSV1015", Check("[Owned] public sealed class A { public int N; public A? Other; [Invariant, Pure] public bool V() => Other == null || Other.N >= 0; }"));
            Assert.Equal("CSV1015", Check("[Owned] public sealed class A { public int N; [Invariant, Pure] public bool V() => Ok(this); [Pure] static bool Ok(A a) => a.N >= 0; }"));
            Assert.Equal("", Check("[Owned] public sealed class A { public int N; [Invariant, Pure] public bool V() => N >= 0 && this.N < 100; }"));
            // array contents can be changed by anyone holding the array; its length cannot
            Assert.Equal("CSV1015", Check("[Owned] public sealed class A { public int[]? Items; [Invariant, Pure] public bool V() => Items == null || Items.Length == 0 || Items[0] > 0; }"));
            Assert.Equal("", Check("[Owned] public sealed class A { public int[]? Items; [Invariant, Pure] public bool V() => Items != null && Items.Length > 0; }"));
        }

        [Fact]
        public void UnknownCode_CannotChangeWhatItHasNoViewOf() =>
            Assert.Empty(Errors("M", @"static void M(IAudit audit) {
                var a = Own.New(new Account(50), out var va);
                a.Withdraw(20);
                audit.Record(20);
                Spec.Assert(a.Balance == 30);
                Own.Drop(va); }"));

        [Fact]
        public void TwoViewsInHand_OwnTwoObjects() =>
            Assert.Empty(Errors("M", @"static void M(Account a, ref Own<Account> va, Account b, ref Own<Account> vb) {
                Spec.Requires(va.Obj.Value == a && vb.Obj.Value == b);
                Spec.Assert(a != b); }"));

        [Fact]
        public void MovingAView_IsNotAContradiction() =>
            Assert.Equal(new[] { "CSV1004" }, Errors("M", "static void M() { var a = Own.New(new Account(0), out var v); var w = v; Spec.Assert(false); Own.Drop(w); }"));
    
        private const string Node = @"
[Owned]
public sealed class Node
{
    public int Val;
    [Owns] public Node? Next;
    [Invariant, Pure] public bool Sorted() => Next == null || Val <= Next.Val;
    public Node(int v) { Spec.Ensures(Val == v && Next == null); Val = v; }
    public void Push(int v)
    {
        Spec.Requires(Val <= v);
        Spec.Ensures(Val == Spec.Old(Val));
        if (Next != null) { var rest = Own.Take(ref Next, out var rv); var n = Own.New(new Node(v), out var nv);
            if (v <= rest.Val) { Own.Give(ref n.Next, rest, rv); Own.Give(ref Next, n, nv); }
            else { Own.Drop(nv); rest.Push(v); Own.Give(ref Next, rest, rv); } }
        else Own.Give(ref Next, Own.New(new Node(v), out var nv2), nv2);
    }
}
";

        private static string[] TreeErrors(string method, string body) =>
            Harness.Verify(Node + "public static class C { " + body + " }").Errors(method);

        [Fact]
        public void OwnershipTrees_UnfoldAndFold()
        {
            Assert.Empty(Harness.Verify(Node).Errors("Push"));
            // what is owned is reached by taking it out; writing it in place, or setting the field, is not allowed
            Assert.Equal(new[] { "CSV1016" }, TreeErrors("M", "static void M(Node a, ref Own<Node> av) { Spec.Requires(av.Obj.Value == a && a.Next != null); a.Next.Val = 0; }"));
            Assert.Equal(new[] { "CSV1016" }, TreeErrors("M", "static void M(Node a, ref Own<Node> av) { Spec.Requires(av.Obj.Value == a); a.Next = null; }"));
            Assert.Equal(new[] { "CSV1016" }, TreeErrors("M", "static void M() { var a = Own.New(new Node(0), out var av); Own.Give(ref a.Next, a, av); }"));
        }

        [Fact]
        public void OwnershipTrees_AreFramesOfTheirOwn()
        {
            // a call that gets one list's root may change that whole list, and nothing in another
            Assert.Empty(TreeErrors("M", @"static void M(Node a, ref Own<Node> av, Node b, ref Own<Node> bv) {
                Spec.Requires(av.Obj.Value == a && bv.Obj.Value == b && a.Val <= 10 && b.Next != null);
                var inner = b.Next; var after = inner.Next;
                a.Push(10);
                Spec.Assert(b.Next == inner && inner.Next == after); }"));
            Assert.Equal(new[] { "CSV1004" }, TreeErrors("M", @"static void M(Node a, ref Own<Node> av) {
                Spec.Requires(av.Obj.Value == a && a.Val <= 10 && a.Next != null);
                var inner = a.Next; var after = inner.Next;
                a.Push(10);
                Spec.Assert(inner.Next == after); }"));
        }

        [Fact]
        public void OwnedChildren_MayBeReadByTheInvariant_OneLevelDown() =>
            Assert.Equal("CSV1015", string.Join(",", Harness.Verify(
                "[Owned] public sealed class N { public int V; [Owns] public N? Next; [Invariant, Pure] public bool I() => Next == null || Next.Next == null || V <= Next.Next.V; }").Errors("I")));

        [Fact]
        public void OwnedQueries_AreFramedByTheirTree()
        {
            const string node = @"
[Owned]
public sealed class N
{
    public int Val;
    [Owns] public N? Next;
    public N? Peer;
    [Pure] public bool TwoSmall => Val < 10 && (Next == null || Next.Val < 10);
    [Pure] public int PeerVal => Peer == null ? 0 : Peer.Val;
    public void Bump() { Val = checked(Val + 1); }
}
public static class C { BODY }";
            var r = Harness.Verify(node.Replace("BODY", @"
    static void Kept(N a, ref Own<N> av, N b, ref Own<N> bv) {
        Spec.Requires(av.Obj.Value == a && bv.Obj.Value == b);
        bool s = b.TwoSmall; a.Bump(); Spec.Assert(b.TwoSmall == s); }
    static void Changed(N a, ref Own<N> av) {
        Spec.Requires(av.Obj.Value == a);
        bool s = a.TwoSmall; a.Bump(); Spec.Assert(a.TwoSmall == s); }
    static void Footprint(N a, ref Own<N> av) {
        Spec.Requires(av.Obj.Value == a && a.Next != null);
        Spec.Assert(Own.Tree(a).Contains(a) && Own.Tree(a).Contains(a.Next)); }"));
            Assert.Empty(r.Errors("Kept"));
            Assert.Equal(new[] { "CSV1004" }, r.Errors("Changed"));
            Assert.Empty(r.Errors("Footprint"));
            // a query reads only its own tree
            Assert.Equal(new[] { "CSV1017" }, r.Errors("get_PeerVal"));
        }

        [Fact]
        public void Trees_CanBeLentThroughModifies()
        {
            var r = Harness.Verify(@"
[Owned]
public sealed class Node
{
    public int Val;
    [Owns] public Node? Next;
    [Pure] public int First => Val;
}
public static class C
{
    static void Reset(Node n) { Spec.Modifies(Own.Tree(n)); Spec.Ensures(n.Val == 0); n.Val = 0; if (n.Next != null) n.Next.Val = 0; }
    static void Use(Node a, ref Own<Node> av, Node b, ref Own<Node> bv) {
        Spec.Requires(av.Obj.Value == a && bv.Obj.Value == b);
        int bf = b.First; Reset(a); Spec.Assert(a.Val == 0 && b.First == bf); }
    static void NoView(Node a) { Reset(a); }
    static void Outside(Node a, Node b) { Spec.Modifies(Own.Tree(a)); b.Val = 1; }
}");
            // a Dafny-style method borrows a whole tree from a caller that holds its view; nothing else changes
            Assert.Empty(r.Errors("Reset"));
            Assert.Empty(r.Errors("Use"));
            Assert.Equal(new[] { "CSV1016" }, r.Errors("NoView"));
            Assert.Equal(new[] { "CSV1016" }, r.Errors("Outside"));
        }

        [Fact]
        public void Packages_CarryTheirViews()
        {
            var r = Harness.Verify(@"
[Owned]
public sealed class Cell
{
    public int V;
    [Invariant, Pure] public bool Valid() => V >= 0;
    public Cell() { Spec.Ensures(V == 0); V = 0; }
}
[Linear]
public readonly record struct Holder(Own<Cell> View, Cell Obj)
{
    [Invariant, GhostFunction] public bool Valid() => View.Obj.Value == Obj;
}
public static class C
{
    static Holder Make() { var c = Own.New(new Cell(), out var v); return new Holder(v, c); }
    static void Poke(ref Holder h) { var (v, c) = h; c.V = 5; h = new Holder(v, c); }
    static void Other(Cell d, ref Own<Cell> dv) {
        Spec.Requires(dv.Obj.Value == d);
        d.V = 1; var h = Make(); Poke(ref h); Spec.Assert(d.V == 1);
        var (v, c) = h; Own.Drop(v); }
    static void Stale(ref Holder h) {
        var (v, c) = h; int before = c.V; h = new Holder(v, c); Poke(ref h); Spec.Assert(c.V == before); }
    static void Inside(ref Holder h) { h.Obj.V = 3; }
}");
            // a package hands its views over when built and back when taken apart; a call sees the views in it
            Assert.Empty(r.Errors("Make"));
            Assert.Empty(r.Errors("Poke"));
            Assert.Empty(r.Errors("Other"));
            Assert.Equal(new[] { "CSV1004" }, r.Errors("Stale"));
            Assert.Contains("CSV1016", r.Errors("Inside"));
        }

        [Fact]
        public void Packages_AreLinear()
        {
            const string decls = @"
[Owned] public sealed class Cell { public int V; }
[Linear] public readonly record struct Holder(Own<Cell> View, Cell Obj);
";
            // built from views, taken apart into views: nothing is lost or copied
            Assert.Empty(Harness.Analyze(decls + @"
public static class C
{
    static Holder Make() { var c = Own.New(new Cell(), out var v); return new Holder(v, c); }
    static void Use() { var (v, c) = Make(); Own.Drop(v); }
}"));
            // a view read out of a package that still holds it would be a second copy
            Assert.Contains("CSV0004", Harness.Analyze(decls + @"
public static class C { static void Copy(Holder h) { var w = h.View; Own.Drop(w); var (v, c) = h; Own.Drop(v); } }"));
            // a package not taken apart loses its views
            Assert.Contains("CSV0001", Harness.Analyze(decls + @"
public static class C { static void Leak() { var c = Own.New(new Cell(), out var v); var h = new Holder(v, c); } }"));
        }

        [Fact]
        public void FieldPermissions_SplitAndRejoin()
        {
            var r = Harness.Verify(@"
[Owned]
public sealed class Pt { public int X, Y; }
public static class C
{
    static void SetX(Pt p, int v) { Spec.Requires(Spec.Acc(p, nameof(Pt.X))); Spec.Ensures(Spec.Acc(p, nameof(Pt.X)) && p.X == v); p.X = v; }
    static void Both(Pt p, ref Own<Pt> v) {
        Spec.Requires(v.Obj.Value == p);
        p.Y = 7; SetX(p, 3); Spec.Assert(p.Y == 7 && p.X == 3); p.Y = 8; p.X = 5; }
    static void Whole(Pt p) {
        Spec.Requires(Spec.Acc(p, nameof(Pt.X)) && Spec.Acc(p, nameof(Pt.Y))); Spec.Ensures(Spec.Acc(p)); }
    static void Other(Pt p) { Spec.Requires(Spec.Acc(p, nameof(Pt.X))); p.Y = 1; }
    static void Same(Pt p, Pt q) { Spec.Requires(Spec.Acc(p, nameof(Pt.X)) && Spec.Acc(q, nameof(Pt.X))); Spec.Assert(p != q); }
    static void Lost(Pt p, ref Own<Pt> v) { Spec.Requires(v.Obj.Value == p); Give(p); Keep(ref v); }
    static void Give(Pt p) { Spec.Requires(Spec.Acc(p, nameof(Pt.X))); }
    static void Keep(ref Own<Pt> v) { }
}");
            // a field given out of a whole object leaves the others in hand; with all back it is whole again
            Assert.Empty(r.Errors("SetX"));
            Assert.Empty(r.Errors("Both"));
            Assert.Empty(r.Errors("Whole"));
            Assert.Empty(r.Errors("Same"));
            Assert.Equal(new[] { "CSV1016" }, r.Errors("Other"));
            Assert.Equal(new[] { "CSV1016" }, r.Errors("Lost"));
        }

        [Fact]
        public void CellsInPredicates_AreFramed()
        {
            var r = Harness.Verify(@"
[Owned]
public sealed class Box { public int[] Cells; }
public static class C
{
    [Predicate] static bool Held(Box b) => Spec.Acc(b) && b.Cells != null && Spec.Acc(b.Cells) && b.Cells.Length > 0;
    [Predicate] static bool Peeks(Box b) => Spec.Acc(b) && b.Cells != null && b.Cells.Length > 0 && b.Cells[0] > 0;
    static void Set(Box b) { Spec.Requires(Held(b)); Spec.Ensures(Held(b)); Spec.Unfold(Held(b)); b.Cells[0] = 1; Spec.Fold(Held(b)); }
    static void Other(Box a, Box b) {
        Spec.Requires(Held(a) && Held(b));
        Spec.Unfold(Held(a)); int v = a.Cells[0]; Spec.Fold(Held(a));
        Set(b);
        Spec.Unfold(Held(a)); Spec.Assert(a.Cells[0] == v); Spec.Fold(Held(a)); }
    static void Folded(Box b) {
        Spec.Requires(Held(b));
        Spec.Unfold(Held(b)); var cells = b.Cells; Spec.Fold(Held(b));
        cells[0] = 2; }
}");
            // a predicate holds its array's cells: a call that gets it changes only them, and nobody writes them while folded
            Assert.Empty(r.Errors("Held"));
            Assert.Empty(r.Errors("Set"));
            Assert.Empty(r.Errors("Other"));
            Assert.Equal(new[] { "CSV1016" }, r.Errors("Peeks"));
            Assert.Equal(new[] { "CSV1016" }, r.Errors("Folded"));
        }

        // (a function over two instances, or one not of its parameters: an ordinary function of the memory, defined by its
        // body; what holds by the instances, its postconditions, its calls give; no axiom says them of every memory)
        [Fact]
        public void FunctionsOverSeveralInstances()
        {
            var r = Harness.Verify(@"
[Owned] public sealed class Cell { public int V; }
public sealed class Pair { public Cell L = new Cell(); public Pair() { } }
public static class P
{
    [Predicate] public static bool One(Cell c) => c != null && Spec.Acc(c) && c.V >= 0 && c.V < 1000;
    [Pure] public static int Get(Cell c) { Spec.Requires(One(c)); Spec.Ensures((int r) => r >= 0); Spec.Unfold(One(c)); return c.V; }
    [Pure] public static int Sum(Cell a, Cell b) { Spec.Requires(One(a) && One(b)); Spec.Ensures((int r) => r >= 0); Spec.Unfold(One(a)); Spec.Unfold(One(b)); return a.V + b.V; }
    public static int Use(Cell a, Cell b) { Spec.Requires(One(a) && One(b)); Spec.Ensures(One(a) && One(b)); Spec.Ensures((int r) => r >= 0); return Sum(a, b); }
    public static int Bad(Cell a, Cell b) { Spec.Requires(One(a) && One(b)); Spec.Ensures(One(a) && One(b)); Spec.Ensures((int r) => r > 0); return Sum(a, b); }
    [Pure] public static int Left(Pair p) { Spec.Requires(p != null && One(p.L)); Spec.Ensures((int r) => r >= 0); return Get(p.L); }
    public static int UseLeft(Pair p) { Spec.Requires(p != null && One(p.L)); Spec.Ensures(One(p.L)); Spec.Ensures((int r) => r >= 0); return Left(p); }
    // (the axioms are consistent: a cell below 0, which the predicate's facts rule out, contradicts none)
    public static void NoFalse(Cell a) { Spec.Requires(Spec.Acc(a)); Spec.Ensures(Spec.Acc(a)); a.V = -5; Spec.Assert(false); }
}");
            foreach (var good in new[] { "P.Sum", "P.Use", "P.Left", "P.UseLeft" })
                Assert.True(r[good].Verified, good + ": " + string.Join("; ", r[good].Diagnostics.Select(d => d.Message)));
            Assert.Equal(new[] { "CSV1002" }, r.Errors("P.Bad"));
            Assert.Equal(new[] { "CSV1004" }, r.Errors("P.NoFalse"));
        }

        // (a predicate's facts hold in its instance's snapshot, a library function's arguments read there too: what a
        // function over it gives, the predicate's facts speak of)
        [Fact]
        public void PredicateFactsInTheSnapshot()
        {
            var r = Harness.Verify(@"
[Owned] public sealed class Box { public string S = ""a""; }
public static class P
{
    [Predicate] public static bool Has(Box b) => b != null && Spec.Acc(b) && b.S != null && b.S.Contains(""a"");
    [Pure] public static string Get(Box b) { Spec.Requires(Has(b)); Spec.Unfold(Has(b)); return b.S; }
    public static void Use(Box b) { Spec.Requires(Has(b)); Spec.Ensures(Has(b)); Spec.Assert(Get(b).Contains(""a"")); }
    public static void Bad(Box b) { Spec.Requires(Has(b)); Spec.Ensures(Has(b)); Spec.Assert(Get(b).Contains(""b"")); }
}");
            Assert.True(r["P.Use"].Verified, "P.Use: " + string.Join("; ", r["P.Use"].Diagnostics.Select(d => d.Message)));
            Assert.Equal(new[] { "CSV1004" }, r.Errors("P.Bad"));
        }
}
}
