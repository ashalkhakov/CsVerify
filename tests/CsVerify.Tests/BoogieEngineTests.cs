using System.IO;
using System.Linq;
using CsVerify.Verifier;
using Xunit;

namespace CsVerify.Tests
{
    /// <summary>
    /// The Boogie engine (docs/boogie.md): on every method it verifies, it reports what CsVerify's own engine does (each
    /// diagnostic's id and line), and what it doesn't translate is verified as always.
    /// </summary>
    public class BoogieEngineTests
    {
        // (written for these tests: one of each construct the translation covers, and a bug of each kind it checks)
        private const string Corpus = @"
public static class A
{
    public static int Abs(int x) { Spec.Requires(x > int.MinValue); Spec.Ensures<int>(r => r >= 0 && (r == x || r == -x)); if (x < 0) return -x; return x; }
    public static int Sum(int n)
    {
        Spec.Requires(0 <= n && n <= 1000);
        Spec.Ensures<int>(r => r == n * (n + 1) / 2);
        int s = 0, i = 0;
        while (i < n) { Spec.Invariant(0 <= i && i <= n && s == i * (i + 1) / 2); i++; s += i; }
        return s;
    }
    public static long Wide(int x) { Spec.Ensures<long>(r => r == 2L * x); long y = x; return y + y; }
    public static int Twice(int x) { Spec.Requires(x > -1000 && x < 1000); Spec.Ensures<int>(r => r == 2 * x); return x + x; }
    public static int UseAbs(int y) { Spec.Ensures<int>(r => r >= 0); return Abs(y); }
    public static int UseAbsSafely(int y) { Spec.Ensures<int>(r => r >= 0); return y == int.MinValue ? 0 : Abs(y); }
    public static bool Between(int a, int b, int c) { Spec.Ensures<bool>(r => r == (a <= b && b <= c)); return a <= b && b <= c; }
    public static int Checked(int x) { Spec.Ensures<int>(r => r == x + 1); return checked(x + 1); }
    public static int Truncates(int a) { Spec.Requires(a == -7); Spec.Ensures<int>(r => r == -3); return a / 2; }
    public static int Remainder(int a) { Spec.Requires(a == -7); Spec.Ensures<int>(r => r == -1); return a % 2; }
    public static int Overflows(int x) => x + 1;
    public static int Div(int a, int b) => a / b;
    public static void Assertion(int x) { Spec.Requires(x > 3); Spec.Assert(x > 4); }
    public static int BadInv(int n) { Spec.Requires(n >= 0 && n < 100); int i = 0; while (i < n) { Spec.Invariant(i < n); i++; } return i; }
    public static int BadPost(int x) { Spec.Ensures<int>(r => r > x); return x; }
    public static int Elsewhere(int x) { Spec.Ensures<int>(r => r == x); decimal d = 0.5m; d = d + 1m; return x; }
    public static void Fill(int[] a, int v) { Spec.Ensures(Spec.Forall(0, a.Length, k => a[k] == v)); for (int i = 0; i < a.Length; i++) { Spec.Invariant(0 <= i && i <= a.Length && Spec.Forall(0, i, k => a[k] == v)); a[i] = v; } }
    public static int First(int[] a) { Spec.Requires(a.Length > 0); return a[0]; }
    public static int FirstBad(int[] a) => a[0];
    public static int KeepsOwn(int[] a) { Spec.Requires(a.Length > 0); var b = new int[1]; b[0] = 5; Fill(a, 3); Spec.Assert(b[0] == 5); return b[0]; }
    public static void WfBad(int[] a) { Spec.Requires(a[0] > 0); }
    public static int Wraps(int x) { Spec.Ensures<int>(r => x != int.MaxValue || r == int.MinValue); return unchecked(x + 1); }
    public static int Read(int[] a, int i) { Spec.Requires(0 <= i && i < a.Length); Spec.Ensures<int>(r => r == a[i]); return a[i]; }
    public static void CallNull() { int[]? n = null; First(n!); }
    public static int[] Make(int n) { Spec.Requires(n >= 0); Spec.Ensures<int[]>(r => r.Length == n); return new int[n]; }
    public static int Digit(char c) { Spec.Requires('0' <= c && c <= '9'); Spec.Ensures<int>(r => 0 <= r && r <= 9); return c - '0'; }
    public static byte Low(int x) => (byte)x;
    public static byte LowChecked(int x) { Spec.Ensures<byte>(r => r == x); return checked((byte)x); }
    public static byte LowWraps(int x) { Spec.Requires(x == 257); Spec.Ensures<byte>(r => r == 1); return unchecked((byte)x); }
    public static uint TwiceU(uint u) => u * 2;
    public static short Neg(short s) { Spec.Ensures<short>(r => r == -s); return (short)-s; }
    [Pure] public static int Max(int a, int b) => a > b ? a : b;
    [GhostFunction] public static int Fact(int n) { Spec.Requires(n >= 0); Spec.Decreases(n); return n == 0 ? 1 : n * Fact(n - 1); }
    public static int UseMax(int x) { Spec.Ensures<int>(r => r == Max(x, 0)); return x > 0 ? x : 0; }
    public static void UnfoldsOnce() { Spec.Assert(Fact(3) == 6); }
    public static void OutsideTheDomain() { Spec.Assert(Fact(-1) == 1); }
    [GhostFunction] public static int Up(int n) { Spec.Decreases(n); return n <= 0 ? 0 : Up(n + 1); }
    [Pure] public static int NoMeasure(int n) => n <= 0 ? 0 : NoMeasure(n - 1);
    public static int CountDown(int n) { Spec.Requires(n >= 0); int i = n; while (i > 0) { Spec.Decreases(i); i--; } return i; }
    public static int Stuck(int n) { Spec.Requires(n >= 0); int i = n; while (i > 0) { Spec.Decreases(i); if (n > 5) i--; } return i; }
    public static bool Has(int[] a, int v) { Spec.Ensures<bool>(r => !r || Spec.Exists(0, a.Length, k => a[k] == v)); for (int i = 0; i < a.Length; i++) { Spec.Invariant(0 <= i && i <= a.Length); if (a[i] == v) return true; } return false; }
}";

        // (objects: fields as maps, constructors, instance methods, non-nullable fields and locals)
        private const string Objects = @"
public class Counter
{
    public int Count;
    public int[] Data = new int[4];
    public Counter(int start) { Spec.Requires(start >= 0); Spec.Ensures(Count == start); Count = start; }
    public void Inc() { Spec.Requires(Count < 100); Spec.Ensures(Count == Spec.Old(Count) + 1); Count++; }
    public int Get() { Spec.Ensures<int>(r => r == Count); return Count; }
    public void Overflow() { Count++; }
    public int First() { return Data[0]; }
}
public class Node
{
    public int Val;
    public Node? Next;
    public Node(int v) { Spec.Ensures(Val == v && Next == null); Val = v; }
}
public class Box
{
    public int[] Items;
    public int Size { get; set; }
    public Box(int n) { Spec.Requires(n >= 0); Spec.Ensures(Items.Length == n); Items = new int[n]; Size = n; }
}
public class Unset
{
    public int[] Items;
    public Unset(bool b) { if (b) Items = new int[1]; }
}
public class Plain { public int X; public int[] Ys = new int[2]; }
public static class O
{
    static int total;
    public static int UseCounter() { var c = new Counter(5); c.Inc(); Spec.Assert(c.Count == 6); return c.Get(); }
    public static void Alias(Counter a, Counter b) { Spec.Requires(a.Count < 10 && b.Count < 10); a.Inc(); Spec.Assert(b.Count < 11); }
    public static void AliasBad(Counter a, Counter b) { Spec.Requires(a.Count < 10 && b.Count < 10); int before = b.Count; a.Inc(); Spec.Assert(b.Count == before); }
    public static void Fresh(Counter a) { Spec.Requires(a.Count < 10); var c = new Counter(0); Spec.Assert(a.Count < 10 && c.Count == 0); }
    public static void Forgets(Counter a, Counter b) { Spec.Requires(b.Count < 10); var c = new Counter(0); c.Inc(); Spec.Assert(b.Count < 10); }
    public static int NextVal(Node n) { return n.Next.Val; }
    public static int NextValSafe(Node n) { if (n.Next == null) return 0; return n.Next.Val; }
    public static Node Cons(int v, Node? next) { var n = new Node(v); n.Next = next; Spec.Assert(n.Val == v); return n; }
    public static int Length(Box b) { return b.Items.Length; }
    public static int SizeOf(Box b) { Spec.Ensures<int>(r => r == b.Size); return b.Size; }
    public static void SetNull(Box b) { b.Items = null!; }
    public static int NullReceiver(Counter? c) { return c.Get(); }
    public static void Add(int x) { Spec.Requires(0 <= x && x <= 1000 && 0 <= total && total <= 1000); total += x; Spec.Assert(total >= x); }
    public static void LocalNull(int[]? a) { int[] b = a; }
    public static int Defaults() { var p = new Plain(); Spec.Assert(p.X == 0); return p.Ys.Length; }
    public static int FieldsSpec(Box b) { Spec.Requires(b.Items.Length > 0); return b.Items[0]; }
}";

        // (ownership: [Owned] classes, their invariants, views by value, by ref and out, Own.New and Own.Drop)
        private const string Ownership = @"
[Owned]
public sealed class Acct
{
    public int Balance;
    [Invariant, Pure] public bool Valid() => Balance >= 0;
    public Acct(int initial) { Spec.Requires(initial >= 0); Spec.Ensures(Balance == initial); Balance = initial; }
    public void Deposit(int amount) { Spec.Requires(amount >= 0); Spec.Ensures(Balance == Spec.Old(Balance) + amount); Balance = checked(Balance + amount); }
    public void Withdraw(int amount) { Spec.Requires(0 <= amount && amount <= Balance); Spec.Ensures(Balance == Spec.Old(Balance) - amount); Balance -= amount; }
    public void Overdraw() { Balance = -1; }
    [Pure] public int Get() => Balance;
}
public static class W
{
    public static void Transfer(Acct from, ref Own<Acct> fromView, Acct to, ref Own<Acct> toView, int amount)
    {
        Spec.Requires(fromView.Obj.Value == from && toView.Obj.Value == to);
        Spec.Requires(0 <= amount && amount <= from.Balance);
        Spec.Ensures(from.Balance == Spec.Old(from.Balance) - amount && to.Balance == Spec.Old(to.Balance) + amount);
        from.Withdraw(amount);
        to.Deposit(amount);
    }
    public static int Make()
    {
        Spec.Ensures((int r) => r == 6);
        var a = Own.New(new Acct(5), out var va);
        a.Deposit(1);
        int r = a.Balance;
        Own.Drop(va);
        return r;
    }
    public static void KeepsOther(Acct a, ref Own<Acct> va, Acct b)
    {
        Spec.Requires(va.Obj.Value == a);
        int before = b.Balance;
        a.Deposit(1);
        Spec.Assert(b.Balance == before || b == a);
    }
    public static void NoView(Acct a) { a.Deposit(1); }
    public static void Broken(Acct a, ref Own<Acct> va) { Spec.Requires(va.Obj.Value == a); a.Balance = -1; a.Deposit(0); a.Balance = 0; }
    public static void Consume(Acct a, Own<Acct> va) { Spec.Requires(va.Obj.Value == a); a.Deposit(1); Own.Drop(va); }
    public static void AfterConsume()
    {
        var a = Own.New(new Acct(0), out var va);
        Consume(a, va);
        a.Deposit(1);
    }
    public static Acct Open(out Own<Acct> v) { return Own.New(new Acct(0), out v); }
    public static void Unlinked() { var a = Open(out var va); a.Deposit(1); Own.Drop(va); }
    public static void BadMake() { var a = Own.New(new Acct(0), out var va); a.Balance = -5; Own.Drop(va); }
    public static int NonNegative(Acct a, ref Own<Acct> va) { Spec.Requires(va.Obj.Value == a); Spec.Ensures((int r) => r >= 0); return a.Get(); }
    public static void Twice(Acct a, ref Own<Acct> va, Acct b, ref Own<Acct> vb) { Spec.Requires(va.Obj.Value == a && vb.Obj.Value == b); Spec.Ensures(a != b); }
}";

        [Fact]
        public void Ownership_BothEnginesReportTheSame()
        {
            var (c, b) = Both(o => Engine.VerifySources(new[] { ("Test.cs", Harness.Usings + Ownership) }, o));
            var boogie = b.Methods.Where(m => m.Engine == "boogie").Select(m => m.Name).ToList();
            Assert.True(Agree(c, b) >= 18, "by Boogie: " + string.Join(", ", boogie));
            foreach (var bug in new[] { "Acct.Overdraw", "W.NoView", "W.Broken", "W.AfterConsume", "W.Unlinked" })
                Assert.False(b[bug].Verified, bug);
            foreach (var good in new[] { "Acct..ctor", "Acct.Deposit", "Acct.Withdraw", "Acct.Valid", "Acct.Get", "W.Transfer", "W.Make", "W.KeepsOther", "W.Consume", "W.Open", "W.NonNegative", "W.Twice", "W.BadMake" })
                Assert.True(b[good].Verified, good);
        }

        // (predicates, Viper style: Spec.Acc, instances, fold and unfold, permissions given and got by calls)
        private const string Predicates = @"
[Owned] public sealed class Cell { public int V; public Cell? Next; }
public static class P
{
    [Predicate] public static bool One(Cell c) => c != null && Spec.Acc(c) && c.V >= 0;
    [Predicate] public static bool Peeks(Cell c) => c != null && c.V > 0;
    public static void Set(Cell c, int v) { Spec.Requires(v >= 0 && One(c)); Spec.Ensures(One(c)); Spec.Unfold(One(c)); c.V = v; Spec.Fold(One(c)); }
    public static void SetBad(Cell c) { Spec.Requires(One(c)); Spec.Ensures(One(c)); Spec.Unfold(One(c)); c.V = -1; Spec.Fold(One(c)); }
    public static void Keep(Cell a, Cell b) { Spec.Requires(One(a) && Spec.Acc(b)); Spec.Ensures(One(a) && Spec.Acc(b)); int before = b.V; Set(a, 1); Spec.Assert(b.V == before); }
    public static void Twice(Cell a) { Spec.Requires(One(a)); Set(a, 1); Spec.Unfold(One(a)); Spec.Unfold(One(a)); }
    public static int Read(Cell a) { Spec.Requires(One(a)); Spec.Ensures((int r) => r >= 0); Spec.Unfold(One(a)); return a.V; }
    public static void NoAcc(Cell a) { Spec.Requires(a != null); Spec.Fold(One(a)); }
    public static void Folded(Cell a) { Spec.Requires(One(a)); a.V = 2; }
    public static void Given(Cell a) { Spec.Requires(Spec.Acc(a)); Spec.Ensures(Spec.Acc(a) && a.V == 3); a.V = 3; }
    public static void Lost(Cell a) { Spec.Requires(Spec.Acc(a)); Spec.Ensures(Spec.Acc(a)); Given(a); Given(a); }
}";

        [Fact]
        public void Predicates_BothEnginesReportTheSame()
        {
            var (c, b) = Both(o => Engine.VerifySources(new[] { ("Test.cs", Harness.Usings + Predicates) }, o));
            var boogie = b.Methods.Where(m => m.Engine == "boogie").Select(m => m.Name).ToList();
            Assert.True(Agree(c, b) >= 11, "by Boogie: " + string.Join(", ", boogie));
            foreach (var bug in new[] { "P.Peeks", "P.SetBad", "P.Twice", "P.NoAcc", "P.Folded" })
                Assert.False(b[bug].Verified, bug);
            foreach (var good in new[] { "P.One", "P.Set", "P.Keep", "P.Read", "P.Given", "P.Lost" })
                Assert.True(b[good].Verified, good);
        }

        // (inheritance: base classes, virtual and abstract members, overrides inheriting contracts, base(...))
        private const string Inheritance = @"
public abstract class Shape
{
    public int Sides;
    protected Shape(int sides) { Spec.Requires(sides >= 0); Spec.Ensures(Sides == sides); Sides = sides; }
    public abstract int Area();
}
[ContractClassFor(typeof(Shape))]
internal abstract class ShapeContract : Shape
{
    protected ShapeContract() : base(0) { }
    public override int Area() { Spec.Ensures<int>(r => r >= 0); return default; }
}
public class Square : Shape
{
    public int Side;
    public Square(int side) : base(4) { Spec.Requires(0 <= side && side <= 1000); Spec.Ensures(Side == side && Sides == 4); Side = side; }
    public override int Area() { return 0 <= Side && Side <= 1000 ? Side * Side : 0; }
}
public class Hole : Shape
{
    public Hole() : base(0) { }
    public override int Area() { return -1; }
}
public class Account
{
    public int Balance;
    public virtual void Deposit(int amount) { Spec.Requires(0 <= amount && amount <= 1000 && 0 <= Balance && Balance <= 1000000); Spec.Ensures(Balance == Spec.Old(Balance) + amount); Balance += amount; }
    public virtual int Fee() { Spec.Ensures<int>(r => r >= 0); return 0; }
}
public class Savings : Account
{
    public int Rate;
    public Savings(int rate) : base() { Spec.Requires(rate >= 0); Spec.Ensures(Rate == rate); Rate = rate; }
    public override void Deposit(int amount) { Balance += amount; }
    public override int Fee() { return 1; }
}
public class Greedy : Account
{
    public override void Deposit(int amount) { Balance += amount + 1; }
    public override int Fee() { return -1; }
}
public class Picky : Account
{
    public override void Deposit(int amount) { Spec.Requires(amount > 10 && Balance <= 1000000); Balance += amount; }
}
public interface ICounter { int Next(); }
[ContractClassFor(typeof(ICounter))]
internal abstract class CounterContract : ICounter { public int Next() { Spec.Ensures<int>(r => r > 0); return default; } }
public class One : ICounter { public int Next() { return 1; } }
public class Zero : ICounter { public int Next() { return 0; } }
public static class I
{
    public static int Ask(ICounter c) { Spec.Ensures<int>(r => r > 0); return c.Next(); }
    public static void Use(Account a) { Spec.Requires(a.Balance == 0); a.Deposit(5); Spec.Assert(a.Balance == 5); }
    public static int Charge(Account a) { Spec.Ensures<int>(r => r >= 0); return a.Fee(); }
    public static int Measure(Shape s) { Spec.Ensures<int>(r => r >= 0); return s.Area(); }
    public static void Forgets(Savings s) { Spec.Requires(s.Rate == 3 && s.Balance == 0); s.Deposit(2); Spec.Assert(s.Rate == 3); }
    public static int Build() { var q = new Square(3); Spec.Assert(q.Side == 3 && q.Sides == 4); return q.Side; }
}";

        private const string Higher = @"
public static class F
{
    public static int Sum(int[] a)
    {
        Spec.Requires(a.Length < 100 && Spec.Forall(0, a.Length, k => 0 <= a[k] && a[k] < 100));
        int s = 0;
        foreach (var x in a) { Spec.Invariant(0 <= s && s <= 100 * Spec.Index(x)); s += x; }
        return s;
    }
    public static int Count(string t) { int n = 0; foreach (char c in t) { Spec.Invariant(n == Spec.Index(c)); n++; } return n; }
    public static int BadInv(int[] a) { int s = 0; foreach (var x in a) { Spec.Invariant(s == Spec.Index(x) + 1); s++; } return s; }
    public static long Widen(int[] a) { Spec.Ensures<long>(r => r == (a.Length > 0 ? a[a.Length - 1] : 0)); long s = 0; foreach (long x in a) { Spec.Invariant(Spec.Index(x) == 0 ? s == 0 : s == a[Spec.Index(x) - 1]); s = x; } return s; }
    public static int Overflow(int[] a) { int s = 0; foreach (var x in a) s += x; return s; }
    public static int Skip(int[] a) { int s = 0; foreach (var x in a) { Spec.Invariant(0 <= s && s <= Spec.Index(x)); if (x < 0) continue; s++; } return s; }
    public static int Upto(string t) { Spec.Ensures<int>(r => 0 <= r && r <= t.Length); int n = 0; foreach (var c in t) { Spec.Invariant(n == Spec.Index(c)); if (c == ' ') break; n++; } return n; }
}
public static class D
{
    public static int Apply(Func<int, int> f, int x) { Spec.Requires(Spec.Pre(f, x)); Spec.Ensures<int>(r => Spec.Post(f, x, r)); return f(x); }
    public static int NoPre(Func<int, int> f) => f(1);
    public static int ApplyAll(Func<int, int> f) { Spec.Requires(Spec.Total(f)); return f(3) + 0 * f(4); }
    public static void UseValue() { int y = Apply(x => x + 1, 1); Spec.Assert(y == 2); }
    public static void UseValueBad() { int y = Apply(x => x + 1, 1); Spec.Assert(y == 3); }
    public static void Needs() { int y = Apply(x => { Spec.Requires(x > 5); return x; }, 1); }
    public static void NeedsOk() { int y = Apply(x => { Spec.Requires(x > 0); Spec.Ensures<int>(r => r == x); return x; }, 1); Spec.Assert(y == 1); }
    public static void Captured(int k) { Spec.Requires(k >= 0 && k < 100); int y = Apply(x => x + k, 1); Spec.Assert(y == 1 + k); }
    public static void Keeps(int[] a, Func<int, int> f) { Spec.Requires(a.Length == 1 && Spec.Pre(f, 0) && Spec.ChangesNothing(f)); a[0] = 5; f(0); Spec.Assert(a[0] == 5); }
    public static void Loses(int[] a, Func<int, int> f) { Spec.Requires(a.Length == 1 && Spec.Pre(f, 0)); a[0] = 5; f(0); Spec.Assert(a[0] == 5); }
    public static void Act(Action<int> g) { Spec.Requires(Spec.Total(g)); g(1); }
    public static void UseAct() { Act(x => { }); }
    public static void TotalBad() { int y = ApplyAll(x => { Spec.Requires(x != 4); return x; }); }
}";

        private const string Delegates = @"public delegate int Pricing(int q);
[ContractClassFor(typeof(Pricing))]
internal abstract class PricingContract { public int Invoke(int q) { Spec.Requires(0 <= q && q <= 1000); Spec.Ensures<int>(r => 0 <= r && r <= 100 * q); return default; } }
public static class Mg
{
    public static int Apply(Func<int, int> f, int x) { Spec.Requires(Spec.Pre(f, x)); Spec.Ensures<int>(r => Spec.Post(f, x, r)); return f(x); }
    public static int Inc(int x) { Spec.Requires(x < 100); Spec.Ensures<int>(r => r == x + 1); return x + 1; }
    [Pure] public static int Twice(int x) { Spec.Requires(x >= 0 && x < 1000); Spec.Ensures<int>(r => r == 2 * x); return 2 * x; }
    public static void UseInc() { int y = Apply(Inc, 5); Spec.Assert(y == 6); }
    public static void UseIncBad() { int y = Apply(Inc, 500); }
    public static void UseTwice() { int y = Apply(Twice, 4); Spec.Assert(y == 8); }
    public static int Quote(Pricing p, int q) { Spec.Requires(0 <= q && q <= 1000); Spec.Ensures<int>(r => 5 <= r && r <= 100005); return p(q) + 5; }
    public static int QuoteBad(Pricing p, int q) { Spec.Requires(0 <= q && q <= 2000); return p(q); }
    public static int QuoteWrong(Pricing p) { Spec.Ensures<int>(r => r <= 50); return p(1); }
    public static int MakeAndQuote() { Pricing p = q => 100 * q; return Quote(p, 3); }
}
public sealed class Cell { public int V; }
public static class Rd
{
    public static bool Ask(Cell c, Cell other, Func<Cell, bool> rule)
    {
        Spec.Requires(c != other && Spec.Pre(rule, c) && Spec.ReadsOf(rule, c).IsSubsetOf(ObjSet.Of(c)));
        other.V = 1;
        return rule(c);
    }
    public static bool AskBad(Cell c, Func<Cell, bool> rule)
    {
        Spec.Requires(Spec.Pre(rule, c) && Spec.ReadsOf(rule, c).IsSubsetOf(ObjSet.Of(c)));
        c.V = 1;
        return rule(c);
    }
    public static int Probe(Cell c, Cell d, Func<int, int> g)
    {
        Spec.Requires(c != d && Spec.Pre(g, 0) && Spec.Reads(g, x => ObjSet.Of(c)));
        d.V = 3;
        return g(0);
    }
    public static int ProbeBad(Cell c, Func<int, int> g)
    {
        Spec.Requires(Spec.Pre(g, 0) && Spec.Reads(g, x => ObjSet.Of(c)));
        c.V = 3;
        return g(0);
    }
    public static bool UseAsk(Cell c, Cell other)
    {
        Spec.Requires(c != other);
        c.V = 5;
        return Ask(c, other, x => { Spec.Reads(ObjSet.Of(x)); Spec.Requires(x.V > 0); return x.V > 1; });
    }
    public static bool NoFrame(Cell c, Cell other)
    {
        Spec.Requires(c != other);
        c.V = 5;
        return Ask(c, other, x => { Spec.Requires(x.V > 0); return true; });
    }
    public static bool OutOfFrame(Cell c, Cell other)
    {
        Spec.Requires(c != other);
        c.V = 5; other.V = 1;
        return Ask(c, other, x => { Spec.Reads(ObjSet.Of(x)); Spec.Requires(x.V > 0 && other.V > 0); return true; });
    }
    public static int Apply(Func<int, int> f, int x) { Spec.Requires(Spec.Pre(f, x)); return f(x); }
    public static int PassReading(Cell c, Func<int, int> g)
    {
        Spec.Requires(Spec.Pre(g, 0) && Spec.Reads(g, x => ObjSet.Of(c)));
        return Apply(g, 0);
    }
    public static void Touch(Cell a, Cell b, Func<Cell, int> g)
    {
        Spec.Requires(a != b && a.V == 1 && b.V == 2 && Spec.Total(g) && Spec.Changes(g, x => ObjSet.Of(x)));
        g(a);
        Spec.Assert(b.V == 2);
    }
    public static void TouchBad(Cell a, Cell b, Func<Cell, int> g)
    {
        Spec.Requires(a != b && a.V == 1 && Spec.Total(g) && Spec.Changes(g, x => ObjSet.Of(x)));
        g(a);
        Spec.Assert(a.V == 1);
    }
    public static void Run(Action<int> g) { Spec.Requires(Spec.Total(g)); g(1); }
    public static void Sums()
    {
        int s = 0;
        Action<int> add = x => { s = 7; };
        Spec.Assert(s == 0);
        Run(add);
        Spec.Assert(s == 0);
    }
}
";

        [Fact]
        public void DelegatesThatReadState_BothEnginesReportTheSame()
        {
            var (c, b) = Both(o => Engine.VerifySources(new[] { ("Test.cs", Harness.Usings + Delegates) }, o));
            var boogie = b.Methods.Where(m => m.Engine == "boogie").Select(m => m.Name).ToList();
            Assert.Equal(23, Agree(c, b));
            foreach (var bug in new[] { "Mg.UseIncBad", "Mg.QuoteBad", "Mg.QuoteWrong", "Rd.AskBad", "Rd.ProbeBad", "Rd.NoFrame", "Rd.OutOfFrame", "Rd.PassReading", "Rd.TouchBad", "Rd.Sums" })
                Assert.False(b[bug].Verified, bug);
            foreach (var good in new[] { "Mg.UseInc", "Mg.UseTwice", "Mg.Quote", "Mg.MakeAndQuote", "Rd.Ask", "Rd.Probe", "Rd.UseAsk", "Rd.Touch", "Rd.Run" })
                Assert.True(b[good].Verified, good);
        }

        private const string Lists = @"using System.Collections.Generic; using CsVerify.Bcl;
public sealed class Item { public int V; }
public static class Ls
{
    public static int Sum(List<int> l)
    {
        Spec.Requires(l.Count <= 1000 && Spec.Forall(0, l.Count, i => 0 <= l[i] && l[i] <= 100));
        Spec.Ensures<int>(r => 0 <= r && r <= 100 * l.Count);
        int s = 0;
        foreach (int x in l) { Spec.Invariant(0 <= s && s <= 100 * Spec.Index(x)); s += x; }
        return s;
    }
    public static int SumBad(List<int> l)
    {
        int s = 0;
        foreach (int x in l) s += x;
        return s;
    }
    public static int First(List<int> l) { Spec.Requires(l.Count > 0); return l[0]; }
    public static int FirstBad(List<int> l) => l[0];
    public static void Grow(List<int> l) { Spec.Ensures(l.Count == Spec.Old(l.Count) + 1); l.Add(3); }
    public static void GrowBad(List<int> l) { Spec.Ensures(l.Count == Spec.Old(l.Count)); l.Add(3); }
    public static int Fresh() { var l = new List<int>(); l.Add(4); l.Add(5); Spec.Assert(l.Count == 2 && l[1] == 5); return l[0]; }
    public static void Keeps(List<int> a, List<int> b) { Spec.Requires(a != b && b.Count == 1); a.Add(1); Spec.Assert(b.Count == 1); }
    public static void Loses(List<int> a, List<int> b) { Spec.Requires(b.Count == 1); a.Add(1); Spec.Assert(b.Count == 1); }
    public static bool Has(List<int> l) { Spec.Requires(l.Count == 1 && l[0] == 7); return l.Contains(7); }
    public static void Set(List<int> l) { Spec.Requires(l.Count == 2); l[1] = 9; Spec.Assert(l[1] == 9 && l.Count == 2); }
    public static void Items(List<int> l) { Spec.Requires(l.Size() == 2); l.Add(1); Spec.Assert(l.Items()[2] == Ghost.Of(1)); }
    public static int Objs(List<Item> l) { Spec.Requires(l.Count > 0 && l[0] != null); return l[0].V; }
    public static int WfBad(List<int> l) { Spec.Requires(l[0] > 0); return 0; }
    public static int Mutates(List<int> l) { int s = 0; foreach (var x in l) { l.Add(1); s = x; } return s; }
}
";

        [Fact]
        public void Lists_BothEnginesReportTheSame()
        {
            var (c, b) = Both(o => Engine.VerifySources(new[] { ("Test.cs", Harness.Usings + Lists) }, o));
            Assert.Equal(15, Agree(c, b));
            foreach (var bug in new[] { "Ls.SumBad", "Ls.FirstBad", "Ls.GrowBad", "Ls.Loses", "Ls.WfBad", "Ls.Mutates" })
                Assert.False(b[bug].Verified, bug);
            foreach (var good in new[] { "Ls.Sum", "Ls.First", "Ls.Grow", "Ls.Fresh", "Ls.Keeps", "Ls.Has", "Ls.Set", "Ls.Items", "Ls.Objs" })
                Assert.True(b[good].Verified, good);
        }

        private const string Finally = @"public sealed class Res : IDisposable
{
    public bool Open;
    public Res() { Spec.Ensures(Open); Open = true; }
    public void Dispose() { Spec.Ensures(!Open); Open = false; }
}
public static class Fin
{
    public static int Digit(char c)
    {
        Spec.Ensures((int r) => 0 <= r && r <= 9);
        Spec.EnsuresOnThrow<ArgumentException>(true);
        if (c < '0' || c > '9') throw new ArgumentException(""x"");
        return c - '0';
    }
    public static int Marks(bool[] done, char c)
    {
        Spec.Requires(done.Length == 1);
        Spec.Ensures((int r) => done[0]);
        Spec.EnsuresOnThrow<Exception>(done[0]);
        done[0] = false;
        try { return Digit(c); }
        finally { done[0] = true; }
    }
    public static int Forgets(bool[] done, char c)
    {
        Spec.Requires(done.Length == 1);
        Spec.EnsuresOnThrow<Exception>(done[0]);
        done[0] = false;
        try { return Digit(c); }
        finally { done[0] = done[0]; }
    }
    public static int Undoes(int[] a)
    {
        Spec.Requires(a.Length == 1);
        Spec.Ensures((int r) => a[0] == 1);
        try { a[0] = 1; return 3; }
        finally { a[0] = 2; }
    }
    public static int Nested(int[] a, char c)
    {
        Spec.Requires(a.Length == 2);
        Spec.Ensures((int r) => a[0] == 1 && a[1] == 1);
        try
        {
            try { return Digit(c); }
            catch (ArgumentException) { return -1; }
            finally { a[0] = 1; }
        }
        finally { a[1] = 1; }
    }
    public static int Loop(int[] a)
    {
        Spec.Requires(a.Length == 1);
        Spec.Ensures((int r) => a[0] == 7);
        int i = 0;
        while (i < 10)
        {
            Spec.Invariant(0 <= i && i <= 10);
            try { if (i == 5) break; i++; }
            finally { a[0] = 7; }
        }
        a[0] = 7;
        return i;
    }
    public static int ResultKept()
    {
        Spec.Ensures((int r) => r == 1);
        int x = 1;
        try { return x; }
        finally { x = 2; }
    }
    public static bool Uses()
    {
        Spec.Ensures((bool r) => r);
        var r = new Res();
        bool was;
        using (r) { was = r.Open; }
        return was && !r.Open;
    }
    public static bool UsesBad()
    {
        Spec.Ensures((bool r) => r);
        var r = new Res();
        using (r) { }
        return r.Open;
    }
    public static int UsingVar()
    {
        using var r = new Res();
        Spec.Assert(r.Open);
        return 1;
    }
}
";

        [Fact]
        public void FinallyAndUsing_BothEnginesReportTheSame()
        {
            var (c, b) = Both(o => Engine.VerifySources(new[] { ("Test.cs", Harness.Usings + Finally) }, o));
            Assert.Equal(12, Agree(c, b));
            foreach (var bug in new[] { "Fin.Forgets", "Fin.Undoes", "Fin.Uses", "Fin.UsesBad" })
                Assert.False(b[bug].Verified, bug);
            foreach (var good in new[] { "Fin.Digit", "Fin.Marks", "Fin.Nested", "Fin.Loop", "Fin.ResultKept", "Fin.UsingVar", "Res..ctor" })
                Assert.True(b[good].Verified, good);
        }

        private const string Dictionaries = @"using System.Collections.Generic; using CsVerify.Bcl;
public sealed class Key { public int V; }
public static class Dc
{
    public static int Get(Dictionary<int, int> d) { Spec.Requires(d.ContainsKey(3)); return d[3]; }
    public static int GetBad(Dictionary<int, int> d) => d[3];
    public static void Put(Dictionary<int, int> d) { d[1] = 5; Spec.Assert(d.ContainsKey(1) && d[1] == 5); }
    public static void PutBad(Dictionary<int, int> d) { d[1] = 5; Spec.Assert(d[1] == 6); }
    public static void Adds(Dictionary<int, int> d) { Spec.Requires(!d.ContainsKey(2)); d.Add(2, 7); Spec.Assert(d.Count == Spec.Old(d.Count) + 1); }
    public static void AddsBad(Dictionary<int, int> d) { d.Add(2, 7); }
    public static int Fresh() { var d = new Dictionary<int, int>(); d[4] = 9; Spec.Assert(d.Count == 1); return d[4]; }
    public static bool Tries(Dictionary<int, int> d) { Spec.Requires(d.ContainsKey(8) && d[8] == 1); int v; bool ok = d.TryGetValue(8, out v); Spec.Assert(ok && v == 1); return ok; }
    public static void Removes(Dictionary<int, int> d) { Spec.Requires(d.ContainsKey(1)); bool r = d.Remove(1); Spec.Assert(r && !d.ContainsKey(1)); }
    public static void Keeps(Dictionary<int, int> a, Dictionary<int, int> b) { Spec.Requires(a != b && b.ContainsKey(1)); a[1] = 2; Spec.Assert(b.ContainsKey(1)); }
    public static int Sum(Dictionary<int, int> d)
    {
        int s = 0;
        foreach (var kv in d) { Spec.Assert(d.ContainsKey(kv.Key) && d[kv.Key] == kv.Value); s = kv.Value; }
        return s;
    }
    public static void Writes(Dictionary<int, int> d)
    {
        foreach (var kv in d) { d[kv.Key + 1] = 0; }
    }
    public static void SetHas(HashSet<int> s) { s.Add(3); Spec.Assert(s.Contains(3) && s.Members()[3].Value); }
    public static void SetBad(HashSet<int> s) { s.Remove(3); Spec.Assert(s.Contains(3)); }
    public static int SetCount() { var s = new HashSet<Key>(); var k = new Key(); s.Add(k); s.Add(k); Spec.Assert(s.Count == 1); return s.Count; }
    public static int SetLoop(HashSet<int> s) { int n = 0; foreach (var x in s) { n = x; } return n; }
    public static int SetLoopBad(HashSet<int> s) { int n = 0; foreach (var x in s) { s.Add(x + 1); } return n; }
    public static void Stacks(Stack<int> st) { st.Push(4); Spec.Assert(st.Count >= 1); }
}
";

        [Fact]
        public void DictionariesAndSets_BothEnginesReportTheSame()
        {
            var (c, b) = Both(o => Engine.VerifySources(new[] { ("Test.cs", Harness.Usings + Dictionaries) }, o));
            Assert.Equal(18, Agree(c, b));
            foreach (var bug in new[] { "Dc.GetBad", "Dc.PutBad", "Dc.AddsBad", "Dc.Writes", "Dc.SetBad", "Dc.SetLoopBad" })
                Assert.False(b[bug].Verified, bug);
            foreach (var good in new[] { "Dc.Get", "Dc.Put", "Dc.Adds", "Dc.Fresh", "Dc.Tries", "Dc.Removes", "Dc.Keeps", "Dc.Sum", "Dc.SetHas", "Dc.SetCount", "Dc.SetLoop", "Dc.Stacks" })
                Assert.True(b[good].Verified, good);
        }

        private const string Concurrency = @"using System.Threading.Tasks;
public sealed class Counter { public int N; }
public sealed class Account
{
    private readonly object _lock = new object();
    [GuardedBy(nameof(_lock))] private int _balance;
    [LockInvariant(nameof(_lock)), Pure] private bool Valid() => _balance >= 0;
    public Account() { }
    public int Balance() { Spec.Ensures<int>(r => r >= 0); lock (_lock) { return _balance; } }
    public void Deposit(int x) { Spec.Requires(x >= 0); lock (_lock) { _balance = _balance <= int.MaxValue - x ? _balance + x : _balance; } }
    public void Breaks() { lock (_lock) { _balance = -1; } }
    public void Reset() { _balance = 0; }
    public int Forgets() { lock (_lock) { _balance = 5; } lock (_lock) { return _balance == 5 ? 1 : 0; } }
    public void Twice() { lock (_lock) { _balance = 3; Spec.Assert(_balance == 3); } }
    public void TwiceBad() { lock (_lock) { _balance = 3; } lock (_lock) { Spec.Assert(_balance == 3); } }
}
public static class As
{
    public static async Task<int> Double(int x) { Spec.Requires(0 <= x && x < 1000); Spec.Ensures<int>(r => r == 2 * x); await Task.Yield(); return 2 * x; }
    public static async Task<int> Use() { Spec.Ensures<int>(r => r == 8); int y = await Double(4); return y; }
    public static async Task<int> UseBad() { Spec.Ensures<int>(r => r == 9); return await Double(4); }
    public static async Task<int> Pre() { return await Double(5000); }
    public static async Task Keeps() { var c = new Counter(); c.N = 1; await Task.Yield(); Spec.Assert(c.N == 1); }
    public static async Task Loses(Counter c) { c.N = 1; await Task.Yield(); Spec.Assert(c.N == 1); }
    public static async Task Arrays(int[] a) { Spec.Requires(a.Length == 1); a[0] = 2; await Task.Delay(1); Spec.Assert(a[0] == 2); }
    public static async Task<int> Loop(int n) { Spec.Requires(n >= 0); int i = 0; while (i < n) { Spec.Invariant(0 <= i && i <= n); await Task.Yield(); i++; } return i; }
    public static async Task Config() { await Task.Delay(1).ConfigureAwait(false); }
    public static async Task<int> Overflow(int x) { await Task.Yield(); return x + 1; }
}
";

        [Fact]
        public void AsyncAndLocks_BothEnginesReportTheSame()
        {
            var (c, b) = Both(o => Engine.VerifySources(new[] { ("Test.cs", Harness.Usings + Concurrency) }, o));
            Assert.Equal(19, Agree(c, b));
            foreach (var bug in new[] { "Account.Breaks", "Account.Reset", "Account.TwiceBad", "As.UseBad", "As.Pre", "As.Loses", "As.Arrays", "As.Overflow" })
                Assert.False(b[bug].Verified, bug);
            foreach (var good in new[] { "Account..ctor", "Account.Balance", "Account.Deposit", "Account.Twice", "Account.Forgets", "As.Double", "As.Use", "As.Keeps", "As.Loop", "As.Config" })
                Assert.True(b[good].Verified, good);
        }

        private const string Tasks = @"using System.Threading; using System.Threading.Tasks;
public sealed class Box { public int V; }
public static class Tk
{
    public static async Task<int> Twice(int x) { Spec.Requires(0 <= x && x < 1000); Spec.Ensures<int>(r => r == 2 * x); await Task.Yield(); return 2 * x; }
    public static async Task<int> Both() { Spec.Ensures<int>(r => r == 10); var a = Twice(2); var b = Twice(3); await Task.WhenAll(a, b); return a.Result + b.Result; }
    public static async Task<int> Later() { Spec.Ensures<int>(r => r == 8); var t = Twice(4); int k = 1; int y = await t; return y * k; }
    public static async Task<int> LaterBad() { Spec.Ensures<int>(r => r == 9); var t = Twice(4); return await t; }
    public static async Task Lost(bool w) { var t = Twice(1); if (w) await t; }
    public static async Task<int> Early() { var t = Twice(1); int x = t.Result; await t; return x; }
    public static async Task Shared(Box b) { b.V = 1; var t = Twice(1); Spec.Assert(b.V == 1); await t; }
    public static async Task Mine() { var b = new Box(); b.V = 1; var t = Twice(1); Spec.Assert(b.V == 1); await t; }
    public static async Task<int> PreBad() { var t = Twice(5000); return await t; }
}
public sealed class Cell { public int V; }
public static class Th
{
    [RunsConcurrently] public static int Work(int x) { Spec.Requires(x >= 0 && x < 100); Spec.Ensures<int>(r => r == x + 1); return x + 1; }
    public static async Task<int> Run() { Spec.Ensures<int>(r => r == 4); var t = Task.Run(() => Work(3)); return await t; }
    public static async Task<int> RunBad() { var t = Task.Run(() => Work(300)); return await t; }
    public static async Task Lambda() { var t = Task.Run(() => { int y = 0; y++; }); await t; }
    public static void Threads() { var th = new Thread(() => Work(1)); th.Start(); th.Join(); }
    public static void ThreadsBad() { var th = new Thread(() => Work(500)); th.Start(); th.Join(); }
    public static async Task Shared(Cell c) { c.V = 1; var t = Task.Run(() => Work(1)); Spec.Assert(c.V == 1); await t; }
    public static async Task Mine() { var c = new Cell(); c.V = 1; var t = Task.Run(() => Work(1)); Spec.Assert(c.V == 1); await t; }
}
";

        [Fact]
        public void TasksAndThreads_BothEnginesReportTheSame()
        {
            var (c, b) = Both(o => Engine.VerifySources(new[] { ("Test.cs", Harness.Usings + Tasks) }, o));
            Assert.Equal(17, Agree(c, b));
            foreach (var bug in new[] { "Tk.LaterBad", "Tk.Lost", "Tk.Early", "Tk.Shared", "Tk.PreBad", "Tk.Both", "Th.Run", "Th.Shared", "Th.Mine" })
                Assert.False(b[bug].Verified, bug);
            foreach (var good in new[] { "Tk.Twice", "Tk.Later", "Tk.Mine", "Th.Work", "Th.Lambda", "Th.Threads" })
                Assert.True(b[good].Verified, good);
        }

        private const string TaskPermissions = @"using System.Threading; using System.Threading.Tasks;
public static class Pw
{
    [RunsConcurrently]
    public static void Part(int[] a, int lo, int hi)
    {
        Spec.Requires(0 <= lo && lo <= hi && hi <= a.Length && Spec.Acc(a, lo, hi));
        Spec.Ensures(Spec.Acc(a, lo, hi) && Spec.Forall(lo, hi, i => a[i] == 1));
        for (int k = lo; k < hi; k++) { Spec.Invariant(lo <= k && k <= hi && Spec.Acc(a, lo, hi) && Spec.Forall(lo, k, i => a[i] == 1)); a[k] = 1; }
    }
    public static async Task Halves(int[] a)
    {
        Spec.Requires(Spec.Acc(a));
        Spec.Ensures(Spec.Acc(a) && Spec.Forall(0, a.Length, i => a[i] == 1));
        int mid = a.Length / 2;
        var l = Task.Run(() => Part(a, 0, mid));
        var r = Task.Run(() => Part(a, mid, a.Length));
        await l; await r;
    }
    public static async Task Early(int[] a)
    {
        Spec.Requires(Spec.Acc(a) && a.Length > 2);
        var l = Task.Run(() => Part(a, 0, a.Length));
        a[0] = 2;
        await l;
    }
    public static async Task Bad(int[] a)
    {
        Spec.Requires(Spec.Acc(a));
        var l = Task.Run(() => Part(a, 0, a.Length + 1));
        await l;
    }
    public static void Threads(int[] a)
    {
        Spec.Requires(Spec.Acc(a));
        Spec.Ensures(Spec.Acc(a) && Spec.Forall(0, a.Length, i => a[i] == 1));
        var t = new Thread(() => Part(a, 0, a.Length));
        t.Start();
        t.Join();
    }
}
";

        [Fact]
        public void TasksWithPermissions_BothEnginesReportTheSame()
        {
            // a task's start gives its callee's permissions, its join takes back what it gives
            var (c, b) = Both(o => { if (o.Engine == "boogie") o.TimeoutMs = 60000; return Engine.VerifySources(new[] { ("Test.cs", Harness.Usings + TaskPermissions) }, o); });
            Assert.True(Agree(c, b) >= 4, "agreeing: " + Agree(c, b));
            foreach (var good in new[] { "Pw.Part", "Pw.Halves", "Pw.Threads" })
                Assert.True(b[good].Verified, good);
            Assert.False(b["Pw.Bad"].Verified);
        }

        [Fact]
        public void ForEachAndDelegates_BothEnginesReportTheSame()
        {
            var (c, b) = Both(o => Engine.VerifySources(new[] { ("Test.cs", Harness.Usings + Higher) }, o));
            var boogie = b.Methods.Where(m => m.Engine == "boogie").Select(m => m.Name).ToList();
            Assert.Equal(20, Agree(c, b));
            foreach (var bug in new[] { "F.BadInv", "F.Overflow", "D.NoPre", "D.UseValueBad", "D.Needs", "D.Loses", "D.TotalBad" })
                Assert.False(b[bug].Verified, bug);
            foreach (var good in new[] { "F.Sum", "F.Count", "F.Widen", "F.Skip", "F.Upto", "D.Apply", "D.ApplyAll", "D.UseValue", "D.NeedsOk", "D.Captured", "D.Keeps", "D.Act", "D.UseAct" })
                Assert.True(b[good].Verified, good);
        }

        [Fact]
        public void Inheritance_BothEnginesReportTheSame()
        {
            var (c, b) = Both(o => Engine.VerifySources(new[] { ("Test.cs", Harness.Usings + Inheritance) }, o));
            var boogie = b.Methods.Where(m => m.Engine == "boogie").Select(m => m.Name).ToList();
            Assert.True(Agree(c, b) >= 17, "by Boogie: " + string.Join(", ", boogie));
            foreach (var bug in new[] { "Hole.Area", "Greedy.Deposit", "Greedy.Fee", "Picky.Deposit", "I.Forgets", "Zero.Next" })
                Assert.False(b[bug].Verified, bug);
            foreach (var good in new[] { "Shape..ctor", "Square..ctor", "Square.Area", "Account.Deposit", "Account.Fee", "Savings..ctor", "Savings.Deposit", "Savings.Fee", "I.Use", "I.Charge", "I.Measure", "I.Build", "One.Next", "I.Ask" })
                Assert.True(b[good].Verified, good);
        }

        [Fact]
        public void Objects_BothEnginesReportTheSame()
        {
            var (c, b) = Both(o => Engine.VerifySources(new[] { ("Test.cs", Harness.Usings + Objects) }, o));
            var boogie = b.Methods.Where(m => m.Engine == "boogie").Select(m => m.Name).ToList();
            Assert.True(Agree(c, b) >= 20, "by Boogie: " + string.Join(", ", boogie));
            foreach (var bug in new[] { "Counter.Overflow", "Counter.First", "Unset..ctor", "O.AliasBad", "O.Alias", "O.Forgets", "O.NextVal", "O.SetNull", "O.NullReceiver", "O.LocalNull" })
                Assert.False(b[bug].Verified, bug);
            foreach (var good in new[] { "Counter..ctor", "Counter.Inc", "Counter.Get", "Node..ctor", "Box..ctor", "O.UseCounter", "O.Fresh",
                                         "O.NextValSafe", "O.Cons", "O.Length", "O.SizeOf", "O.Add", "O.Defaults", "O.FieldsSpec" })
                Assert.True(b[good].Verified, good);
        }

        private static (VerificationResult csverify, VerificationResult boogie) Both(System.Func<VerifierOptions, VerificationResult> run)
        {
            var c = run(new VerifierOptions());
            var b = run(new VerifierOptions { Engine = "boogie" });
            return (c, b);
        }

        private static string[] Reported(MethodResult m) =>
            m.Diagnostics.Where(d => d.IsError).Select(d => d.Id + "@" + d.Line).OrderBy(x => x).ToArray();

        /// <summary>Each method Boogie verified reports what CsVerify's engine reports for it.</summary>
        private static int Agree(VerificationResult csverify, VerificationResult boogie)
        {
            int byBoogie = 0;
            foreach (var m in boogie.Methods.Where(m => m.Engine == "boogie"))
            {
                byBoogie++;
                var other = csverify.Methods.Single(x => x.Name == m.Name && x.Declared == m.Declared);
                Assert.True(Reported(other).SequenceEqual(Reported(m)),
                    $"{m.Name}: CsVerify's engine reports [{string.Join(", ", Reported(other))}], Boogie [{string.Join(", ", Reported(m))}]\n" +
                    string.Join("\n", m.Diagnostics.Concat(other.Diagnostics)));
            }
            return byBoogie;
        }

        [Fact]
        public void Corpus_BothEnginesReportTheSame()
        {
            var (c, b) = Both(o => Engine.VerifySources(new[] { ("Test.cs", Harness.Usings + Corpus) }, o));
            Assert.Equal(40, Agree(c, b));
            foreach (var bug in new[] { "UseAbs", "Overflows", "Div", "Assertion", "BadInv", "BadPost", "FirstBad", "KeepsOwn", "WfBad", "CallNull",
                                        "Low", "TwiceU", "Neg", "UnfoldsOnce", "OutsideTheDomain", "Up", "NoMeasure", "Stuck" })
                Assert.False(b["A." + bug].Verified, bug);
            foreach (var good in new[] { "Abs", "Sum", "Wide", "Twice", "UseAbsSafely", "Between", "Checked", "Truncates", "Remainder", "Fill", "First", "Wraps", "Read", "Make", "Has",
                                         "Digit", "LowChecked", "LowWraps", "Max", "Fact", "UseMax", "CountDown" })
                Assert.True(b["A." + good].Verified, good);
        }

        [Fact]
        public void Exceptions_AreBoogies()
        {
            // throw, try/catch by type, rethrow, checked overflow caught, EnsuresOnThrow: by Boogie, as CsVerify's engine says
            var root = Harness.RepoRoot();
            var files = new[] { Path.Combine(root, "samples", "Good", "Exceptions.cs"), Path.Combine(root, "samples", "Buggy", "ExceptionBugs.cs") };
            var b = Engine.VerifyFiles(files, new VerifierOptions { Engine = "boogie-only", TimeoutMs = 120000 });
            var only = new VerifierOptions();
            only.Only.AddRange(b.Methods.Select(m => m.Name));
            var c = Engine.VerifyFiles(files, only);
            Assert.Equal(11, Agree(c, b));
            foreach (var good in new[] { "Digit", "DigitOrMinusOne", "SaturatingSum", "Update", "Guarded" })
                Assert.True(b["ExceptionSamples." + good].Verified, good);
            foreach (var bug in new[] { "AtLeastOne", "NoRollback", "WrongKind", "ThrowsNull" })
                Assert.False(b["ExceptionBugs." + bug].Verified, bug);
        }

        [Fact]
        public void DataTypesAndGenerics_AreBoogies()
        {
            // records as data types (patterns, switches, casts, ranks, invariants), generic data and generic methods
            var root = Harness.RepoRoot();
            var files = new[] { Path.Combine(root, "samples", "Good", "DataTypes.cs"), Path.Combine(root, "samples", "Buggy", "DataBugs.cs") };
            var b = Engine.VerifyFiles(files, new VerifierOptions { Engine = "boogie-only", TimeoutMs = 120000 });
            var only = new VerifierOptions();
            only.Only.AddRange(b.Methods.Select(m => m.Name));
            var c = Engine.VerifyFiles(files, only);
            Assert.True(Agree(c, b) >= 28, "agreeing: " + Agree(c, b));
            foreach (var good in new[] { "DataTypes.Length", "DataTypes.AppendLength", "DataTypes.ReverseLength", "DataTypes.ReversedCount", "DataTypes.Evaluate",
                                         "DataTypes.FoldPreservesEval", "DataTypes.FactIsFunctional", "DataTypes.Factorial", "DataTypes.Widen", "DataTypes.Demo", "Interval.Width" })
                Assert.True(b[good].Verified, good);
            foreach (var bug in new[] { "DataBugs.Key", "DataBugs.Size", "DataBugs.FoldPreservesEval", "DataBugs.Factorial", "DataBugs.Backwards" })
                Assert.False(b[bug].Verified, bug);
        }

        [Fact]
        public void LockLevelsAndAtomics_AreBoogies()
        {
            // locks in order of levels and ids (through calls too), semaphores above them, atomic fields by their steps
            var root = Harness.RepoRoot();
            var files = new[] { "Good/LockLevels.cs", "Buggy/LockLevelBugs.cs", "Good/AtomicFields.cs", "Buggy/AtomicBugs.cs" }
                .Select(f => Path.Combine(root, "samples", f)).ToArray();
            var b = Engine.VerifyFiles(files, new VerifierOptions { Engine = "boogie-only", TimeoutMs = 120000 });
            var only = new VerifierOptions();
            only.Only.AddRange(b.Methods.Select(m => m.Name));
            var c = Engine.VerifyFiles(files, only);
            Assert.True(Agree(c, b) >= 30, "agreeing: " + Agree(c, b));
            foreach (var good in new[] { "Bank.Transfer", "Bank.Sweep", "AuditLog.WriteAsync", "Stats.Hit", "Stats.Observe", "Stats.Configuration", "Stats.Use" })
                Assert.True(b[good].Verified, good);
            foreach (var bug in new[] { "LevelBugs.Transfer", "Counter.LostUpdate", "Counter.Wraps", "Counter.TwoReads", "Counter.Torn" })
                Assert.False(b[bug].Verified, bug);
        }

        [Fact]
        public void OwnershipTrees_AreBoogies()
        {
            // [Owns] fields: Own.Take splits a tree, Own.Give joins one; a call's frame is the trees it doesn't own
            var root = Harness.RepoRoot();
            var files = new[] { "Good/OwnedList.cs", "Good/AtsViewtypes.cs", "Buggy/TreeOwnershipBugs.cs", "Buggy/ViewtypeBugs.cs" }
                .Select(f => Path.Combine(root, "samples", f)).ToArray();
            var b = Engine.VerifyFiles(files, new VerifierOptions { Engine = "boogie-only", TimeoutMs = 120000 });
            var only = new VerifierOptions();
            only.Only.AddRange(b.Methods.Select(m => m.Name));
            var c = Engine.VerifyFiles(files, only);
            Assert.True(Agree(c, b) >= 35, "agreeing: " + Agree(c, b));
            foreach (var good in new[] { "SortedNode.InsertAfter", "SortedNode.Digits", "BNode.Insert" })
                Assert.True(b[good].Verified, good);
            foreach (var bug in new[] { "Link.AppendSmaller", "TreeOwnershipBugs.Reach", "TreeOwnershipBugs.Bypass", "TreeOwnershipBugs.Cycle", "TreeOwnershipBugs.Stale" })
                Assert.False(b[bug].Verified, bug);
        }

        [Fact]
        public void SharesAndPackages_AreBoogies()
        {
            // read shares counted as CsVerify's engine's fractions, in views lent read-only; packages of views
            var root = Harness.RepoRoot();
            var files = new[] { "Good/Shares.cs", "Buggy/ShareBugs.cs", "Good/Packages.cs", "Buggy/PackageBugs.cs" }
                .Select(f => Path.Combine(root, "samples", f)).ToArray();
            var b = Engine.VerifyFiles(files, new VerifierOptions { Engine = "boogie-only", TimeoutMs = 120000 });
            var only = new VerifierOptions();
            only.Only.AddRange(b.Methods.Select(m => m.Name));
            var c = Engine.VerifyFiles(files, only);
            Assert.True(Agree(c, b) >= 30, "agreeing: " + Agree(c, b));
            foreach (var good in new[] { "Shares.Demo", "Shares.Within", "Shares.Contains2", "Packages.Demo", "Packages.Tick", "Packages.Make" })
                Assert.True(b[good].Verified, good);
            foreach (var bug in new[] { "ShareBugs.WriteWhileShared", "ShareBugs.LendWhileShared", "ShareBugs.WriteThroughShare", "ShareBugs.WrongJoin",
                                        "ShareBugs.LendBroken", "ShareBugs.Distinct", "PackageBugs.StaleRead", "PackageBugs.PackBroken",
                                        "PackageBugs.WriteThroughBox", "PackageBugs.Mismatch" })
                Assert.False(b[bug].Verified, bug);
        }

        // (parameters the body assigns, this(...), object initializers)
        private const string Parameters = @"
public static class Pa {
    public static int Entry(int x) { Spec.Requires(0 <= x && x < 100); Spec.Ensures((int r) => r == x + 1); x = x + 1; return x; }
    public static int Now(int x) { Spec.Requires(0 <= x && x < 100); Spec.Ensures((int r) => r == x); x = x + 1; return x; }
    public static int Was(int x) { Spec.Requires(0 <= x && x < 100); Spec.Ensures((int r) => r == Spec.Old(x) + 1); x++; return x; }
    public static int Loop(int n) { Spec.Requires(0 <= n && n < 100); Spec.Ensures((int r) => r == 0); while (n > 0) { Spec.Invariant(n >= 0); n--; } return n; }
    public static int Caller() { Spec.Ensures((int r) => r == 0); return Loop(5); }
}
public sealed class Ch
{
    public int V; public int W = 3;
    public Ch(int v) { Spec.Ensures(V == v && W == 3); V = v; }
    public Ch() : this(7) { Spec.Ensures(V == 7 && W == 3); }
    public Ch(bool b) : this(b ? 1 : 2) { Spec.Ensures(W == 4); }
}
public sealed class In { public int X; public int Y { get; set; } public required string Name { get; init; } }
public static class Mk {
    public static int Make() { Spec.Ensures((int r) => r == 3); var p = new In { X = 1, Y = 2, Name = ""a"" }; return p.X + p.Y; }
    public static int Bad() { Spec.Ensures((int r) => r == 4); var p = new In { X = 1, Y = 2, Name = ""a"" }; return p.X + p.Y; }
    public static int Seven() { Spec.Ensures((int r) => r == 7); return new Ch().V; }
}
";

        [Fact]
        public void Parameters_BothEnginesReportTheSame()
        {
            var (c, b) = Both(o => Engine.VerifySources(new[] { ("Test.cs", Harness.Usings + Parameters) }, o));
            var boogie = b.Methods.Where(m => m.Engine == "boogie").Select(m => m.Name).ToList();
            Assert.True(Agree(c, b) >= 11, "by Boogie: " + string.Join(", ", boogie));
            foreach (var bug in new[] { "Pa.Entry", "Ch..ctor", "Mk.Bad" })
                Assert.Contains(b.Methods, m => m.Name == bug && !m.Verified);
            foreach (var good in new[] { "Pa.Now", "Pa.Was", "Pa.Loop", "Mk.Make", "Mk.Seven" })
                Assert.True(b[good].Verified, good);
        }

        // (bitwise operators and shifts, as CsVerify's engine has them; Math.Max, Min and Abs)
        private const string Bits = @"
public static class Bi {
    public static void Holds0(int x) { Spec.Assert((x & 255) >= 0 && (x & 255) <= 255); }
    public static void Holds1(int x) { Spec.Assert((x | 1) != 0); }
    public static void Holds2(int x) { Spec.Assert((x >> 1) * 2 + (x & 1) == x); }
    public static void Holds3(int x) { Spec.Assert((~x) == -x - 1); }
    public static void Holds4(int x) { Spec.Assert((x >>> 31) == (x < 0 ? 1 : 0)); }
    public static void Holds5(int x) { Spec.Assert((x ^ 0) == x); }
    public static void Holds6(int x) { Spec.Assert((x ^ -1) == ~x); }
    public static void Holds7(int x) { Spec.Assert((x & -1) == x); }
    public static void Holds8(int x) { Spec.Assert((x << 32) == x); }
    public static void Holds9(int x) { Spec.Assert((x >> 33) == (x >> 1)); }
    public static void Wrong0(int x) { Spec.Assert((x >> 1) >= 0); }
    public static void Wrong1(int x) { Spec.Assert((x >>> 1) == (x >> 1)); }
    public static void Wrong2(int x) { Spec.Assert((x & 255) == x); }
    public static void Wrong3(int x) { Spec.Assert((x | 1) == x + 1); }
    public static void Wrong4(int x) { Spec.Assert((x ^ 1) == x + 1); }
    public static void Long(long x) { Spec.Assert((x >> 40) * 1099511627776L + (x & 1099511627775L) == x); }
    public static void Unsigned(uint x) { Spec.Assert((x >> 31) <= 1u && (~x) == 4294967295u - x); }
    public static int Shifts(int x) { return checked(x << 8); }
    public static void Packing(byte a, byte b) { int n = (a << 8) | b; Spec.Assert((n >> 8) == a && (n & 255) == b); }
    public static void WrongHalf(byte a, byte b) { int n = (a << 8) | b; Spec.Assert((n >> 8) == b); }
    public static void Masks(byte b) { if ((b & 0xE0) == 0xC0) Spec.Assert(0xC0 <= b && b <= 0xDF); }
    public static void Compound(byte a, sbyte s, short h) { byte c = a; c &= 15; Spec.Assert(c <= 15); sbyte d = s; d &= 15; Spec.Assert(0 <= d && d <= 15); short e = h; e |= 1; Spec.Assert(e != 0); }
    public static byte Narrow(int x) { return (byte)(x & 255); }
    public static byte TooWide(int x) { return (byte)(x & 511); }
    public static void TwoUnknowns(int x, int y) { Spec.Requires(x == 12 && y == 10); Spec.Assert((x & y) == 8 && (x | y) == 14 && (x ^ y) == 6); }
    public static void NotAnything(int x, int y) { Spec.Assert((x & y) == x); }
    public static int ByCount(int x, int k) { Spec.Requires(0 <= x && x < 1000 && 0 <= k && k < 4); Spec.Ensures((int r) => 0 <= r && r <= x); return x >> k; }
    public static int Big(int a, int b) { Spec.Ensures((int r) => r >= a && r >= b && (r == a || r == b)); return Math.Max(a, b); }
    public static int Clamp(int x) { Spec.Ensures((int r) => 0 <= r && r <= 10); return Math.Min(Math.Max(x, 0), 10); }
    public static int Size(int a) { Spec.Ensures((int r) => r >= 0); return Math.Abs(a); }
    public static int Wrongly(int a) { Spec.Ensures((int r) => r > 0); return Math.Abs(a); }
}
";

        [Fact]
        public void Bits_BothEnginesReportTheSame()
        {
            var (c, b) = Both(o => Engine.VerifySources(new[] { ("Test.cs", Harness.Usings + Bits) }, o));
            var boogie = b.Methods.Where(m => m.Engine == "boogie").Select(m => m.Name).ToList();
            Assert.True(Agree(c, b) >= 31, "by Boogie: " + string.Join(", ", boogie));
            foreach (var bug in new[] { "Bi.Wrong0", "Bi.Wrong1", "Bi.Wrong2", "Bi.Wrong3", "Bi.Wrong4", "Bi.WrongHalf", "Bi.TooWide", "Bi.NotAnything", "Bi.Wrongly" })
                Assert.False(b[bug].Verified, bug);
            foreach (var good in new[] { "Bi.Holds0", "Bi.Holds2", "Bi.Long", "Bi.Packing", "Bi.Masks", "Bi.Compound", "Bi.TwoUnknowns", "Bi.ByCount", "Bi.Clamp", "Bi.Size" })
                Assert.True(b[good].Verified, good);
        }

        // (invariants that call functions of values, a base type's values valid as their cases, records as objects,
        // an invariant over mutable state, immutable classes' invariants)
        private const string Invariants = @"
public abstract record Av
{
    private Av() { }
    public sealed record E() : Av;
    public sealed record N(int H, Av L, Av R) : Av
    {
        [Invariant, GhostFunction] public bool Bal() => H == 1 + Math.Max(Iv.Ht(L), Iv.Ht(R)) && Math.Abs(Iv.Ht(L) - Iv.Ht(R)) <= 1;
    }
}
public sealed class Gg { public int Level; }
public sealed record Rd(Gg G)
{
    [Invariant, Pure] public bool Positive() => G.Level > 0;
}
public sealed class Sq
{
    public readonly int Side;
    [Invariant, Pure] public bool Valid() => Side >= 0;
    public Sq(int side) { Spec.Requires(side >= 0); Spec.Ensures(Side == side); Side = side; }
    [Pure] public long Area() { Spec.Ensures((long r) => r >= 0); return (long)Side * Side; }
}
public sealed class Tl
{
    public readonly int Side;
    [Invariant, Pure] public bool Valid() => Side > 0;
    public Tl(int side) { Side = side; }
}
public static class Iv
{
    [Pure] public static int Ht(Av t) => t switch { Av.N n => n.H, _ => 0 };
    public static Av Node(Av l, Av r)
    {
        Spec.Requires(Math.Abs(Ht(l) - Ht(r)) <= 1);
        Spec.Ensures((Av t) => Ht(t) == 1 + Math.Max(Ht(l), Ht(r)));
        return new Av.N(checked(1 + Math.Max(Ht(l), Ht(r))), l, r);
    }
    public static Av Bad(Av l) { return new Av.N(checked(Ht(l) + 3), l, new Av.E()); }
    public static int Kids(Av t)
    {
        Spec.Ensures((int r) => r <= 1);
        if (t is not Av.N n) return 0;
        Spec.Assume(n.L is Av.E);
        return Ht(n.R) <= 1 ? Ht(n.R) : 1;
    }
    public static void Same()
    {
        object a = new Av.E();
        object b = new Av.E();
        Spec.Assert(a == b);
    }
    public static long Uses(Sq s) { Spec.Requires(s != null); Spec.Ensures((long r) => r >= 0); return s.Side; }
}
";

        [Fact]
        public void Invariants_BothEnginesReportTheSame()
        {
            var (c, b) = Both(o => Engine.VerifySources(new[] { ("Test.cs", Harness.Usings + Invariants) }, o));
            var boogie = b.Methods.Where(m => m.Engine == "boogie").Select(m => m.Name).ToList();
            Assert.True(Agree(c, b) >= 14, "by Boogie: " + string.Join(", ", boogie));
            var names = string.Join(", ", b.Methods.Select(m => m.Name + (m.Verified ? "" : "!")));
            foreach (var bug in new[] { "Iv.Bad", "Iv.Same", "Rd.Positive", "Tl..ctor" })
                Assert.True(b.Methods.Any(m => m.Name == bug && !m.Verified), bug + ": " + names);
            foreach (var good in new[] { "Iv.Node", "Iv.Kids", "Iv.Uses", "Sq.Area", "N.Bal" })
                Assert.True(b.Methods.Any(m => m.Name == good && m.Verified), good + ": " + names);
        }

        // interfaces as parameters, generic classes, constrained type parameters, a function's call resolved by its object's class
        private const string Polymorphism = @"
public interface ICounter { int Get(); void Bump(); }
public sealed class Ct : ICounter
{
    public int N;
    public int Get() { Spec.Ensures((int r) => r >= 0); return N; }
    public void Bump() { N = N + 1; }
}
public interface IPos { int Next(int x); }
public sealed class Bx { public int V; }
public static class If
{
    public static int Twice(ICounter c)
    {
        int a = c.Get();
        int b = c.Get();
        Spec.Assert(a == b);
        return 0;
    }
    public static int Keep(IPos p, Bx b)
    {
        Spec.Requires(b.V == 3);
        int r = p.Next(1);
        Spec.Assert(b.V == 3);
        return r;
    }
    public static int Mine(IPos p)
    {
        var b = new Bx();
        b.V = 3;
        p.Next(1);
        Spec.Assert(b.V == 3);
        return b.V;
    }
}
public interface IKeyed { int Key(); }
public sealed class K : IKeyed { public int K0; public int Key() { return K0; } }
public sealed class Cell<T>
{
    public T Item;
    public int Uses;
    public Cell(T item) { Spec.Ensures(Uses == 0); Item = item; }
    public T Take() { Spec.Requires(Uses < 10); Spec.Ensures(Uses == Spec.Old(Uses) + 1); Uses = Uses + 1; return Item; }
    public void Set(T x) { Item = x; }
    public void Bad() { Uses = Uses + 1; }
}
public sealed class Holder<T> where T : class, IKeyed
{
    public T? Held;
    public int Peek() { return Held!.Key(); }
    public int Safe() { return Held == null ? 0 : Held.Key(); }
}
public static class Gn
{
    public static int Keyed<T>(T a) where T : IKeyed { return a.Key(); }
    public static int KeyedSafe<T>(T a) where T : class, IKeyed { return a == null ? 0 : a.Key(); }
    public static void Use(K x, K y)
    {
        var c = new Cell<K>(x);
        c.Set(y);
        Spec.Assert(c.Item == y);
        var k = c.Take();
        Spec.Assert(c.Uses == 1);
    }
    public static int Ints()
    {
        var c = new Cell<int>(5);
        c.Set(7);
        int v = c.Take();
        Spec.Assert(c.Uses == 2);
        return v;
    }
    public static int Counts()
    {
        var c = new Cell<bool>(true);
        c.Take();
        c.Take();
        return c.Uses;
    }
}
public abstract class Sh { [Pure] public abstract long Area(); public abstract int Grow(int by); }
public sealed class Sq : Sh
{
    public readonly int Side;
    [Invariant, Pure] public bool Valid() => Side >= 0 && Side <= 1000;
    public Sq(int side) { Spec.Requires(side >= 0 && side <= 1000); Spec.Ensures(Side == side); Side = side; }
    [Pure] public override long Area() => (long)Side * Side;
    public override int Grow(int by) { Spec.Ensures((int r) => r == Side + 1); return Side + 1; }
}
public sealed class Ci : Sh
{
    [Pure] public override long Area() => 7;
    public override int Grow(int by) { return 0; }
}
public static class Dv
{
    public static long Nine() { Spec.Ensures((long r) => r == 9); Sh s = new Sq(3); return s.Area(); }
    public static long Ten() { Spec.Ensures((long r) => r == 10); Sh s = new Sq(3); return s.Area(); }
    public static int Four() { Spec.Ensures((int r) => r == 4); Sh s = new Sq(3); return s.Grow(1); }
    public static long Again() { Spec.Ensures((long r) => r == 16); Sh s = new Sq(3); s = new Sq(4); return s.Area(); }
    public static long Seven() { Spec.Ensures((long r) => r == 7); Sh s = new Ci(); return s.Area(); }
}
";

        [Fact]
        public void Polymorphism_BothEnginesReportTheSame()
        {
            var (c, b) = Both(o => Engine.VerifySources(new[] { ("Test.cs", Harness.Usings + Polymorphism) }, o));
            var boogie = b.Methods.Where(m => m.Engine == "boogie").Select(m => m.Name).ToList();
            Assert.True(Agree(c, b) >= 28, "by Boogie: " + string.Join(", ", boogie));
            var names = string.Join(", ", b.Methods.Select(m => m.Name + (m.Verified ? "" : "!")));
            foreach (var bug in new[] { "If.Twice", "If.Keep", "If.Mine", "Cell.Bad", "Holder.Peek", "Gn.Keyed", "Gn.Use", "Gn.Ints", "Dv.Ten", "Dv.Four" })
                Assert.True(b.Methods.Any(m => m.Name == bug && !m.Verified), bug + ": " + names);
            foreach (var good in new[] { "Cell.Take", "Holder.Safe", "Gn.KeyedSafe", "Gn.Counts", "Dv.Nine", "Dv.Again", "Dv.Seven" })
                Assert.True(b.Methods.Any(m => m.Name == good && m.Verified && m.Engine == "boogie"), good + ": " + names);
        }

        [Fact]
        public void ConstrainedGenerics_BoogieProvesWhatTheirContractsSay()
        {
            // (CsVerify's engine doesn't keep that the result is one of the arguments; Boogie does)
            var r = Engine.VerifySources(new[] { ("Test.cs", Harness.Usings + Polymorphism + @"
public static class Pk
{
    public static T Pick<T>(T a, T b) where T : class, IKeyed
    {
        Spec.Requires(a != null && b != null);
        Spec.Ensures((T r) => r == a || r == b);
        return a.Key() >= b.Key() ? a : b;
    }
    public static void Use(K x, K y) { var p = Pick(x, y); Spec.Assert(p == x || p == y); }
    public static void Wrong(K x, K y) { var p = Pick(x, y); Spec.Assert(p == x); }
}") }, new VerifierOptions { Engine = "boogie-only" });
            Assert.True(r["Pk.Pick"].Verified && r["Pk.Pick"].Engine == "boogie");
            Assert.True(r["Pk.Use"].Verified);
            Assert.False(r["Pk.Wrong"].Verified);
        }

        // arrays of objects, of strings, and null patterns of references
        private const string ObjectArrays = @"
public sealed class N { public int V; public N? Next; }
public abstract class Sh { [Pure] public abstract long Area(); }
public sealed class Sq : Sh
{
    public readonly int Side;
    [Invariant, Pure] public bool Valid() => Side >= 0 && Side <= 1000;
    public Sq(int side) { Spec.Requires(side >= 0 && side <= 1000); Spec.Ensures(Side == side); Side = side; }
    [Pure] public override long Area() { Spec.Ensures((long r) => r >= 0); return (long)Side * Side; }
}
public static class Ar
{
    public static int A(N? n) { if (n is null) return 0; return n.V; }
    public static int B(N? n) { if (n is not null) return n.V; return 0; }
    public static int C(N? n) { if (n is { } m) return m.V; return 0; }
    public static int D(N? n) { if (n is N m) return m.V; return 0; }
    public static int E(N? n) { if (n is not { } m) return n!.V; return m.V; }
    public static int F(string?[] xs) { Spec.Requires(xs.Length > 0); return xs[0] is null ? 0 : xs[0]!.Length; }
    public static int G(N?[] xs) { Spec.Requires(xs.Length > 0); return xs[0]!.V; }
    public static void H(N[] xs, N y) { Spec.Requires(xs.Length > 1); xs[0] = y; Spec.Assert(xs[0] == y); Spec.Assert(xs[1] == y); }
    public static N?[] Mk() { Spec.Ensures((N?[] r) => r.Length == 2); var a = new N?[2]; Spec.Assert(a[0] == null); return a; }
    public static long Total(Sh[] shapes)
    {
        Spec.Requires(Spec.Forall(0, shapes.Length, i => shapes[i] != null));
        long total = 0;
        for (int i = 0; i < shapes.Length; i++)
        {
            Spec.Invariant(0 <= i && i <= shapes.Length && total >= 0);
            total = checked(total + shapes[i].Area());
        }
        return total;
    }
    public static long Unchecked(Sh[] shapes) { Spec.Requires(shapes.Length > 0); return shapes[0].Area(); }
    public static int Count(string[] words)
    {
        int n = 0;
        foreach (var w in words) { Spec.Invariant(n >= 0); if (w is not null && w.Length > 0 && n < int.MaxValue) n++; }
        return n;
    }
    public static long Made() { var s = new Sh[] { new Sq(3), new Sq(4) }; return Total(s); }
}
";

        [Fact]
        public void ObjectArrays_BothEnginesReportTheSame()
        {
            var (c, b) = Both(o => Engine.VerifySources(new[] { ("Test.cs", Harness.Usings + ObjectArrays) }, o));
            var boogie = b.Methods.Where(m => m.Engine == "boogie").Select(m => m.Name).ToList();
            Assert.True(Agree(c, b) >= 15, "by Boogie: " + string.Join(", ", boogie));
            var names = string.Join(", ", b.Methods.Select(m => m.Name + (m.Verified ? "" : "!")));
            foreach (var bug in new[] { "Ar.E", "Ar.G", "Ar.H", "Ar.Total", "Ar.Unchecked" })
                Assert.True(b.Methods.Any(m => m.Name == bug && !m.Verified), bug + ": " + names);
            foreach (var good in new[] { "Ar.A", "Ar.B", "Ar.C", "Ar.D", "Ar.F", "Ar.Mk", "Ar.Count", "Ar.Made" })
                Assert.True(b.Methods.Any(m => m.Name == good && m.Verified && m.Engine == "boogie"), good + ": " + names);
        }

        // exception filters, multisets, collections keyed by strings, Keys and Values, collections through their interfaces
        private const string Collections5 = @"
using System.Collections.Generic;
public sealed class E1 : Exception { }
public static class Fl
{
    static void Thr(int c) { if (c > 0) throw new E1(); }
    public static int A(int c) { Spec.Ensures((int r) => r == 0 || r == 1 || r == 2); try { Thr(c); return 0; } catch (E1) when (c > 5) { return 1; } catch (E1) { return 2; } }
    public static int B(int c) { Spec.Ensures((int r) => r == 0 || r == 1); try { Thr(c); return 0; } catch (E1) when (c > 5) { return 1; } catch (Exception) { return 3; } }
    public static int C(int c, int[] a) { Spec.Ensures((int r) => r >= 0); try { Thr(c); return 0; } catch (E1) when (a[0] > 0) { return 1; } catch (E1) { return 2; } }
    public static int D(int c) { Spec.Ensures((int r) => r == 1); try { Thr(c); return 1; } catch (E1) when (c > 5) { return 1; } }
}
public static class Ms
{
    static void Sw(int[] a, int i, int j) { Spec.Requires(0 <= i && i < a.Length && 0 <= j && j < a.Length); Spec.Ensures(Spec.Multiset(a, a.Length) == Spec.Old(Spec.Multiset(a, a.Length))); int t = a[i]; a[i] = a[j]; a[j] = t; }
    static void Bad(int[] a, int i, int j) { Spec.Requires(0 <= i && i < a.Length && 0 <= j && j < a.Length); Spec.Ensures(Spec.Multiset(a, a.Length) == Spec.Old(Spec.Multiset(a, a.Length))); a[i] = a[j]; }
    static void Out(int[] a, int n) { Spec.Requires(0 <= n && n < a.Length); var before = Ghost.Of(Spec.Multiset(a, n).Count(0)); a[n] = 42; Spec.Assert(Spec.Multiset(a, n).Count(0) == before.Value); }
    static void Conc() { var a = new[] { 2, 7, 2 }; Spec.Assert(Spec.Multiset(a, 3).Count(2) == 2 && Spec.Multiset(a, 3).Count(5) == 0); Spec.Assert(Spec.Multiset(a, 3) == Bag.Of(7).Add(2).Add(2)); }
    static void Wd(int[] a) { Spec.Requires(Spec.Multiset(a, a.Length + 1).Count(0) == 0); }
    static void Un(int[] a) { Spec.Requires(a.Length == 2); Spec.Assert(Spec.Multiset(a, 2) == Bag.Of(a[0]).Union(Bag.Of(a[1]))); Spec.Assert(Spec.Multiset(a, 2).Contains(a[1])); }
}
public static class Sk
{
    public static int Lookup(Dictionary<string, int> d, string key) => d[key];
    public static int Safe(Dictionary<string, int> d, string key) { if (d.ContainsKey(key)) return d[key]; return 0; }
    public static void Put(Dictionary<string, int> d) { d[""a""] = 1; Spec.Assert(d.ContainsKey(""a"")); Spec.Assert(d[""a""] == 1); }
    public static void Two(Dictionary<string, int> d, string x) { Spec.Requires(x == ""a""); d[""a""] = 1; Spec.Assert(d[x] == 1); }
    public static void Other(Dictionary<string, int> d, string x) { d[""a""] = 1; Spec.Assert(d[x] == 1); }
    public static void Set(HashSet<string> s) { s.Add(""x""); Spec.Assert(s.Contains(""x"")); Spec.Assert(s.Contains(""y"")); }
    public static void Cnt() { var e = new Dictionary<string, int>(); e[""k""] = 1; e[""k""] = 2; Spec.Assert(e.Count == 1); Spec.Assert(e[""k""] == 2); }
}
public static class Kv
{
    public static void KeysAdd(Dictionary<int, int> d) { foreach (var k in d.Keys) { d[k + 1000] = 0; } }
    public static void KeysAssign(Dictionary<string, int> d) { foreach (var k in d.Keys) { d[k] = 0; } }
    public static void KeysRemove(Dictionary<int, int> d) { foreach (var k in d.Keys) { d.Remove(k); } }
    public static int Count(Dictionary<int, int> d) { Spec.Ensures<int>(r => r == d.Count); return d.Keys.Count; }
    public static int Has(Dictionary<int, int> d) { foreach (var k in d.Keys) { Spec.Assert(d.ContainsKey(k)); return d[k]; } return 0; }
}
public static class Qi
{
    public static int First(IReadOnlyList<int> xs) { Spec.Requires(xs.Count > 0); return xs[0]; }
}
public static class Il
{
    public static int List() { var l = new List<int>(); l.Add(4); return Qi.First(l); }
    public static int Array() { var a = new int[] { 1, 2 }; return Qi.First(a); }
    public static int Kept(List<int> l) { Spec.Requires(l.Count == 1 && l[0] == 7); Spec.Ensures<int>(r => r == 7); IReadOnlyList<int> xs = l; return xs[0]; }
    public static int Stable(IReadOnlyList<int> xs) { Spec.Requires(xs.Count > 0); var a = xs[0]; Spec.Assert(a == xs[0]); return a; }
    public static int Mutable(IList<int> xs) { Spec.Requires(xs.Count > 1); return xs[1]; }
    public static int Empty() { var l = new List<int>(); return Qi.First(l); }
    public static int Unchecked(IReadOnlyList<int> xs) => xs[0];
    public static int Aliased(List<int> l, IReadOnlyList<int> xs) { Spec.Requires(xs.Count > 0); Spec.Modifies(ObjSet.Of(l)); l.Clear(); return xs[0]; }
}
";

        [Fact]
        public void Collections_BothEnginesReportTheSame()
        {
            var (c, b) = Both(o => Engine.VerifySources(new[] { ("Test.cs", Harness.Usings + Collections5) }, o));
            var boogie = b.Methods.Where(m => m.Engine == "boogie").Select(m => m.Name).ToList();
            Assert.True(Agree(c, b) >= 32, "by Boogie: " + string.Join(", ", boogie));
            var names = string.Join(", ", b.Methods.Select(m => m.Name + (m.Verified ? "" : "!")));
            foreach (var bug in new[] { "Fl.B", "Fl.C", "Ms.Bad", "Ms.Wd", "Sk.Lookup", "Sk.Other", "Sk.Set", "Kv.KeysAdd", "Il.Empty", "Il.Unchecked", "Il.Aliased" })
                Assert.True(b.Methods.Any(m => m.Name == bug && !m.Verified), bug + ": " + names);
            foreach (var good in new[] { "Fl.A", "Fl.D", "Ms.Sw", "Ms.Out", "Ms.Conc", "Ms.Un", "Sk.Safe", "Sk.Put", "Sk.Two", "Sk.Cnt", "Kv.KeysAssign", "Kv.KeysRemove",
                                         "Kv.Count", "Kv.Has", "Qi.First", "Il.List", "Il.Array", "Il.Kept", "Il.Stable", "Il.Mutable" })
                Assert.True(b.Methods.Any(m => m.Name == good && m.Verified && m.Engine == "boogie"), good + ": " + names);
        }

        [Fact]
        public void ManualMemory_IsBoogies()
        {
            // ATS's views (PointsTo, ArrayView, ArrayHole) and Mem: every method of these samples by Boogie, verified
            foreach (var name in new[] { "Memory", "ArrayViews", "MemoryModel", "AtsIntro", "AtsArrays", "AtsMatrixAndTakeOut" })
            {
                var file = Path.Combine(Harness.RepoRoot(), "samples", "Good", name + ".cs");
                var r = Engine.VerifyFiles(new[] { file }, new VerifierOptions { Engine = "boogie-only", TimeoutMs = 120000 });
                Assert.True(r.Methods.Count > 0 && r.Methods.All(m => m.Engine == "boogie" && m.Verified),
                    name + ": " + string.Join(", ", r.Methods.Select(m => m.Name + "/" + m.Engine + (m.Verified ? "" : "!"))) + " " + r.BoogieFailure);
            }
        }

        // Monitor.Wait and Pulse, tasks one is given, tuples
        private const string WaitsAndTuples = @"
using System.Threading;
using System.Threading.Tasks;
public sealed class Qu
{
    private readonly object _lock = new object();
    [GuardedBy(nameof(_lock))] private int _count;
    public Qu() { _count = 0; }
    [LockInvariant(nameof(_lock)), Pure] private bool Ok() => _count >= 0;
    public void Put() { lock (_lock) { if (_count < 1000) _count++; Monitor.Pulse(_lock); } }
    public int Take()
    {
        lock (_lock)
        {
            while (_count == 0) { Spec.Invariant(_count >= 0); Monitor.Wait(_lock); }
            _count--;
            return _count;
        }
    }
    public void Bad() { lock (_lock) { _count = -1; Monitor.Wait(_lock); _count = 0; } }
    public int Stale() { lock (_lock) { _count = 5; Monitor.Wait(_lock); Spec.Assert(_count == 5); return 0; } }
}
public sealed class Bx { public int V; }
public static class Gt
{
    public static void W(Task t, Bx b) { int x = b.V; t.Wait(); Spec.Assert(b.V == x); }
    public static async Task A(Task t, Bx b) { int x = b.V; await t; Spec.Assert(b.V == x); }
    public static async Task<int> R(Task<int> t) { int v = await t; Spec.Assert(v >= 0); return v; }
    public static int Res(Task<int> t) { return t.Result; }
}
public static class Tu
{
    public static (int lo, int hi) Order(int a, int b)
    {
        Spec.Ensures<(int lo, int hi)>(r => r.lo <= r.hi && (r.lo == a || r.lo == b));
        return a <= b ? (a, b) : (b, a);
    }
    public static int Spread(int a, int b) { Spec.Ensures<int>(r => r >= 0); var (lo, hi) = Order(a, b); return hi - lo; }
    public static int Swap(int a, int b) { Spec.Ensures<int>(r => r == b); int x = a, y = b; (x, y) = (y, x); return x; }
    public static int Wrong(int a, int b) { Spec.Ensures<int>(r => r == a); var p = Order(a, b); return p.lo; }
}
";

        [Fact]
        public void WaitsAndTuples_BothEnginesReportTheSame()
        {
            var (c, b) = Both(o => Engine.VerifySources(new[] { ("Test.cs", Harness.Usings + WaitsAndTuples) }, o));
            var boogie = b.Methods.Where(m => m.Engine == "boogie").Select(m => m.Name).ToList();
            Assert.True(Agree(c, b) >= 14, "by Boogie: " + string.Join(", ", boogie));
            var names = string.Join(", ", b.Methods.Select(m => m.Name + (m.Verified ? "" : "!")));
            foreach (var bug in new[] { "Qu.Bad", "Qu.Stale", "Gt.A", "Gt.R", "Tu.Spread", "Tu.Wrong" })
                Assert.True(b.Methods.Any(m => m.Name == bug && !m.Verified), bug + ": " + names);
            foreach (var good in new[] { "Qu.Put", "Qu.Take", "Gt.W", "Tu.Order", "Tu.Swap" })
                Assert.True(b.Methods.Any(m => m.Name == good && m.Verified && m.Engine == "boogie"), good + ": " + names);
        }

        [Fact]
        public void WhatIsntTranslated_IsVerifiedAsAlways()
        {
            var r = Engine.VerifySources(new[] { ("Test.cs", Harness.Usings + Corpus) }, new VerifierOptions { Engine = "boogie" });
            Assert.Equal("csverify", r["A.Elsewhere"].Engine);
            Assert.True(r["A.Elsewhere"].Verified);
        }

        [Fact]
        public void Samples_BothEnginesReportTheSame()
        {
            foreach (var dir in new[] { "Good", "Buggy" })
            {
                var files = Directory.GetFiles(Path.Combine(Harness.RepoRoot(), "samples", dir), "*.cs");
                // (Boogie's methods, then those alone by CsVerify's engine)
                // (Boogie's time limit long enough for a loaded machine, where Z3 giving up reads as a failure: this compares
                // what the engines say, not how fast; CsVerify's engine retries a query that runs out of time)
                var b = Engine.VerifyFiles(files, new VerifierOptions { Engine = "boogie-only", TimeoutMs = 120000 });
                var only = new VerifierOptions();
                only.Only.AddRange(b.Methods.Select(m => m.Name));
                var c = Engine.VerifyFiles(files, only);
                Assert.True(Agree(c, b) > 0, dir + ": no method went to Boogie: " + b.BoogieFailure);
            }
        }
    }
}
