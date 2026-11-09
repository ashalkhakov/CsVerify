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
    public static int Elsewhere(int x) { Spec.Ensures<int>(r => r == x); try { return x; } catch (System.Exception) { throw; } }
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
                // (a solver's time limit long enough for a loaded machine: this compares what the engines say, not how fast)
                var b = Engine.VerifyFiles(files, new VerifierOptions { Engine = "boogie-only", TimeoutMs = 60000 });
                var only = new VerifierOptions { TimeoutMs = 60000 };
                only.Only.AddRange(b.Methods.Select(m => m.Name));
                var c = Engine.VerifyFiles(files, only);
                Assert.True(Agree(c, b) > 0, dir + ": no method went to Boogie: " + b.BoogieFailure);
            }
        }
    }
}
