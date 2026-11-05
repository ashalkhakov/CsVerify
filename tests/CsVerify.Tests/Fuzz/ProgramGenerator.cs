using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace CsVerify.Tests.Fuzz
{
    /// <summary>
    /// Random methods for testing the verifier itself, after "Testing Dafny" (Irfan et al., ISSTA 2022). Each method
    /// is rendered three ways: with its specifications (Spec.Requires, Spec.Ensures, Spec.Assert) for the verifier,
    /// with them as run-time checks, and with every assertion slot and candidate postcondition recorded (the probe).
    ///
    /// Methods take (int a, int b, int[] xs, Cell c, Cell? d) and return an int; d may be null, c itself, or another
    /// cell. Their preconditions either pin every input to a constant (the verifier is then all but exact, so true
    /// assertions verify, which is what makes the test bite) or bound them. Bodies have:
    /// <list type="bullet">
    /// <item>integers: arithmetic (multiplication by constants), Math, conditionals, array reads and writes, LINQ;</item>
    /// <item>objects: field reads and writes through c, d (aliased or not, null or not) and new cells;</item>
    /// <item>floats: doubles from the integers, rounding, NaN, Sqrt, and casts back to int (which must fit);</item>
    /// <item>exceptions: throw, try/catch of the program's Escape, checked arithmetic caught as OverflowException;</item>
    /// <item>data records: Pt(X, Y), its fields and its value equality;</item>
    /// <item>ifs, for loops over xs, and assertions.</item>
    /// </list>
    /// </summary>
    public sealed class ProgramGenerator
    {
        private readonly Random _r;
        private Pools _p = new Pools();
        private int _fresh;
        private int _depth;
        private bool _inLoop;
        private int _slots;
        private bool _spec; // (in a specification: no LINQ, which is not [Pure])
        private bool _pinned; // (the method's inputs are constants)

        /// <summary>The most statements a body has (a soak can ask for bigger programs).</summary>
        public int Size = 4;

        public ProgramGenerator(int seed) { _r = new Random(seed); }

        public enum Mode { Verify, Run, Probe }

        /// <summary>
        /// What both the verified and the running program declare: the types, and a library of helpers with real
        /// contracts for the methods to call (frames, array permissions, an owned class with an invariant, a [Pure]
        /// function). The helpers are verified too, in every batch.
        /// </summary>
        public const string Prelude = @"
public sealed class Cell { public int V; }
public sealed record Pt(int X, int Y);
public sealed class Escape : Exception { }

public static class H
{
    // changes only x, by k
    public static void Bump(Cell x, int k)
    {
        Spec.Requires(-1000 <= k && k <= 1000 && -100000 <= x.V && x.V <= 100000);
        Spec.Modifies(ObjSet.Of(x));
        Spec.Ensures(x.V == Spec.Old(x.V) + k);
        x.V = x.V + k;
    }

    // changes only x, saying nothing of how
    public static void Scramble(Cell x)
    {
        Spec.Modifies(ObjSet.Of(x));
        x.V = 7;
    }

    // writes only a[i]: the permission to that cell
    public static void SetCell(int[] a, int i, int v)
    {
        Spec.Requires(0 <= i && i < a.Length && Spec.Acc(a, i, i + 1));
        Spec.Ensures(Spec.Acc(a, i, i + 1) && a[i] == v);
        a[i] = v;
    }

    [Pure]
    public static int Twice(int x)
    {
        Spec.Requires(-100000 <= x && x <= 100000);
        return 2 * x;
    }
}

// owned (ATS style): written only through its view, never overdrawn
[Owned]
public sealed class Account
{
    public int Balance;

    [Invariant, Pure] public bool Valid() => Balance >= 0;

    public Account(int initial)
    {
        Spec.Requires(0 <= initial && initial <= 100000);
        Spec.Ensures(Balance == initial);
        Balance = initial;
    }

    public void Deposit(int amount)
    {
        Spec.Requires(0 <= amount && amount <= 1000 && Balance <= 100000);
        Spec.Ensures(Balance == Spec.Old(Balance) + amount);
        Balance = Balance + amount;
    }

    public void Withdraw(int amount)
    {
        Spec.Requires(0 <= amount && amount <= Balance);
        Spec.Ensures(Balance == Spec.Old(Balance) - amount);
        Balance = Balance - amount;
    }

    // two views in hand: two different accounts
    public static void Transfer(Account from, ref Own<Account> fromView, Account to, ref Own<Account> toView, int amount)
    {
        Spec.Requires(fromView.Obj.Value == from && toView.Obj.Value == to);
        Spec.Requires(0 <= amount && amount <= from.Balance && to.Balance <= 100000 && amount <= 1000);
        Spec.Ensures(from.Balance == Spec.Old(from.Balance) - amount && to.Balance == Spec.Old(to.Balance) + amount);
        from.Withdraw(amount);
        to.Deposit(amount);
    }
}

// an ownership tree: a box owns the box inside it, and its invariant reads that one, one level down
[Owned]
public sealed class Box
{
    public int Val;
    [Owns] public Box? Inner;

    [Invariant, Pure] public bool Valid() => Val >= 0 && (Inner == null || Inner.Val <= Val);

    public Box(int v)
    {
        Spec.Requires(0 <= v && v <= 100000);
        Spec.Ensures(Val == v && Inner == null);
        Val = v;
    }
}

// a node a predicate holds the permission to
[Owned]
public sealed class Node
{
    public int Val;

    public Node(int v)
    {
        Spec.Ensures(Val == v);
        Val = v;
    }
}

public static class Preds
{
    // two nodes' permissions, and their order: folded, nobody writes them
    [Predicate]
    public static bool Ordered(Node a, Node b) => Spec.Acc(a) && Spec.Acc(b) && a.Val <= b.Val;

    // a reader with a share: the invariant holds, and nobody writes the account meanwhile
    public static int Peek(in Shared<Account> s, Account a)
    {
        Spec.Requires(s.Obj.Value == a);
        Spec.Ensures((int r) => r == a.Balance && r >= 0);
        return a.Balance;
    }
}

// recursion and induction: Tri unfolds one level per use; the lemma, erased from the program, gives all of it
public static class L
{
    [Pure]
    public static int Tri(int n)
    {
        Spec.Requires(0 <= n && n <= 1000);
        Spec.Ensures((int r) => 0 <= r && r <= 1000 * n);
        Spec.Decreases(n);
        return n == 0 ? 0 : n + Tri(n - 1);
    }

    [Lemma, Conditional(Spec.Symbol)]
    public static void TriFormula(int n)
    {
        Spec.Requires(0 <= n && n <= 1000);
        Spec.Ensures(2 * Tri(n) == n * (n + 1));
        Spec.Decreases(n);
        if (n > 0) TriFormula(n - 1);
    }
}

// virtual calls: the base's contract, which the override inherits and is checked against; a [Pure] virtual query
public class Counter
{
    public virtual int Next(int k)
    {
        Spec.Requires(0 <= k && k <= 1000);
        Spec.Ensures((int r) => k < r && r <= 2 * k + 1);
        return k + 1;
    }

    [Pure] public virtual int Weight() => 1;
}

public sealed class Doubler : Counter
{
    public override int Next(int k) => 2 * k + 1;

    [Pure] public override int Weight() => 2;
}

// an interface, its contract in a contract class, and two implementations checked against it
public interface IGauge
{
    int Read(int k);
    [Pure] int Scale();
}

[ContractClassFor(typeof(IGauge))]
internal abstract class IGaugeContract : IGauge
{
    public int Read(int k)
    {
        Spec.Requires(0 <= k && k <= 1000);
        Spec.Ensures((int r) => k <= r && r <= k + 10);
        return 0;
    }

    public int Scale()
    {
        Spec.Ensures((int r) => 1 <= r && r <= 3);
        return 0;
    }
}

public sealed class Exact : IGauge
{
    public int Read(int k) => k;
    [Pure] public int Scale() => 1;
}

public sealed class Plus : IGauge
{
    public int Read(int k) => k + 10;
    [Pure] public int Scale() => 3;
}

// dynamic frames (Dafny's Valid()/Repr): two cells of its own; a change to one Duo leaves every other object
public sealed class Duo
{
    public Cell? A, B;
    public Ghost<ObjSet> Repr;

    [GhostFunction] public bool Valid()
    {
        Spec.Reads(Repr.Value.Add(this));
        return Repr.Value.Contains(this) && A != null && B != null && A != B && Repr.Value.Contains(A) && Repr.Value.Contains(B);
    }

    public Duo()
    {
        Spec.Ensures(Valid() && A!.V == 0 && B!.V == 0 && Spec.Fresh(Repr.Value));
        A = new Cell();
        B = new Cell();
        Repr = Ghost.Of(ObjSet.Of(this).Add(A).Add(B));
    }

    public void IncA()
    {
        Spec.Requires(Valid() && A!.V < 1000);
        Spec.Modifies(Repr.Value);
        Spec.Ensures(Valid() && Repr.Value == Spec.Old(Repr.Value) && A!.V == Spec.Old(A!.V) + 1 && B!.V == Spec.Old(B!.V));
        A!.V++;
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

        /// <summary>An input: d is null (DMode 0), c itself (1), or a cell of its own (2).</summary>
        public sealed class Input
        {
            public int A, B, CV, DMode, DV;
            public int[] Xs;
            public object[] Arguments() => new object[] { A, B, Xs.ToArray(), CV, DMode, DV };
            public override string ToString() =>
                $"a = {A}, b = {B}, xs = [{string.Join(", ", Xs)}], c.V = {CV}, d = {(DMode == 0 ? "null" : DMode == 1 ? "c" : $"a cell with V = {DV}")}";
        }

        /// <summary>
        /// One method: its precondition, body (assertion slots numbered), result and candidate postconditions, and
        /// inputs: those the probe runs on, and fresh ones to check a verified method on.
        /// </summary>
        public sealed class Method
        {
            public string Name;
            public bool Pinned;
            internal string Pre, Result;
            internal List<Stmt> Body;
            public List<string> Posts = new List<string>();
            public int Slots;
            public List<Input> Inputs = new List<Input>();
            public List<Input> Fresh = new List<Input>();

            /// <summary>
            /// The method as the verifier sees it (Mode.Verify), with checks (Mode.Run), or recording every slot and
            /// candidate postcondition (Mode.Probe): with the slots in keep (and planted), and the postcondition post.
            /// Run and probe renderings add an entry, name + "_", that makes the cells from integers.
            /// </summary>
            public string Render(Mode mode, string name, ISet<int> keep = null, int planted = -1, int post = -1)
            {
                var sb = new StringBuilder();
                if (mode != Mode.Verify)
                {
                    sb.AppendLine($"    public static int {name}_(int a, int b, int[] xs, int cv, int dmode, int dv)");
                    sb.AppendLine("    {");
                    sb.AppendLine("        var c = new Cell { V = cv };");
                    sb.AppendLine("        var d = dmode == 0 ? null : dmode == 1 ? c : new Cell { V = dv };");
                    sb.AppendLine($"        return {name}(a, b, xs, c, d);");
                    sb.AppendLine("    }");
                }
                sb.AppendLine($"    public static int {name}(int a, int b, int[] xs, Cell c, Cell{(mode == Mode.Verify ? "?" : "")} d)");
                sb.AppendLine("    {");
                if (mode == Mode.Verify)
                {
                    sb.AppendLine($"        Spec.Requires({Pre});");
                    if (post >= 0) sb.AppendLine($"        Spec.Ensures<int>(r => {Posts[post]});");
                }
                else sb.AppendLine($"        if (!({Pre.Replace("Spec.Forall", "RT.Forall")})) throw new Skip();");
                bool Kept(int id) => mode == Mode.Probe || keep != null && keep.Contains(id) || id == planted;
                foreach (var st in Body) Emit(sb, st, 2, mode, Kept);
                if (mode == Mode.Verify) sb.AppendLine($"        return {Result};");
                else
                {
                    sb.AppendLine($"        int r = {Result};");
                    if (mode == Mode.Run && post >= 0) sb.AppendLine($"        if (!({Posts[post]})) throw new Failed(\"the postcondition\");");
                    if (mode == Mode.Probe)
                        for (int k = 0; k < Posts.Count; k++) sb.AppendLine($"        Probe.Post({k}, () => {Posts[k]});");
                    sb.AppendLine("        return r;");
                }
                sb.AppendLine("    }");
                return sb.ToString();
            }
        }

        /// <summary>The variables in scope, by type.</summary>
        private sealed class Pools
        {
            public List<string> Ints = new List<string>(), Doubles = new List<string>(), Cells = new List<string>(), Pts = new List<string>();
            public List<string> Accounts = new List<string>(); // (owned: account oK, its view wK)
            public List<(string share, string account)> Shares = new List<(string, string)>();
            public List<string> Boxes = new List<string>();    // (boxes bK readable; those in Held have their view uK in hand)
            public List<string> Held = new List<string>();
            public List<string> Nodes = new List<string>();    // (nodes qK whose permission is in hand, or folded)
            public List<(string, string)> Folded = new List<(string, string)>();
            public List<string> Counters = new List<string>(); // (a Counter or a Doubler)
            public List<string> Gauges = new List<string>();   // (an Exact or a Plus, as an IGauge)
            public List<string> Duos = new List<string>();     // (dynamic frames)
            public List<string> Mems = new List<string>();     // (Mem cells: pointer ptrK, view mK)
            public Pools Copy() => new Pools
            {
                Ints = Ints.ToList(), Doubles = Doubles.ToList(), Cells = Cells.ToList(), Pts = Pts.ToList(), Accounts = Accounts.ToList(),
                Shares = Shares.ToList(), Boxes = Boxes.ToList(), Held = Held.ToList(), Nodes = Nodes.ToList(), Folded = Folded.ToList(),
                Counters = Counters.ToList(), Gauges = Gauges.ToList(), Duos = Duos.ToList(), Mems = Mems.ToList(),
            };
            public IEnumerable<string> Writable => Nodes.Where(n => !Folded.Any(f => f.Item1 == n || f.Item2 == n));
        }

        public Method Next(string name)
        {
            _fresh = 0;
            _slots = 0;
            var m = new Method { Name = name };
            m.Pinned = _pinned = _r.Next(3) > 0;
            if (m.Pinned)
            {
                var input = new Input { A = Small(), B = Small(), Xs = Enumerable.Range(0, _r.Next(5)).Select(_ => Small()).ToArray(), CV = Small(), DMode = _r.Next(3), DV = Small() };
                string dPre = input.DMode == 0 ? "d == null" : input.DMode == 1 ? "d == c" : $"d != null && d != c && d.V == {input.DV}";
                m.Pre = $"a == {input.A} && b == {input.B} && xs.Length == {input.Xs.Length}" + string.Concat(input.Xs.Select((x, i) => $" && xs[{i}] == {x}")) +
                        $" && c.V == {input.CV} && {dPre}";
                m.Inputs.Add(input);
            }
            else
            {
                int bound = new[] { 10, 100, 1000 }[_r.Next(3)];
                m.Pre = $"-{bound} <= a && a <= {bound} && -{bound} <= b && b <= {bound} && Spec.Forall(0, xs.Length, i => -{bound} <= xs[i] && xs[i] <= {bound})" +
                        $" && -{bound} <= c.V && c.V <= {bound} && (d == null || -{bound} <= d.V && d.V <= {bound})";
                int minLength = _r.Next(2) == 0 ? _r.Next(1, 3) : 0;
                if (minLength > 0) m.Pre += $" && xs.Length >= {minLength}";
                int Any() => _r.Next(-bound, bound + 1);
                int Extreme() => _r.Next(2) == 0 ? bound : -bound;
                // (the extremes too: where overflow and off-by-one live)
                Input Make(Func<int> v) => new Input { A = v(), B = v(), Xs = Enumerable.Range(0, _r.Next(minLength, 6)).Select(_ => v()).ToArray(), CV = v(), DMode = _r.Next(3), DV = v() };
                for (int k = 0; k < 30; k++) m.Inputs.Add(Make(k % 5 == 0 ? (Func<int>)Extreme : Any));
                for (int k = 0; k < 60; k++) m.Fresh.Add(Make(k % 5 == 0 ? (Func<int>)Extreme : Any));
            }
            _p = new Pools();
            _p.Ints.Add("a");
            _p.Ints.Add("b");
            _p.Cells.Add("c");
            m.Body = Block(_r.Next(1, 1 + Size));
            m.Result = Int(2);
            // (a postcondition is stated before the body's locals)
            _p = new Pools();
            _p.Ints.Add("a");
            _p.Ints.Add("b");
            _p.Cells.Add("c");
            for (int k = 0; k < 4; k++) m.Posts.Add(Spec(() => Bool(2, "r")));
            m.Slots = _slots;
            return m;
        }

        private string Spec(Func<string> make)
        {
            _spec = true;
            try { return make(); }
            finally { _spec = false; }
        }

        private int Small() => _r.Next(10) < 8 ? _r.Next(-5, 10) : _r.Next(-100, 100);

        private T Pick<T>(List<T> list) => list[_r.Next(list.Count)];

        // ------------------------------------------------------------------ statements

        internal abstract class Stmt { }
        internal sealed class Line : Stmt { public string Text; }                       // a simple statement
        internal sealed class If : Stmt { public string Cond; public List<Stmt> Then, Else; }
        internal sealed class For : Stmt { public string Var; public List<Stmt> Body; public List<Assert> Invariants = new List<Assert>(); }
        internal sealed class Try : Stmt { public List<Stmt> Body, Handler; public string Catches; }
        internal sealed class Assert : Stmt { public string Cond; public int Id; }

        private readonly Stack<Pools> _scopes = new Stack<Pools>();

        private List<Stmt> Block(int n)
        {
            var saved = _p.Copy();
            _scopes.Push(saved);
            var list = new List<Stmt>();
            for (int k = 0; k < n; k++) list.Add(Statement());
            // (what the block made is given back at its end, shares before views: each is linear, and must not be lost)
            foreach (var (sh, acct) in _p.Shares.Except(saved.Shares)) list.Add(new Line { Text = $"Own.Unshare(ref w{acct.Substring(1)}, {sh});" });
            foreach (var o in _p.Accounts.Except(saved.Accounts)) list.Add(new Line { Text = $"Own.Drop(w{o.Substring(1)});" });
            foreach (var b in _p.Held.Except(saved.Held).Where(b => !saved.Boxes.Contains(b))) list.Add(new Line { Text = $"Own.Drop(u{b.Substring(1)});" });
            foreach (var m in _p.Mems.Except(saved.Mems)) list.Add(new Line { Text = $"Mem.Free(m{m}, ptr{m});" });
            _scopes.Pop();
            _p = saved; // (a block's declarations end with it)
            return list;
        }

        private Stmt Statement()
        {
            _depth++;
            try
            {
                // (simple statements 0..8 and 13..15; compound ones 9..12 only near the top)
                int pick = _r.Next(_depth > 1 ? 15 : 19);
                if (_depth > 1 && pick >= 9) pick += 4;
                if (pick <= 2 && _r.Next(2) == 0) pick = 13 + _r.Next(6); // (calls and owned objects more often)
                if (pick == 13 && _p.Accounts.Count == 1 && _r.Next(2) == 0) pick = 14;
                switch (pick)
                {
                    case 0:
                    {
                        var v = "v" + _fresh++;
                        var s = new Line { Text = $"int {v} = {Int(2)};" };
                        _p.Ints.Add(v);
                        return s;
                    }
                    case 1:
                    {
                        var targets = _p.Ints.Where(l => l.StartsWith("v")).ToList();
                        if (targets.Count == 0) goto case 0;
                        return new Line { Text = $"{Pick(targets)} = {Int(2)};" };
                    }
                    case 2: return new Line { Text = $"if (xs.Length > 0) xs[{Index()}] = {Int(1)};" };
                    case 3: return new Assert { Cond = Spec(() => Bool(2, null)), Id = _slots++ };
                    case 4:
                    {
                        // a field write: through c, a new cell, or d (guarded, mostly)
                        switch (_r.Next(4))
                        {
                            case 0: return new Line { Text = $"if (d != null) d.V = {Int(1)};" };
                            case 1 when _r.Next(3) == 0: return new Line { Text = $"d!.V = {Int(1)};" };
                            default: return new Line { Text = $"{Pick(_p.Cells)}.V = {Int(1)};" };
                        }
                    }
                    case 5:
                    {
                        if (_r.Next(2) == 0)
                        {
                            var n = "n" + _fresh++;
                            var s = new Line { Text = $"var {n} = new Cell {{ V = {Int(1)} }};" };
                            _p.Cells.Add(n);
                            return s;
                        }
                        var p = "p" + _fresh++;
                        var t = new Line { Text = $"var {p} = new Pt({Int(1)}, {Int(1)});" };
                        _p.Pts.Add(p);
                        return t;
                    }
                    case 6:
                    {
                        var f = "f" + _fresh++;
                        var s = new Line { Text = $"double {f} = {Double(2)};" };
                        _p.Doubles.Add(f);
                        return s;
                    }
                    case 7: return new Line { Text = $"if ({Bool(1, null)}) throw new Escape();" };
                    case 8:
                    {
                        // checked arithmetic, caught: the handler sets the target otherwise
                        var targets = _p.Ints.Where(l => l.StartsWith("v")).ToList();
                        if (targets.Count == 0) goto case 0;
                        var v = Pick(targets);
                        return new Try
                        {
                            Body = new List<Stmt> { new Line { Text = $"{v} = checked({Int(2)} + {Int(1)});" } },
                            Catches = "OverflowException",
                            Handler = new List<Stmt> { new Line { Text = $"{v} = {Small()};" } },
                        };
                    }
                    case 13:
                    {
                        // an owned account and its view (made with a balance that may break its precondition)
                        // (often two, so that a transfer has both ends; and then often one at once)
                        var text = new StringBuilder();
                        var made = new List<string>();
                        for (int k = _r.Next(2); k < 2; k++)
                        {
                            var o = "o" + _fresh++;
                            text.Append($"var {o} = Own.New(new Account({(_r.Next(4) == 0 ? Int(1) : $"Math.Abs({Int(1)}) % 100")}), out var w{o.Substring(1)}); ");
                            _p.Accounts.Add(o);
                            made.Add(o);
                        }
                        if (made.Count == 2 && _r.Next(2) == 0)
                        {
                            var amount = _r.Next(3) == 0 ? Int(1) : $"Math.Abs({Int(1)}) % 50";
                            var (f, t) = _r.Next(2) == 0 ? (made[0], made[1]) : (made[1], made[0]);
                            text.Append($"if ({amount} <= {f}.Balance && {t}.Balance <= 1000) Account.Transfer({f}, ref w{f.Substring(1)}, {t}, ref w{t.Substring(1)}, {amount});");
                        }
                        return new Line { Text = text.ToString().TrimEnd() };
                    }
                    case 14:
                    {
                        if (_p.Accounts.Count == 0) goto case 13;
                        var o = Pick(_p.Accounts);
                        var amount = _r.Next(3) == 0 ? Int(1) : $"Math.Abs({Int(1)}) % 50";
                        switch (_r.Next(4))
                        {
                            case 0: return new Line { Text = $"{o}.Deposit({amount});" };
                            case 1: return new Line { Text = $"if ({amount} <= {o}.Balance) {o}.Withdraw({amount});" };
                            case var _ when _p.Accounts.Count > 1 && _r.Next(2) == 0:
                            {
                                var t = Pick(_p.Accounts.Where(x => x != o).ToList());
                                return new Line { Text = $"if ({amount} <= {o}.Balance && {t}.Balance <= 1000) Account.Transfer({o}, ref w{o.Substring(1)}, {t}, ref w{t.Substring(1)}, {amount});" };
                            }
                            default: return new Line { Text = $"{o}.Withdraw({amount});" }; // (may overdraw: then it must not verify)
                        }
                    }
                    case 15:
                    {
                        // calls to the helpers: what they may change, and what they may not
                        switch (_r.Next(9))
                        {
                            case 0: return new Line { Text = $"L.TriFormula(Math.Abs({Int(1)}) % 30);" }; // (a lemma: a proof, erased)
                            case 2:
                            {
                                // an interface call: the contract class's contract, whichever class it is
                                var g = "g" + _fresh++;
                                var v = "v" + _fresh++;
                                var make = _r.Next(3) == 0 ? "new Plus()" : $"({Bool(1, null)} ? new Exact() : new Plus())";
                                var use = _r.Next(2) == 0 ? $"{g}.Read(Math.Abs({Int(1)}) % 100)" : $"{g}.Scale()";
                                _p.Gauges.Add(g);
                                _p.Ints.Add(v);
                                return new Line { Text = $"IGauge {g} = {make}; int {v} = {use};" };
                            }
                            case 3:
                            {
                                // a framed object: its methods change only its representation
                                var e = "e" + _fresh++;
                                var text = $"var {e} = new Duo();";
                                for (int k = _r.Next(3); k > 0; k--) text += _r.Next(2) == 0 ? $" {e}.IncA();" : $" {e}.Swap();";
                                _p.Duos.Add(e);
                                return new Line { Text = text };
                            }
                            case 4:
                            {
                                // a Mem cell and its view: written and read, freed at the block's end
                                var m = _fresh++.ToString();
                                var v = "v" + _fresh++;
                                var text = $"var ptr{m} = Mem.Alloc({Int(1)}, out PointsTo<int> m{m});";
                                if (_r.Next(2) == 0) text += $" Mem.Write(ref m{m}, ptr{m}, {Int(1)});";
                                text += $" int {v} = Mem.Read(in m{m}, ptr{m});";
                                _p.Mems.Add(m);
                                _p.Ints.Add(v);
                                return new Line { Text = text };
                            }
                            case 1:
                            {
                                // a counter of either class: a call through the base type
                                var k = "k" + _fresh++;
                                var make = _r.Next(3) == 0 ? "new Doubler()" : $"({Bool(1, null)} ? new Counter() : new Doubler())";
                                // (and a call at once, through the base type: Next, or the query Weight)
                                var v = "v" + _fresh++;
                                var use = _r.Next(2) == 0 ? $"{k}.Next(Math.Abs({Int(1)}) % 100)" : $"{k}.Weight()";
                                _p.Counters.Add(k);
                                _p.Ints.Add(v);
                                return new Line { Text = $"Counter {k} = {make}; int {v} = {use};" };
                            }
                        }
                        var cell = _r.Next(3) == 0 ? "d" : Pick(_p.Cells);
                        var call = new[]
                        {
                            $"H.Bump({cell}, {Int(1)});",
                            $"H.Bump({cell}, Math.Abs({Int(1)}) % 100);",
                            $"H.Scramble({cell});",
                            $"if (xs.Length > 0) H.SetCell(xs, {Index()}, {Int(1)});",
                        }[_r.Next(4)];
                        return new Line { Text = cell == "d" && !call.StartsWith("if") ? $"if (d != null) {call}" : call };
                    }
                    case 16: return BoxStatement();
                    case 17: return NodeStatement();
                    case 18:
                    {
                        // a read share of an account: while it is out, the view cannot write (or be lent)
                        var free = _p.Accounts.Where(o => !_p.Shares.Any(x => x.account == o)).ToList();
                        if (free.Count == 0) goto case 13;
                        var o = Pick(free);
                        var sh = "s" + _fresh++;
                        _p.Shares.Add((sh, o));
                        return new Line { Text = $"Own.Share(ref w{o.Substring(1)}, out var {sh});" };
                    }
                    case 9:
                    case 10: return new If { Cond = Bool(2, null), Then = Block(_r.Next(1, 3)), Else = _r.Next(2) == 0 ? Block(_r.Next(1, 3)) : null };
                    case 11: return new Try { Body = Block(_r.Next(1, 3)), Catches = "Escape", Handler = Block(_r.Next(1, 2)) };
                    default:
                    {
                        if (_inLoop) goto case 3;
                        var i = "i" + _fresh++;
                        _p.Ints.Add(i);
                        // invariants, as slots: what held at every head is kept, one that failed may be planted
                        var invariants = new List<Assert>();
                        for (int k = _r.Next(3); k > 0; k--)
                            invariants.Add(new Assert { Id = _slots++, Cond = Spec(() => k == 1 && _r.Next(2) == 0 ? $"0 <= {i} && {i} <= xs.Length" : Bool(1, null)) });
                        _inLoop = true;
                        var body = Block(_r.Next(1, 3));
                        _inLoop = false;
                        _p.Ints.Remove(i);
                        return new For { Var = i, Body = body, Invariants = invariants };
                    }
                }
            }
            finally { _depth--; }
        }

        /// <summary>An ownership tree: make a box, write one in hand, give one made here into another, take one out.</summary>
        private Stmt BoxStatement()
        {
            var here = _p.Held.Except(_scopes.Peek().Held).ToList(); // (views made in this block: given only here)
            switch (_r.Next(5))
            {
                case 1 when _p.Held.Count > 0:
                    return new Line { Text = $"{Pick(_p.Held)}.Val = {(_r.Next(3) == 0 ? Int(1) : $"Math.Abs({Int(1)}) % 100")};" };
                case 2 when here.Count > 0 && _p.Held.Count > 1:
                {
                    var child = Pick(here);
                    var parent = Pick(_p.Held.Where(b => b != child).ToList());
                    _p.Held.Remove(child);
                    return new Line { Text = $"Own.Give(ref {parent}.Inner, {child}, u{child.Substring(1)});" };
                }
                case 3 when _p.Held.Count > 0:
                {
                    var parent = Pick(_p.Held);
                    var b = "b" + _fresh++;
                    _p.Boxes.Add(b);
                    _p.Held.Add(b);
                    return new Line { Text = $"var {b} = Own.Take(ref {parent}.Inner, out var u{b.Substring(1)});" };
                }
                default:
                {
                    string NewBox(out string b)
                    {
                        b = "b" + _fresh++;
                        var v = _r.Next(4) == 0 ? Int(1) : $"Math.Abs({Int(1)}) % 100"; // (before it is in scope)
                        _p.Boxes.Add(b);
                        _p.Held.Add(b);
                        return $"var {b} = Own.New(new Box({v}), out var u{b.Substring(1)});";
                    }
                    var text = NewBox(out var outer);
                    if (_r.Next(2) == 0)
                    {
                        // (often a tree at once: a second box given into the first, and perhaps taken out again)
                        text += " " + NewBox(out var inner) + $" Own.Give(ref {outer}.Inner, {inner}, u{inner.Substring(1)});";
                        _p.Held.Remove(inner);
                        if (_r.Next(2) == 0)
                        {
                            var t = "b" + _fresh++;
                            _p.Boxes.Add(t);
                            _p.Held.Add(t);
                            text += $" var {t} = Own.Take(ref {outer}.Inner, out var u{t.Substring(1)});";
                        }
                    }
                    return new Line { Text = text };
                }
            }
        }

        /// <summary>A predicate: nodes whose permissions are in hand, folded into Ordered and unfolded, or written.</summary>
        private Stmt NodeStatement()
        {
            var writable = _p.Writable.ToList();
            switch (_r.Next(5))
            {
                case 1 when writable.Count > 0:
                    return new Line { Text = $"{Pick(writable)}.Val = {Int(1)};" };
                case 2 when writable.Count > 0:
                {
                    // (two of them, or one twice: a footprint cannot be held twice)
                    var a = Pick(writable);
                    var b = _r.Next(6) == 0 ? a : Pick(writable);
                    _p.Folded.Add((a, b));
                    return new Line { Text = $"Spec.Fold(Preds.Ordered({a}, {b}));" };
                }
                case 3 when _p.Folded.Count > 0:
                {
                    var f = Pick(_p.Folded);
                    _p.Folded.Remove(f);
                    return new Line { Text = $"Spec.Unfold(Preds.Ordered({f.Item1}, {f.Item2}));" };
                }
                default:
                {
                    string NewNode(out string q)
                    {
                        q = "q" + _fresh++;
                        var v = Int(1); // (before it is in scope)
                        _p.Nodes.Add(q);
                        return $"var {q} = Own.New(new Node({v}), out var z{q.Substring(1)}); Own.ToAcc(z{q.Substring(1)});";
                    }
                    var text = NewNode(out var a);
                    if (_r.Next(2) == 0)
                    {
                        // (often a fold at once, of two nodes, and perhaps the unfold)
                        text += " " + NewNode(out var b) + $" Spec.Fold(Preds.Ordered({a}, {b}));";
                        if (_r.Next(2) == 0) text += $" Spec.Unfold(Preds.Ordered({a}, {b}));";
                        else _p.Folded.Add((a, b));
                    }
                    return new Line { Text = text };
                }
            }
        }

        // ------------------------------------------------------------------ expressions

        /// <summary>An index: often guarded into range, sometimes not (the verifier must then reject it).</summary>
        private string Index()
        {
            var e = Int(1);
            return _r.Next(4) == 0 ? e : $"xs.Length == 0 ? 0 : (({e}) % xs.Length + xs.Length) % xs.Length";
        }

        private string Int(int depth, string extra = null)
        {
            if (depth <= 0 || _r.Next(4) == 0)
            {
                switch (_r.Next(extra != null ? 6 : 5))
                {
                    case 0: return Small().ToString();
                    case 1: return "xs.Length";
                    case 2: return _r.Next(2) == 0 ? $"{Pick(_p.Cells)}.V" : "(d == null ? 0 : d.V)";
                    case 3 when _p.Pts.Count > 0: return $"{Pick(_p.Pts)}.{(_r.Next(2) == 0 ? "X" : "Y")}";
                    case 4 when _p.Accounts.Count > 0:
                    {
                        var o = Pick(_p.Accounts);
                        var sh = _p.Shares.Where(x => x.account == o).Select(x => x.share).FirstOrDefault();
                        return sh != null && !_spec && _r.Next(2) == 0 ? $"Preds.Peek({sh}, {o})" : $"{o}.Balance";
                    }
                    case 4 when _p.Boxes.Count > 0:
                    {
                        var b = Pick(_p.Boxes);
                        return _r.Next(2) == 0 ? $"{b}.Val" : $"({b}.Inner == null ? 0 : {b}.Inner.Val)";
                    }
                    case 4 when _p.Nodes.Count > 0: return $"{Pick(_p.Nodes)}.Val";
                    case 4 when _p.Gauges.Count > 0: return $"{Pick(_p.Gauges)}.Scale()";
                    case 4 when _p.Duos.Count > 0: return $"{Pick(_p.Duos)}.{(_r.Next(2) == 0 ? "A" : "B")}!.V";
                    case 5: return extra;
                    default: return Pick(_p.Ints);
                }
            }
            int d = depth - 1;
            // (LINQ one time in eight: each call is a definition the verifier runs, so it is the costly part)
            int kind = _spec || _r.Next(8) > 0 ? _r.Next(11) : 11 + _r.Next(4);
            switch (kind)
            {
                case 0: case 1: return $"({Int(d, extra)} + {Int(d, extra)})";
                case 2: return $"({Int(d, extra)} - {Int(d, extra)})";
                case 3: return $"({_r.Next(-4, 5)} * {Int(d, extra)})"; // (by a constant: nonlinear arithmetic the solver cannot decide)
                case 4: return $"({Int(d, extra)} / {Divisor(d, extra)})";
                case 5: return $"({Int(d, extra)} % {Divisor(d, extra)})";
                case 6: return $"Math.{(_r.Next(2) == 0 ? "Min" : "Max")}({Int(d, extra)}, {Int(d, extra)})";
                case 7:
                    switch (_r.Next(5))
                    {
                        case 0: return $"H.Twice({Int(d, extra)})";
                        case 1: return $"L.Tri(Math.Abs({Int(d, extra)}) % 30)";
                        case 2 when _p.Counters.Count > 0:
                            return _spec || _r.Next(2) == 0 ? $"{Pick(_p.Counters)}.Weight()" : $"{Pick(_p.Counters)}.Next(Math.Abs({Int(d, extra)}) % 100)";
                        default: return $"Math.Abs({Int(d, extra)})";
                    }
                case 8: return $"({Bool(d, extra)} ? {Int(d, extra)} : {Int(d, extra)})";
                case 9:
                {
                    // an element (inside a loop, often the loop's own)
                    var loopVar = _p.Ints.LastOrDefault(l => l.StartsWith("i"));
                    if (loopVar != null && _r.Next(2) == 0) return $"xs[{loopVar}]";
                    return $"(xs.Length == 0 ? 0 : xs[{Index()}])";
                }
                case 10:
                {
                    // a double back to an int: guarded into range, or not (then it must fit)
                    var f = Double(d);
                    return _r.Next(3) == 0 ? $"(int){Paren(f)}" : $"({f} >= -1000.0 && {f} <= 1000.0 ? (int){Paren(f)} : 0)";
                }
                case 11: return $"xs.Count(x => {Lambda()})";
                case 12: return $"xs.Where(x => {Lambda()}).Count()";
                case 13: return _r.Next(2) == 0 ? "xs.Sum()" : $"xs.Select(x => {LambdaInt()}).Sum()";
                default: return _r.Next(2) == 0 ? $"(xs.Length == 0 ? 0 : xs.{(_r.Next(2) == 0 ? "Max" : "Min")}())" : $"xs.Select(x => {LambdaInt()}).FirstOrDefault()";
            }
        }

        private static string Paren(string e) => e.StartsWith("(") && e.EndsWith(")") ? e : $"({e})";

        private string Double(int depth)
        {
            if (depth <= 0 || _r.Next(3) == 0)
            {
                switch (_r.Next(4))
                {
                    case 0 when _p.Doubles.Count > 0: return Pick(_p.Doubles);
                    case 1:
                    {
                        // (through a - a, exactly zero, so that C# does not fold it: (int)1e300 would not compile)
                        var lit = new[] { "0.5", "0.1", "-0.0", "1e300", "3.0", "double.NaN", "double.PositiveInfinity" }[_r.Next(7)];
                        return lit == "-0.0" ? "(-(double)(a - a))" : $"((double)(a - a) + {lit})";
                    }
                    // (an integer as a double: with symbolic inputs that is costly for the solver, so only pinned)
                    default: return _pinned ? $"(double){Int(0)}" : $"((double)(a - a) + {new[] { "2.0", "-1.5", "1e10" }[_r.Next(3)]})";
                }
            }
            int d = depth - 1;
            switch (_r.Next(7))
            {
                case 0: return $"({Double(d)} + {Double(d)})";
                case 1: return $"({Double(d)} - {Double(d)})";
                case 2: return $"({Double(d)} * {Double(d)})";
                case 3: return $"({Double(d)} / {Double(d)})";
                case 4: return $"Math.Sqrt({Double(d)})";
                case 5: return $"Math.{(_r.Next(2) == 0 ? "Min" : "Max")}({Double(d)}, {Double(d)})";
                default: return $"Math.{new[] { "Abs", "Floor", "Ceiling" }[_r.Next(3)]}({Double(d)})";
            }
        }

        // a divisor: often one that cannot be zero
        private string Divisor(int depth, string extra)
        {
            if (_r.Next(3) > 0)
                return _r.Next(2) == 0 ? (_r.Next(1, 7) * (_r.Next(2) == 0 ? 1 : -1)).ToString() : $"(Math.Abs({Int(depth, extra)}) % 5 + 1)";
            // any: a constant zero would not compile, so a constant is made to depend on a
            var e = Int(depth, extra);
            return e.Any(char.IsLetter) ? e : $"(a - a + {e})";
        }

        private string Lambda() => $"x {Cmp()} {Small()}";
        // (a lambda is verified on its own, for any x: so nothing that can overflow)
        private string LambdaInt() => new[] { "x", $"x % {_r.Next(1, 5)}", $"x / {_r.Next(1, 5)}", $"Math.Max(x, {Small()})", $"Math.Min(x, {Small()})", $"(x > {Small()} ? 1 : 0)" }[_r.Next(6)];

        private string Cmp() => new[] { "<", "<=", ">", ">=", "==", "!=" }[_r.Next(6)];

        private string Bool(int depth, string extra)
        {
            if (depth <= 0 || _r.Next(3) == 0) return $"{Int(1, extra)} {Cmp()} {Int(1, extra)}";
            int d = depth - 1;
            switch (_r.Next(_spec ? 6 : 7))
            {
                case 0: return $"({Bool(d, extra)} && {Bool(d, extra)})";
                case 1: return $"({Bool(d, extra)} || {Bool(d, extra)})";
                case 2: return $"!({Bool(d, extra)})";
                case 3: return _r.Next(2) == 0 ? $"double.IsNaN({Double(d)})" : $"{Double(d)} {Cmp()} {Double(d)}";
                case 4:
                {
                    // aliasing, and records' value equality
                    if (_p.Pts.Count > 0 && _r.Next(2) == 0) return $"{Pick(_p.Pts)} {(_r.Next(2) == 0 ? "==" : "!=")} {Pick(_p.Pts)}";
                    return $"{Pick(_p.Cells)} {(_r.Next(2) == 0 ? "==" : "!=")} {(_r.Next(2) == 0 ? "d" : Pick(_p.Cells))}";
                }
                case 6: return $"xs.Any(x => {Lambda()})";
                default: return $"{Int(d, extra)} {Cmp()} {Int(d, extra)}";
            }
        }

        // ------------------------------------------------------------------ rendering

        private static void Emit(StringBuilder sb, Stmt s, int indent, Mode mode, Func<int, bool> kept)
        {
            var pad = new string(' ', 4 * indent);
            void Body(List<Stmt> list)
            {
                sb.AppendLine($"{pad}{{");
                foreach (var t in list) Emit(sb, t, indent + 1, mode, kept);
                sb.AppendLine($"{pad}}}");
            }
            switch (s)
            {
                case Line l: sb.AppendLine(pad + l.Text); break;
                case Assert a:
                    if (!kept(a.Id)) break;
                    sb.AppendLine(mode == Mode.Verify ? $"{pad}Spec.Assert({a.Cond});"
                                : mode == Mode.Run ? $"{pad}if (!({a.Cond})) throw new Failed(\"assertion {a.Id}\");"
                                : $"{pad}Probe.Hit({a.Id}, () => {a.Cond});");
                    break;
                case If i:
                    sb.AppendLine($"{pad}if ({i.Cond})");
                    Body(i.Then);
                    if (i.Else != null)
                    {
                        sb.AppendLine($"{pad}else");
                        Body(i.Else);
                    }
                    break;
                case For f:
                {
                    var invariants = f.Invariants.Where(a => kept(a.Id)).ToList();
                    if (mode == Mode.Verify)
                    {
                        sb.AppendLine($"{pad}for (int {f.Var} = 0; {f.Var} < xs.Length; {f.Var}++)");
                        sb.AppendLine($"{pad}{{");
                        foreach (var a in invariants) sb.AppendLine($"{pad}    Spec.Invariant({a.Cond});");
                        foreach (var t in f.Body) Emit(sb, t, indent + 1, mode, kept);
                        sb.AppendLine($"{pad}}}");
                        break;
                    }
                    // (to run: the loop as a while, its invariants checked at every head, the last, on leaving, too)
                    sb.AppendLine($"{pad}{{");
                    sb.AppendLine($"{pad}    int {f.Var} = 0;");
                    sb.AppendLine($"{pad}    while (true)");
                    sb.AppendLine($"{pad}    {{");
                    foreach (var a in invariants)
                        sb.AppendLine(mode == Mode.Run ? $"{pad}        if (!({a.Cond})) throw new Failed(\"invariant {a.Id}\");" : $"{pad}        Probe.Hit({a.Id}, () => {a.Cond});");
                    sb.AppendLine($"{pad}        if (!({f.Var} < xs.Length)) break;");
                    foreach (var t in f.Body) Emit(sb, t, indent + 2, mode, kept);
                    sb.AppendLine($"{pad}        {f.Var}++;");
                    sb.AppendLine($"{pad}    }}");
                    sb.AppendLine($"{pad}}}");
                    break;
                }
                case Try t:
                    sb.AppendLine($"{pad}try");
                    Body(t.Body);
                    sb.AppendLine($"{pad}catch ({t.Catches})");
                    Body(t.Handler);
                    break;
            }
        }
    }
}
