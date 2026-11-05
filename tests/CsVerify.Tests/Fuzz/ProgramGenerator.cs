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

        /// <summary>The most statements a body has (a soak can ask for bigger programs).</summary>
        public int Size = 4;

        public ProgramGenerator(int seed) { _r = new Random(seed); }

        public enum Mode { Verify, Run, Probe }

        /// <summary>What both the verified and the running program declare.</summary>
        public const string Prelude = @"
public sealed class Cell { public int V; }
public sealed record Pt(int X, int Y);
public sealed class Escape : Exception { }
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
                else sb.AppendLine($"        if (!({Pre})) throw new Skip();");
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
            public Pools Copy() => new Pools { Ints = Ints.ToList(), Doubles = Doubles.ToList(), Cells = Cells.ToList(), Pts = Pts.ToList() };
        }

        public Method Next(string name)
        {
            _fresh = 0;
            _slots = 0;
            var m = new Method { Name = name };
            m.Pinned = _r.Next(3) > 0;
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
        internal sealed class For : Stmt { public string Var; public List<Stmt> Body; }
        internal sealed class Try : Stmt { public List<Stmt> Body, Handler; public string Catches; }
        internal sealed class Assert : Stmt { public string Cond; public int Id; }

        private List<Stmt> Block(int n)
        {
            var saved = _p.Copy();
            var list = new List<Stmt>();
            for (int k = 0; k < n; k++) list.Add(Statement());
            _p = saved; // (a block's declarations end with it)
            return list;
        }

        private Stmt Statement()
        {
            _depth++;
            try
            {
                switch (_r.Next(_depth > 1 ? 9 : 13))
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
                    case 9:
                    case 10: return new If { Cond = Bool(2, null), Then = Block(_r.Next(1, 3)), Else = _r.Next(2) == 0 ? Block(_r.Next(1, 3)) : null };
                    case 11: return new Try { Body = Block(_r.Next(1, 3)), Catches = "Escape", Handler = Block(_r.Next(1, 2)) };
                    default:
                    {
                        if (_inLoop) goto case 3;
                        var i = "i" + _fresh++;
                        _p.Ints.Add(i);
                        _inLoop = true;
                        var body = Block(_r.Next(1, 3));
                        _inLoop = false;
                        _p.Ints.Remove(i);
                        return new For { Var = i, Body = body };
                    }
                }
            }
            finally { _depth--; }
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
                case 7: return $"Math.Abs({Int(d, extra)})";
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
                    default: return $"(double){Int(0)}";
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
                    sb.AppendLine($"{pad}for (int {f.Var} = 0; {f.Var} < xs.Length; {f.Var}++)");
                    Body(f.Body);
                    break;
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
