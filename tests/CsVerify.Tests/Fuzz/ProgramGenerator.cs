using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace CsVerify.Tests.Fuzz
{
    /// <summary>
    /// Random methods for testing the verifier itself, after "Testing Dafny" (Irfan et al., ISSTA 2022). Each method
    /// is rendered twice: with its specifications (Spec.Requires, Spec.Ensures, Spec.Assert) for the verifier, and with
    /// them as run-time checks for running. A method the verifier reports verified must pass its checks, and not throw,
    /// on every input its precondition admits; one that does not is a soundness bug.
    ///
    /// Methods take (int a, int b, int[] xs) and return an int. Their preconditions either pin every input to a constant
    /// (the verifier is then all but exact, so random assertions often verify, which is what makes the test bite) or
    /// bound them. Bodies are declarations, assignments, array writes, ifs, for loops over xs, assertions, and
    /// expressions with arithmetic, Math, conditionals, array reads and LINQ.
    /// </summary>
    public sealed class ProgramGenerator
    {
        private readonly Random _r;
        private List<string> _locals = new List<string>();
        private int _fresh;
        private int _depth;
        private bool _inLoop;
        private int _slots;
        private bool _spec; // (in a specification: no LINQ, which is not [Pure])

        /// <summary>The most statements a body has (a soak can ask for bigger programs).</summary>
        public int Size = 4;

        public ProgramGenerator(int seed) { _r = new Random(seed); }

        public enum Mode { Verify, Run, Probe }

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
            public List<(int a, int b, int[] xs)> Inputs = new List<(int, int, int[])>();
            public List<(int a, int b, int[] xs)> Fresh = new List<(int, int, int[])>();

            /// <summary>
            /// The method as the verifier sees it (Mode.Verify), with checks (Mode.Run), or recording every slot and
            /// candidate postcondition (Mode.Probe): with the slots in keep (and planted), and the postcondition post.
            /// </summary>
            public string Render(Mode mode, string name, ISet<int> keep = null, int planted = -1, int post = -1)
            {
                var sb = new StringBuilder();
                sb.AppendLine($"    public static int {name}(int a, int b, int[] xs)");
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

        public Method Next(string name)
        {
            _locals = new List<string>();
            _fresh = 0;
            _slots = 0;
            var m = new Method { Name = name };
            m.Pinned = _r.Next(3) > 0;
            if (m.Pinned)
            {
                int a = Small(), b = Small();
                var xs = Enumerable.Range(0, _r.Next(5)).Select(_ => Small()).ToArray();
                m.Pre = $"a == {a} && b == {b} && xs.Length == {xs.Length}" + string.Concat(xs.Select((x, i) => $" && xs[{i}] == {x}"));
                m.Inputs.Add((a, b, xs));
            }
            else
            {
                int bound = new[] { 10, 100, 1000 }[_r.Next(3)];
                m.Pre = $"-{bound} <= a && a <= {bound} && -{bound} <= b && b <= {bound} && Spec.Forall(0, xs.Length, i => -{bound} <= xs[i] && xs[i] <= {bound})";
                int minLength = _r.Next(2) == 0 ? _r.Next(1, 3) : 0;
                if (minLength > 0) m.Pre += $" && xs.Length >= {minLength}";
                (int, int, int[]) Input() => (_r.Next(-bound, bound + 1), _r.Next(-bound, bound + 1),
                                              Enumerable.Range(0, _r.Next(minLength, 6)).Select(_ => _r.Next(-bound, bound + 1)).ToArray());
                // (the extremes too: where overflow and off-by-one live)
                (int, int, int[]) Edge() => (_r.Next(2) == 0 ? bound : -bound, _r.Next(2) == 0 ? bound : -bound,
                                             Enumerable.Range(0, _r.Next(minLength, 6)).Select(_ => _r.Next(2) == 0 ? bound : -bound).ToArray());
                for (int k = 0; k < 30; k++) m.Inputs.Add(k % 5 == 0 ? Edge() : Input());
                for (int k = 0; k < 60; k++) m.Fresh.Add(k % 5 == 0 ? Edge() : Input());
            }
            _locals.Add("a");
            _locals.Add("b");
            m.Body = Block(_r.Next(1, 1 + Size));
            m.Result = Int(2);
            _locals = new List<string> { "a", "b" }; // (a postcondition is stated before the body's locals)
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

        // ------------------------------------------------------------------ statements

        internal abstract class Stmt { }
        internal sealed class Decl : Stmt { public string Name, Value; }
        internal sealed class Assign : Stmt { public string Name, Value; }
        internal sealed class Store : Stmt { public string Index, Value; }
        internal sealed class If : Stmt { public string Cond; public List<Stmt> Then, Else; }
        internal sealed class For : Stmt { public string Var; public List<Stmt> Body; }
        internal sealed class Assert : Stmt { public string Cond; public int Id; }

        private List<Stmt> Block(int n)
        {
            var saved = _locals.ToList();
            var list = new List<Stmt>();
            for (int k = 0; k < n; k++) list.Add(Statement());
            _locals = saved; // (a block's declarations end with it)
            return list;
        }

        private Stmt Statement()
        {
            _depth++;
            try
            {
                int pick = _r.Next(_depth > 1 ? 4 : 7);
                switch (pick)
                {
                    case 0:
                    {
                        var v = "v" + _fresh++;
                        var d = new Decl { Name = v, Value = Int(2) };
                        _locals.Add(v);
                        return d;
                    }
                    case 1:
                    {
                        var targets = _locals.Where(l => l.StartsWith("v")).ToList();
                        if (targets.Count == 0) goto case 0;
                        return new Assign { Name = targets[_r.Next(targets.Count)], Value = Int(2) };
                    }
                    case 2: return new Store { Index = Index(), Value = Int(1) };
                    case 3: return new Assert { Cond = Spec(() => Bool(2, null)), Id = _slots++ };
                    case 4:
                    case 5: return new If { Cond = Bool(2, null), Then = Block(_r.Next(1, 3)), Else = _r.Next(2) == 0 ? Block(_r.Next(1, 3)) : null };
                    default:
                    {
                        if (_inLoop) goto case 3;
                        var i = "i" + _fresh++;
                        _locals.Add(i);
                        _inLoop = true;
                        var body = Block(_r.Next(1, 3));
                        _inLoop = false;
                        _locals.Remove(i);
                        return new For { Var = i, Body = body };
                    }
                }
            }
            finally { _depth--; }
        }

        // ------------------------------------------------------------------ expressions

        private string Var() => _locals[_r.Next(_locals.Count)];

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
                switch (_r.Next(extra != null ? 4 : 3))
                {
                    case 0: return Small().ToString();
                    case 1: return "xs.Length";
                    case 3: return extra;
                    default: return Var();
                }
            }
            int d = depth - 1;
            // (LINQ one time in eight: each call is a definition the verifier runs, so it is the costly part)
            int kind = _spec || _r.Next(8) > 0 ? _r.Next(10) : 10 + _r.Next(4);
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
                    var loopVar = _locals.LastOrDefault(l => l.StartsWith("i"));
                    if (loopVar != null && _r.Next(2) == 0) return $"xs[{loopVar}]";
                    return $"(xs.Length == 0 ? 0 : xs[{Index()}])";
                }
                case 10: return $"xs.Count(x => {Lambda()})";
                case 11: return $"xs.Where(x => {Lambda()}).Count()";
                case 12: return _r.Next(2) == 0 ? "xs.Sum()" : $"xs.Select(x => {LambdaInt()}).Sum()";
                default: return _r.Next(2) == 0 ? $"(xs.Length == 0 ? 0 : xs.{(_r.Next(2) == 0 ? "Max" : "Min")}())" : $"xs.Select(x => {LambdaInt()}).FirstOrDefault()";
            }
        }

        // a divisor: often one that cannot be zero
        private string Divisor(int depth, string extra) =>
            _r.Next(3) == 0 ? Int(depth, extra) : _r.Next(2) == 0 ? (_r.Next(1, 7) * (_r.Next(2) == 0 ? 1 : -1)).ToString() : $"(Math.Abs({Int(depth, extra)}) % 5 + 1)";

        private string Lambda() => $"x {Cmp()} {Small()}";
        // (a lambda is verified on its own, for any x: so nothing that can overflow)
        private string LambdaInt() => new[] { "x", $"x % {_r.Next(1, 5)}", $"x / {_r.Next(1, 5)}", $"Math.Max(x, {Small()})", $"Math.Min(x, {Small()})", $"(x > {Small()} ? 1 : 0)" }[_r.Next(6)];

        private string Cmp() => new[] { "<", "<=", ">", ">=", "==", "!=" }[_r.Next(6)];

        private string Bool(int depth, string extra)
        {
            if (depth <= 0 || _r.Next(3) == 0) return $"{Int(1, extra)} {Cmp()} {Int(1, extra)}";
            int d = depth - 1;
            switch (_r.Next(_spec ? 3 : 5))
            {
                case 0: return $"({Bool(d, extra)} && {Bool(d, extra)})";
                case 1: return $"({Bool(d, extra)} || {Bool(d, extra)})";
                case 2: return $"!({Bool(d, extra)})";
                case 3: return $"xs.Any(x => {Lambda()})";
                default: return $"{Int(d, extra)} {Cmp()} {Int(d, extra)}";
            }
        }

        // ------------------------------------------------------------------ rendering

        private static void Emit(StringBuilder sb, Stmt s, int indent, Mode mode, Func<int, bool> kept)
        {
            var pad = new string(' ', 4 * indent);
            switch (s)
            {
                case Decl d: sb.AppendLine($"{pad}int {d.Name} = {d.Value};"); break;
                case Assign a: sb.AppendLine($"{pad}{a.Name} = {a.Value};"); break;
                case Store st: sb.AppendLine($"{pad}if (xs.Length > 0) xs[{st.Index}] = {st.Value};"); break;
                case Assert a:
                    if (!kept(a.Id)) break;
                    sb.AppendLine(mode == Mode.Verify ? $"{pad}Spec.Assert({a.Cond});"
                                : mode == Mode.Run ? $"{pad}if (!({a.Cond})) throw new Failed(\"assertion {a.Id}\");"
                                : $"{pad}Probe.Hit({a.Id}, () => {a.Cond});");
                    break;
                case If i:
                    sb.AppendLine($"{pad}if ({i.Cond})");
                    sb.AppendLine($"{pad}{{");
                    foreach (var t in i.Then) Emit(sb, t, indent + 1, mode, kept);
                    sb.AppendLine($"{pad}}}");
                    if (i.Else != null)
                    {
                        sb.AppendLine($"{pad}else");
                        sb.AppendLine($"{pad}{{");
                        foreach (var t in i.Else) Emit(sb, t, indent + 1, mode, kept);
                        sb.AppendLine($"{pad}}}");
                    }
                    break;
                case For f:
                    sb.AppendLine($"{pad}for (int {f.Var} = 0; {f.Var} < xs.Length; {f.Var}++)");
                    sb.AppendLine($"{pad}{{");
                    foreach (var t in f.Body) Emit(sb, t, indent + 1, mode, kept);
                    sb.AppendLine($"{pad}}}");
                    break;
            }
        }
    }
}
