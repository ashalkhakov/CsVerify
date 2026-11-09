using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.CodeAnalysis;
using static CsVerify.Verifier.Boogie.KernelTypes;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>
    /// Pass 4: the kernel, after Checks and Heap, as Boogie text; each check on a line of its own, which
    /// <see cref="Lines"/> maps back to the CsVerify diagnostic it is.
    /// </summary>
    internal sealed class BoogiePrinter
    {
        private readonly StringBuilder _text = new StringBuilder();
        private int _line = 1;

        public readonly Dictionary<int, Check> Lines = new Dictionary<int, Check>();

        public string Text => _text.ToString();

        private void Line(string text, Check check = null)
        {
            if (check != null) Lines[_line] = check;
            _text.Append(text).Append('\n');
            _line++;
        }

        private static string Param(SpecialType t) => "m" + t.ToString().Substring("System_".Length);

        private static readonly string InRangeOfMemory = "$InRange(" + string.Join(", ", Widths.Keys.Select(ElementMap)) + ")";

        private static string MapParams => string.Join(", ", ElementTypes.Select(t => $"h{ElementMap(t)}: [Ref][int]{(t == SpecialType.System_Boolean ? "bool" : "int")}"));

        /// <summary>What every program has: C#'s division, fuel, and the heap of arrays (Dafny's encoding).</summary>
        public void Prelude()
        {
            Line("// C#'s / and % truncate toward zero; Boogie's div and mod are Euclidean");
            Line("function cs#div(a: int, b: int): int { if a >= 0 then (if b > 0 then a div b else -(a div (-b))) else (if b > 0 then -((-a) div b) else (-a) div (-b)) }");
            Line("function cs#rem(a: int, b: int): int { a - b * cs#div(a, b) }");
            Line("// fuel, as Dafny's: a function's definition unfolds once for each $LS");
            Line("type LayerType;");
            Line("const $LZ: LayerType;");
            Line("function $LS(ly: LayerType): LayerType;");
            Line("// arrays: references, the allocated ones, each one's length, and a map of elements per element type");
            Line("type Ref;");
            Line("const null: Ref;");
            Line("var $Alloc: [Ref]bool;");
            Line("function len(a: Ref): int;");
            Line("axiom (forall a: Ref :: 0 <= len(a) && len(a) <= 2147483647); // (an array's Length is an int)");
            foreach (var t in ElementTypes) Line($"var {ElementMap(t)}: [Ref][int]{(t == SpecialType.System_Boolean ? "bool" : "int")};");
            Line("// what is read from memory is in its type's range");
            Line("function $InRange(" + string.Join(", ", Widths.Keys.Select(t => $"{Param(t)}: [Ref][int]int")) + "): bool { " +
                 string.Join(" && ", Widths.Keys.Select(t => { var (lo, hi) = Range(t); return $"(forall r: Ref, j: int :: {lo} <= {Param(t)}[r][j] && {Param(t)}[r][j] <= {hi})"; })) + " }");
        }

        // ------------------------------------------------------------------ expressions

        /// <summary>Where an expression is: in a procedure, or in a function's axiom (its layer, its maps h-named, what stands for its result).</summary>
        private sealed class Context
        {
            public bool InFunction;
            public string Layer = "$LS($LZ)";
            public string Result = "result";
        }

        private static readonly Context InProcedure = new Context();

        private static string Map(string name, Context cx) => cx.InFunction && name.StartsWith("$E.") ? "h" + name : name;

        private static string Maps(Context cx) => string.Join(", ", ElementTypes.Select(t => Map(ElementMap(t), cx)));

        private static string E(KExpr e, Context cx)
        {
            switch (e)
            {
                case KLit l: return l.Text;
                case KVar v: return v.Name == "result" ? cx.Result : Map(v.Name, cx);
                case KFnApp f: return $"{f.Function}({f.Layer ?? cx.Layer}, {Maps(cx)}{string.Join("", f.Args.Select(a => ", " + E(a, cx)))})";
                case KQuant q when q.Range == null: return $"(forall {q.Var}: int :: {E(q.Body, cx)})";
                case KQuant q: return q.Forall ? $"(forall {q.Var}: int :: {E(q.Range, cx)} ==> {E(q.Body, cx)})" : $"(exists {q.Var}: int :: {E(q.Range, cx)} && {E(q.Body, cx)})";
                case KOp op:
                {
                    var a = op.Args.Select(x => E(x, cx)).ToArray();
                    switch (op.Op)
                    {
                        case "!": return $"!({a[0]})";
                        case "ite": return $"(if {a[0]} then {a[1]} else {a[2]})";
                        case "div": return $"cs#div({a[0]}, {a[1]})";
                        case "rem": return $"cs#rem({a[0]}, {a[1]})";
                        case "len": return $"len({a[0]})";
                        case "old": return $"old({a[0]})";
                        case "wrap": return $"((({a[0]}) - ({a[1]})) mod {a[2]} + ({a[1]}))";
                        case "sel": return a.Length == 2 ? $"{a[0]}[{a[1]}]" : $"{a[0]}[{a[1]}][{a[2]}]";
                        default:
                            if (a.Length != 2) throw new NotTranslated("the kernel's operator " + op.Op);
                            return $"({a[0]} {op.Op} {a[1]})";
                    }
                }
                default: throw new NotTranslated("not printable: " + e.GetType().Name);
            }
        }

        // ------------------------------------------------------------------ functions

        /// <summary>
        /// A function procedure as a Boogie function too: declared on a layer and the heap's maps; defined, where its
        /// precondition holds, by its body on the next layer (so one unfolding per use); its postcondition, and its
        /// range for a run-time one, of every value.
        /// </summary>
        public void Function(KProcedure p)
        {
            var m = p.Method;
            var name = FunctionName(m);
            var ps = string.Join("", m.Parameters.Select(x => $", {Local(x)}: {TypeOf(x.Type)}"));
            var args = string.Join("", m.Parameters.Select(x => ", " + Local(x)));
            var bound = $"ly: LayerType, {MapParams}{ps}";
            string At(string layer) => $"{name}({layer}, {string.Join(", ", ElementTypes.Select(t => "h" + ElementMap(t)))}{args})";
            Line($"function {name}(ly: LayerType, {MapParams}{ps}): {TypeOf(m.ReturnType)};");
            Line($"axiom (forall {bound} :: {{ {At("$LS(ly)")} }} {At("$LS(ly)")} == {At("ly")});");
            var cx = new Context { InFunction = true, Layer = "ly", Result = At("ly") };
            var guard = p.Requires.Count == 0 ? "true" : string.Join(" && ", p.Requires.Select(r => E(r.Expr, cx)));
            Line($"axiom (forall {bound} :: {{ {At("$LS(ly)")} }} {guard} ==> {At("$LS(ly)")} == {E(p.FunctionBody, cx)});");
            foreach (var e in p.Ensures) Line($"axiom (forall {bound} :: {{ {At("ly")} }} {guard} ==> {E(e.Expr, cx)});");
            if (!p.Ghost && IsIntegral(m.ReturnType)) Line($"axiom (forall {bound} :: {{ {At("ly")} }} {E(InRange(new KLit(At("ly")), m.ReturnType), cx)});");
        }

        // ------------------------------------------------------------------ procedures

        /// <summary>A procedure: its header (what it modifies: <paramref name="modifies"/>, closed over calls), its locals, its blocks.</summary>
        public void Procedure(KProcedure p, ISet<string> modifies, bool isFunction)
        {
            var m = p.Method;
            var cx = InProcedure;
            var ps = string.Join(", ", m.Parameters.Select(x => $"{Local(x)}: {TypeOf(x.Type)}"));
            var ret = m.ReturnsVoid ? "" : $" returns (result: {TypeOf(m.ReturnType)})";
            Line($"procedure {p.Name}({ps}){ret}");
            if (modifies.Count > 0) Line($"  modifies {string.Join(", ", Heap.Globals.Where(modifies.Contains))};");
            if (modifies.Contains("$Alloc")) Line("  free ensures (forall r: Ref :: old($Alloc[r]) ==> $Alloc[r]);");
            Line($"  free requires {InRangeOfMemory};");
            Line($"  free ensures {InRangeOfMemory};");
            foreach (var x in m.Parameters)
            {
                if (IsIntegral(x.Type)) Line($"  free requires {E(InRange(new KVar(Local(x)), x.Type), cx)};");
                if (IsArray(x.Type))
                {
                    Line($"  free requires {Local(x)} == null || $Alloc[{Local(x)}];");
                    // (not null: checked at each call's argument)
                    if (NotNullable(x.Type)) Line($"  free requires {Local(x)} != null;");
                }
            }
            foreach (var r in p.Requires) Line($"  requires {E(r.Expr, cx)};", r.Check);
            // (checked at each return, where it is reported: Boogie would report one return path of each)
            foreach (var e in p.Ensures) Line($"  free ensures {E(e.Expr, cx)};");
            if (!m.ReturnsVoid && IsIntegral(m.ReturnType) && !p.Ghost) Line($"  free ensures {E(InRange(new KVar("result"), m.ReturnType), cx)};");
            if (isFunction) Line($"  free ensures result == {FunctionName(m)}($LZ, {Maps(cx)}{string.Join("", m.Parameters.Select(x => ", " + Local(x)))});");
            if (!m.ReturnsVoid && IsArray(m.ReturnType))
            {
                Line("  free ensures result == null || $Alloc[result];");
                if (NotNullable(m.ReturnType)) Line("  free ensures result != null;");
            }
            Line("{");
            // (an integer variable is always in its type's range: where Boogie havocs it, at a loop head, too)
            foreach (var l in p.Locals)
                Line(IsIntegral(l.Type) ? $"  var {l.Name}: int where {E(InRange(new KVar(l.Name), l.Type), cx)};" : $"  var {l.Name}: {TypeOf(l.Type)};");
            foreach (var s in p.Entry) Statement(s, cx);
            foreach (var b in p.Blocks)
            {
                Line($"  {b.Label}:");
                foreach (var s in b.Stmts) Statement(s, cx);
                switch (b.Jump)
                {
                    case KGoto g: Line($"    goto {string.Join(", ", g.Targets)};"); break;
                    case KReturn _: Line("    return;"); break;
                    default: Line("    assume false;"); Line("    return;"); break;
                }
            }
            Line("}");
        }

        private void Statement(KStmt s, Context cx)
        {
            switch (s)
            {
                case KAssign a: Line($"    {a.Var} := {E(a.Value, cx)};"); return;
                case KMapUpdate u: Line($"    {u.Map}[{E(u.Ref, cx)}]{(u.Index == null ? "" : $"[{E(u.Index, cx)}]")} := {E(u.Value, cx)};"); return;
                case KAssert a: Line($"    assert {(a.NotAssumedAfter ? "{:subsumption 0} " : "")}{E(a.Cond, cx)};", a.Check); return;
                case KAssume a: Line($"    assume {E(a.Cond, cx)};"); return;
                case KHavoc h: Line($"    havoc {h.Var};"); return;
                case KCall c:
                    Line($"    call {(c.Result == null ? "" : c.Result + " := ")}{Name(c.Callee)}({string.Join(", ", c.Args.Select(a => E(a, cx)))});", c.Check);
                    return;
                default: throw new NotTranslated("not printable: " + s.GetType().Name);
            }
        }
    }
}
