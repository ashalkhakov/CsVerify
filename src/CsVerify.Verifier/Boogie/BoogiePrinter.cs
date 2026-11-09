using System;
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
        /// <summary>
        /// A function that reads arrays only through its own array parameters: each one's elements (its argument,
        /// and the element map it is read from), which it takes in place of the element maps. Null: the maps.
        /// </summary>
        public Func<IMethodSymbol, List<(int arg, string param, string map)>> OwnArrays = _ => null;

        /// <summary>The maps of [Owned] classes' fields: a call changes them only at the objects whose views it gets.</summary>
        public HashSet<string> OwnedMaps = new HashSet<string>();

        private sealed class Context
        {
            /// <summary>The ref parameters, named by their values on entry (p$x$in) where this says so: in requires, and in old().</summary>
            public HashSet<string> Ins = new HashSet<string>();
            public bool AtEntry;
            /// <summary>In such a function: each array parameter's elements.</summary>
            public Dictionary<string, string> Elems;
            public bool InFunction;
            public string Layer = "$LS($LZ)";
            public string Result = "result";
        }

        private static readonly Context InProcedure = new Context();

        private static string Map(string name, Context cx) => cx.InFunction && (name.StartsWith("$E.") || name.StartsWith("$F.")) ? "h" + name : name;

        private static string Maps(Context cx) => string.Join(", ", ElementTypes.Select(t => Map(ElementMap(t), cx)));

        private string E(KExpr e, Context cx)
        {
            switch (e)
            {
                case KLit l: return l.Text;
                case KVar v when cx.AtEntry && cx.Ins.Contains(v.Name): return v.Name + "$in";
                case KVar v: return v.Name == "result" ? cx.Result : Map(v.Name, cx);
                case KOp { Op: "old" } old when cx.Ins.Count > 0 && !cx.AtEntry:
                    return $"old({E(old.Args[0], new Context { Ins = cx.Ins, AtEntry = true, Elems = cx.Elems, InFunction = cx.InFunction, Layer = cx.Layer, Result = cx.Result })})";
                case KFnApp f:
                {
                    var own = OwnArrays(f.Callee);
                    var parts = new List<string> { f.Layer ?? cx.Layer };
                    if (own == null) parts.Add(Maps(cx));
                    else parts.AddRange(own.Select(o => Elements(o.map, f.Args[o.arg], cx)));
                    parts.AddRange(f.Fields.Select(x => Map(x, cx)));
                    parts.AddRange(f.Args.Select(a => E(a, cx)));
                    return $"{f.Function}({string.Join(", ", parts)})";
                }
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
                        case "sel" when a.Length == 3 && op.Args[1] is KVar arr && cx.Elems != null && cx.Elems.TryGetValue(arr.Name, out var elems):
                            return $"{elems}[{a[2]}]";
                        case "sel": return a.Length == 2 ? $"{a[0]}[{a[1]}]" : $"{a[0]}[{a[1]}][{a[2]}]";
                        case "store": return $"{a[0]}[{a[1]} := {a[2]}]";
                        case "lambda": return $"(lambda {a[0]} :: {a[1]})";
                        case "inst": return $"{a[0]}({string.Join(", ", a.Skip(1))})";
                        default:
                            if (a.Length != 2) throw new NotTranslated("the kernel's operator " + op.Op);
                            return $"({a[0]} {op.Op} {a[1]})";
                    }
                }
                default: throw new NotTranslated("not printable: " + e.GetType().Name);
            }
        }

        // ------------------------------------------------------------------ predicates

        /// <summary>
        /// Predicate instances: a type of their own, each predicate's a constructor of its arguments, injective (as its
        /// inverses say) and of its own kind, none of them i#none (what owns an object no instance does).
        /// </summary>
        public void Instances(IEnumerable<IMethodSymbol> preds)
        {
            Line("type Inst;");
            Line("const i#none: Inst;");
            Line("function i#kind(q: Inst): int;");
            Line("axiom i#kind(i#none) == 0;");
            int kind = 0;
            foreach (var p in preds.OrderBy(x => Checks.InstanceName(x), System.StringComparer.Ordinal))
            {
                kind++;
                var name = Checks.InstanceName(p);
                var xs = p.Parameters.Select((x, k) => (name: "x" + k, type: TypeOf(x.Type))).ToList();
                Line($"function {name}({string.Join(", ", xs.Select(x => $"{x.name}: {x.type}"))}): Inst;");
                for (int k = 0; k < xs.Count; k++) Line($"function {name}#{k}(q: Inst): {xs[k].type};");
                var app = $"{name}({string.Join(", ", xs.Select(x => x.name))})";
                var facts = new[] { $"i#kind({app}) == {kind}" }.Concat(xs.Select((x, k) => $"{name}#{k}({app}) == {x.name}"));
                Line(xs.Count == 0 ? $"axiom {string.Join(" && ", facts)};"
                    : $"axiom (forall {string.Join(", ", xs.Select(x => $"{x.name}: {x.type}"))} :: {{ {app} }} {string.Join(" && ", facts)});");
            }
        }

        // ------------------------------------------------------------------ fields

        /// <summary>
        /// Each field's map, object to value (a static field's at null): an integer one's values in its type's range,
        /// which Boogie assumes wherever it forgets the map (after a call that modifies it, at a loop head).
        /// </summary>
        public void Fields(IEnumerable<ISymbol> fields)
        {
            foreach (var f in fields.OrderBy(FieldMap, System.StringComparer.Ordinal))
            {
                var map = FieldMap(f);
                var t = FieldType(f);
                var where = IsIntegral(t) ? $" where (forall o: Ref :: {E(InRange(new KOp("sel", new KVar(map), new KVar("o")), t), InProcedure)})" : "";
                Line($"var {map}: [Ref]{TypeOf(t)}{where};");
            }
        }

        private static string FieldParams(IEnumerable<string> fields, IEnumerable<ISymbol> symbols) =>
            string.Join("", fields.Select(x => $", h{x}: [Ref]{TypeOf(FieldType(symbols.First(s => FieldMap(s) == x)))}"));

        /// <summary>An array's elements, as an argument: a parameter's own, or read from the map.</summary>
        private string Elements(string map, KExpr array, Context cx) =>
            array is KVar v && cx.Elems != null && cx.Elems.TryGetValue(v.Name, out var elems) ? elems : $"{Map(map, cx)}[{E(array, cx)}]";

        // ------------------------------------------------------------------ functions

        /// <summary>
        /// A function procedure as a Boogie function too: declared on a layer and the heap's maps; defined, where its
        /// precondition holds, by its body on the next layer (so one unfolding per use); its postcondition, and its
        /// range for a run-time one, of every value.
        /// </summary>
        public void Function(KProcedure p, List<string> fields, IEnumerable<ISymbol> symbols)
        {
            var m = p.Method;
            var name = FunctionName(m);
            var self = m.IsStatic ? "" : ", this: Ref";
            var ps = FieldParams(fields, symbols) + self + string.Join("", m.Parameters.Select(x => $", {Local(x)}: {TypeOf(x.Type)}"));
            var args = string.Join("", fields.Select(x => ", h" + x)) + (m.IsStatic ? "" : ", this") + string.Join("", m.Parameters.Select(x => ", " + Local(x)));
            var own = OwnArrays(m);
            var memory = own == null ? MapParams : string.Join(", ", own.Select(o => $"e{o.param}: [int]{(o.map == ElementMap(SpecialType.System_Boolean) ? "bool" : "int")}"));
            var memoryArgs = own == null ? string.Join(", ", ElementTypes.Select(t => "h" + ElementMap(t))) : string.Join(", ", own.Select(o => "e" + o.param));
            string Sep(string x) => x.Length == 0 ? "" : ", " + x;
            var bound = $"ly: LayerType{Sep(memory)}{ps}";
            string At(string layer) => $"{name}({layer}{Sep(memoryArgs)}{args})";
            Line($"function {name}(ly: LayerType{Sep(memory)}{ps}): {TypeOf(m.ReturnType)};");
            Line($"axiom (forall {bound} :: {{ {At("$LS(ly)")} }} {At("$LS(ly)")} == {At("ly")});");
            var cx = new Context { InFunction = true, Layer = "ly", Result = At("ly"), Elems = own?.ToDictionary(o => o.param, o => "e" + o.param) };
            var guard = p.Requires.Count == 0 ? "true" : string.Join(" && ", p.Requires.Select(r => E(r.Expr, cx)));
            Line($"axiom (forall {bound} :: {{ {At("$LS(ly)")} }} {guard} ==> {At("$LS(ly)")} == {E(p.FunctionBody, cx)});");
            foreach (var e in p.Ensures) Line($"axiom (forall {bound} :: {{ {At("ly")} }} {guard} ==> {E(e.Expr, cx)});");
            if (!p.Ghost && IsIntegral(m.ReturnType)) Line($"axiom (forall {bound} :: {{ {At("ly")} }} {E(InRange(new KLit(At("ly")), m.ReturnType), cx)});");
        }

        // ------------------------------------------------------------------ procedures

        /// <summary>A procedure: its header (what it modifies: <paramref name="modifies"/>, closed over calls), its locals, its blocks.</summary>
        public void Procedure(KProcedure p, ISet<string> modifies, ISet<string> anyWrites, List<string> functionFields)
        {
            var m = p.Method;
            var ins = m.Parameters.Where(x => x.RefKind == RefKind.Ref).Select(Local).ToHashSet();
            var cx = new Context { Ins = ins };
            var atEntry = new Context { Ins = ins, AtEntry = true };
            // (a ref parameter comes in as p$x$in and goes out as p$x; an out one only goes out)
            var ps = string.Join(", ", (p.HasThis ? new[] { "this: Ref" } : new string[0])
                .Concat(m.Parameters.Where(x => x.RefKind != RefKind.Out).Select(x => $"{Local(x)}{(x.RefKind == RefKind.Ref ? "$in" : "")}: {TypeOf(x.Type)}")));
            var outs = (m.ReturnsVoid ? new string[0] : new[] { $"result: {TypeOf(m.ReturnType)}" })
                .Concat(m.Parameters.Where(x => x.RefKind is RefKind.Ref or RefKind.Out).Select(x => $"{Local(x)}: {TypeOf(x.Type)}")).ToList();
            var ret = outs.Count == 0 ? "" : $" returns ({string.Join(", ", outs)})";
            Line($"procedure {p.Name}({ps}){ret}", Undecided(p));
            if (modifies.Count > 0)
                Line($"  modifies {string.Join(", ", Heap.Globals.Where(modifies.Contains).Concat(modifies.Where(x => x.StartsWith("$F.")).OrderBy(x => x, System.StringComparer.Ordinal)))};");
            if (modifies.Contains("$Alloc")) Line("  free ensures (forall r: Ref :: old($Alloc[r]) ==> $Alloc[r]);");
            // (a field written only at this object, in its constructor, or at objects allocated since: the same at every other)
            foreach (var map in modifies.Where(x => x.StartsWith("$F.") && !anyWrites.Contains(x) && !OwnedMaps.Contains(x)).OrderBy(x => x, System.StringComparer.Ordinal))
                Line($"  free ensures (forall o: Ref :: {(p.IsCtor ? "o != this && " : "")}old($Alloc[o]) ==> {map}[o] == old({map}[o]));");
            // (an [Owned] object's field: written only where its view is, which the procedure holds only for this, the
            // views it gets, and the objects it makes)
            var views = (p.ThisIsView ? new[] { "this" } : new string[0])
                .Concat(m.Parameters.Where(x => IsView(x.Type) && x.RefKind != RefKind.Out).Select(x => Local(x) + (x.RefKind == RefKind.Ref ? "$in" : ""))).ToList();
            foreach (var map in modifies.Where(OwnedMaps.Contains).OrderBy(x => x, System.StringComparer.Ordinal))
                Line($"  free ensures (forall o: Ref :: old($Alloc[o]){string.Concat(views.Select(v => $" && o != {v}"))} ==> {map}[o] == old({map}[o]));");
            Line($"  free ensures {InRangeOfMemory};");
            Given(p, atEntry);
            foreach (var x in m.Parameters.Where(x => x.RefKind is RefKind.Ref or RefKind.Out))
            {
                if (IsIntegral(x.Type)) Line($"  free ensures {E(InRange(new KVar(Local(x)), x.Type), cx)};");
                if (IsRef(x.Type))
                {
                    Line($"  free ensures {Local(x)} == null || $Alloc[{Local(x)}];");
                    if (NotNullable(x.Type)) Line($"  free ensures {Local(x)} != null;");
                }
            }
            foreach (var r in p.Requires) Line($"  requires {E(r.Expr, atEntry)};", r.Check);
            // (checked at each return, where it is reported: Boogie would report one return path of each)
            foreach (var e in p.Ensures) Line($"  free ensures {E(e.Expr, cx)};");
            if (!m.ReturnsVoid && IsIntegral(m.ReturnType) && !p.Ghost) Line($"  free ensures {E(InRange(new KVar("result"), m.ReturnType), cx)};");
            if (functionFields != null)
                Line($"  free ensures result == {E(new KFnApp { Callee = m, Function = FunctionName(m), Layer = "$LS($LZ)", Fields = functionFields, Args = (p.HasThis ? new[] { new KVar("this") } : new KExpr[0]).Concat(m.Parameters.Select(x => (KExpr)new KVar(Local(x)))).ToArray() }, cx)};");
            if (!m.ReturnsVoid && IsRef(m.ReturnType))
            {
                Line("  free ensures result == null || $Alloc[result];");
                if (NotNullable(m.ReturnType)) Line("  free ensures result != null;");
            }
            Line("{");
            if (p.UsesPerm)
            {
                Line("  var perm: [Ref]bool;");
                Line("  var pinst: [Inst]int;");
                Line("  var owner: [Ref]Inst;");
                if (p.UsesCells)
                {
                    Line("  var cells: [Ref][int]real;");
                    Line("  var cowner: [Ref][int]Inst;");
                }
            }
            // (an integer variable is always in its type's range: where Boogie havocs it, at a loop head, too)
            foreach (var l in p.Locals)
                Line(l.Raw != null ? $"  var {l.Name}: {l.Raw};" :
                     IsIntegral(l.Type) ? $"  var {l.Name}: int where {E(InRange(new KVar(l.Name), l.Type), cx)};" : $"  var {l.Name}: {TypeOf(l.Type)};");
            foreach (var x in ins) Line($"    {x} := {x}$in;");
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
            // the preconditions well-defined: a procedure of their own, which doesn't assume them (as Dafny's
            // well-formedness checks are), each under those before it
            if (p.Entry.Any(s => s is KAssert))
            {
                Line($"procedure {p.Name}$wf({ps})", Undecided(p));
                Given(p, atEntry);
                Line("{");
                foreach (var s in p.Entry) Statement(s, atEntry);
                Line("}");
            }
        }

        private static Check Undecided(KProcedure p) => new Check
        {
            Id = BoogieTranslator.Undecided, Method = p.Result, Message = "Boogie couldn't decide it",
            Span = (p.Method.Locations.FirstOrDefault() ?? Location.None).GetLineSpan(),
        };

        /// <summary>What a procedure is given, free: memory in range, this, a new object's defaults, its parameters' ranges and allocation.</summary>
        private void Given(KProcedure p, Context cx)
        {
            var m = p.Method;
            Line($"  free requires {InRangeOfMemory};");
            if (p.HasThis) Line("  free requires this != null && $Alloc[this];");
            // (a new object's fields are their defaults: its caller made them so)
            if (p.IsCtor)
                foreach (var f in InstanceFields(m.ContainingType).OrderBy(FieldMap, System.StringComparer.Ordinal))
                    Line($"  free requires {FieldMap(f)}[this] == {E(Default(FieldType(f)), cx)};");
            foreach (var x in m.Parameters.Where(x => x.RefKind != RefKind.Out))
            {
                var name = E(new KVar(Local(x)), cx);
                if (IsIntegral(x.Type)) Line($"  free requires {E(InRange(new KVar(Local(x)), x.Type), cx)};");
                if (IsRef(x.Type) || IsView(x.Type)) Line($"  free requires {name} == null || $Alloc[{name}];");
                // (not null: checked at each call's argument)
                if (IsRef(x.Type) && NotNullable(x.Type)) Line($"  free requires {name} != null;");
            }
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
                case KRaw raw: Line("    " + raw.Text); return;
                case KCallFrame { After: false } frame:
                    foreach (var x in new[] { "perm", "pinst", "owner", "$Alloc" }.Concat(frame.Maps).Concat(frame.Cells ? new[] { "cells", "cowner" }.Concat(frame.ElementMaps) : new string[0]))
                        Line($"    s{frame.Id}{(x.StartsWith("$") ? "" : "$")}{x} := {x};");
                    return;
                case KCallFrame frame:
                {
                    // (what the caller still holds, whole or folded into an instance it holds, the call couldn't change)
                    var sn = "s" + frame.Id;
                    var kept = $"{sn}$Alloc[y] && (({sn}$perm[y]{(frame.Receiver == null ? "" : $" && y != {E(frame.Receiver, cx)}")}) || {sn}$pinst[{sn}$owner[y]] >= 1)";
                    Line("    havoc owner;");
                    Line($"    assume (forall y: Ref :: {kept} ==> owner[y] == {sn}$owner[y]);");
                    foreach (var map in frame.Maps) Line($"    assume (forall y: Ref :: {kept} ==> {map}[y] == {sn}{map}[y]);");
                    if (frame.Cells)
                    {
                        // (a call that takes cells changes only those it got, and those folded into the instances it got, but
                        // for those still in hand; and arrays it allocates)
                        var (xv, iv) = (new KVar("x$"), new KVar("i$"));
                        var parts = frame.Given.Select(g => g.atom switch
                        {
                            KCells c => E(Checks.InCells(g.guard, c, xv, iv), cx),
                            KInst q => $"({E(g.guard, cx)} && {sn}$cowner[x$][i$] == {E(Checks.Instance(q.Pred, q.Args), cx)})",
                            _ => null,
                        }).Where(x => x != null).ToList();
                        var changed = parts.Count == 0 ? "false" : $"(({string.Join(" || ", parts)}) && {sn}$cells[x$][i$] < 1.0)";
                        var unchanged = $"{sn}$Alloc[x$] && !{changed}";
                        foreach (var map in frame.ElementMaps) Line($"    assume (forall x$: Ref, i$: int :: {unchanged} ==> {map}[x$][i$] == {sn}{map}[x$][i$]);");
                        Line("    havoc cowner;");
                        Line($"    assume (forall x$: Ref, i$: int :: {unchanged} ==> cowner[x$][i$] == {sn}$cowner[x$][i$]);");
                    }
                    return;
                }
                case KSnapshot snap:
                    if (snap.Frame.Maps.Count == 0) return;
                    foreach (var map in new[] { "$Alloc" }.Concat(snap.Frame.Maps)) Line($"    s${snap.Frame.Head}{map} := {map};");
                    return;
                case KLoopFrame frame:
                    // (an assume at the head: what Boogie keeps across the loop's havoc, as an invariant)
                    foreach (var map in frame.Maps)
                    {
                        var others = string.Join("", frame.Writers.Select(w => $" && r != {E(w, cx)}"));
                        Line($"    assume (forall r: Ref :: s${frame.Head}$Alloc[r]{others} ==> {map}[r] == s${frame.Head}{map}[r]);");
                    }
                    return;
                case KCall c:
                {
                    var targets = (c.Result == null ? new string[0] : new[] { c.Result }).Concat(c.RefOuts.OrderBy(x => x.param).Select(x => x.var)).ToList();
                    var given = c.Args.Where((a, k) => c.Callee.Parameters[k].RefKind != RefKind.Out);
                    Line($"    call {(targets.Count == 0 ? "" : string.Join(", ", targets) + " := ")}{Name(c.Callee)}({string.Join(", ", (c.Receiver == null ? given : new[] { c.Receiver }.Concat(given)).Select(a => E(a, cx)))});", c.Check);
                    return;
                }
                default: throw new NotTranslated("not printable: " + s.GetType().Name);
            }
        }
    }
}
