using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using CsVerify.Analyzers;
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
        /// <summary>Arithmetic of variables and literals alone, as an index is (a heap's parent, (j - 1) / 2).</summary>
        private static bool IndexArithmetic(KExpr e) => e switch
        {
            KVar or KLit => true,
            KOp { Op: "+" or "-" or "*" or "neg" } o => o.Args.All(IndexArithmetic),
            _ => false,
        };
        /// <summary>Where a case's test is printed as its tag, the cases' tags.</summary>
        private Dictionary<string, int> _tags;

        private readonly StringBuilder _text = new StringBuilder();
        private int _line = 1;

        public readonly Dictionary<int, Check> Lines = new Dictionary<int, Check>();

        /// <summary>
        /// The program. A prelude's optional part (multisets, a collection's kinds behind its interfaces, string keys) is
        /// tagged with what it declares, and kept only where the rest of the program uses it: else a blank line (the
        /// lines' numbers, which Lines maps to checks, stay), so a program that doesn't is the same as before them.
        /// </summary>
        public string Text
        {
            get
            {
                var lines = _text.ToString().Split('\n');
                // (a loop's inferred fact that didn't hold: left out, its line kept)
                foreach (var d in Disabled) if (d - 1 < lines.Length) lines[d - 1] = "    assert true;";
                var used = string.Join("\n", lines.Where(l => !(l.Length > 0 && l[0] == '\u0001')));
                return string.Join("\n", lines.Select(l =>
                {
                    if (!(l.Length > 0 && l[0] == '\u0001')) return l;
                    int end = l.IndexOf('\u0002');
                    var key = l.Substring(Tagged.Length, end - Tagged.Length);
                    return used.Contains(key) ? l.Substring(end + 1) : "";
                }));
            }
        }

        /// <summary>The lines (1-based) of loop facts left out: they didn't hold on entry or at a back edge.</summary>
        public readonly HashSet<int> Disabled = new HashSet<int>();

        private const string Tagged = "\u0001";

        /// <summary>The tuples' element functions used ($tup.i.Kind): declared at the end.</summary>
        private readonly HashSet<string> _tuples = new HashSet<string>();

        private readonly HashSet<string> _tupleMakers = new HashSet<string>();
        /// <summary>The scalars of the nullable values it names (int?: Int32).</summary>
        private readonly HashSet<string> _nullables = new HashSet<string>();

        public void Tuples()
        {

            foreach (var mk in _tupleMakers.OrderBy(x => x, System.StringComparer.Ordinal))
            {
                var types = mk.Substring("$tupmk.".Length).Split('_').Select(t => t.StartsWith("-") ? "[" + t.Substring(1).Replace("-", "]") : t).ToList();
                var ps = string.Join(", ", types.Select((t, i) => $"x{i}: {t}"));
                var app = $"{mk}({string.Join(", ", types.Select((t, i) => "x" + i))})";
                Line($"function {mk}({ps}): Ref;");
                for (int i = 0; i < types.Count; i++)
                {
                    var item = $"$tup.{i}.{types[i].Replace("[", "_").Replace("]", "_")}";
                    _tuples.Add(item);
                    Line($"axiom (forall {ps} :: {{ {app} }} {item}({app}) == x{i});");
                }
            }
            // (a nullable value: null, or the one reference of its value)
            foreach (var u in _nullables.OrderBy(x => x, System.StringComparer.Ordinal))
            {
                var st = System.Enum.Parse<SpecialType>("System_" + u);
                var ty = st == SpecialType.System_Boolean ? "bool" : "int";
                var range = st == SpecialType.System_Boolean ? "true" : $"{Range(st).lo} <= v && v <= {Range(st).hi}";
                Line($"function $nv.{u}(x: Ref): {ty};");
                Line($"function $nmk.{u}(v: {ty}): Ref;");
                Line($"axiom (forall v: {ty} :: {{ $nmk.{u}(v) }} {range} ==> $nmk.{u}(v) != null && $nv.{u}($nmk.{u}(v)) == v);");
                Line($"axiom (forall x: Ref :: {{ $nv.{u}(x) }} x != null ==> $nmk.{u}($nv.{u}(x)) == x);");
                if (st != SpecialType.System_Boolean) Line($"axiom (forall x: Ref :: {{ $nv.{u}(x) }} {Range(st).lo} <= $nv.{u}(x) && $nv.{u}(x) <= {Range(st).hi});");
            }
            foreach (var f in _tuples.OrderBy(x => x, System.StringComparer.Ordinal))
            {
                var ty = f.Substring(f.IndexOf('.', 5) + 1);
                var boogie = ty.StartsWith("_") ? "[" + ty.Substring(1).Replace("_", "]") : ty;
                Line($"function {f}(t: Ref): {boogie};");
            }
        }

        /// <summary>A prelude line kept only where the program names this.</summary>
        private void Optional(string key, string text) => Line(Tagged + key + "\u0002" + text);

        private void Line(string text, Check check = null)
        {
            if (check != null) Lines[_line] = check;
            _text.Append(text).Append('\n');
            _line++;
        }

        private static string Param(SpecialType t) => "m" + t.ToString().Substring("System_".Length);

        private static string InRangeOfMemory => "$InRange(" + string.Join(", ", IntegerMaps.Select(ElementMap)) + ")";

        /// <summary>The integer element types whose maps the program has.</summary>
        private static IEnumerable<SpecialType> IntegerMaps => Widths.Keys.Where(t => ElementTypes.Contains(t));

        private static string MapParams => string.Join(", ", ElementTypes.Select(t => $"h{ElementMap(t)}: [Ref][int]{ElementValue(t)}"));

        /// <summary>What every program has: C#'s division, fuel, and the heap of arrays (Dafny's encoding).</summary>
        public void Prelude()
        {
            // (a type parameter's values, Dafny's boxes)
            Line("type Box;");
            foreach (var t in new[] { "int", "bool", "Ref" })
            {
                Line($"function $box.{t}(x: {t}): Box;");
                Line($"function $unbox.{t}(b: Box): {t};");
                Line($"axiom (forall x: {t} :: {{ $box.{t}(x) }} $unbox.{t}($box.{t}(x)) == x);");
            }

            Line("// C#'s / and % truncate toward zero; Boogie's div and mod are Euclidean");
            Optional("cs#div(", "function cs#div(a: int, b: int): int { if a >= 0 then (if b > 0 then a div b else -(a div (-b))) else (if b > 0 then -((-a) div b) else (-a) div (-b)) }");
            // (what they are, which the solver reasons on, as a key's remainder; but a quotient of index arithmetic, a heap's
            // parent (j - 1) / 2, the function, which keeps the triggers of quantifiers over indices simple)
            Line("function {:inline} cs#divI(a: int, b: int): int { if a >= 0 then (if b > 0 then a div b else -(a div (-b))) else (if b > 0 then -((-a) div b) else (-a) div (-b)) }");
            Line("function {:inline} cs#remI(a: int, b: int): int { a - b * cs#divI(a, b) }");
            Line("// bitwise operators of two variables (as CsVerify's engine has them), and a shift count's power of two");
            foreach (var w in new[] { 32, 64 })
            {
                foreach (var op in new[] { "and", "or", "xor" }) Line($"function $bit.{op}{w}(x: int, y: int): int;");
                var pow = (System.Numerics.BigInteger.One << (w - 1)).ToString();
                for (int i = w - 2; i >= 0; i--) pow = $"(if n == {i} then {System.Numerics.BigInteger.One << i} else {pow})";
                Line($"function $pow{w}(n: int): int {{ {pow} }}");
            }
            Line("// fuel, as Dafny's: a function's definition unfolds once for each $LS");
            Line("type LayerType;");
            Line("const $LZ: LayerType;");
            Line("function $LS(ly: LayerType): LayerType;");
            Optional("$canBeCanceled(", "function $canBeCanceled(t: Ref): bool; // a cancellation token's, which never changes");
            Optional("$eqc(", "function $eqc(o: Ref): Ref; // a class's own Equals: its class of equals, not known");
            Optional("$refEq(", "function $refEq(a: Ref, b: Ref): bool; // anonymous objects' references compared: not known");
            Optional("$sfRef(", "function $sfRef(k: int): Ref; // a static readonly field's value, which never changes");
            Optional("$sfInt(", "function $sfInt(k: int): int;");
            Optional("$sfBool(", "function $sfBool(k: int): bool;");
            Optional("$eqc(", "axiom (forall o: Ref :: { $eqc(o) } o != null ==> $eqc(o) != null);");
            Optional("$dataEq(", "function $dataEq(a: Ref, b: Ref): bool; // records' ==, of fields that don't compare as values (strings'): not known");
            Optional("$cell(", "// a rectangular array's cell: an injective pairing of its indices, as CsVerify's engine's cv_cell");
            Optional("$cell(", "function $cell(i: int, j: int): int;");
            Optional("$cell(", "function $crow(c: int): int;");
            Optional("$cell(", "function $ccol(c: int): int;");
            Optional("$cell(", "axiom (forall i: int, j: int :: { $cell(i, j) } $crow($cell(i, j)) == i && $ccol($cell(i, j)) == j);");
            Optional("$sbase(", "// a span's base array and offset (its length is len)");
            Optional("$sbase(", "function $sbase(s: Ref): Ref;");
            Optional("$sbase(", "function $soff(s: Ref): int;");
            Optional("$dim(", "// a rectangular array's length of a dimension");
            Optional("$dim(", "function $dim(a: Ref, d: int): int;");
            Optional("$dim(", "axiom (forall a: Ref, d: int :: { $dim(a, d) } 0 <= $dim(a, d) && $dim(a, d) <= 2147483647);");
            Optional("$bag", "// multisets (Bag): maps from value to count, as CsVerify's engine has them. $bag(ly, r, n) is the multiset of");
            Optional("$bag", "// r[0..n), unfolded once per $LS; writing r[i] inside the prefix trades the old element for the new one, outside");
            Optional("$bag", "// it changes nothing. The write axioms are triggered only by the multiset of a written array, so they can't loop.");
            Optional("$bag", "const $bag.empty: [int]int;");
            Optional("$bag", "axiom (forall v: int :: $bag.empty[v] == 0);");
            Optional("$bag", "function $badd(m: [int]int, x: int): [int]int { m[x := m[x] + 1] }");
            Optional("$bag", "function $bremove(m: [int]int, x: int): [int]int { m[x := m[x] - 1] }");
            Optional("$bag", "function $bunion(a: [int]int, b: [int]int): [int]int;");
            Optional("$bag", "axiom (forall a: [int]int, b: [int]int, v: int :: { $bunion(a, b)[v] } $bunion(a, b)[v] == a[v] + b[v]);");
            Optional("$bag", "function $bag(ly: LayerType, r: [int]int, n: int): [int]int;");
            Optional("$bag", "axiom (forall ly: LayerType, r: [int]int, n: int :: { $bag($LS(ly), r, n) } $bag($LS(ly), r, n) == $bag(ly, r, n));");
            Optional("$bag", "axiom (forall ly: LayerType, r: [int]int :: { $bag(ly, r, 0) } $bag(ly, r, 0) == $bag.empty);");
            Optional("$bag", "axiom (forall ly: LayerType, r: [int]int, n: int :: { $bag($LS(ly), r, n) } 0 < n ==> $bag($LS(ly), r, n) == $badd($bag(ly, r, n - 1), r[n - 1]));");
            Optional("$bag", "axiom (forall ly: LayerType, r: [int]int, i: int, v: int, n: int :: { $bag(ly, r[i := v], n) } 0 <= i && i < n ==> $bag(ly, r[i := v], n) == $badd($bremove($bag(ly, r, n), r[i]), v));");
            Optional("$bag", "axiom (forall ly: LayerType, r: [int]int, i: int, v: int, n: int :: { $bag(ly, r[i := v], n) } (i < 0 || n <= i) ==> $bag(ly, r[i := v], n) == $bag(ly, r, n));");
            Line("// arrays: references, the allocated ones, each one's length, and a map of elements per element type");
            Line("type Ref;");
            Line("const null: Ref;");
            Line("var $Alloc: [Ref]bool;");
            Line("function len(a: Ref): int;");
            Optional("$arr(", "// what a collection behind an interface is: an array, or a modeled collection (List, Dictionary, ...), never both");
            Optional("$arr(", "function $arr(r: Ref): bool;");
            Optional("$arr(", "function $coll(r: Ref): bool;");
            Optional("$arr(", "axiom (forall r: Ref :: { $arr(r) } { $coll(r) } !($arr(r) && $coll(r)));");
            // (EF's entities: what type an object is, where the change tracker asks; Lowering.EfTracker)
            if (KernelTypes.Ef != null)
            {
                var entities = KernelTypes.Ef.Entities.Select(e => e.Type.OriginalDefinition).Distinct<ITypeSymbol>(SymbolEqualityComparer.Default).ToList();
                bool Derives(ITypeSymbol a, ITypeSymbol b) { for (var c = a.BaseType; c != null; c = c.BaseType) if (SymbolEqualityComparer.Default.Equals(c.OriginalDefinition, b)) return true; return false; }
                foreach (var a in entities) Optional("$isa.", $"function {Lowering.IsaFunction(a)}(r: Ref): bool;");
                foreach (var a in entities)
                    foreach (var b in entities.Where(b => !SymbolEqualityComparer.Default.Equals(a, b)))
                        if (Derives(a, b)) Optional("$isa.", $"axiom (forall r: Ref :: {{ {Lowering.IsaFunction(a)}(r) }} {Lowering.IsaFunction(a)}(r) ==> {Lowering.IsaFunction(b)}(r));");
                        else if (!Derives(b, a) && string.CompareOrdinal(Lowering.IsaFunction(a), Lowering.IsaFunction(b)) < 0)
                            Optional("$isa.", $"axiom (forall r: Ref :: {{ {Lowering.IsaFunction(a)}(r), {Lowering.IsaFunction(b)}(r) }} !({Lowering.IsaFunction(a)}(r) && {Lowering.IsaFunction(b)}(r)));");
            }
            // (strings as a database compares them, by its collation: an equivalence, as the same key; equal strings have
            // one. CsVerify's engine's cv_collate, without the axioms that make the solver go round)
            Optional("$ckey(", "function $ckey(s: Ref): int;");
            Line("axiom (forall a: Ref :: 0 <= len(a) && len(a) <= 2147483647); // (an array's Length is an int)");
            foreach (var t in ElementTypes) Line($"var {ElementMap(t)}: [Ref][int]{ElementValue(t)};");
            // (float and double as IEEE 754: Z3's floating point, rounding to nearest as .NET does)
            foreach (var (n, t, size, bv) in new[] { ("32", "float24e8", "8 24", "bv32"), ("64", "float53e11", "11 53", "bv64") })
            {
                string F(string name, string builtin, string ps, string ret) { return $"function {{:builtin \"{builtin}\"}} $fp.{name}{n}({ps}): {ret};"; }
                var x = $"x: {t}"; var xy = $"x: {t}, y: {t}";
                foreach (var (name, op) in new[] { ("add", "fp.add RNE"), ("sub", "fp.sub RNE"), ("mul", "fp.mul RNE"), ("div", "fp.div RNE") }) Optional("$fp.", F(name, op, xy, t));
                foreach (var (name, op) in new[] { ("eq", "fp.eq"), ("lt", "fp.lt"), ("leq", "fp.leq"), ("gt", "fp.gt"), ("geq", "fp.geq") }) Optional("$fp.", F(name, op, xy, "bool"));
                foreach (var (name, op) in new[] { ("neg", "fp.neg"), ("abs", "fp.abs"), ("sqrt", "fp.sqrt RNE"), ("floor", "fp.roundToIntegral RTN"),
                                                    ("ceil", "fp.roundToIntegral RTP"), ("trunc", "fp.roundToIntegral RTZ"), ("round", "fp.roundToIntegral RNE") })
                    Optional("$fp.", F(name, op, x, t));
                Optional("$fp.", F("fma", "fp.fma RNE", $"x: {t}, y: {t}, z: {t}", t));
                foreach (var (name, op) in new[] { ("isNaN", "fp.isNaN"), ("isInf", "fp.isInfinite"), ("isPos", "fp.isPositive"), ("isNeg", "fp.isNegative"),
                                                    ("isNormal", "fp.isNormal"), ("isSubnormal", "fp.isSubnormal") })
                    Optional("$fp.", F(name, op, x, "bool"));
                Optional("$fp.", F("real", "fp.to_real", x, "real"));
                Optional("$fp.", F("ofReal", $"(_ to_fp {size}) RNE", "r: real", t));
                Optional("$fp.", F("bits", $"(_ to_fp {size})", $"b: {bv}", t));
            }
            Optional("$toreal(", "function $toreal(i: int): real { real(i) }");
            Optional("$toint(", "function $toint(r: real): int { int(r) }");
            Optional("$fp.", "function {:builtin \"(_ to_fp 11 53) RNE\"} $fp.widen(x: float24e8): float53e11;");
            Optional("$fp.", "function {:builtin \"(_ to_fp 8 24) RNE\"} $fp.narrow(x: float53e11): float24e8;");
            Optional("$mem.", "// manual memory (ATS's): a pointer's, a view's ghost properties, functions of it");
            Optional("$mem.", "function $mem.Addr(v: Ref): int;");
            Optional("$mem.", "function $mem.Length(v: Ref): int;");
            Optional("$mem.", "function $mem.Index(v: Ref): int;");
            foreach (var t in Widths.Keys.Append(SpecialType.System_Boolean))
            {
                var k = t.ToString().Substring("System_".Length);
                var ty = t == SpecialType.System_Boolean ? "bool" : "int";
                Optional("$mem.", $"function $mem.Value.{k}(v: Ref): {ty};");
                Optional("$mem.", $"function $mem.Elems.{k}(v: Ref): [int]{ty};");
            }
            Line("// strings: values, of a length and UTF-16 code units (null counts as empty where it is concatenated)");
            Line("function slen(s: Ref): int;");
            Line("axiom (forall s: Ref :: { slen(s) } 0 <= slen(s) && slen(s) <= 2147483647);");
            Line("function sat(s: Ref, i: int): int;");
            Line("axiom (forall s: Ref, i: int :: { sat(s, i) } 0 <= sat(s, i) && sat(s, i) <= 65535);");
            Line("function sl(s: Ref): int { if s == null then 0 else slen(s) }");
            Line("function scat(a: Ref, b: Ref): Ref;");
            Line("// (a concatenation is as long as both, as CsVerify's engine has it: one too long throws OutOfMemoryException, a path not followed)");
            Line("axiom (forall a: Ref, b: Ref :: { scat(a, b) } scat(a, b) != null && slen(scat(a, b)) == sl(a) + sl(b));");
            Line("axiom (forall a: Ref, b: Ref, i: int :: { sat(scat(a, b), i) } 0 <= i && i < sl(a) + sl(b) ==> sat(scat(a, b), i) == (if i < sl(a) then sat(a, i) else sat(b, i - sl(a))));");
            Line("function sdiff(a: Ref, b: Ref): int;");
            Optional("$keyed(", "// a collection's string key: the string itself, marked; two marked keys of one content are one key (a string is its characters)");
            Optional("$keyed(", "function $key(s: Ref): bool;");
            Optional("$keyed(", "function $keyed(s: Ref): Ref;");
            Optional("$keyed(", "axiom (forall s: Ref :: { $keyed(s) } $keyed(s) == s && $key(s));");
            Optional("$keyed(", "axiom (forall a: Ref, b: Ref :: { $key(a), $key(b) } a != null && b != null && a != b && slen(a) == slen(b) ==> 0 <= sdiff(a, b) && sdiff(a, b) < slen(a) && sat(a, sdiff(a, b)) != sat(b, sdiff(a, b)));");
            Line("// what is read from memory is in its type's range");
            Line("function $InRange(" + string.Join(", ", IntegerMaps.Select(t => $"{Param(t)}: [Ref][int]int")) + "): bool { " +
                 string.Join(" && ", IntegerMaps.Select(t => { var (lo, hi) = Range(t); return $"(forall r: Ref, j: int :: {lo} <= {Param(t)}[r][j] && {Param(t)}[r][j] <= {hi})"; })) + " }");
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

        /// <summary>Is a call of b from a recursive (each reaches the other)?</summary>
        public Func<IMethodSymbol, IMethodSymbol, bool> Recursive = (a, b) => true;

        private sealed class Context
        {
            /// <summary>The ref parameters, named by their values on entry (p$x$in) where this says so: in requires, and in old().</summary>
            public HashSet<string> Ins = new HashSet<string>();
            public bool AtEntry;
            /// <summary>In a function's axioms: what its memory's parameters are named by (h$E.Int32...).</summary>
            public string Prefix = "h";
            /// <summary>In a function's axioms: is a callee in its recursion group?</summary>
            public Func<IMethodSymbol, bool> Group;
            /// <summary>In such a function: each array parameter's elements.</summary>
            public Dictionary<string, string> Elems;
            public bool InFunction;
            public string Layer = "$LS($LZ)";
            public string Result = "result";
            /// <summary>A map read in another state (a snapshot's: $st.m($sst(s))), in place of the memory's.</summary>
            public Func<string, string> MapAt;
        }

        private static readonly Context InProcedure = new Context();

        private static string Map(string name, Context cx) =>
            cx.MapAt != null && (name.StartsWith("$E.") || name.StartsWith("$F.")) ? cx.MapAt(name) :
            cx.InFunction && (name.StartsWith("$E.") || name.StartsWith("$F.")) ? cx.Prefix + name : name;

        private static string Maps(Context cx) => string.Join(", ", ElementTypes.Select(t => Map(ElementMap(t), cx)));

        private string E(KExpr e, Context cx)
        {
            switch (e)
            {
                case KLit l: return l.Text;
                case KVar v when cx.AtEntry && cx.Ins.Contains(v.Name): return v.Name + "$in";
                case KVar v: return v.Name == "result" ? cx.Result : Map(v.Name, cx);
                case KOp { Op: "old" } old when cx.Ins.Count > 0 && !cx.AtEntry:
                    return $"old({E(old.Args[0], new Context { Ins = cx.Ins, AtEntry = true, Elems = cx.Elems, InFunction = cx.InFunction, Layer = cx.Layer, Result = cx.Result, Group = cx.Group })})";
                case KFnApp f when f.Plain:
                    return $"{f.Function}({string.Join(", ", f.Args.Select(a => E(a, cx)))})";
                case KFnApp f when f.Snap != null:
                    return $"{f.Function}({string.Join(", ", new[] { f.Snap }.Concat(f.Args).Select(a => E(a, cx)))})";
                case KFnApp f:
                {
                    var own = OwnArrays(f.Callee);
                    // (in a function's axioms, only a call back into its recursion group is on the layer below: Dafny's rule;
                    // any other has the fuel a specification's call has)
                    var layer = f.Layer ?? (cx.Group != null && !cx.Group(f.Callee) ? "$LS($LZ)" : cx.Layer);
                    var parts = new List<string> { layer };
                    // (of a call frame's snapshot of the memory: its maps as they were then)
                    string At(string map) => f.MapsAt != null ? f.MapsAt + map : Map(map, cx);
                    if (own == null) parts.Add(f.MapsAt != null ? string.Join(", ", ElementTypes.Select(t => At(ElementMap(t)))) : Maps(cx));
                    else parts.AddRange(own.Select(o => f.MapsAt != null ? $"{At(o.map)}[{E(f.Args[o.arg], cx)}]" : Elements(o.map, f.Args[o.arg], cx)));
                    parts.AddRange(f.Fields.Select(At));
                    parts.AddRange(f.Args.Select(a => E(a, cx)));
                    return $"{f.Function}({string.Join(", ", parts)})";
                }
                case KQuant q when q.Range == null: return $"(forall {q.Var}: {q.Type} :: {E(q.Body, cx)})";
                case KQuant q: return q.Forall ? $"(forall {q.Var}: {q.Type} :: {E(q.Range, cx)} ==> {E(q.Body, cx)})" : $"(exists {q.Var}: {q.Type} :: {E(q.Range, cx)} && {E(q.Body, cx)})";
                case KOp op:
                {
                    var a = op.Args.Select(x => E(x, cx)).ToArray();
                    if (_tags != null && op.Args.Length == 1 && _tags.TryGetValue(op.Op, out var tag)) return $"($tag({a[0]}) == {tag})";
                    switch (op.Op)
                    {
                        case "!": return $"!({a[0]})";
                        case "ite": return $"(if {a[0]} then {a[1]} else {a[2]})";
                        case "div": return $"cs#div{(IndexArithmetic(op.Args[0]) ? "" : "I")}({a[0]}, {a[1]})";
                        case "rem": return $"cs#remI({a[0]}, {a[1]})";
                        case "ediv": return $"({a[0]} div {a[1]})";
                        case "emod": return $"({a[0]} mod {a[1]})";
                        case "len": return $"len({a[0]})";
                        case "old": return $"old({a[0]})";
                        case "wrap": return $"((({a[0]}) - ({a[1]})) mod {a[2]} + ({a[1]}))";
                        case "sel" when a.Length == 3 && op.Args[1] is KVar arr && cx.Elems != null && cx.Elems.TryGetValue(arr.Name, out var elems):
                            return $"{elems}[{a[2]}]";
                        case "sel": return a.Length == 2 ? $"{a[0]}[{a[1]}]" : $"{a[0]}[{a[1]}][{a[2]}]";
                        case "store": return $"{a[0]}[{a[1]} := {a[2]}]";
                        case "seq.drop": return $"(lambda j$: int :: {a[0]}[j$ + {a[1]}])";
                        case "seq.concat": return $"(lambda j$: int :: (if j$ < {a[1]} then {a[0]}[j$] else {a[2]}[j$ - {a[1]}]))";
                        case "seq.const": return $"(lambda j$: int :: {a[0]})";
                        case var mc when mc.StartsWith("map.const."): return $"(lambda k$: {mc.Substring("map.const.".Length)} :: {a[0]})";
                        case "set.of": return $"(lambda r$: Ref :: r$ == {a[0]})";
                        case "set.add": return $"{a[0]}[{a[1]} := true]";
                        case "set.freshc": return $"(forall r$: Ref :: {a[0]}[r$] ==> r$ == {a[2]} || !{a[1]}[r$])";
                        case "set.fresh": return $"(forall r$: Ref :: {a[0]}[r$] ==> !{a[1]}[r$])";
                        case "set.union": return $"(lambda r$: Ref :: {a[0]}[r$] || {a[1]}[r$])";
                        case "$tree": return $"(lambda r$: Ref :: $root[r$] == $root[{a[0]}])";
                        case "set.subset": return $"(forall r$: Ref :: {a[0]}[r$] ==> {a[1]}[r$])";
                        case "set.disjoint": return $"(forall r$: Ref :: !({a[0]}[r$] && {a[1]}[r$]))";
                        case "$state": return State;
                        case "slen": return $"slen({a[0]})";
                        case "sl": return $"sl({a[0]})";
                        case "sat": return $"sat({a[0]}, {a[1]})";
                        case "scat": return $"scat({a[0]}, {a[1]})";
                        case "sdiff": return $"sdiff({a[0]}, {a[1]})";
                        case "dtype": return $"dtype({a[0]})";
                        case "sub": return $"sub({a[0]}, {a[1]})";
                        case "streq": return $"({a[0]} == {a[1]})";
                        case "$collate": return $"($ckey({a[0]}) == $ckey({a[1]}))";
                        case "lambda": return $"(lambda {a[0]} :: {a[1]})";
                        case "inst": return $"{a[0]}({string.Join(", ", a.Skip(1))})";
                        case var f when f.StartsWith("$tup."): _tuples.Add(f); return $"{f}({string.Join(", ", a)})";
                        case var f when f.StartsWith("$tupmk."): _tupleMakers.Add(f); return $"{f}({string.Join(", ", a)})";
                        case var f when f.StartsWith("$nv.") || f.StartsWith("$nmk."): _nullables.Add(f.Substring(f.IndexOf('.') + 1)); return $"{f}({string.Join(", ", a)})";
                        case var f when f.StartsWith("$") || f.StartsWith("mk."): return $"{f}({string.Join(", ", a)})";
                        default:
                            if (a.Length != 2) throw new NotTranslated("the kernel's operator " + op.Op);
                            return $"({a[0]} {op.Op} {a[1]})";
                    }
                }
                default: throw new NotTranslated("not printable: " + e.GetType().Name);
            }
        }

        // ------------------------------------------------------------------ strings' literals, and library stubs

        /// <summary>Each literal: a value of its own (unique), not null, of its length and characters.</summary>
        public void Literals(IReadOnlyDictionary<string, string> literals)
        {
            foreach (var (text, name) in literals.OrderBy(kv => kv.Value, System.StringComparer.Ordinal))
            {
                Line($"const unique {name}: Ref;");
                var facts = new[] { $"{name} != null", $"slen({name}) == {text.Length}" }.Concat(text.Select((c, i) => $"sat({name}, {i}) == {(int)c}"));
                Line($"axiom {string.Join(" && ", facts)};");
            }
        }

        /// <summary>A library member's stub, as a function: its postconditions, where its preconditions hold, of all its arguments.</summary>
        public void Stub(IMethodSymbol m, Contract contract, List<KExpr> requires, List<KExpr> ensures)
        {
            var name = Checks.StubName(m);
            // (a collection's: of its models first, its parameters of its type here)
            var models = Checks.StubModels(m, contract);
            var given = models.Select((x, k) => (name: "m$" + k, type: x.Type)).ToList();
            var ps = given.Concat(contract.Stub.Parameters.Select((x, k) => (name: Local(x), type: TypeOf(models.Count == 0 ? x.Type : k == 0 ? m.ContainingType : m.Parameters[k - 1].Type)))).ToList();
            if (models.Count > 0)
            {
                var at = models.Select((x, k) => (x.Name, k)).ToDictionary(x => x.Name, x => (KExpr)new KVar("m$" + x.k));
                at["this"] = new KVar(Local(contract.Stub.Parameters[0]));
                requires = requires.Select(r => Checks.Rename(r, at)).ToList();
                ensures = ensures.Select(e => Checks.Rename(e, at)).ToList();
            }
            var bound = string.Join(", ", ps.Select(x => $"{x.name}: {x.type}"));
            var app = $"{name}({string.Join(", ", ps.Select(x => x.name))})";
            Line($"function {name}({bound}): {TypeOf(m.ReturnType)};");
            var cx = new Context { Result = app };
            var pre = requires.Count == 0 ? "true" : string.Join(" && ", requires.Select(r => E(r, cx)));
            string Axiom(string body) => ps.Count == 0 ? $"axiom {body};" : $"axiom (forall {bound} :: {{ {app} }} {body});";
            foreach (var e in ensures) Line(Axiom($"{pre} ==> {E(e, cx)}"));
            // (trusted for its annotations: a non-nullable result isn't null; an integer one is in its type's range)
            if (IsNullable(m.ReturnType) && NotNullable(m.ReturnType)) Line(Axiom($"{app} != null"));
            if (IsIntegral(m.ReturnType)) Line(Axiom(E(InRange(new KLit(app), m.ReturnType), InProcedure)));
        }

        // ------------------------------------------------------------------ data types

        /// <summary>A data case: its constructor's parameters, its tag, and what each field of a value it makes is.</summary>
        public sealed class DataCase
        {
            public INamedTypeSymbol Type;
            public string Name;
            public int Tag;
            public List<(string name, string type, bool data, string field)> Params = new List<(string, string, bool, string)>();
            public List<(string function, KExpr value)> Fields = new List<(string, KExpr)>();
        }

        /// <summary>
        /// Data types as Dafny's: boxes for generic values; a value's tag ($tag, tested by $is.C) and rank ($rank, never
        /// negative); each field a function; each case's constructor a function whose value has its tag, its fields,
        /// and a rank above its data parts'; and a value of a case is that case's constructor of its fields.
        /// </summary>
        public void Data(List<DataCase> cases, List<(string function, string type, KExpr fact)> fields)
        {
            Line("function $tag(d: Ref): int;");
            Line("function $rank(d: Ref): int;");
            Line("axiom (forall d: Ref :: { $rank(d) } $rank(d) >= 0);");
            var cx = InProcedure;
            // (a field's case, by its tag: a test of the case ($is.C) would be a term that makes the case's value its
            // constructor of its fields, whose fields' cases would make more, without end)
            _tags = cases.ToDictionary(c => "$is." + c.Name.Substring(3), c => c.Tag);
            foreach (var (function, type, fact) in fields)
            {
                Line($"function {function}(d: Ref): {type};");
                if (fact != null) Line($"axiom (forall d: Ref :: {{ {function}(d) }} {E(fact, cx)});");
            }
            _tags = null;
            foreach (var c in cases)
            {
                Line($"function $is.{c.Name.Substring(3)}(d: Ref): bool {{ $tag(d) == {c.Tag} }}");
                var ps = string.Join(", ", c.Params.Select(x => $"{x.name}: {x.type}"));
                var app = $"{c.Name}({string.Join(", ", c.Params.Select(x => x.name))})";
                Line($"function {c.Name}({ps}): Ref;");
                var facts = new List<string> { $"{app} != null", $"$tag({app}) == {c.Tag}" };
                foreach (var (function, value) in c.Fields) facts.Add($"{function}({app}) == {E(value, cx)}");
                foreach (var x in c.Params.Where(x => x.data)) facts.Add($"({x.name} != null ==> $rank({x.name}) < $rank({app}))");
                Line(c.Params.Count == 0 ? $"axiom {string.Join(" && ", facts)};" : $"axiom (forall {ps} :: {{ {app} }} {string.Join(" && ", facts)});");
                // (a value of the case is the case's constructor of its fields)
                var eta = $"{c.Name}({string.Join(", ", c.Params.Select(x => $"{x.field}(d)"))})";
                Line($"axiom (forall d: Ref :: {{ $is.{c.Name.Substring(3)}(d) }} d != null && $is.{c.Name.Substring(3)}(d) ==> d == {eta});");
            }
        }

        /// <summary>
        /// Valid values of data types with invariants: their invariants hold; and, of each case, the parts with
        /// invariants are valid (where the case is tested, so the parts aren't unfolded without end).
        /// </summary>
        public void Valid(List<(string name, KExpr invariant, List<(string isCase, KExpr part)> parts)> types)
        {
            foreach (var (name, _, _) in types) Line($"function {name}(d: Ref): bool;");
            foreach (var (name, invariant, parts) in types)
            {
                Line($"axiom (forall d: Ref :: {{ {name}(d) }} {name}(d) && d != null ==> {E(invariant, InProcedure)});");
                foreach (var (isCase, part) in parts)
                    Line($"axiom (forall d: Ref :: {{ {name}(d), {isCase}(d) }} {name}(d) && {isCase}(d) ==> {E(part, InProcedure)});");
            }
        }

        // ------------------------------------------------------------------ delegates

        /// <summary>
        /// For each Func and Action signature: what one accepts ($pre), gives ($post) and accepts always ($total), the
        /// same in every state; a call of one ($call), which may change anything, unless it changes nothing ($nochange).
        /// </summary>
        public void Delegates(IEnumerable<string> keys, ISet<string> maps)
        {
            var all = keys.Distinct().OrderBy(x => x, System.StringComparer.Ordinal).ToList();
            if (all.Count == 0 && !UsesState) return;
            string Ty(string part) => part == "Ref" ? "Ref" : part == "Boolean" ? "bool" : "int";
            Line("function $nochange(d: Ref): bool;");
            // (a state: the memory, each map of it given back; a steady delegate is the same in all of them)
            Line("type St;");
            Line("function $steady(d: Ref): bool;");
            var ms = string.Join(", ", _stateMaps.Select(m => $"{m.name}: {m.type}"));
            var mns = string.Join(", ", _stateMaps.Select(m => m.name));
            Line($"function $st({ms}): St;");
            foreach (var m in _stateMaps)
            {
                Line($"function $st.{m.name}(s: St): {m.type};");
                Line($"axiom (forall {ms} :: {{ $st({mns}) }} $st.{m.name}($st({mns})) == {m.name});");
            }
            if (UsesState)
            {
                // (a function over a predicate's snapshot: the state it is of)
                Line("function $sst(s: int): St;");
                // (a collection through its interface, neither an array nor a modeled collection: values of the state)
                Line("function $ocount(r: Ref, s: St): int;");
                Line("axiom (forall r: Ref, s: St :: { $ocount(r, s) } 0 <= $ocount(r, s) && $ocount(r, s) <= 2147483647);");
                foreach (var k in ElementTypes.Where(t => !(t is SpecialType.System_Single or SpecialType.System_Double)).Select(t => t == SpecialType.System_Object ? "Ref" : t.ToString().Substring("System_".Length)))
                {
                    Line($"function $oitem.{k}(r: Ref, i: int, s: St): {BoogieOf(k)};");
                    if (k is not ("Ref" or "Boolean"))
                    {
                        var (lo, hi) = Range((SpecialType)System.Enum.Parse(typeof(SpecialType), "System_" + k));
                        Line($"axiom (forall r: Ref, i: int, s: St :: {{ $oitem.{k}(r, i, s) }} {(lo < 0 ? $"({lo})" : lo.ToString())} <= $oitem.{k}(r, i, s) && $oitem.{k}(r, i, s) <= {hi});");
                    }
                }
            }
            var modifies = Heap.Globals.Where(maps.Contains).Concat(maps.Where(x => x.StartsWith("$F.")).OrderBy(x => x, System.StringComparer.Ordinal)).ToList();
            foreach (var key in all)
            {
                var parts = key.Split('.');
                var res = parts[parts.Length - 1];
                var xs = parts.Take(parts.Length - 1).Select((t, k) => (name: $"x{k}", type: Ty(t))).ToList();
                var decl = string.Concat(xs.Select(x => $", {x.name}: {x.type}"));
                var use = string.Concat(xs.Select(x => $", {x.name}"));
                Line($"function $pre.{key}(d: Ref{decl}): bool;");
                Line($"function $post.{key}(d: Ref{decl}{(res == "void" ? "" : $", r: {Ty(res)}")}): bool;");
                Line($"function $total.{key}(d: Ref): bool;");
                Line(xs.Count == 0
                    ? $"axiom (forall d: Ref :: {{ $total.{key}(d) }} $total.{key}(d) <==> $pre.{key}(d));"
                    : $"axiom (forall d: Ref :: {{ $total.{key}(d) }} $total.{key}(d) <==> (forall {string.Join(", ", xs.Select(x => $"{x.name}: {x.type}"))} :: {{ $pre.{key}(d{use}) }} $pre.{key}(d{use})));");
                var rr = res == "void" ? "" : $", r: {Ty(res)}";
                var ru = res == "void" ? "" : ", r";
                // in a state: steady, as in every state; one that reads state, the same where what it reads is
                Line($"function $preS.{key}(d: Ref, s: St{decl}): bool;");
                Line($"function $postS.{key}(d: Ref, s: St{decl}{rr}): bool;");
                Line($"function $readsS.{key}(d: Ref, s: St{decl}): [Ref]bool;");
                Line($"function $frame.{key}(d: Ref{decl}): [Ref]bool;");
                Line($"axiom (forall d: Ref, s: St{decl} :: {{ $preS.{key}(d, s{use}) }} $steady(d) ==> $preS.{key}(d, s{use}) == $pre.{key}(d{use}));");
                Line($"axiom (forall d: Ref, s: St{decl}{rr} :: {{ $postS.{key}(d, s{use}{ru}) }} $steady(d) ==> $postS.{key}(d, s{use}{ru}) == $post.{key}(d{use}{ru}));");
                Line($"axiom (forall d: Ref, s: St{decl}, o: Ref :: {{ $readsS.{key}(d, s{use})[o] }} $steady(d) ==> !$readsS.{key}(d, s{use})[o]);");
                Line($"axiom (forall d: Ref{decl}, o: Ref :: {{ $frame.{key}(d{use})[o] }} $nochange(d) ==> !$frame.{key}(d{use})[o]);");
                string Agree(string r) => _stateMaps.Count == 0 ? "true" :
                    $"(forall o: Ref :: {r}[o] ==> {string.Join(" && ", _stateMaps.Select(m => $"$st.{m.name}(s1)[o] == $st.{m.name}(s2)[o]"))})";
                var r1 = $"$readsS.{key}(d, s1{use})";
                Line($"axiom (forall d: Ref, s1: St, s2: St{decl} :: {{ $preS.{key}(d, s1{use}), $preS.{key}(d, s2{use}) }} {{ {r1}, $preS.{key}(d, s2{use}) }} {{ {r1}, $readsS.{key}(d, s2{use}) }} " +
                     $"{Agree(r1)} ==> $preS.{key}(d, s1{use}) == $preS.{key}(d, s2{use}) && {r1} == $readsS.{key}(d, s2{use}));");
                Line($"axiom (forall d: Ref, s1: St, s2: St{decl}{rr} :: {{ $postS.{key}(d, s1{use}{ru}), $postS.{key}(d, s2{use}{ru}) }} " +
                     $"{Agree(r1)} ==> $postS.{key}(d, s1{use}{ru}) == $postS.{key}(d, s2{use}{ru}));");
                Line($"procedure $call.{key}(d: Ref{decl}){(res == "void" ? "" : $" returns (res: {Ty(res)})")};");
                if (modifies.Count > 0) Line($"  modifies {string.Join(", ", modifies)};");
                foreach (var l in StepsKept(modifies, true)) Line("  " + l);
                if (modifies.Contains("$Alloc")) Line("  free ensures (forall r: Ref :: old($Alloc[r]) ==> $Alloc[r]);");
                Line($"  free ensures {InRangeOfMemory};");
                Line($"  free ensures $postS.{key}(d, old({State}){use}{(res == "void" ? "" : ", res")});");
                // (only what's in its frame changes, of what was allocated)
                foreach (var m in _stateMaps.Where(m => modifies.Contains(m.name)))
                    Line($"  free ensures (forall o: Ref :: old($Alloc[o]) && !$frame.{key}(d{use})[o] ==> {m.name}[o] == old({m.name}[o]));");
                if (res != "void" && res != "Ref" && res != "Boolean")
                {
                    var (lo, hi) = Range((SpecialType)System.Enum.Parse(typeof(SpecialType), "System_" + res));
                    Line($"  free ensures {(lo < 0 ? $"({lo})" : lo.ToString())} <= res && res <= {hi};");
                }
                var same = modifies.Where(x => x != "$Alloc").ToList();
                if (same.Count > 0) Line($"  free ensures $nochange(d) ==> {string.Join(" && ", same.Select(x => $"{x} == old({x})"))};");
            }
        }

        /// <summary>A call of code whose contract isn't known: anything may change (but what's allocated stays so).</summary>
        public void Havoc(ISet<string> maps)
        {
            var modifies = Heap.Globals.Where(maps.Contains).Concat(maps.Where(x => x.StartsWith("$F.")).OrderBy(x => x, System.StringComparer.Ordinal)).ToList();
            foreach (var (name, these) in new[] { ("$havoc", modifies), ("$havocProgram", modifies.Where(x => !x.StartsWith("$F.$M.")).ToList()) })
            {
                Line($"procedure {name}();");
                if (these.Count > 0) Line($"  modifies {string.Join(", ", these)};");
                foreach (var l in StepsKept(these, true)) Line("  " + l);
                if (these.Contains("$Alloc")) Line("  free ensures (forall r: Ref :: old($Alloc[r]) ==> $Alloc[r]);");
                Line($"  free ensures {InRangeOfMemory};");
            }
        }

        /// <summary>What the method's permissions cover stays: the cells it holds, the fields of the [Owned] objects whose views it holds.</summary>
        private IEnumerable<string> HeldKept(ICollection<string> modifies)
        {
            foreach (var t in ElementTypes.Select(ElementMap).Where(modifies.Contains))
                yield return $"  free ensures (forall a: Ref, i: int :: c[a][i] > 0.0 ==> {t}[a][i] == old({t}[a][i]));";
            foreach (var m in modifies.Where(OwnedMaps.Contains).OrderBy(x => x, System.StringComparer.Ordinal))
                yield return $"  free ensures (forall o: Ref :: p[o] ==> {m}[o] == old({m}[o]));";
        }

        /// <summary>
        /// An await: other code runs, which may change anything but the objects the method alone has (its confined
        /// locals'); what's allocated stays so.
        /// </summary>
        public void Await(ISet<string> maps)
        {
            var modifies = Heap.Globals.Where(maps.Contains).Concat(maps.Where(x => x.StartsWith("$F.")).OrderBy(x => x, System.StringComparer.Ordinal)).ToList();
            // (each: always, or where a task the method started may be running alongside, changing nothing if none is;
            // and, for a method of permissions, keeping what they cover)
            foreach (var (name, when, held) in new[] { ("$await", false, false), ("$awaitIf", true, false), ("$awaitHeld", false, true), ("$awaitIfHeld", true, true) })
            {
                Line($"procedure {name}({(when ? "w: bool, " : "")}k: [Ref]bool{(held ? ", c: [Ref][int]real, p: [Ref]bool" : "")});");
                if (modifies.Count > 0) Line($"  modifies {string.Join(", ", modifies)};");
                foreach (var l in StepsKept(modifies, true)) Line("  " + l);
                if (modifies.Contains("$Alloc")) Line("  free ensures (forall r: Ref :: old($Alloc[r]) ==> $Alloc[r]);");
                Line($"  free ensures {InRangeOfMemory};");
                foreach (var m in _stateMaps.Where(m => modifies.Contains(m.name)))
                    Line($"  free ensures (forall o: Ref :: k[o] ==> {m.name}[o] == old({m.name}[o]));");
                if (when) foreach (var m in modifies) Line($"  free ensures !w ==> {m} == old({m});");
                if (held) foreach (var l in HeldKept(modifies)) Line(l);
            }
        }

        // ------------------------------------------------------------------ exceptions

        private int _forks;

        /// <summary>The side branches of checks not assumed after.</summary>
        private int _sides;
        private bool _leading;

        /// <summary>The callees started as tasks or threads (their twins, of free preconditions, are declared once the procedures are).</summary>
        public readonly HashSet<IMethodSymbol> Started = new HashSet<IMethodSymbol>(SymbolEqualityComparer.Default);

        /// <summary>The callees a call of throws (their twins are declared once the procedures are).</summary>
        public readonly HashSet<IMethodSymbol> Throwing = new HashSet<IMethodSymbol>(SymbolEqualityComparer.Default);

        /// <summary>
        /// Dynamic types: a constant each of the exception types and the classes and interfaces named, how they derive
        /// (sub, as C# does). Every exception type is an Exception (with no class named, every type is). Classes form a
        /// tree, so unrelated ones have no instance in common, nor have a sealed type and one not above it; a sealed
        /// type's instances are of it exactly. As CsVerify's engine has them.
        /// </summary>
        public void ExceptionTypes(IEnumerable<ITypeSymbol> types, ITypeSymbol exception, IEnumerable<ITypeSymbol> classes)
        {
            var classList = classes.ToList();
            var all = types.Concat(exception == null ? new ITypeSymbol[0] : new[] { exception }).Concat(classList).Select(t => t.OriginalDefinition)
                .Distinct(SymbolEqualityComparer.Default).Cast<ITypeSymbol>().OrderBy(TypeConst, System.StringComparer.Ordinal).ToList();
            Line("type Ty;");
            Line("function dtype(r: Ref): Ty;");
            Line("function sub(a: Ty, b: Ty): bool;");
            Line("axiom (forall a: Ty :: sub(a, a));");
            Line("axiom (forall a: Ty, b: Ty, c: Ty :: { sub(a, b), sub(b, c) } sub(a, b) && sub(b, c) ==> sub(a, c));");
            foreach (var t in all) Line($"const unique {TypeConst(t)}: Ty;");
            if (exception != null && classList.Count == 0) Line($"axiom (forall a: Ty :: sub(a, {TypeConst(exception)}));");
            bool Derives(ITypeSymbol a, ITypeSymbol b)
            {
                for (var c = (a as INamedTypeSymbol)?.BaseType; c != null; c = c.BaseType)
                    if (SymbolEqualityComparer.Default.Equals(c.OriginalDefinition, b.OriginalDefinition)) return true;
                return a.AllInterfaces.Any(i => SymbolEqualityComparer.Default.Equals(i.OriginalDefinition, b.OriginalDefinition));
            }
            foreach (var a in all)
                foreach (var b in all.Where(b => !SymbolEqualityComparer.Default.Equals(a, b)))
                    Line($"axiom {(Derives(a, b) ? "" : "!")}sub({TypeConst(a)}, {TypeConst(b)});");
            if (classList.Count == 0) return;
            for (int i = 0; i < all.Count; i++)
            {
                var a = all[i];
                if (a.IsSealed) Line($"axiom (forall t: Ty :: {{ sub(t, {TypeConst(a)}) }} sub(t, {TypeConst(a)}) ==> t == {TypeConst(a)});");
                for (int j = i + 1; j < all.Count; j++)
                {
                    var b = all[j];
                    if (Derives(a, b) || Derives(b, a)) continue;
                    if (a.TypeKind == TypeKind.Class && b.TypeKind == TypeKind.Class || a.IsSealed || b.IsSealed)
                        Line($"axiom (forall t: Ty :: {{ sub(t, {TypeConst(a)}), sub(t, {TypeConst(b)}) }} !(sub(t, {TypeConst(a)}) && sub(t, {TypeConst(b)})));");
                }
            }
        }

        /// <summary>
        /// A callee's twin, for the way it throws: its inputs, what it modifies, an exception that isn't null, and only
        /// what its EnsuresOnThrow clauses say of it (nothing of its postconditions).
        /// </summary>
        public void Throws(KProcedure callee, ISet<string> modifies, List<(ITypeSymbol type, KExpr cond)> clauses)
        {
            var m = callee.Method;
            var ins = m.Parameters.Where(x => x.RefKind == RefKind.Ref).Select(Local).ToHashSet();
            var cx = new Context { Ins = ins };
            var ps = string.Join(", ", (callee.HasThis ? new[] { "this: Ref" } : new string[0])
                .Concat(m.Parameters.Where(x => x.RefKind != RefKind.Out).Select(x => $"{Local(x)}{(x.RefKind == RefKind.Ref ? "$in" : "")}: {TypeOf(x.Type)}")));
            Line($"procedure {callee.Name}$throws({ps}) returns (ex: Ref);");
            if (modifies.Count > 0)
                Line($"  modifies {string.Join(", ", Heap.Globals.Where(modifies.Contains).Concat(modifies.Where(x => x.StartsWith("$F.")).OrderBy(x => x, System.StringComparer.Ordinal)))};");
            Line("  free ensures ex != null;");
            foreach (var (type, cond) in clauses)
                Line($"  free ensures {E(new KOp("==>", Checks.Is(new KVar("ex"), type), cond), new Context { Ins = ins, AtEntry = false })};");
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
        /// <summary>The memory a delegate's state is: the element maps and the field maps (with their types).</summary>
        private readonly List<(string name, string type)> _stateMaps = new List<(string, string)>();

        /// <summary>Some procedure reads a collection through an interface: the state ($st) is declared, and its functions.</summary>
        public bool UsesState;

        /// <summary>This state, as delegates take it.</summary>
        private string State => $"$st({string.Join(", ", _stateMaps.Select(m => m.name))})";

        /// <summary>
        /// The collections' models: maps as fields are (a size never negative, what an integer's holds in its range); and
        /// the dictionaries' pairs' Key and Value, functions of them.
        /// </summary>
        public void Models(List<ModelMap> models, List<(string key, string value)> pairs)
        {
            string Bound(string kind, string at)
            {
                if (kind == null || kind is "Ref" or "Boolean") return null;
                var (lo, hi) = Range((SpecialType)System.Enum.Parse(typeof(SpecialType), "System_" + kind));
                return $"{(lo < 0 ? $"({lo})" : lo.ToString())} <= {at} && {at} <= {hi}";
            }
            foreach (var m in models)
            {
                string where = "";
                if (m.Name == SizeMap || m.Name == "$F.$M.Length") where = $" where (forall o: Ref :: {m.Name}[o] >= 0)";
                else if (m.Range != null && Bound(m.Range, "x") != null)
                {
                    var key = m.Type.Substring("[Ref][".Length, m.Type.IndexOf(']', 5) - "[Ref][".Length);
                    where = $" where (forall o: Ref, j: {key} :: {Bound(m.Range, $"{m.Name}[o][j]")})";
                }
                Line($"var {m.Name}: {m.Type}{where};");
                _stateMaps.Add((m.Name, m.Type));
            }
            foreach (var k in pairs.Select(p => p.key).Distinct().OrderBy(x => x, System.StringComparer.Ordinal))
            {
                Line($"function $kvp.Key.{k}(p: Ref): {BoogieOf(k)};");
                if (Bound(k, $"$kvp.Key.{k}(p)") is string b) Line($"axiom (forall p: Ref :: {{ $kvp.Key.{k}(p) }} {b});");
            }
            foreach (var v in pairs.Select(p => p.value).Distinct().OrderBy(x => x, System.StringComparer.Ordinal))
            {
                Line($"function $kvp.Value.{v}(p: Ref): {BoogieOf(v)};");
                if (Bound(v, $"$kvp.Value.{v}(p)") is string b) Line($"axiom (forall p: Ref :: {{ $kvp.Value.{v}(p) }} {b});");
            }
        }

        /// <summary>The atomic fields' maps with a step, and their steps (of x$old and x$now).</summary>
        public Dictionary<string, KExpr> AtomicSteps = new Dictionary<string, KExpr>();

        /// <summary>Every atomic field among these maps went by steps since the state "before" (old(...)), at every object there then (and the statics').</summary>
        private IEnumerable<string> StepsKept(IEnumerable<string> maps, bool free)
        {
            foreach (var map in maps.Where(AtomicSteps.ContainsKey).OrderBy(x => x, System.StringComparer.Ordinal))
            {
                string At(string o) => E(Checks.Rename(Checks.Rename(AtomicSteps[map], "x$old", new KLit($"old({map}[{o}])")), "x$now", new KLit($"{map}[{o}]")), InProcedure);
                yield return $"{(free ? "free ensures" : "assume")} (forall o: Ref :: old($Alloc[o]) ==> {At("o")});";
                yield return $"{(free ? "free ensures" : "assume")} {At("null")};";
            }
        }

        /// <summary>The memory's maps, with their types (once the fields and models are declared).</summary>
        public IReadOnlyList<(string name, string type)> StateMaps => _stateMaps;

        public void Fields(IEnumerable<ISymbol> fields)
        {
            _stateMaps.Clear();
            foreach (var t in ElementTypes) _stateMaps.Add((ElementMap(t), "[Ref][int]" + ElementValue(t)));
            foreach (var f in fields.OrderBy(FieldMap, System.StringComparer.Ordinal)) _stateMaps.Add((FieldMap(f), $"[Ref]{TypeOf(FieldType(f))}"));
            foreach (var f in fields.OrderBy(FieldMap, System.StringComparer.Ordinal))
            {
                var map = FieldMap(f);
                var t = FieldType(f);
                var where = IsIntegral(t) ? $" where (forall o: Ref :: {E(InRange(new KOp("sel", new KVar(map), new KVar("o")), t), InProcedure)})" : "";
                Line($"var {map}: [Ref]{TypeOf(t)}{where};");
            }
            // (each object's ownership tree's root)
            if (KernelTypes.Trees) Line("var $root: [Ref]Ref;");
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
        /// <summary>Does it read memory, or a procedure's state (a global, a snapshot, a function of the memory)?</summary>
        private static bool ReadsMemory(KExpr e) => e switch
        {
            KVar v => v.Name.StartsWith("$") || v.Name == "psnap",
            KOp op => op.Op == "old" || op.Args.Any(ReadsMemory),
            KQuant q => (q.Range != null && ReadsMemory(q.Range)) || ReadsMemory(q.Body),
            KFnApp _ => true,
            _ => false,
        };

        private static IEnumerable<KExpr> Conjuncts(KExpr e) => e is KOp { Op: "&&" } and ? and.Args.SelectMany(Conjuncts) : new[] { e };

        /// <summary>Does it speak of snapshots (a function over a predicate)?</summary>
        private static bool Snapshots(KExpr e) => e switch
        {
            KFnApp f => f.Snap != null || f.Args.Any(Snapshots),
            KOp op => op.Args.Any(Snapshots),
            KQuant q => (q.Range != null && Snapshots(q.Range)) || Snapshots(q.Body),
            KVar v => v.Name == "psnap",
            _ => false,
        };

        /// <summary>
        /// A function over a predicate: of the instance's snapshot and its arguments, its value what folding and unfolding
        /// the instance say (no axioms but its range).
        /// </summary>
        public void FunctionOverPredicate(KProcedure p)
        {
            var m = p.Method;
            var name = FunctionName(m);
            var ps = string.Join("", m.Parameters.Select(x => $", {Local(x)}: {TypeOf(x.Type)}"));
            Line($"function {name}(s: int{ps}): {TypeOf(m.ReturnType)};");
            var app = $"{name}(s{string.Join("", m.Parameters.Select(x => ", " + Local(x)))})";
            if (!p.Ghost && IsIntegral(m.ReturnType))
                Line($"axiom (forall s: int{ps} :: {{ {app} }} {E(InRange(new KLit(app), m.ReturnType), InProcedure)});");
            // its postconditions, of every snapshot, where its precondition's facts hold (those that read no memory: an
            // axiom is about every state)
            var cx = new Context { Result = app };
            var pre = p.Requires.Where(r => !ReadsMemory(r.Expr)).Select(r => E(r.Expr, cx)).DefaultIfEmpty("true");
            // (conjunct by conjunct: those of them that read no memory)
            foreach (var e in p.Ensures.SelectMany(e => Conjuncts(e.Expr)).Where(e => !ReadsMemory(e)))
                Line($"axiom (forall s: int{ps} :: {{ {app} }} {string.Join(" && ", pre)} ==> {E(e, cx)});");
            // (its value is its body, read in the snapshot's state: so the functions over one snapshot agree with each
            // other, as CsVerify's engine's functions of one memory do; where its body reads no snapshot of its own)
            if (p.FunctionBody != null && Closed(p.FunctionBody, m.Parameters.Select(Local).ToHashSet()))
            {
                UsesState = true;
                var bx = new Context { Result = app, MapAt = map => $"$st.{map}($sst(s))" };
                Line($"axiom (forall s: int{ps} :: {{ {app} }} {app} == {E(p.FunctionBody, bx)});");
            }
        }

        /// <summary>An expression of these variables and the memory's maps alone (no snapshot, no local, no old).</summary>
        private bool Closed(KExpr e, HashSet<string> vars) => e switch
        {
            KVar v => vars.Contains(v.Name) || _stateMaps.Any(m => m.name == v.Name),
            KLit _ => true,
            KOp { Op: "old" } => false,
            KOp op => op.Args.All(a => Closed(a, vars)),
            KQuant q => Closed(q.Range ?? new KLit("true"), new HashSet<string>(vars) { q.Var }) && Closed(q.Body, new HashSet<string>(vars) { q.Var }),
            KFnApp f => f.Snap == null && f.MapsAt == null && f.Args.All(a => Closed(a, vars)),
            _ => false,
        };

        /// <summary>The queries of [Owned] classes (no parameters, no arrays read): each reads only its object's tree.</summary>
        private readonly List<(IMethodSymbol method, List<string> fields)> _ownedQueries = new List<(IMethodSymbol, List<string>)>();

        private static bool ReadsArrays(KExpr e) => e is KElem || e is KLen ||
            e != null && e.GetType().GetFields().Any(f => f.GetValue(e) is KExpr k && ReadsArrays(k) || f.GetValue(e) is IEnumerable<KExpr> ks && ks.Any(ReadsArrays));

        /// <summary>An override's dispatch: of an object exactly of its class, the base member's function is the override's.</summary>
        public void Dispatch(IMethodSymbol b, List<string> bFields, IMethodSymbol o, List<string> oFields, IEnumerable<ISymbol> symbols)
        {
            // (each reads all the arrays, or none of them)
            if (OwnArrays(b) is { Count: > 0 } || OwnArrays(o) is { Count: > 0 }) return;
            var all = bFields.Union(oFields).ToList();
            var ps = FieldParams(all, symbols) + ", this: Ref" + string.Join("", o.Parameters.Select(x => $", {Local(x)}: {TypeOf(x.Type)}"));
            string Sep(string x) => x.Length == 0 ? "" : ", " + x;
            string Memory(IMethodSymbol m) => OwnArrays(m) == null ? string.Join(", ", ElementTypes.Select(t => "h" + ElementMap(t))) : "";
            string App(IMethodSymbol m, List<string> fs) => $"{FunctionName(m)}(ly{Sep(Memory(m))}{string.Join("", fs.Select(x => ", h" + x))}, this{string.Join("", o.Parameters.Select(x => ", " + Local(x)))})";
            Line($"axiom (forall ly: LayerType{Sep(MapParams)}{ps} :: {{ {App(b, bFields)} }} dtype(this) == {TypeConst(o.ContainingType)} ==> {App(b, bFields)} == {App(o, oFields)});");
        }

        public void Function(KProcedure p, List<string> fields, IEnumerable<ISymbol> symbols)
        {
            var m = p.Method;
            if (KernelTypes.Trees && !m.IsStatic && SpecSymbols.IsOwned(m.ContainingType) && m.Parameters.Length == 0 && p.FunctionBody != null && !ReadsArrays(p.FunctionBody))
                _ownedQueries.Add((m, fields));
            var name = FunctionName(m);
            var self = m.IsStatic ? "" : ", this: Ref";
            var ps = FieldParams(fields, symbols) + self + string.Join("", m.Parameters.Select(x => $", {Local(x)}: {TypeOf(x.Type)}"));
            var args = string.Join("", fields.Select(x => ", h" + x)) + (m.IsStatic ? "" : ", this") + string.Join("", m.Parameters.Select(x => ", " + Local(x)));
            var own = OwnArrays(m);
            var memory = own == null ? MapParams : string.Join(", ", own.Select(o => $"e{o.param}: [int]{ElementValue(o.map)}"));
            var memoryArgs = own == null ? string.Join(", ", ElementTypes.Select(t => "h" + ElementMap(t))) : string.Join(", ", own.Select(o => "e" + o.param));
            string Sep(string x) => x.Length == 0 ? "" : ", " + x;
            var bound = $"ly: LayerType{Sep(memory)}{ps}";
            string At(string layer) => $"{name}({layer}{Sep(memoryArgs)}{args})";
            Line($"function {name}(ly: LayerType{Sep(memory)}{ps}): {TypeOf(m.ReturnType)};");
            Line($"axiom (forall {bound} :: {{ {At("$LS(ly)")} }} {At("$LS(ly)")} == {At("ly")});");
            var cx = new Context { InFunction = true, Layer = "ly", Result = At("ly"), Elems = own?.ToDictionary(o => o.param, o => "e" + o.param),
                                   Group = callee => callee != null && Recursive(m, callee) };
            var guard = p.Requires.Count == 0 ? "true" : string.Join(" && ", p.Requires.Select(r => E(r.Expr, cx)));
            // (its Spec.Reads, Dafny's frame axiom: two memories that agree on every object it reads give one value)
            if (p.ReadsFrame != null && own == null)
            {
                string Mem(string pre) => string.Join(", ", ElementTypes.Select(t => $"{pre}{ElementMap(t)}: [Ref][int]{ElementValue(t)}"))
                                        + string.Join("", fields.Select(x => $", {pre}{x}: [Ref]{TypeOf(FieldType(symbols.First(f => FieldMap(f) == x)))}"));
                string App(string pre) => $"{name}(ly, {string.Join(", ", ElementTypes.Select(t => pre + ElementMap(t)))}{string.Join("", fields.Select(x => ", " + pre + x))}{(m.IsStatic ? "" : ", this")}{string.Join("", m.Parameters.Select(x => ", " + Local(x)))})";
                var r = E(p.ReadsFrame, new Context { InFunction = true, Layer = "ly", Prefix = "a", Group = cx.Group });
                var agree = ElementTypes.Select(t => $"(forall o: Ref, i: int :: {r}[o] ==> a{ElementMap(t)}[o][i] == b{ElementMap(t)}[o][i])")
                    .Concat(fields.Select(x => $"(forall o: Ref :: {r}[o] ==> a{x}[o] == b{x}[o])"));
                Line($"axiom (forall ly: LayerType, {Mem("a")}, {Mem("b")}{self}{string.Join("", m.Parameters.Select(x => $", {Local(x)}: {TypeOf(x.Type)}"))} :: {{ {App("a")}, {App("b")} }} {string.Join(" && ", agree)} ==> {App("a")} == {App("b")});");
            }
            // (its definition, where it has one: an abstract or virtual one is of its contract alone)
            if (p.FunctionBody != null) Line($"axiom (forall {bound} :: {{ {At("$LS(ly)")} }} {guard} ==> {At("$LS(ly)")} == {E(p.FunctionBody, cx)});");
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
                .Concat(m.Parameters.Where(x => x.RefKind != RefKind.Out).Select(x => $"{Local(x)}{(x.RefKind == RefKind.Ref ? "$in" : "")}: {TypeOf(x.Type)}"))
                // (what a lambda or a local function captures: inputs of its own)
                .Concat(p.Captured.Select(c => $"{c.input}: {TypeOf(c.type)}")));
            var outs = (p.ListCtor ? new[] { "result: Ref" } : p.StructThis ? new[] { "this: Ref" } : Returns(m) == null ? new string[0] : new[] { $"result: {TypeOf(Returns(m))}" })
                .Concat(m.Parameters.Where(x => x.RefKind is RefKind.Ref or RefKind.Out).Select(x => $"{Local(x)}: {TypeOf(x.Type)}")).ToList();
            var ret = outs.Count == 0 ? "" : $" returns ({string.Join(", ", outs)})";
            // (an abstract member's: a declaration, its specifications after it, no body)
            Line($"procedure {p.Name}({ps}){ret}{(p.Abstract ? ";" : "")}", Undecided(p));
            if (modifies.Count > 0)
                Line($"  modifies {string.Join(", ", Heap.Globals.Where(modifies.Contains).Concat(modifies.Where(x => x.StartsWith("$F.")).OrderBy(x => x, System.StringComparer.Ordinal)))};");
            if (modifies.Contains("$Alloc")) Line("  free ensures (forall r: Ref :: old($Alloc[r]) ==> $Alloc[r]);");
            foreach (var f in RefFieldsOf(p).Where(f => modifies.Contains(FieldMap(f)))) Line($"  free ensures {GoodField(f)};");
            foreach (var f in RefFieldsOf(p).Where(f => SpecSymbols.IsOwnsField(f) && KernelTypes.Trees && (modifies.Contains(FieldMap(f)) || modifies.Contains("$root")))) Line($"  free ensures {TreeField(f)};");
            // (a method that writes only arrays it makes, as CsVerify's engine infers it (MayWriteHeap): every other array as it was)
            if ((!p.Abstract || p.Opaque) && p.Frame == null && KernelTypes.MayWriteHeap != null && !KernelTypes.MayWriteHeap(p.Method))
                foreach (var map in modifies.Where(x => x.StartsWith("$E.")).OrderBy(x => x, System.StringComparer.Ordinal))
                    Line($"  free ensures (forall o: Ref :: old($Alloc[o]) ==> {map}[o] == old({map}[o]));");
            // (a field written only at this object, in its constructor, or at objects allocated since: the same at every other)
            foreach (var map in modifies.Where(x => x.StartsWith("$F.") && !anyWrites.Contains(x) && !OwnedMaps.Contains(x)).OrderBy(x => x, System.StringComparer.Ordinal))
                Line($"  free ensures (forall o: Ref :: {(p.IsCtor ? "o != this && " : "")}old($Alloc[o]) ==> {map}[o] == old({map}[o]));");
            // (an [Owned] object's field: written only where its view is, which the procedure holds only for this, the
            // views it gets, and the objects it makes)
            var views = (p.ThisIsView ? new[] { "this" } : new string[0])
                .Concat(m.Parameters.Where(HoldsView).Select(x => Local(x) + (x.RefKind == RefKind.Ref ? "$in" : "")))
                // (and the views in the packages it gets)
                .Concat(m.Parameters.Where(x => IsPackage(x.Type) && x.RefKind is RefKind.None or RefKind.Ref)
                    .SelectMany(x => PackageViews(x.Type).Select(f => $"{FieldFunction(f)}({Local(x)}{(x.RefKind == RefKind.Ref ? "$in" : "")})"))).ToList();
            // (with ownership trees: the views' whole trees, and their roots)
            // (a constructor's own object is a tree of its own, its root not set yet)
            string Outside(string o) => KernelTypes.Trees
                ? string.Concat(views.Select(v => p.IsCtor && v == "this" ? $" && {o} != this" : $" && old($root[{o}]) != old($root[{v}])"))
                : string.Concat(views.Select(v => $" && {o} != {v}"));
            foreach (var map in modifies.Where(OwnedMaps.Contains).OrderBy(x => x, System.StringComparer.Ordinal))
                Line($"  free ensures (forall o: Ref :: old($Alloc[o]){Outside("o")} ==> {map}[o] == old({map}[o]));");
            if (KernelTypes.Trees && modifies.Contains("$root"))
                Line($"  free ensures (forall o: Ref :: old($Alloc[o]){Outside("o")} ==> $root[o] == old($root[o]));");
            // (Spec.Modifies: every field and cell of an object allocated before, and not in the frame then, is as it was)
            if (p.Frame != null)
            {
                var w = E(new KOp("old", p.Frame), cx);
                foreach (var map in modifies.Where(x => x.StartsWith("$F.") && !OwnedMaps.Contains(x)).OrderBy(x => x, System.StringComparer.Ordinal))
                    Line($"  free ensures (forall o: Ref :: old($Alloc[o]) && !{w}[o] ==> {map}[o] == old({map}[o]));");
                foreach (var map in modifies.Where(x => x.StartsWith("$E.")).OrderBy(x => x, System.StringComparer.Ordinal))
                    Line($"  free ensures (forall a: Ref, i: int :: old($Alloc[a]) && !{w}[a] ==> {map}[a][i] == old({map}[a][i]));");
            }
            Line($"  free ensures {InRangeOfMemory};");
            foreach (var l in StepsKept(modifies, true)) Line("  " + l);
            Given(p, atEntry);
            foreach (var x in m.Parameters.Where(x => x.RefKind is RefKind.Ref or RefKind.Out))
            {
                if (IsIntegral(x.Type)) Line($"  free ensures {E(InRange(new KVar(Local(x)), x.Type), cx)};");
                if (IsRef(x.Type)) Line($"  free ensures {Local(x)} == null || $Alloc[{Local(x)}];");
                if (IsData(x.Type) && x.Type.IsValueType) Line($"  free ensures {DataFacts(Local(x), x.Type, cx)};");
                // (a library member's, as its nullability says: [MaybeNullWhen(b)] not null where it returns !b)
                if (m.DeclaringSyntaxReferences.Length == 0 && IsNullable(x.Type))
                {
                    if (StaticChecks.IsNonNullable(x)) Line($"  free ensures {Local(x)} != null;");
                    else if (StaticChecks.NotNullWhen(x) is bool when && m.ReturnType.SpecialType == SpecialType.System_Boolean)
                        Line($"  free ensures {(when ? "result" : "!result")} ==> {Local(x)} != null;");
                }
                else if (IsNullable(x.Type) && NotNullable(x.Type)) Line($"  free ensures {Local(x)} != null;");
            }
            // (one that speaks of snapshots of predicate instances, the procedure's own state, is checked and assumed in its body)
            foreach (var r in p.Requires) Line($"  {(p.FreeRequires ? "free requires" : "requires")} {(Snapshots(r.Expr) ? "true" : E(r.Expr, atEntry))};", p.FreeRequires ? null : r.Check);
            // (checked at each return, where it is reported: Boogie would report one return path of each)
            // (one of a parameter the body assigns is of its value at return, which callers don't see: they get none)
            foreach (var e in p.Ensures) Line($"  free ensures {(Snapshots(e.Expr) || MentionsAny(e.Expr, p.AssignedParams.Keys) ? "true" : E(e.Expr, cx))};");
            if (Returns(m) != null && IsIntegral(Returns(m)) && !p.Ghost) Line($"  free ensures {E(InRange(new KVar("result"), Returns(m)), cx)};");
            if (functionFields != null)
                Line($"  free ensures result == {E(new KFnApp { Callee = m, Function = FunctionName(m), Layer = "$LS($LZ)", Fields = functionFields, Args = (p.HasThis ? new[] { new KVar("this") } : new KExpr[0]).Concat(m.Parameters.Select(x => (KExpr)new KVar(Local(x)))).ToArray() }, cx)};");
            if (Returns(m) != null && IsRef(Returns(m))) Line("  free ensures result == null || $Alloc[result];");
            // (a list's constructor: a new list)
            if (p.ListCtor) Line("  free ensures result != null && !old($Alloc[result]) && $Alloc[result];");
            if (Returns(m) != null && IsNullable(Returns(m)) && NotNullable(Returns(m))) Line("  free ensures result != null;");
            if (Returns(m) != null && IsData(Returns(m))) Line($"  free ensures {DataFacts("result", Returns(m), cx)};");
            // (a constructor has set the fields that may not be null: it asserts so at each return)
            if (p.IsCtor)
                foreach (var f in InstanceFields(m.ContainingType).Where(f => IsNullable(FieldType(f)) && NotNullable(FieldType(f)) &&
                                                                         (!Checks.IsRequired(f) || m.GetAttributes().Any(a => a.AttributeClass?.Name == "SetsRequiredMembersAttribute"))))
                    Line($"  free ensures {FieldMap(f)}[this] != null;");
            if (p.Abstract) return;
            Line("{");
            if (p.UsesPerm)
            {
                Line("  var perm: [Ref]bool;");
                Line("  var pk: [Ref]int;");
                Line("  var pkg: [Ref]bool;");
                Line("  var pinst: [Inst]int;");
                Line("  var owner: [Ref]Inst;");
                Line("  var psnap: [Inst]int;");
                Line("  var psnap$entry: [Inst]int;");
                if (p.UsesFields)
                {
                    Line("  var fperm: [Ref][int]bool;");
                    Line("  var fowner: [Ref][int]Inst;");
                }
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
                // (a block's leading assertions and assumptions are a loop's invariants where it is a head: kept whole there)
                // (elsewhere a check not assumed after is on a side branch: inline, a failing one would make what follows vacuous)
                int lead = !p.LoopBodies.ContainsKey(b.Ordinal) || b.Label != $"b{b.Ordinal}" ? 0 : b.Stmts.TakeWhile(x => x is KAssert || x is KAssume || x is KLoopFrame || x is KAtomicSteps || x is KConfinedFrame).Count();
                for (int k = 0; k < b.Stmts.Count; k++) { _leading = k < lead; Statement(b.Stmts[k], cx); }
                _leading = false;
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
                if (p.UsesPerm) Line("  var psnap: [Inst]int;");
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
        private static bool MentionsAny(KExpr e, IEnumerable<string> names) => names.Any() && e switch
        {
            KOp { Op: "old" } => false,
            KLit => false,
            KVar v => names.Contains(v.Name),
            KOp op => op.Args.Any(a => MentionsAny(a, names)),
            KQuant q => (q.Range != null && MentionsAny(q.Range, names)) || MentionsAny(q.Body, names),
            KFnApp f => f.Args.Any(a => MentionsAny(a, names)),
            KFnCall c => (c.Receiver != null && MentionsAny(c.Receiver, names)) || c.Args.Any(a => MentionsAny(a, names)),
            _ => true,
        };

        /// <summary>
        /// What a data value is: one of its type's cases (or null); a struct's (a package's) is never null, and its
        /// non-nullable references aren't either (each construction checked them).
        /// </summary>
        private string DataFacts(string local, ITypeSymbol t, Context cx)
        {
            var name = E(new KVar(local), cx);
            var isCase = E(IsCase(new KVar(local), t), cx);
            if (!t.IsValueType) return $"{name} == null || {isCase}";
            var refs = KernelTypes.Data.Fields((INamedTypeSymbol)t).Where(f => IsRef(f.Type) || IsView(f.Type)).ToList();
            var fields = refs.Where(f => NotNullable(f.Type)).Select(f => $" && {FieldFunction(f)}({name}) != null")
                .Concat(refs.Select(f => $" && ({FieldFunction(f)}({name}) == null || $Alloc[{FieldFunction(f)}({name})])"));
            return $"{name} != null && {isCase}{string.Concat(fields)}";
        }

        /// <summary>The reference-valued fields a procedure reads or writes, in order.</summary>
        private static IEnumerable<ISymbol> RefFieldsOf(KProcedure p) =>
            p.Fields.Where(f => IsField(f) && IsRef(FieldType(f)) && !IsTypeParameter(FieldType(f))).OrderBy(FieldMap, System.StringComparer.Ordinal);

        /// <summary>What an [Owns] field holds is in its container's tree, and isn't its root (Own.Give and Own.Take keep it so).</summary>
        private static string TreeField(ISymbol f) =>
            $"(forall o: Ref :: {{ {FieldMap(f)}[o] }} $Alloc[o] && {FieldMap(f)}[o] != null ==> $root[{FieldMap(f)}[o]] == $root[o] && $root[{FieldMap(f)}[o]] != {FieldMap(f)}[o])";

        private static string GoodField(ISymbol f) => f.IsStatic
            ? $"({FieldMap(f)}[null] == null || $Alloc[{FieldMap(f)}[null]])"
            : $"(forall o: Ref :: {{ {FieldMap(f)}[o] }} $Alloc[o] && {FieldMap(f)}[o] != null ==> $Alloc[{FieldMap(f)}[o]])";

        private void Given(KProcedure p, Context cx)
        {
            var m = p.Method;
            Line($"  free requires {InRangeOfMemory};");
            if (p.HasThis && p.ThisIsView && KernelTypes.Trees) Line("  free requires $root[this] == this;");
            if (p.HasThis && !IsStruct(m.ContainingType)) Line(IsData(m.ContainingType) ? $"  free requires {E(IsCase(new KVar("this"), m.ContainingType), cx)};" : "  free requires this != null && $Alloc[this];");
            // (a reference in a field of an allocated object is to an allocated object: Dafny's good heap, as CsVerify's engine assumes where it reads one)
            foreach (var f in RefFieldsOf(p)) Line($"  free requires {GoodField(f)};");
            foreach (var f in RefFieldsOf(p).Where(f => SpecSymbols.IsOwnsField(f) && KernelTypes.Trees)) Line($"  free requires {TreeField(f)};");
            // (a new object's fields are their defaults: its caller made them so)
            if (p.IsCtor)
                foreach (var f in InstanceFields(m.ContainingType).Where(f => !IsTypeParameter(FieldType(f))).OrderBy(FieldMap, System.StringComparer.Ordinal))
                    Line($"  free requires {FieldMap(f)}[this] == {E(Default(FieldType(f)), cx)};");
            foreach (var x in m.Parameters.Where(x => x.RefKind != RefKind.Out))
                foreach (var fact in ValueFacts(Local(x), x.Type, x, cx)) Line($"  free requires {fact};");
            // (what a lambda or a local function captures: some value of its type)
            foreach (var (input, type, notNull) in p.Captured)
            {
                foreach (var fact in ValueFacts(input, type, null, cx)) Line($"  free requires {fact};");
                if (notNull && !(IsNullable(type) && NotNullable(type))) Line($"  free requires {input} != null;");
            }
        }

        /// <summary>What a value from elsewhere is, of its type: a parameter's, a variable a lambda captures.</summary>
        private IEnumerable<string> ValueFacts(string local, ITypeSymbol type, IParameterSymbol x, Context cx)
        {
            var name = E(new KVar(local), cx);
            if (IsIntegral(type)) yield return E(InRange(new KVar(local), type), cx);
            // (a span from elsewhere: its cells some array's, within its length)
            if (IsSpan(type)) yield return $"$sbase({name}) != null && $Alloc[$sbase({name})] && 0 <= $soff({name}) && 0 <= len({name}) && $soff({name}) + len({name}) <= len($sbase({name}))";
            if (IsRef(type) || IsView(type) || IsShare(type)) yield return $"{name} == null || $Alloc[{name}]";
            // (not null: checked at each call's argument)
            if (IsNullable(type) && (NotNullable(type) || x != null && IsQueryParameter(x))) yield return $"{name} != null";
            // (a view's object is its tree's root)
            if (KernelTypes.Trees && x != null && HoldsView(x)) yield return $"$root[{name}] == {name}";
            if (KernelTypes.Trees && IsPackage(type) && (x == null || x.RefKind is RefKind.None or RefKind.Ref))
                foreach (var f in PackageViews(type)) yield return $"$root[{FieldFunction(f)}({name})] == {FieldFunction(f)}({name})";
            // (a data value is one of its type's cases)
            if (IsData(type)) yield return DataFacts(local, type, cx);
        }

        private void Statement(KStmt s, Context cx)
        {
            switch (s)
            {
                case KAssign a: Line($"    {a.Var} := {E(a.Value, cx)};"); return;
                case KMapUpdate u: Line($"    {u.Map}[{E(u.Ref, cx)}]{(u.Index == null ? "" : $"[{E(u.Index, cx)}]")} := {E(u.Value, cx)};"); return;
                // (a check not assumed after: on a branch of its own that ends, so that, reported, it isn't assumed where
                // Boogie looks for the next failure either, which would hide those after it on the same path)
                case KAssert a when a.NotAssumedAfter && _leading: Line($"    assert {{:subsumption 0}} {E(a.Cond, cx)};", a.Check); return;
                case KAssert a when a.NotAssumedAfter:
                {
                    var side = $"nc${_sides++}";
                    Line($"    goto {side}, {side}$go;");
                    Line($"  {side}:");
                    Line($"    assert {E(a.Cond, cx)};", a.Check);
                    Line("    assume false;");
                    Line("    return;");
                    Line($"  {side}$go:");
                    return;
                }
                case KAssert a: Line($"    assert {E(a.Cond, cx)};", a.Check); return;
                case KAssume a: Line($"    assume {E(a.Cond, cx)};"); return;
                case KHavoc h: Line($"    havoc {h.Var};"); return;
                case KRoots roots when roots.Join:
                    Line($"    $root := (lambda y: Ref :: (if $root[y] == {E(roots.Child, cx)} then $root[{E(roots.Container, cx)}] else $root[y]));");
                    return;
                case KRoots roots:
                {
                    var c = E(roots.Container, cx);
                    var x = E(roots.Child, cx);
                    Line("    havoc split$;");
                    Line($"    $root := (lambda y: Ref :: (if y == {x} then {x} else (if $root[y] == $root[{c}] && y != {c}{string.Concat(roots.Siblings.Select(g => $" && y != {g}[{c}]"))} && split$[y] then {x} else $root[y])));");
                    return;
                }
                case KAtomicSteps st when st.Head >= 0:
                    // (since the loop's entry: of its snapshot)
                    foreach (var map in st.Maps.Where(AtomicSteps.ContainsKey).OrderBy(x => x, System.StringComparer.Ordinal))
                    {
                        string At(string o) => E(Checks.Rename(Checks.Rename(AtomicSteps[map], "x$old", new KLit($"as{st.Head}{map}[{o}]")), "x$now", new KLit($"{map}[{o}]")), InProcedure);
                        Line($"    assume (forall o: Ref :: as{st.Head}$Alloc[o] ==> {At("o")});");
                        Line($"    assume {At("null")};");
                    }
                    return;
                case KAtomicSteps _:
                    foreach (var l in StepsKept(AtomicSteps.Keys, false)) Line("    " + l);
                    return;
                case KHavocAll ha:
                    var havoc = ha.ProgramState ? "$havocProgram" : "$havoc";
                    Line(ha.Unless == null ? $"    call {havoc}();" : $"    if (!({E(ha.Unless, cx)})) {{ call {havoc}(); }}");
                    return;
                case KKeep keep when !keep.After:
                    foreach (var m in _stateMaps) Line($"    k${keep.Id}{m.name} := {m.name};");
                    return;
                case KKeep keep:
                    foreach (var m in _stateMaps)
                        Line($"    assume (forall o: Ref :: ({string.Join(" || ", keep.Keep.Select(x => $"o == {E(new KVar(x), cx)}"))}) ==> {m.name}[o] == k${keep.Id}{m.name}[o]);");
                    return;
                case KAwait aw:
                {
                    var k = $"(lambda r$: Ref :: {(aw.Keep.Count == 0 ? "false" : string.Join(" || ", aw.Keep.Select(x => $"r$ == {E(new KVar(x), cx)}")))})";
                    // (what its permissions cover, kept too: cells it holds, objects whose views it holds)
                    var held = aw.Cells || aw.Perm ? $", {(aw.Cells ? "cells" : "(lambda a: Ref :: (lambda i: int :: 0.0))")}, {(aw.Perm ? "perm" : "(lambda o: Ref :: false)")}" : "";
                    var suffix = held.Length > 0 ? "Held" : "";
                    Line(aw.When == null ? $"    call $await{suffix}({k}{held});" : $"    call $awaitIf{suffix}({E(aw.When, cx)}, {k}{held});");
                    return;
                }
                case KInvoke iv:
                    Line($"    call {(iv.Result == null ? "" : iv.Result + " := ")}$call.{iv.Key}({string.Join(", ", new[] { iv.Delegate }.Concat(iv.Args).Select(x => E(x, cx)))});");
                    return;
                case KLambda lam:
                {
                    string Bind(IEnumerable<string> more) => string.Join(", ", lam.Params.Select(x => $"{x.name}: {x.type}").Concat(more));
                    string App(string fn, string more) => $"{fn}({lam.Var}{string.Concat(lam.Params.Select(x => ", " + x.name))}{more})";
                    string All(IEnumerable<string> more, string trigger, string body) =>
                        lam.Params.Count == 0 && !more.Any() ? body : $"(forall {Bind(more)} :: {{ {trigger} }} {body})";
                    var pre = App("$pre." + lam.Key, "");
                    Line($"    assume {All(new string[0], pre, lam.Pre == null ? pre : $"{pre} == ({E(lam.Pre, cx)})")};");
                    var rs = lam.ResultType == null ? new string[0] : new[] { $"q$r: {lam.ResultType}" };
                    var post = App("$post." + lam.Key, lam.ResultType == null ? "" : ", q$r");
                    foreach (var fact in lam.Posts)
                        Line($"    assume {All(rs, post, $"{post} && {pre} ==> ({E(fact, cx)})")};");
                    if (lam.NoChange) Line($"    assume $nochange({lam.Var});");
                    if (lam.Steady) Line($"    assume $steady({lam.Var});");
                    var preS = $"$preS.{lam.Key}({lam.Var}, {State}{string.Concat(lam.Params.Select(x => ", " + x.name))})";
                    var readsS = $"$readsS.{lam.Key}({lam.Var}, {State}{string.Concat(lam.Params.Select(x => ", " + x.name))})";
                    if (lam.PreS != null) Line($"    assume {All(new string[0], preS, $"{preS} == ({E(lam.PreS, cx)})")};");
                    if (lam.Reads != null) Line($"    assume {All(new[] { "o$: Ref" }, $"{readsS}[o$]", $"{readsS}[o$] ==> ({E(lam.Reads, cx)})[o$]")};");
                    // (in any state: what it accepts and what it gives are of that state's memory, which its frame says it reads)
                    var atS = new Context { MapAt = map => $"$st.{map}(s$)" };
                    string InS(string f) => f.Replace($"{lam.Var}, {State}", $"{lam.Var}, s$");
                    if (lam.PreS != null)
                        Line($"    assume (forall s$: St{string.Concat(lam.Params.Select(x => $", {x.name}: {x.type}"))} :: {{ {InS(preS)} }} {InS(preS)} == ({E(lam.PreS, atS)}));");
                    if (lam.PostsS.Count > 0)
                    {
                        var postS = $"$postS.{lam.Key}({lam.Var}, s${string.Concat(lam.Params.Select(x => ", " + x.name))}{(lam.ResultType == null ? "" : ", q$r")})";
                        foreach (var fact in lam.PostsS)
                            Line($"    assume (forall s$: St{string.Concat(lam.Params.Select(x => $", {x.name}: {x.type}"))}{(lam.ResultType == null ? "" : $", q$r: {lam.ResultType}")} :: {{ {postS} }} {postS} && {InS(preS)} ==> ({E(fact, atS)}));");
                    }
                    var frame = $"$frame.{lam.Key}({lam.Var}{string.Concat(lam.Params.Select(x => ", " + x.name))})";
                    if (lam.Changes != null) Line($"    assume {All(new[] { "o$: Ref" }, $"{frame}[o$]", $"{frame}[o$] ==> ({E(lam.Changes, cx)})[o$]")};");
                    return;
                }
                case KNewExc ne:
                    Line($"    havoc {ne.Var};");
                    Line($"    assume {ne.Var} != null && dtype({ne.Var}) == {TypeConst(ne.Type)};");
                    return;
                case KFork fork:
                {
                    // the way it throws, then the way it doesn't (a block of its own each)
                    var n = _forks++;
                    Line($"    goto f${n}$x, f${n};");
                    Line($"  f${n}$x:");
                    if (fork.Call != null)
                    {
                        var given = fork.Call.Args.Where((a, k) => k >= fork.Call.Callee.Parameters.Length || fork.Call.Callee.Parameters[k].RefKind != RefKind.Out);
                        Line($"    call ex$ := {Name(fork.Call.Callee)}$throws({string.Join(", ", (fork.Call.Receiver == null ? given : new[] { fork.Call.Receiver }.Concat(given)).Select(a => E(a, cx)))});");
                        Throwing.Add(fork.Call.Callee);
                    }
                    else
                    {
                        Line($"    assume !({E(fork.Overflow, cx)});");
                        Line("    havoc ex$;");
                        Line(fork.Exception == null ? "    assume ex$ != null;" : $"    assume ex$ != null && dtype(ex$) == {fork.Exception};");
                    }
                    Line($"    goto {fork.Target};");
                    Line($"  f${n}:");
                    return;
                }
                case KCallFrame { After: false } frame:
                    foreach (var x in new[] { "perm", "pinst", "owner", "psnap", "$Alloc" }.Concat(KernelTypes.Trees ? new[] { "$root" } : new string[0]).Concat(frame.Maps).Concat(frame.Fields ? new[] { "fperm", "fowner" } : new string[0])
                                 .Concat(frame.Cells ? new[] { "cells", "cowner" }.Concat(frame.ElementMaps) : new string[0]).Concat(frame.OldGlobals).Distinct())
                        Line($"    s{frame.Id}{(x.StartsWith("$") ? "" : "$")}{x} := {x};");
                    return;
                case KCallFrame frame:
                {
                    // (what the caller still holds, whole or folded into an instance it holds, the call couldn't change)
                    var sn = "s" + frame.Id;
                    var kept = $"{sn}$Alloc[y] && (({sn}$perm[y]{(frame.Receiver == null ? "" : $" && y != {E(frame.Receiver, cx)}")}) || {sn}$pinst[{sn}$owner[y]] >= 1)";
                    Line("    havoc owner;");
                    Line($"    assume (forall y: Ref :: {kept} ==> owner[y] == {sn}$owner[y]);");
                    foreach (var map in frame.Maps)
                    {
                        // (a field: also kept where the caller holds that field alone, or has it folded into an instance it holds)
                        var k = frame.FieldIds.TryGetValue(map, out var id) ? id : 0;
                        var field = frame.Fields ? $" || {sn}$fperm[y][{k}] || {sn}$pinst[{sn}$fowner[y][{k}]] >= 1" : "";
                        // (and, in a tree, where the caller holds its root's view: what the root owns goes with it)
                        var tree = KernelTypes.Trees ? $" || ({sn}$perm[{sn}$root[y]] && {sn}$root[y] != y{(frame.Receiver == null ? "" : $" && {sn}$root[y] != {E(frame.Receiver, cx)}")})" : "";
                        var keptHere = $"{sn}$Alloc[y] && (({sn}$perm[y]{(frame.Receiver == null ? "" : $" && y != {E(frame.Receiver, cx)}")}){field}{tree} || {sn}$pinst[{sn}$owner[y]] >= 1)";
                        Line($"    assume (forall y: Ref :: {keptHere} ==> {map}[y] == {sn}{map}[y]);");
                    }
                    // (a query of an [Owned] object reads only its tree: of one the caller keeps, what it was)
                    if (KernelTypes.Trees)
                        foreach (var (qm, qfields) in _ownedQueries.Where(q => q.fields.Any(frame.Maps.Contains)))
                        {
                            var x = new KVar("x$q");
                            var now = E(new KFnApp { Callee = qm, Function = FunctionName(qm), Layer = "$LS($LZ)", Fields = qfields, Args = new KExpr[] { x } }, cx);
                            var maps = OwnArrays(qm) == null ? Maps(cx) : "";
                            var then = $"{FunctionName(qm)}($LS($LZ){(maps.Length == 0 ? "" : ", " + maps)}{string.Join("", qfields.Select(f => ", " + (frame.Maps.Contains(f) ? sn + f : Map(f, cx))))}, x$q)";
                            var recv = frame.Receiver == null ? "" : $" && x$q != {E(frame.Receiver, cx)} && {sn}$root[x$q] != {E(frame.Receiver, cx)}";
                            Line($"    assume (forall x$q: Ref :: {{ {now} }} {sn}$Alloc[x$q] && ({sn}$perm[x$q] || {sn}$perm[{sn}$root[x$q]]){recv} ==> {now} == {then});");
                        }
                    if (frame.Fields)
                    {
                        var keptField = $"{sn}$Alloc[y] && (({sn}$perm[y]{(frame.Receiver == null ? "" : $" && y != {E(frame.Receiver, cx)}")}) || {sn}$fperm[y][k] || {sn}$pinst[{sn}$owner[y]] >= 1 || {sn}$pinst[{sn}$fowner[y][k]] >= 1)";
                        Line("    havoc fowner;");
                        Line($"    assume (forall y: Ref, k: int :: {keptField} ==> fowner[y][k] == {sn}$fowner[y][k]);");
                    }
                    if (frame.Cells)
                    {
                        // (a call that takes cells changes only those it got, and those folded into the instances it got, but
                        // for those of which a share is still in hand, which nobody else can write; and arrays it allocates)
                        var (xv, iv) = (new KVar("x$"), new KVar("i$"));
                        var parts = frame.Given.Select(g => g.atom switch
                        {
                            KCells c => E(Checks.InCells(g.guard, c, xv, iv), cx),
                            KInst q => $"({E(g.guard, cx)} && {sn}$cowner[x$][i$] == {E(Checks.Instance(q.Pred, q.Args), cx)})",
                            _ => null,
                        }).Where(x => x != null).ToList();
                        var changed = parts.Count == 0 ? "false" : $"(({string.Join(" || ", parts)}) && {sn}$cells[x$][i$] <= 0.0)";
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
                case KConfinedSnapshot cs:
                    foreach (var (name, _) in _stateMaps) Line($"    c${cs.Head}{name} := {name};");
                    return;
                case KConfinedFrame cf:
                    foreach (var (local, written) in cf.Locals.OrderBy(x => x.Key, System.StringComparer.Ordinal))
                        foreach (var (name, _) in _stateMaps.Where(m => !written.Contains(m.name) && !(written.Contains("$M.") && m.name.StartsWith("$F.$M."))))
                            Line($"    assume {local} != null ==> {name}[{local}] == c${cf.Head}{name}[{local}];");
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
                    var given = c.Args.Where((a, k) => k >= c.Callee.Parameters.Length || c.Callee.Parameters[k].RefKind != RefKind.Out);
                    if (c.Phase == 2) Started.Add(c.Callee);
                    Line($"    call {(targets.Count == 0 ? "" : string.Join(", ", targets) + " := ")}{Name(c.Callee)}{(c.Phase == 2 ? "$started" : "")}({string.Join(", ", (c.Receiver == null ? given : new[] { c.Receiver }.Concat(given)).Select(a => E(a, cx)))});", c.Check);
                    return;
                }
                default: throw new NotTranslated("not printable: " + s.GetType().Name);
            }
        }
    }
}
