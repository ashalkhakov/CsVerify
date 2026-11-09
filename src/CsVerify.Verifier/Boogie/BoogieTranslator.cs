using System;
using System.Collections.Generic;
using System.Globalization;
using System.Linq;
using System.Text;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.FlowAnalysis;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>What a line of the Boogie program checks: the diagnostic it is, and where in the C# source.</summary>
    internal sealed class Check
    {
        public string Id;
        public string Message;
        public FileLinePositionSpan Span;
        public MethodResult Method;
        /// <summary>For a requires or an ensures (Id Aux): the diagnostic a failure of it is (CSV1001 or CSV1014; CSV1002 or CSV1014).</summary>
        public string ReportAs;
    }

    /// <summary>A construct outside the subset the Boogie translation covers: the method is verified the other way.</summary>
    internal sealed class NotTranslated : Exception
    {
        public NotTranslated(string why) : base(why) { }
    }

    /// <summary>
    /// C# to Boogie (docs/boogie.md): each method a procedure, its body Roslyn's control-flow graph block for block (an
    /// unstructured Boogie procedure: blocks and gotos), its Spec.Requires and Spec.Ensures the procedure's contract,
    /// and each check an assert on a line of its own, which <see cref="Lines"/> maps back to a CsVerify diagnostic.
    ///
    /// The subset so far: static methods of int, long and bool and of one-dimensional arrays of them; arithmetic
    /// (checked, unchecked and the default), comparisons, if and loops (with Spec.Invariant), calls of each other,
    /// array reads, writes, lengths and allocation, Spec.Assert and Spec.Assume, and in specifications Spec.Forall,
    /// Spec.Exists, Spec.Old and Spec.Result. Arrays are Dafny's encoding: references, an allocated set, a length, a
    /// map of elements per element type; a procedure modifies the maps it (or what it calls) writes. Integers follow
    /// docs/semantics.md; specifications are mathematical, and checked well-defined (CSV1012) as Dafny's are.
    /// </summary>
    internal sealed class BoogieTranslator
    {
        private readonly StringBuilder _text = new StringBuilder();
        private int _line = 1;

        /// <summary>The check each line of the program is (1-based, as Boogie reports).</summary>
        public readonly Dictionary<int, Check> Lines = new Dictionary<int, Check>();

        /// <summary>How many obligations each procedure has.</summary>
        public readonly Dictionary<MethodResult, int> Obligations = new Dictionary<MethodResult, int>();

        /// <summary>A line that says what a failure is about (a requires, an ensures, a return), not a check of its own.</summary>
        internal const string Aux = "aux";

        private readonly HashSet<IMethodSymbol> _procedures = new HashSet<IMethodSymbol>(SymbolEqualityComparer.Default);
        private readonly bool _checkOverflow;

        /// <summary>The procedures translated, written when all are (their modifies need what each calls).</summary>
        private readonly List<Pending> _pending = new List<Pending>();

        private sealed class Pending
        {
            public IMethodSymbol Method;
            public MethodResult Result;
            public List<(string text, Check check)> Header, Body;
            public HashSet<string> Writes;
            public HashSet<IMethodSymbol> Calls;
            public int Obligations;
        }

        public BoogieTranslator(bool checkOverflow) { _checkOverflow = checkOverflow; }

        public string Text => _text.ToString();

        // ------------------------------------------------------------------ the subset

        private static bool IsIntegral(ITypeSymbol t) => t != null && Widths.ContainsKey(t.SpecialType);

        /// <summary>Each C# integer type: its bits, and whether it is signed (char is an unsigned 16-bit integer here).</summary>
        private static readonly Dictionary<SpecialType, (int bits, bool signed)> Widths = new Dictionary<SpecialType, (int, bool)>
        {
            [SpecialType.System_SByte] = (8, true), [SpecialType.System_Byte] = (8, false),
            [SpecialType.System_Int16] = (16, true), [SpecialType.System_UInt16] = (16, false), [SpecialType.System_Char] = (16, false),
            [SpecialType.System_Int32] = (32, true), [SpecialType.System_UInt32] = (32, false),
            [SpecialType.System_Int64] = (64, true), [SpecialType.System_UInt64] = (64, false),
        };

        private static readonly SpecialType[] ElementTypes = Widths.Keys.Append(SpecialType.System_Boolean).ToArray();

        private static bool IsArray(ITypeSymbol t) => t is IArrayTypeSymbol a && a.IsSZArray && Scalar(a.ElementType);

        private static bool Scalar(ITypeSymbol t) => IsIntegral(t) || t?.SpecialType == SpecialType.System_Boolean;

        private static bool InSubset(ITypeSymbol t) => Scalar(t) || IsArray(t);

        /// <summary>Could this method be a procedure (before its body is looked at)?</summary>
        public static bool Candidate(IMethodSymbol m, Contract c) =>
            m.IsStatic && !m.IsAsync && !m.IsGenericMethod && m.MethodKind == MethodKind.Ordinary &&
            (m.ReturnsVoid || InSubset(m.ReturnType)) && m.Parameters.All(p => p.RefKind == RefKind.None && InSubset(p.Type)) &&
            c.Modifies == null && c.Reads == null && c.ThrowEnsures.Count == 0 && !c.IsTrusted &&
            c.Ensures.All(e => e.Guard == null) && c.Bases.Count == 0;

        /// <summary>Why a method isn't a candidate (for CSVERIFY_TRACE).</summary>
        public static string WhyNot(IMethodSymbol m, Contract c) =>
            !m.IsStatic ? "an instance member" : m.IsAsync ? "async" : m.IsGenericMethod ? "generic" : m.MethodKind != MethodKind.Ordinary ? m.MethodKind.ToString() :
            !(m.ReturnsVoid || InSubset(m.ReturnType)) ? "returns " + m.ReturnType :
            m.Parameters.FirstOrDefault(p => p.RefKind != RefKind.None || !InSubset(p.Type)) is IParameterSymbol bad ? $"a parameter of {(bad.RefKind != RefKind.None ? bad.RefKind + " " : "")}{bad.Type}" :
            c.Modifies != null ? "Spec.Modifies" : c.Reads != null ? "Spec.Reads" : c.ThrowEnsures.Count > 0 ? "Spec.EnsuresOnThrow" :
            c.IsTrusted ? "[Trusted]" : "an inherited contract";

        /// <summary>Each method's contract (CsVerify's reading of its Spec statements).</summary>
        public Func<IMethodSymbol, Contract> ContractOf;

        /// <summary>What each procedure calls, directly or not (its recursion groups: each other's).</summary>
        private readonly Dictionary<IMethodSymbol, HashSet<IMethodSymbol>> _reaches = new Dictionary<IMethodSymbol, HashSet<IMethodSymbol>>(SymbolEqualityComparer.Default);

        /// <summary>The procedures in the program (each candidate whose body translates): calls of them are calls.</summary>
        public void Declare(IEnumerable<(IMethodSymbol method, SyntaxNode decl, SemanticModel model)> procedures)
        {
            var list = procedures.ToList();
            foreach (var p in list) _procedures.Add(p.method.OriginalDefinition);
            var calls = new Dictionary<IMethodSymbol, HashSet<IMethodSymbol>>(SymbolEqualityComparer.Default);
            foreach (var (m, decl, model) in list)
                calls[m.OriginalDefinition] = new HashSet<IMethodSymbol>(decl.DescendantNodes().OfType<InvocationExpressionSyntax>()
                    .Select(i => (model.GetSymbolInfo(i).Symbol as IMethodSymbol)?.OriginalDefinition).Where(x => x != null && _procedures.Contains(x)), SymbolEqualityComparer.Default);
            foreach (var m in calls.Keys)
            {
                var seen = new HashSet<IMethodSymbol>(SymbolEqualityComparer.Default);
                var work = new Stack<IMethodSymbol>(calls[m]);
                while (work.Count > 0)
                {
                    var x = work.Pop();
                    if (!seen.Add(x)) continue;
                    if (calls.TryGetValue(x, out var next)) foreach (var y in next) work.Push(y);
                }
                _reaches[m] = seen;
            }
        }

        /// <summary>Is a call of b from a recursive (b calls a back, or is a)?</summary>
        private bool Recursive(IMethodSymbol a, IMethodSymbol b) =>
            _reaches.TryGetValue(b, out var fromB) && fromB.Contains(a) && _reaches.TryGetValue(a, out var fromA) && fromA.Contains(b);

        /// <summary>
        /// A [Pure] or [GhostFunction] method with a single expression for its body: a Boogie function too, which
        /// specifications call (as Dafny's functions, with fuel: one unfolding per use, as CsVerify's engine).
        /// </summary>
        private bool IsFunction(IMethodSymbol m) => _procedures.Contains(m.OriginalDefinition) && ContractOf?.Invoke(m) is Contract c && c.IsPure && c.PureBody != null;

        private static string FunctionName(IMethodSymbol m) => "f$" + Name(m);

        private static string MapParams => string.Join(", ", ElementTypes.Select(t => $"h{ElementMap(t)}: [Ref][int]{(t == SpecialType.System_Boolean ? "bool" : "int")}"));

        // ------------------------------------------------------------------ writing

        private void Line(string text, Check check = null)
        {
            if (check != null) Lines[_line] = check;
            _text.Append(text).Append('\n');
            _line++;
        }

        private static string Name(IMethodSymbol m) =>
            Ident(m.ContainingType.ToDisplayString() + "." + m.Name + "$" + string.Join("$", m.Parameters.Select(p => p.Type.ToDisplayString())));

        private static string Ident(string s)
        {
            var b = new StringBuilder();
            foreach (var ch in s) b.Append(char.IsLetterOrDigit(ch) || ch == '_' || ch == '.' || ch == '$' ? ch : '_');
            return b.ToString();
        }

        private static string Local(ISymbol s) => s is IParameterSymbol p ? "p$" + p.Name : "l$" + s.Name + "$" + s.Locations.FirstOrDefault()?.SourceSpan.Start;

        private static string TypeOf(ITypeSymbol t) => IsArray(t) ? "Ref" : t.SpecialType == SpecialType.System_Boolean ? "bool" : "int";

        /// <summary>The map of an array type's elements.</summary>
        private static string Elements(ITypeSymbol array) => ElementMap(((IArrayTypeSymbol)array).ElementType.SpecialType);

        private static string ElementMap(SpecialType t) => "$E." + t.ToString().Substring("System_".Length);

        private static (string lo, string hi) Range(ITypeSymbol t) => Range(t.SpecialType);

        private static (string lo, string hi) Range(SpecialType t)
        {
            var (bits, signed) = Widths[t];
            var size = System.Numerics.BigInteger.Pow(2, bits);
            return signed ? ((-(size / 2)).ToString(CultureInfo.InvariantCulture), (size / 2 - 1).ToString(CultureInfo.InvariantCulture))
                          : ("0", (size - 1).ToString(CultureInfo.InvariantCulture));
        }

        /// <summary>x wrapped around into t's range (two's complement, as Euclidean mod).</summary>
        private static string Wrap(string x, ITypeSymbol t)
        {
            var (lo, _) = Range(t);
            var size = System.Numerics.BigInteger.Pow(2, Widths[t.SpecialType].bits).ToString(CultureInfo.InvariantCulture);
            return $"((({x}) - ({lo})) mod {size} + ({lo}))";
        }

        private static string InRange(string e, ITypeSymbol t)
        {
            var (lo, hi) = Range(t);
            return $"({lo} <= {e} && {e} <= {hi})";
        }

        private static readonly string[] Heap = new[] { "$Alloc" }.Concat(ElementTypes.Select(ElementMap)).ToArray();

        /// <summary>What every program has: C#'s division, wrap-around, and the heap of arrays (Dafny's encoding).</summary>
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

        private static string Param(SpecialType t) => "m" + t.ToString().Substring("System_".Length);

        private static readonly string InRangeOfMemory = "$InRange(" + string.Join(", ", Widths.Keys.Select(ElementMap)) + ")";

        // ------------------------------------------------------------------ a method

        /// <summary>The method as a procedure; throws <see cref="NotTranslated"/> for one outside the subset (then nothing is kept).</summary>
        public void Procedure(IMethodSymbol m, Contract contract, SyntaxNode decl, SemanticModel model, MethodResult result)
        {
            var body = new Body(this, m, contract, decl, model, result);
            body.Translate(); // (throws before anything is kept)
            if (IsFunction(m)) _functions.AddRange(body.Function());
            _pending.Add(new Pending
            {
                Method = m.OriginalDefinition, Result = result, Header = body.Header, Body = body.Lines, Writes = body.Writes, Calls = body.Calls,
                Obligations = body.Header.Concat(body.Lines).Count(l => l.check != null && l.check.Id != Aux) + contract.Ensures.Count,
            });
        }

        private readonly List<(string text, Check check)> _functions = new List<(string, Check)>();

        /// <summary>Writes the functions and the procedures: each modifies what it writes, and what what it calls does.</summary>
        public void Finish()
        {
            foreach (var (text, check) in _functions) Line(text, check);
            var byMethod = _pending.ToDictionary(p => p.Method, p => p, SymbolEqualityComparer.Default);
            var writes = _pending.ToDictionary(p => p.Method, p => new HashSet<string>(p.Writes), SymbolEqualityComparer.Default);
            for (bool grew = true; grew;)
            {
                grew = false;
                foreach (var p in _pending)
                    foreach (var c in p.Calls)
                        if (writes.TryGetValue(c, out var w))
                            foreach (var g in w)
                                if (writes[p.Method].Add(g)) grew = true;
            }
            foreach (var p in _pending)
            {
                var w = writes[p.Method];
                foreach (var (text, check) in p.Header)
                {
                    if (text == "  // modifies")
                    {
                        if (w.Count > 0) Line($"  modifies {string.Join(", ", Heap.Where(w.Contains))};");
                        if (w.Contains("$Alloc")) Line("  free ensures (forall r: Ref :: old($Alloc[r]) ==> $Alloc[r]);");
                        continue;
                    }
                    Line(text, check);
                }
                foreach (var (text, check) in p.Body) Line(text, check);
                Obligations[p.Result] = p.Obligations;
            }
            _pending.Clear();
        }

        private sealed class Body
        {
            private readonly BoogieTranslator _t;
            private readonly IMethodSymbol _m;
            private readonly Contract _contract;
            private readonly SyntaxNode _decl;
            private readonly SemanticModel _model;
            private readonly MethodResult _result;
            private List<(string text, Check check)> _out = new List<(string, Check)>();
            private readonly List<string> _locals = new List<string>();
            private int _temps;
            public List<(string text, Check check)> Header, Lines;
            public readonly HashSet<string> Writes = new HashSet<string>();
            public readonly HashSet<IMethodSymbol> Calls = new HashSet<IMethodSymbol>(SymbolEqualityComparer.Default);

            /// <summary>Ghost code (a [GhostFunction] or a lemma): mathematical, as specifications are.</summary>
            private readonly bool _ghost;

            // (a specification's context: in a function's definition, its layer and its heap; what stands for the
            // result; parameters given values, for a callee's contract at a call)
            private string _layer = "$LS($LZ)";
            private bool _inFunction;
            private string _resultName = "result";
            private Dictionary<ISymbol, string> _subst;

            public Body(BoogieTranslator t, IMethodSymbol m, Contract contract, SyntaxNode decl, SemanticModel model, MethodResult result)
            {
                _t = t; _m = m; _contract = contract; _decl = decl; _model = model; _result = result;
                _ghost = SpecSymbols.IsGhostFunction(m) || contract.IsLemma;
            }

            private string Map(string name) => _inFunction ? "h" + name : name;

            private string Maps => string.Join(", ", ElementTypes.Select(t => Map(ElementMap(t))));

            /// <summary>
            /// The method as a Boogie function: declared on a layer and the heap's maps; defined, where its precondition
            /// holds, by its body on the next layer (so one unfolding per use); its postcondition, and its range for a
            /// run-time one, of every value.
            /// </summary>
            public List<(string, Check)> Function()
            {
                var name = FunctionName(_m);
                var ps = string.Join("", _m.Parameters.Select(p => $", {Local(p)}: {TypeOf(p.Type)}"));
                var args = string.Join("", _m.Parameters.Select(p => ", " + Local(p)));
                var bound = $"ly: LayerType, {MapParams}{ps}";
                string At(string layer) => $"{name}({layer}, {string.Join(", ", ElementTypes.Select(t => "h" + ElementMap(t)))}{args})";
                var lines = new List<(string, Check)> { ($"function {name}(ly: LayerType, {MapParams}{ps}): {TypeOf(_m.ReturnType)};", null) };
                lines.Add(($"axiom (forall {bound} :: {{ {At("$LS(ly)")} }} {At("$LS(ly)")} == {At("ly")});", null));
                _inFunction = true;
                _layer = "ly";
                try
                {
                    var pre = _contract.Requires.Select(r => SpecTerm(r, null, out _)).ToList();
                    var guard = pre.Count == 0 ? "true" : string.Join(" && ", pre);
                    var body = SpecTerm(_contract.PureBody, null, out _);
                    lines.Add(($"axiom (forall {bound} :: {{ {At("$LS(ly)")} }} {guard} ==> {At("$LS(ly)")} == {body.Replace("(ly, ", "(ly, ")});", null));
                    _resultName = At("ly");
                    foreach (var e in _contract.Ensures)
                        lines.Add(($"axiom (forall {bound} :: {{ {At("ly")} }} {guard} ==> {SpecTerm(e.Expr, e.ResultParameter, out _)});", null));
                    if (!_ghost && IsIntegral(_m.ReturnType)) lines.Add(($"axiom (forall {bound} :: {{ {At("ly")} }} {InRange(At("ly"), _m.ReturnType)});", null));
                }
                finally { _inFunction = false; _layer = "$LS($LZ)"; _resultName = "result"; }
                return lines;
            }

            private Check At(string id, SyntaxNode at, string message, string reportAs = null) =>
                new Check { Id = id, Message = message, Span = at.GetLocation().GetLineSpan(), Method = _result, ReportAs = reportAs };

            private void Emit(string text, Check check = null) => _out.Add((text, check));

            private static bool NotNullable(ITypeSymbol t) => t.NullableAnnotation != NullableAnnotation.Annotated;

            public void Translate()
            {
                if (!(_model.GetOperation(_decl) is IMethodBodyOperation bodyOp)) throw new NotTranslated("no body");
                var cfg = ControlFlowGraph.Create(bodyOp);
                if (cfg.Root.NestedRegions.SelectMany(AllRegions).Concat(cfg.Root.NestedRegions).Any(r => r.Kind != ControlFlowRegionKind.LocalLifetime))
                    throw new NotTranslated("try, catch or finally");
                // the header: parameters, result, contract
                var ps = string.Join(", ", _m.Parameters.Select(p => $"{Local(p)}: {TypeOf(p.Type)}"));
                var ret = _m.ReturnsVoid ? "" : $" returns (result: {TypeOf(_m.ReturnType)})";
                Header = new List<(string, Check)> { ($"procedure {Name(_m)}({ps}){ret}", null), ("  // modifies", null) };
                Header.Add(($"  free requires {InRangeOfMemory};", null));
                Header.Add(($"  free ensures {InRangeOfMemory};", null));
                foreach (var p in _m.Parameters)
                {
                    if (IsIntegral(p.Type)) Header.Add(($"  free requires {InRange(Local(p), p.Type)};", null));
                    if (IsArray(p.Type))
                    {
                        Header.Add(($"  free requires {Local(p)} == null || $Alloc[{Local(p)}];", null));
                        // (not null: checked at each call's argument)
                        if (NotNullable(p.Type)) Header.Add(($"  free requires {Local(p)} != null;", null));
                    }
                }
                foreach (var r in _contract.Requires)
                    Header.Add(($"  requires {SpecTerm(r, null, out _)};", At(Aux, r.Syntax, $"precondition '{r.Syntax}' of '{_m.Name}'", "CSV1001")));
                // (checked at each return, where it is reported: Boogie would report one return path of each)
                foreach (var e in _contract.Ensures)
                    Header.Add(($"  free ensures {SpecTerm(e.Expr, e.ResultParameter, out _)};", null));
                if (!_m.ReturnsVoid && IsIntegral(_m.ReturnType) && !_ghost) Header.Add(($"  free ensures {InRange("result", _m.ReturnType)};", null));
                if (_t.IsFunction(_m))
                    Header.Add(($"  free ensures result == {FunctionName(_m)}($LZ, {Maps}{string.Join("", _m.Parameters.Select(p => ", " + Local(p)))});", null));
                if (!_m.ReturnsVoid && IsArray(_m.ReturnType))
                {
                    Header.Add(("  free ensures result == null || $Alloc[result];", null));
                    if (NotNullable(_m.ReturnType)) Header.Add(("  free ensures result != null;", null));
                }
                // the body: the requires well-defined, in order; then each block
                var heads = LoopHeads(cfg);
                var invariants = Invariants(cfg, heads);
                var blocks = new List<(string, Check)>();
                _out = blocks;
                var before = new List<string>();
                foreach (var r in _contract.Requires)
                {
                    var term = SpecTerm(r, null, out var wf);
                    WellDefined(wf, r.Syntax, before);
                    before.Add(term);
                }
                foreach (var b in cfg.Blocks)
                {
                    Emit($"  b{b.Ordinal}:");
                    if (invariants.TryGetValue(b.Ordinal, out var invs))
                        foreach (var inv in invs)
                        {
                            var term = SpecTerm(inv, null, out var wf);
                            WellDefined(wf, inv.Syntax, null);
                            Emit($"    assert {term};", At("CSV1005", inv.Syntax, $"loop invariant '{inv.Syntax}'"));
                        }
                    if (_measures.TryGetValue(b.Ordinal, out var measure))
                        for (int k = 0; k < measure.Count; k++)
                            Emit($"    {Declare($"m${b.Ordinal}${k}", measure[k].Type)} := {SpecTerm(measure[k], null, out _)};");
                    if (b.Kind == BasicBlockKind.Exit) { Emit("    assume false;"); Emit("    return;"); continue; }
                    foreach (var op in b.Operations) Statement(op);
                    Branch(b);
                }
                Header.Add(("{", null));
                Header.AddRange(_locals.Select(l => ((string)$"  var {l};", (Check)null)));
                Lines = blocks;
                Lines.Add(("}", null));
            }

            /// <summary>A specification's well-definedness, asserted (CSV1012) where it is evaluated, under what holds before it.</summary>
            private void WellDefined(List<string> wf, SyntaxNode at, List<string> before)
            {
                if (wf.Count == 0) return;
                var cond = string.Join(" && ", wf);
                if (before != null && before.Count > 0) cond = $"({string.Join(" && ", before)}) ==> ({cond})";
                // (checked, not assumed after: what an ill-defined specification says is unknown, as in CsVerify's engine)
                Emit($"    assert {{:subsumption 0}} {cond};", At("CSV1012", at, $"specification might not be well-defined: '{at}'"));
            }

            private static IEnumerable<ControlFlowRegion> AllRegions(ControlFlowRegion r) => r.NestedRegions.Concat(r.NestedRegions.SelectMany(AllRegions));

            /// <summary>The blocks a later block goes back to: loop heads.</summary>
            private static HashSet<int> LoopHeads(ControlFlowGraph cfg)
            {
                var heads = new HashSet<int>();
                foreach (var b in cfg.Blocks)
                    foreach (var s in new[] { b.FallThroughSuccessor, b.ConditionalSuccessor })
                        if (s?.Destination != null && s.Destination.Ordinal <= b.Ordinal) heads.Add(s.Destination.Ordinal);
                return heads;
            }

            /// <summary>Each Spec.Invariant, at the head of the innermost loop it is in (asserts at a head are Boogie's invariants).</summary>
            /// <summary>Each loop's Spec.Decreases measure (its head's), read at the head of each iteration.</summary>
            private readonly Dictionary<int, List<IOperation>> _measures = new Dictionary<int, List<IOperation>>();

            /// <summary>The innermost loop a block is in: the latest head before it whose back edge comes from it or after it; -1 if none.</summary>
            private static int HeadOf(ControlFlowGraph cfg, HashSet<int> heads, BasicBlock b) =>
                heads.Where(h => h <= b.Ordinal && cfg.Blocks.Any(x => x.Ordinal >= b.Ordinal &&
                    new[] { x.FallThroughSuccessor, x.ConditionalSuccessor }.Any(s => s?.Destination?.Ordinal == h))).DefaultIfEmpty(-1).Max();

            private Dictionary<int, List<IOperation>> Invariants(ControlFlowGraph cfg, HashSet<int> heads)
            {
                var at = new Dictionary<int, List<IOperation>>();
                foreach (var b in cfg.Blocks)
                    foreach (var op in b.Operations)
                    {
                        if (SpecCall(op, "Decreases") is IInvocationOperation dec && HeadOf(cfg, heads, b) is int h && h >= 0)
                            _measures[h] = (_model.GetOperation(dec.Syntax) as IInvocationOperation)?.Arguments.Select(a => a.Value).ToList()
                                           ?? throw new NotTranslated("a measure without its operation");
                        if (SpecCall(op, "Invariant") is IInvocationOperation inv)
                        {
                            var head = heads.Where(h => h <= b.Ordinal && cfg.Blocks.Any(x => x.Ordinal >= b.Ordinal &&
                                new[] { x.FallThroughSuccessor, x.ConditionalSuccessor }.Any(s => s?.Destination?.Ordinal == h))).DefaultIfEmpty(-1).Max();
                            if (head < 0) throw new NotTranslated("an invariant outside a loop");
                            if (!at.TryGetValue(head, out var list)) at[head] = list = new List<IOperation>();
                            list.Add(SpecArgument(inv));
                        }
                    }
                return at;
            }

            /// <summary>
            /// A Spec statement's argument as written: the control-flow graph lowers && and ?: in it into blocks, but a
            /// specification is one formula.
            /// </summary>
            private IOperation SpecArgument(IInvocationOperation inv) =>
                (_model.GetOperation(inv.Syntax) as IInvocationOperation)?.Arguments[0].Value ?? throw new NotTranslated("a specification without its operation");

            private static IInvocationOperation SpecCall(IOperation op, string name) =>
                (op is IExpressionStatementOperation es ? es.Operation : op) is IInvocationOperation inv &&
                SpecSymbols.IsSpecClass(inv.TargetMethod.ContainingType) && inv.TargetMethod.Name == name ? inv : null;

            // ------------------------------------------------------------------ statements

            /// <summary>
            /// Is this syntax inside a Spec statement's argument? The control-flow graph lowers && and ?: there into
            /// blocks and captures too, but specification arguments never run ([Conditional]): what they lower to is
            /// skipped, and each branch of theirs is a choice of either way (both meet again at the Spec call).
            /// </summary>
            private bool InSpec(SyntaxNode at) =>
                at != null && at.AncestorsAndSelf().OfType<ArgumentSyntax>().Any(arg => arg.Parent?.Parent is InvocationExpressionSyntax call &&
                    _model.GetSymbolInfo(call).Symbol is IMethodSymbol m && SpecSymbols.IsSpecClass(m.ContainingType));

            private void Statement(IOperation op)
            {
                if (op is IExpressionStatementOperation es) op = es.Operation;
                if (op is IFlowCaptureOperation spec && InSpec(spec.Value.Syntax)) return;
                switch (op)
                {
                    case IInvocationOperation inv when SpecSymbols.IsSpecClass(inv.TargetMethod.ContainingType):
                        switch (inv.TargetMethod.Name)
                        {
                            case "Requires": case "Ensures": case "Invariant": case "Decreases": return; // (the contract; the loop heads)
                            case "Assert":
                            {
                                var term = SpecTerm(SpecArgument(inv), null, out var wf);
                                WellDefined(wf, inv.Arguments[0].Syntax, null);
                                Emit($"    assert {term};", At("CSV1004", inv.Syntax, $"assertion '{inv.Arguments[0].Syntax}'"));
                                return;
                            }
                            case "Assume":
                            {
                                var term = SpecTerm(SpecArgument(inv), null, out var wf);
                                WellDefined(wf, inv.Arguments[0].Syntax, null);
                                Emit($"    assume {term};");
                                return;
                            }
                            default: throw new NotTranslated("Spec." + inv.TargetMethod.Name);
                        }
                    case IInvocationOperation call:
                        Call(call);
                        return;
                    case ISimpleAssignmentOperation a:
                    {
                        var v = Expr(a.Value);
                        Assign(a.Target, v);
                        return;
                    }
                    case ICompoundAssignmentOperation ca:
                        Assign(ca.Target, Arith(ca.OperatorKind, Expr(ca.Target), Expr(ca.Value), ca.Type, ca.Syntax, ca.IsChecked));
                        return;
                    case IIncrementOrDecrementOperation id:
                        Assign(id.Target, Arith(id.Kind == OperationKind.Increment ? BinaryOperatorKind.Add : BinaryOperatorKind.Subtract, Expr(id.Target), "1", id.Type, id.Syntax, id.IsChecked));
                        return;
                    case IFlowCaptureOperation fc:
                        Emit($"    {Capture(fc.Id, fc.Value.Type)} := {Expr(fc.Value)};");
                        return;
                    default:
                        throw new NotTranslated(op.Kind.ToString());
                }
            }

            private void Assign(IOperation target, string value)
            {
                switch (target)
                {
                    case ILocalReferenceOperation l when InSubset(l.Local.Type):
                        Emit($"    {Declare(Local(l.Local), l.Local.Type)} := {value};");
                        return;
                    case IArrayElementReferenceOperation e:
                    {
                        var (map, a, i) = Element(e);
                        Writes.Add(map);
                        Emit($"    {map}[{a}][{i}] := {value};");
                        return;
                    }
                    case IParameterReferenceOperation: throw new NotTranslated("an assignment to a parameter");
                    default: throw new NotTranslated("an assignment to " + target.Kind);
                }
            }

            private void Branch(BasicBlock b)
            {
                var fall = b.FallThroughSuccessor;
                if (b.ConditionalSuccessor != null && InSpec(b.BranchValue?.Syntax))
                {
                    Emit($"    goto b{b.Ordinal}$then, b{b.Ordinal}$else;");
                    Emit($"  b{b.Ordinal}$then:");
                    Jump(b, b.ConditionalSuccessor.Destination);
                    Emit($"  b{b.Ordinal}$else:");
                    Jump(b, fall.Destination);
                    return;
                }
                if (b.ConditionalSuccessor != null)
                {
                    var c = Expr(b.BranchValue);
                    var cond = b.ConditionKind == ControlFlowConditionKind.WhenTrue ? c : $"!({c})";
                    // (each way through a block of its own, which assumes it: the targets stay plain, for loop heads)
                    Emit($"    goto b{b.Ordinal}$then, b{b.Ordinal}$else;");
                    Emit($"  b{b.Ordinal}$then:");
                    Emit($"    assume {cond};");
                    Jump(b, b.ConditionalSuccessor.Destination);
                    Emit($"  b{b.Ordinal}$else:");
                    Emit($"    assume !({cond});");
                    Goto(b, fall);
                    return;
                }
                if (fall?.Semantics == ControlFlowBranchSemantics.Return && b.BranchValue != null)
                    Emit($"    result := {Expr(b.BranchValue)};");
                else if (fall?.Semantics == ControlFlowBranchSemantics.Throw || fall?.Semantics == ControlFlowBranchSemantics.Rethrow)
                {
                    // (a path that throws need not meet the postcondition: it ends)
                    if (b.BranchValue != null) Expr(b.BranchValue);
                    Emit("    assume false;");
                    Emit("    return;");
                    return;
                }
                Goto(b, fall);
            }

            private void Goto(BasicBlock from, ControlFlowBranch to)
            {
                if (to?.Destination == null) { Emit("    assume false;"); Emit("    return;"); return; }
                Jump(from, to.Destination);
            }

            /// <summary>A return: the result checked not null, the postconditions well-defined and holding, here.</summary>
            private void Return(BasicBlock from)
            {
                {
                    var at = from.BranchValue?.Syntax.Parent as ReturnStatementSyntax as SyntaxNode ?? from.BranchValue?.Syntax ?? (SyntaxNode)(_decl as MethodDeclarationSyntax)?.Body?.CloseBraceToken.Parent ?? _decl;
                    // a result not null where it must not be; the postconditions well-defined here, in order, and holding
                    if (!_m.ReturnsVoid && IsArray(_m.ReturnType) && NotNullable(_m.ReturnType))
                        Emit("    assert result != null;", At("CSV1014", at, $"'{_m.Name}' might return null, but its return type '{_m.ReturnType}' is not nullable"));
                    var before = new List<string>();
                    foreach (var e in _contract.Ensures)
                    {
                        var term = SpecTerm(e.Expr, e.ResultParameter, out var wf);
                        WellDefined(wf, e.Syntax, before);
                        Emit($"    assert {term};", At("CSV1002", at, $"postcondition '{e.Syntax}' might not hold on this return path"));
                        before.Add(term);
                    }
                    Emit("    return;");
                }
            }

            /// <summary>To a block (not the exit): on a back edge, the loop's measure went down (and wasn't negative).</summary>
            private void Jump(BasicBlock from, BasicBlock to)
            {
                if (to.Kind == BasicBlockKind.Exit) { Return(from); return; }
                if (to.Ordinal <= from.Ordinal && _measures.TryGetValue(to.Ordinal, out var measure))
                {
                    var now = measure.Select(m => SpecTerm(m, null, out _)).ToList();
                    var then = Enumerable.Range(0, measure.Count).Select(k => $"m${to.Ordinal}${k}").ToList();
                    // (not assumed after: the loop's invariant is checked on this edge whether or not the measure went down)
                    Emit($"    assert {{:subsumption 0}} {Lexicographic(now, then)};", At("CSV1007", measure[0].Syntax.Parent?.Parent ?? measure[0].Syntax,
                        $"loop measure '{string.Join(", ", measure.Select(m => m.Syntax))}' might not decrease or might be negative"));
                }
                Emit($"    goto b{to.Ordinal};");
            }

            private string Declare(string name, ITypeSymbol type)
            {
                // (an integer variable is always in its type's range: where Boogie havocs it, at a loop head, too)
                var decl = IsIntegral(type) ? $"{name}: int where {InRange(name, type)}" : $"{name}: {TypeOf(type)}";
                if (!_locals.Contains(decl)) _locals.Add(decl);
                return name;
            }

            private string Capture(CaptureId id, ITypeSymbol type)
            {
                if (type == null || !InSubset(type)) throw new NotTranslated("a capture of " + type);
                return Declare("c$" + id.GetHashCode(), type);
            }

            // ------------------------------------------------------------------ expressions (run time)

            /// <summary>An array element as a place: its map, array and index, null and bounds checked.</summary>
            private (string map, string a, string i) Element(IArrayElementReferenceOperation e)
            {
                if (!IsArray(e.ArrayReference.Type) || e.Indices.Length != 1) throw new NotTranslated("an array element of " + e.ArrayReference.Type);
                var a = Expr(e.ArrayReference);
                var i = Expr(e.Indices[0]);
                Emit($"    assert {a} != null;", At("CSV1013", e.Syntax, $"'{e.ArrayReference.Syntax}' might be null in '{e.Syntax}'"));
                Emit($"    assert 0 <= {i} && {i} < len({a});", At("CSV1003", e.Syntax, $"index in '{e.Syntax}' might be out of range"));
                return (Elements(e.ArrayReference.Type), a, i);
            }

            private string Expr(IOperation e)
            {
                switch (e)
                {
                    case ILiteralOperation lit when lit.ConstantValue.HasValue:
                        return Constant(lit.ConstantValue.Value, lit.Type);
                    case { ConstantValue: { HasValue: true } cv } when Scalar(e.Type):
                        return Constant(cv.Value, e.Type);
                    case ILocalReferenceOperation l when InSubset(l.Local.Type): return Declare(Local(l.Local), l.Local.Type);
                    case IParameterReferenceOperation p when InSubset(p.Parameter.Type): return Local(p.Parameter);
                    case IFlowCaptureReferenceOperation r: return Capture(r.Id, r.Type);
                    case IParenthesizedOperation par: return Expr(par.Operand);
                    case IConversionOperation conv when conv.Conversion.IsIdentity || conv.IsImplicit && IsIntegral(conv.Type) && IsIntegral(conv.Operand.Type) && conv.Conversion.IsNumeric:
                        return Expr(conv.Operand);
                    case IConversionOperation conv when IsIntegral(conv.Type) && IsIntegral(conv.Operand.Type) && conv.Conversion.IsNumeric:
                        return Narrow(Expr(conv.Operand), conv);
                    case IUnaryOperation u when u.OperatorKind == UnaryOperatorKind.Not: return $"!({Expr(u.Operand)})";
                    case IUnaryOperation u when u.OperatorKind == UnaryOperatorKind.Plus: return Expr(u.Operand);
                    case IUnaryOperation u when u.OperatorKind == UnaryOperatorKind.Minus && IsIntegral(u.Type):
                        return Arith(BinaryOperatorKind.Subtract, "0", Expr(u.Operand), u.Type, u.Syntax, u.IsChecked);
                    case IBinaryOperation b when b.OperatorMethod == null && InSubset(b.LeftOperand.Type) && InSubset(b.RightOperand.Type):
                        return Binary(b);
                    case IBinaryOperation b when b.OperatorMethod == null && (b.OperatorKind is BinaryOperatorKind.Equals or BinaryOperatorKind.NotEquals) &&
                                                 (IsArray(b.LeftOperand.Type) || IsArray(b.RightOperand.Type)):
                        return Binary(b);
                    case IArrayElementReferenceOperation el:
                    {
                        var (map, a, i) = Element(el);
                        var v = $"{map}[{a}][{i}]";
                        return v;
                    }
                    case IPropertyReferenceOperation pr when pr.Property.Name == "Length" && IsArray(pr.Instance?.Type):
                    {
                        var a = Expr(pr.Instance);
                        Emit($"    assert {a} != null;", At("CSV1013", pr.Syntax, $"'{pr.Instance.Syntax}' might be null in '{pr.Syntax}'"));
                        return $"len({a})";
                    }
                    case IArrayCreationOperation ac when IsArray(ac.Type) && ac.DimensionSizes.Length == 1:
                        return NewArray(ac);
                    case IInvocationOperation call:
                        return Call(call);
                    default:
                        if (e.ConstantValue.HasValue && e.ConstantValue.Value == null && IsArray(e.Type)) return "null";
                        throw new NotTranslated(e.Kind + " '" + e.Syntax + "'");
                }
            }

            /// <summary>new T[n] (or with an initializer): a reference not allocated before, of length n, its elements the default or the initializer's.</summary>
            private string NewArray(IArrayCreationOperation ac)
            {
                var n = Expr(ac.DimensionSizes[0]);
                var t = Declare("t$" + _temps++, ac.Type);
                var map = Elements(ac.Type);
                Writes.Add("$Alloc");
                Writes.Add(map);
                // (a negative size throws: the path ends)
                Emit($"    assume {n} >= 0;");
                Emit($"    havoc {t};");
                Emit($"    assume {t} != null && !$Alloc[{t}] && len({t}) == {n};");
                Emit($"    $Alloc[{t}] := true;");
                Emit($"    {map}[{t}] := (lambda j: int :: {(map == ElementMap(SpecialType.System_Boolean) ? "false" : "0")});");
                if (ac.Initializer != null)
                    for (int k = 0; k < ac.Initializer.ElementValues.Length; k++)
                        Emit($"    {map}[{t}][{k}] := {Expr(ac.Initializer.ElementValues[k])};");
                return t;
            }

            private static string Constant(object v, ITypeSymbol type)
            {
                if (v is bool x) return x ? "true" : "false";
                if (v == null && IsArray(type)) return "null";
                System.Numerics.BigInteger n;
                switch (v)
                {
                    case char c: n = c; break;
                    case sbyte b: n = b; break; case byte b: n = b; break;
                    case short h: n = h; break; case ushort h: n = h; break;
                    case int i: n = i; break; case uint i: n = i; break;
                    case long l: n = l; break; case ulong l: n = l; break;
                    default: throw new NotTranslated("a constant " + v);
                }
                var text = n.ToString(CultureInfo.InvariantCulture);
                return n < 0 ? $"({text})" : text;
            }

            private string Binary(IBinaryOperation b)
            {
                var l = Expr(b.LeftOperand);
                var r = Expr(b.RightOperand);
                switch (b.OperatorKind)
                {
                    case BinaryOperatorKind.Add: case BinaryOperatorKind.Subtract: case BinaryOperatorKind.Multiply:
                    case BinaryOperatorKind.Divide: case BinaryOperatorKind.Remainder:
                        return Arith(b.OperatorKind, l, r, b.Type, b.Syntax, b.IsChecked);
                    case BinaryOperatorKind.Equals: return $"({l} == {r})";
                    case BinaryOperatorKind.NotEquals: return $"({l} != {r})";
                    case BinaryOperatorKind.LessThan: return $"({l} < {r})";
                    case BinaryOperatorKind.LessThanOrEqual: return $"({l} <= {r})";
                    case BinaryOperatorKind.GreaterThan: return $"({l} > {r})";
                    case BinaryOperatorKind.GreaterThanOrEqual: return $"({l} >= {r})";
                    case BinaryOperatorKind.And when b.Type.SpecialType == SpecialType.System_Boolean:
                    case BinaryOperatorKind.ConditionalAnd: return $"({l} && {r})";
                    case BinaryOperatorKind.Or when b.Type.SpecialType == SpecialType.System_Boolean:
                    case BinaryOperatorKind.ConditionalOr: return $"({l} || {r})";
                    case BinaryOperatorKind.ExclusiveOr when b.Type.SpecialType == SpecialType.System_Boolean: return $"({l} != {r})";
                    default: throw new NotTranslated("the operator " + b.OperatorKind);
                }
            }

            /// <summary>
            /// An explicit conversion between integer types: as arithmetic, an obligation in the default context (CSV1010),
            /// the path's end in a checked one, wrap-around in an unchecked one; a widening one is the value.
            /// </summary>
            private string Narrow(string value, IConversionOperation conv)
            {
                var (lo, hi) = Range(conv.Type);
                var (flo, fhi) = Range(conv.Operand.Type);
                if (System.Numerics.BigInteger.Parse(flo) >= System.Numerics.BigInteger.Parse(lo) && System.Numerics.BigInteger.Parse(fhi) <= System.Numerics.BigInteger.Parse(hi)) return value;
                if (!conv.IsChecked && InUnchecked(conv.Syntax)) return Wrap(value, conv.Type);
                if (_ghost) return value;
                if (conv.IsChecked || !_t._checkOverflow) Emit($"    assume {InRange(value, conv.Type)};");
                else Emit($"    assert {InRange(value, conv.Type)};", At("CSV1010", conv.Syntax, $"conversion '{conv.Syntax}' might overflow {conv.Type.Name}"));
                return value;
            }

            private static bool InUnchecked(SyntaxNode at) =>
                at.AncestorsAndSelf().Select(n => n is CheckedExpressionSyntax ce ? ce.Kind() : n is CheckedStatementSyntax cs ? cs.Kind() : SyntaxKind.None)
                    .FirstOrDefault(k => k != SyntaxKind.None) is SyntaxKind.UncheckedExpression or SyntaxKind.UncheckedStatement;

            /// <summary>
            /// Integer arithmetic at run time: division by zero is an obligation; overflow is one in the default context,
            /// ends the path in a checked one (it throws), as MinValue / -1 does anywhere, and wraps around in an
            /// unchecked one (two's complement).
            /// </summary>
            private string Arith(BinaryOperatorKind k, string l, string r, ITypeSymbol type, SyntaxNode at, bool isChecked)
            {
                if (!IsIntegral(type)) throw new NotTranslated("arithmetic on " + type);
                bool wraps = !isChecked && InUnchecked(at);
                string value;
                switch (k)
                {
                    case BinaryOperatorKind.Add: value = $"({l} + {r})"; break;
                    case BinaryOperatorKind.Subtract: value = $"({l} - {r})"; break;
                    case BinaryOperatorKind.Multiply: value = $"({l} * {r})"; break;
                    case BinaryOperatorKind.Divide: case BinaryOperatorKind.Remainder:
                        Emit($"    assert {r} != 0;", At("CSV1009", at, $"division by zero in '{at}'"));
                        // (MinValue / -1 throws in .NET, checked or not)
                        var (lo, _) = Range(type);
                        Emit($"    assume !({l} == {lo} && {r} == -1);");
                        return k == BinaryOperatorKind.Divide ? $"cs#div({l}, {r})" : $"cs#rem({l}, {r})";
                    default: throw new NotTranslated("the operator " + k);
                }
                if (wraps) return Wrap(value, type);
                if (_ghost) return value;
                if (isChecked || !_t._checkOverflow) Emit($"    assume {InRange(value, type)};");
                else Emit($"    assert {InRange(value, type)};", At("CSV1010", at, $"arithmetic '{at}' might overflow {type.Name}"));
                return value;
            }

            private string Call(IInvocationOperation call)
            {
                var callee = call.TargetMethod.OriginalDefinition;
                if (!_t._procedures.Contains(callee)) throw new NotTranslated("a call of " + call.TargetMethod.Name);
                Calls.Add(callee);
                var args = new List<string>();
                foreach (var arg in call.Arguments.OrderBy(a => a.Parameter.Ordinal))
                {
                    var v = Expr(arg.Value);
                    if (IsArray(arg.Parameter.Type) && NotNullable(arg.Parameter.Type))
                        Emit($"    assert {v} != null;", At("CSV1014", arg.Value.Syntax, $"'{arg.Value.Syntax}' might be null, but parameter '{arg.Parameter.Name}' of '{callee.Name}' is not nullable"));
                    args.Add(v);
                }
                Termination(call, callee, args);
                var check = At("CSV1001", call.Syntax, $"'{call.Syntax}'");
                if (callee.ReturnsVoid)
                {
                    Emit($"    call {Name(callee)}({string.Join(", ", args)});", check);
                    return null;
                }
                var t = Declare("t$" + _temps++, callee.ReturnType);
                Emit($"    call {t} := {Name(callee)}({string.Join(", ", args)});", check);
                return t;
            }

            /// <summary>
            /// A call back into its own recursion group: the callee's measure, at the arguments, below the caller's,
            /// lexicographically (CSV1008). A [Pure] function or lemma that recurses without one doesn't terminate
            /// (CSV1011); an ordinary method needn't (partial correctness).
            /// </summary>
            private void Termination(IInvocationOperation call, IMethodSymbol callee, List<string> args)
            {
                if (!_t.Recursive(_m.OriginalDefinition, callee)) return;
                var theirs = _t.ContractOf(callee);
                if (_contract.Decreases != null && theirs?.Decreases != null)
                {
                    var mine = _contract.Decreases.Select(d => SpecTerm(d, null, out _)).ToList();
                    _subst = callee.Parameters.Select((p, k) => (p, k)).ToDictionary(x => (ISymbol)x.p, x => args[x.k], SymbolEqualityComparer.Default);
                    List<string> next;
                    try { next = theirs.Decreases.Select(d => SpecTerm(d, null, out _)).ToList(); }
                    finally { _subst = null; }
                    Emit($"    assert {Lexicographic(next, mine)};", At("CSV1008", call.Syntax,
                        $"cannot prove termination: measure '{string.Join(", ", theirs.Decreases.Select(d => d.Syntax))}' of '{callee.Name}' might not decrease or might be negative"));
                }
                else if (_contract.IsPure || _contract.IsLemma)
                    Emit("    assert false;", At("CSV1011", call.Syntax, $"recursive lemma or [Pure] function '{_m.Name}' needs Spec.Decreases"));
            }

            /// <summary>
            /// next below before, lexicographically, each part bounded below by 0 where it goes down (Dafny's rule: the
            /// part before isn't negative, the next is less, which is well-founded; the next may be negative).
            /// </summary>
            private static string Lexicographic(List<string> next, List<string> before)
            {
                int n = Math.Min(next.Count, before.Count);
                string Below(int k) => k == n - 1
                    ? $"(0 <= {before[k]} && {next[k]} < {before[k]})"
                    : $"((0 <= {before[k]} && {next[k]} < {before[k]}) || ({next[k]} == {before[k]} && {Below(k + 1)}))";
                return n == 0 ? "false" : Below(0);
            }

            // ------------------------------------------------------------------ specifications (mathematical)

            /// <summary>A specification as a Boogie formula, and what makes it well-defined (each a condition, in order).</summary>
            private string SpecTerm(IOperation e, IParameterSymbol result, out List<string> wf)
            {
                wf = new List<string>();
                return Spec(e, result, wf, new List<string>());
            }

            /// <summary>
            /// e as a formula; what makes it well-defined is added to <paramref name="wf"/>, under <paramref name="guard"/>
            /// (what && || ?: make hold where it is evaluated, and the bounds of the quantifiers around it).
            /// </summary>
            private string Spec(IOperation e, IParameterSymbol result, List<string> wf, List<string> guard)
            {
                void Need(string cond) => wf.Add(guard.Count == 0 ? cond : $"(({string.Join(" && ", guard)}) ==> {cond})");
                string Under(string g, IOperation x)
                {
                    guard.Add(g);
                    try { return Spec(x, result, wf, guard); }
                    finally { guard.RemoveAt(guard.Count - 1); }
                }
                switch (e)
                {
                    case IDelegateCreationOperation d: return Spec(d.Target, result, wf, guard);
                    case IAnonymousFunctionOperation fn when fn.Body.Operations.Length == 1 && fn.Body.Operations[0] is IReturnOperation ret:
                        return Spec(ret.ReturnedValue, fn.Symbol.Parameters.FirstOrDefault() ?? result, wf, guard);
                    case { ConstantValue: { HasValue: true } cv } when Scalar(e.Type) || IsArray(e.Type): return Constant(cv.Value, e.Type);
                    case IParameterReferenceOperation p when result != null && SymbolEqualityComparer.Default.Equals(p.Parameter, result): return _resultName;
                    case IParameterReferenceOperation p when _subst != null && _subst.TryGetValue(p.Parameter, out var given): return given;
                    case IParameterReferenceOperation p when p.Parameter.ContainingSymbol is IMethodSymbol { MethodKind: MethodKind.AnonymousFunction }:
                        return "q$" + p.Parameter.Name; // (a quantifier's variable)
                    case IParameterReferenceOperation p when InSubset(p.Parameter.Type): return Local(p.Parameter);
                    case ILocalReferenceOperation l when InSubset(l.Local.Type): return Declare(Local(l.Local), l.Local.Type);
                    case IParenthesizedOperation par: return Spec(par.Operand, result, wf, guard);
                    case IConversionOperation conv when conv.Conversion.IsIdentity || IsIntegral(conv.Type) && IsIntegral(conv.Operand.Type) && conv.Conversion.IsNumeric && conv.IsImplicit:
                        return Spec(conv.Operand, result, wf, guard);
                    case IUnaryOperation u when u.OperatorKind == UnaryOperatorKind.Not: return $"!({Spec(u.Operand, result, wf, guard)})";
                    case IUnaryOperation u when u.OperatorKind == UnaryOperatorKind.Minus: return $"(0 - {Spec(u.Operand, result, wf, guard)})";
                    case IUnaryOperation u when u.OperatorKind == UnaryOperatorKind.Plus: return Spec(u.Operand, result, wf, guard);
                    case IConditionalOperation c when c.WhenFalse != null:
                    {
                        var cond = Spec(c.Condition, result, wf, guard);
                        return $"(if {cond} then {Under(cond, c.WhenTrue)} else {Under($"!({cond})", c.WhenFalse)})";
                    }
                    case IBinaryOperation b when b.OperatorMethod == null && b.OperatorKind is BinaryOperatorKind.ConditionalAnd or BinaryOperatorKind.ConditionalOr:
                    {
                        var l = Spec(b.LeftOperand, result, wf, guard);
                        // (the right only where the left lets it be evaluated)
                        var r = Under(b.OperatorKind == BinaryOperatorKind.ConditionalAnd ? l : $"!({l})", b.RightOperand);
                        return b.OperatorKind == BinaryOperatorKind.ConditionalAnd ? $"({l} && {r})" : $"({l} || {r})";
                    }
                    case IBinaryOperation b when b.OperatorMethod == null:
                    {
                        var l = Spec(b.LeftOperand, result, wf, guard);
                        var r = Spec(b.RightOperand, result, wf, guard);
                        if (b.OperatorKind is BinaryOperatorKind.Divide or BinaryOperatorKind.Remainder) Need($"({r} != 0)");
                        return b.OperatorKind switch
                        {
                            BinaryOperatorKind.Add => $"({l} + {r})",
                            BinaryOperatorKind.Subtract => $"({l} - {r})",
                            BinaryOperatorKind.Multiply => $"({l} * {r})",
                            BinaryOperatorKind.Divide => $"cs#div({l}, {r})",
                            BinaryOperatorKind.Remainder => $"cs#rem({l}, {r})",
                            BinaryOperatorKind.Equals => $"({l} == {r})",
                            BinaryOperatorKind.NotEquals => $"({l} != {r})",
                            BinaryOperatorKind.LessThan => $"({l} < {r})",
                            BinaryOperatorKind.LessThanOrEqual => $"({l} <= {r})",
                            BinaryOperatorKind.GreaterThan => $"({l} > {r})",
                            BinaryOperatorKind.GreaterThanOrEqual => $"({l} >= {r})",
                            BinaryOperatorKind.And => $"({l} && {r})",
                            BinaryOperatorKind.Or => $"({l} || {r})",
                            BinaryOperatorKind.ExclusiveOr => $"({l} != {r})",
                            _ => throw new NotTranslated("the operator " + b.OperatorKind),
                        };
                    }
                    case IArrayElementReferenceOperation el when IsArray(el.ArrayReference.Type) && el.Indices.Length == 1:
                    {
                        var a = Spec(el.ArrayReference, result, wf, guard);
                        var i = Spec(el.Indices[0], result, wf, guard);
                        Need($"({a} != null && 0 <= {i} && {i} < len({a}))");
                        return $"{Map(Elements(el.ArrayReference.Type))}[{a}][{i}]";
                    }
                    case IPropertyReferenceOperation pr when pr.Property.Name == "Length" && IsArray(pr.Instance?.Type):
                    {
                        var a = Spec(pr.Instance, result, wf, guard);
                        Need($"({a} != null)");
                        return $"len({a})";
                    }
                    case IInvocationOperation inv when SpecSymbols.IsSpecClass(inv.TargetMethod.ContainingType):
                        switch (inv.TargetMethod.Name)
                        {
                            case "Old": return $"old({Spec(inv.Arguments[0].Value, result, wf, guard)})";
                            case "Result": return _resultName;
                            case "Forall": case "Exists" when inv.Arguments.Length == 3:
                            {
                                var lo = Spec(inv.Arguments[0].Value, result, wf, guard);
                                var hi = Spec(inv.Arguments[1].Value, result, wf, guard);
                                var fn = (inv.Arguments[2].Value as IDelegateCreationOperation)?.Target as IAnonymousFunctionOperation
                                         ?? throw new NotTranslated("a quantifier without a lambda");
                                if (!(fn.Body.Operations.Length == 1 && fn.Body.Operations[0] is IReturnOperation ret)) throw new NotTranslated("a quantifier's body");
                                var q = "q$" + fn.Symbol.Parameters[0].Name;
                                var range = $"{lo} <= {q} && {q} < {hi}";
                                // (its body well-defined over the range: each condition quantified the same way)
                                var inner = new List<string>();
                                var body = Spec(ret.ReturnedValue, result, inner, new List<string> { range });
                                foreach (var c in inner) Need($"(forall {q}: int :: {c})");
                                return inv.TargetMethod.Name == "Forall" ? $"(forall {q}: int :: {range} ==> {body})" : $"(exists {q}: int :: {range} && {body})";
                            }
                            default: throw new NotTranslated("Spec." + inv.TargetMethod.Name + " in a specification");
                        }
                    case IInvocationOperation fn when _t.IsFunction(fn.TargetMethod):
                    {
                        var callee = fn.TargetMethod.OriginalDefinition;
                        var args = fn.Arguments.OrderBy(a => a.Parameter.Ordinal).Select(a => Spec(a.Value, result, wf, guard)).ToList();
                        // (well-defined where its precondition holds, at the arguments)
                        var theirs = _t.ContractOf(callee);
                        var saved = _subst;
                        _subst = callee.Parameters.Select((p, k) => (p, k)).ToDictionary(x => (ISymbol)x.p, x => args[x.k], SymbolEqualityComparer.Default);
                        try
                        {
                            foreach (var r in theirs.Requires)
                            {
                                var inner = new List<string>();
                                var pre = Spec(r, null, inner, new List<string>());
                                Need(pre);
                            }
                        }
                        finally { _subst = saved; }
                        return $"{FunctionName(callee)}({_layer}, {Maps}{string.Join("", args.Select(a => ", " + a))})";
                    }
                    default:
                        throw new NotTranslated("in a specification: " + e.Kind + " '" + e.Syntax + "'");
                }
            }
        }
    }
}
