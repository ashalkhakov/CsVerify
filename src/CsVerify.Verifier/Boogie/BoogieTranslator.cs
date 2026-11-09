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

        private static bool IsIntegral(ITypeSymbol t) => t?.SpecialType is SpecialType.System_Int32 or SpecialType.System_Int64;

        private static bool IsArray(ITypeSymbol t) => t is IArrayTypeSymbol a && a.IsSZArray && Scalar(a.ElementType);

        private static bool Scalar(ITypeSymbol t) => IsIntegral(t) || t?.SpecialType == SpecialType.System_Boolean;

        private static bool InSubset(ITypeSymbol t) => Scalar(t) || IsArray(t);

        /// <summary>Could this method be a procedure (before its body is looked at)?</summary>
        public static bool Candidate(IMethodSymbol m, Contract c) =>
            m.IsStatic && !m.IsAsync && !m.IsGenericMethod && m.MethodKind == MethodKind.Ordinary &&
            (m.ReturnsVoid || InSubset(m.ReturnType)) && m.Parameters.All(p => p.RefKind == RefKind.None && InSubset(p.Type)) &&
            c.Decreases == null && c.Modifies == null && c.Reads == null && c.ThrowEnsures.Count == 0 && !c.IsLemma && !c.IsPure && !c.IsTrusted &&
            c.Ensures.All(e => e.Guard == null) && c.Bases.Count == 0;

        /// <summary>The procedures in the program (each candidate whose body translates): calls of them are calls.</summary>
        public void Declare(IEnumerable<IMethodSymbol> procedures)
        {
            foreach (var p in procedures) _procedures.Add(p.OriginalDefinition);
        }

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
        private static string Elements(ITypeSymbol array) => ((IArrayTypeSymbol)array).ElementType.SpecialType switch
        {
            SpecialType.System_Int32 => "$I32",
            SpecialType.System_Int64 => "$I64",
            _ => "$B",
        };

        private static (string lo, string hi) Range(ITypeSymbol t) => t.SpecialType == SpecialType.System_Int64
            ? (long.MinValue.ToString(CultureInfo.InvariantCulture), long.MaxValue.ToString(CultureInfo.InvariantCulture))
            : (int.MinValue.ToString(CultureInfo.InvariantCulture), int.MaxValue.ToString(CultureInfo.InvariantCulture));

        private static string InRange(string e, ITypeSymbol t)
        {
            var (lo, hi) = Range(t);
            return $"({lo} <= {e} && {e} <= {hi})";
        }

        private static readonly string[] Heap = { "$Alloc", "$I32", "$I64", "$B" };

        /// <summary>What every program has: C#'s division, wrap-around, and the heap of arrays (Dafny's encoding).</summary>
        public void Prelude()
        {
            Line("// C#'s / and % truncate toward zero; Boogie's div and mod are Euclidean");
            Line("function cs#div(a: int, b: int): int { if a >= 0 then (if b > 0 then a div b else -(a div (-b))) else (if b > 0 then -((-a) div b) else (-a) div (-b)) }");
            Line("function cs#rem(a: int, b: int): int { a - b * cs#div(a, b) }");
            Line("// unchecked: two's complement wrap-around, as Euclidean mod");
            Line("function cs#wrap32(x: int): int { ((x + 2147483648) mod 4294967296) - 2147483648 }");
            Line("function cs#wrap64(x: int): int { ((x + 9223372036854775808) mod 18446744073709551616) - 9223372036854775808 }");
            Line("// arrays: references, the allocated ones, each one's length, and a map of elements per element type");
            Line("type Ref;");
            Line("const null: Ref;");
            Line("var $Alloc: [Ref]bool;");
            Line("function len(a: Ref): int;");
            Line("axiom (forall a: Ref :: 0 <= len(a) && len(a) <= 2147483647); // (an array's Length is an int)");
            Line("var $I32: [Ref][int]int;");
            Line("var $I64: [Ref][int]int;");
            Line("var $B: [Ref][int]bool;");
            Line("// what is read from memory is in its type's range");
            Line($"function $InRange(i32: [Ref][int]int, i64: [Ref][int]int): bool {{ (forall r: Ref, j: int :: {int.MinValue} <= i32[r][j] && i32[r][j] <= {int.MaxValue}) && " +
                 $"(forall r: Ref, j: int :: {long.MinValue} <= i64[r][j] && i64[r][j] <= {long.MaxValue}) }}");
        }

        // ------------------------------------------------------------------ a method

        /// <summary>The method as a procedure; throws <see cref="NotTranslated"/> for one outside the subset (then nothing is kept).</summary>
        public void Procedure(IMethodSymbol m, Contract contract, SyntaxNode decl, SemanticModel model, MethodResult result)
        {
            var body = new Body(this, m, contract, decl, model, result);
            body.Translate(); // (throws before anything is kept)
            _pending.Add(new Pending
            {
                Method = m.OriginalDefinition, Result = result, Header = body.Header, Body = body.Lines, Writes = body.Writes, Calls = body.Calls,
                Obligations = body.Header.Concat(body.Lines).Count(l => l.check != null && l.check.Id != Aux) + contract.Ensures.Count,
            });
        }

        /// <summary>Writes the procedures: each modifies what it writes, and what what it calls does.</summary>
        public void Finish()
        {
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

            public Body(BoogieTranslator t, IMethodSymbol m, Contract contract, SyntaxNode decl, SemanticModel model, MethodResult result)
            {
                _t = t; _m = m; _contract = contract; _decl = decl; _model = model; _result = result;
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
                Header.Add(("  free requires $InRange($I32, $I64);", null));
                Header.Add(("  free ensures $InRange($I32, $I64);", null));
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
                foreach (var e in _contract.Ensures)
                    Header.Add(($"  ensures {SpecTerm(e.Expr, e.ResultParameter, out _)};", At(Aux, e.Syntax, $"postcondition '{e.Syntax}'", "CSV1002")));
                if (!_m.ReturnsVoid && IsIntegral(_m.ReturnType)) Header.Add(($"  free ensures {InRange("result", _m.ReturnType)};", null));
                if (!_m.ReturnsVoid && IsArray(_m.ReturnType))
                {
                    Header.Add(("  free ensures result == null || $Alloc[result];", null));
                    if (NotNullable(_m.ReturnType))
                        Header.Add(("  ensures result != null;", At(Aux, _decl, $"'{_m.Name}' might return null, but its return type '{_m.ReturnType}' is not nullable", "CSV1014")));
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
            private Dictionary<int, List<IOperation>> Invariants(ControlFlowGraph cfg, HashSet<int> heads)
            {
                var at = new Dictionary<int, List<IOperation>>();
                foreach (var b in cfg.Blocks)
                    foreach (var op in b.Operations)
                        if (SpecCall(op, "Invariant") is IInvocationOperation inv)
                        {
                            var head = heads.Where(h => h <= b.Ordinal && cfg.Blocks.Any(x => x.Ordinal >= b.Ordinal &&
                                new[] { x.FallThroughSuccessor, x.ConditionalSuccessor }.Any(s => s?.Destination?.Ordinal == h))).DefaultIfEmpty(-1).Max();
                            if (head < 0) throw new NotTranslated("an invariant outside a loop");
                            if (!at.TryGetValue(head, out var list)) at[head] = list = new List<IOperation>();
                            list.Add(SpecArgument(inv));
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
                            case "Requires": case "Ensures": case "Invariant": return; // (the contract; the loop heads)
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
                    Emit($"    goto b{b.ConditionalSuccessor.Destination.Ordinal}, b{fall.Destination.Ordinal};");
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
                    Emit($"    goto b{b.ConditionalSuccessor.Destination.Ordinal};");
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
                if (to.Destination.Kind == BasicBlockKind.Exit)
                {
                    var at = from.BranchValue?.Syntax.Parent as ReturnStatementSyntax as SyntaxNode ?? from.BranchValue?.Syntax ?? (SyntaxNode)(_decl as MethodDeclarationSyntax)?.Body?.CloseBraceToken.Parent ?? _decl;
                    // the postconditions well-defined here, in order
                    var before = new List<string>();
                    foreach (var e in _contract.Ensures)
                    {
                        var term = SpecTerm(e.Expr, e.ResultParameter, out var wf);
                        WellDefined(wf, e.Syntax, before);
                        before.Add(term);
                    }
                    Emit("    return;", At(Aux, at, "return"));
                    return;
                }
                Emit($"    goto b{to.Destination.Ordinal};");
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
                    case IConversionOperation conv when conv.IsImplicit && IsIntegral(conv.Type) && IsIntegral(conv.Operand.Type) || conv.Conversion.IsIdentity:
                        return Expr(conv.Operand);
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
                Emit($"    {map}[{t}] := (lambda j: int :: {(map == "$B" ? "false" : "0")});");
                if (ac.Initializer != null)
                    for (int k = 0; k < ac.Initializer.ElementValues.Length; k++)
                        Emit($"    {map}[{t}][{k}] := {Expr(ac.Initializer.ElementValues[k])};");
                return t;
            }

            private static string Constant(object v, ITypeSymbol type) => v switch
            {
                bool x => x ? "true" : "false",
                int x => x < 0 ? $"({x.ToString(CultureInfo.InvariantCulture)})" : x.ToString(CultureInfo.InvariantCulture),
                long x => x < 0 ? $"({x.ToString(CultureInfo.InvariantCulture)})" : x.ToString(CultureInfo.InvariantCulture),
                null when IsArray(type) => "null",
                _ => throw new NotTranslated("a constant " + v),
            };

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
                if (wraps) return type.SpecialType == SpecialType.System_Int64 ? $"cs#wrap64({value})" : $"cs#wrap32({value})";
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
                    case IParameterReferenceOperation p when result != null && SymbolEqualityComparer.Default.Equals(p.Parameter, result): return "result";
                    case IParameterReferenceOperation p when p.Parameter.ContainingSymbol is IMethodSymbol { MethodKind: MethodKind.AnonymousFunction }:
                        return "q$" + p.Parameter.Name; // (a quantifier's variable)
                    case IParameterReferenceOperation p when InSubset(p.Parameter.Type): return Local(p.Parameter);
                    case ILocalReferenceOperation l when InSubset(l.Local.Type): return Declare(Local(l.Local), l.Local.Type);
                    case IParenthesizedOperation par: return Spec(par.Operand, result, wf, guard);
                    case IConversionOperation conv when IsIntegral(conv.Type) && IsIntegral(conv.Operand.Type) || conv.Conversion.IsIdentity: return Spec(conv.Operand, result, wf, guard);
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
                        return $"{Elements(el.ArrayReference.Type)}[{a}][{i}]";
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
                            case "Result": return "result";
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
                    default:
                        throw new NotTranslated("in a specification: " + e.Kind + " '" + e.Syntax + "'");
                }
            }
        }
    }
}
