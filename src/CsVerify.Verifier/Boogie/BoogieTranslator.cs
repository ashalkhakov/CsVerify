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
    /// The subset so far: static methods of int, long and bool (parameters, locals, the result), arithmetic and
    /// comparisons, if and loops (with Spec.Invariant), calls of each other, Spec.Assert and Spec.Assume. Integers
    /// follow docs/semantics.md: overflow is an obligation in the default context and ends the path in a checked one,
    /// division truncates as C#'s does, and specifications are mathematical.
    /// </summary>
    internal sealed class BoogieTranslator
    {
        private readonly StringBuilder _text = new StringBuilder();
        private int _line = 1;

        /// <summary>The check each line of the program is (1-based, as Boogie reports).</summary>
        public readonly Dictionary<int, Check> Lines = new Dictionary<int, Check>();

        /// <summary>How many obligations each procedure has (its asserts, preconditions of its calls, its postconditions).</summary>
        public readonly Dictionary<MethodResult, int> Obligations = new Dictionary<MethodResult, int>();

        /// <summary>A line that says what a failure is about (a requires, an ensures, a return), not a check of its own.</summary>
        internal const string Aux = "aux";

        private readonly HashSet<IMethodSymbol> _procedures = new HashSet<IMethodSymbol>(SymbolEqualityComparer.Default);
        private readonly bool _checkOverflow;

        public BoogieTranslator(bool checkOverflow) { _checkOverflow = checkOverflow; }

        public string Text => _text.ToString();

        // ------------------------------------------------------------------ the subset

        private static bool IsIntegral(ITypeSymbol t) => t?.SpecialType is SpecialType.System_Int32 or SpecialType.System_Int64;

        private static bool InSubset(ITypeSymbol t) => IsIntegral(t) || t?.SpecialType == SpecialType.System_Boolean;

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
            Ident(m.ContainingType.ToDisplayString() + "." + m.Name + "$" + string.Join("$", m.Parameters.Select(p => p.Type.Name)));

        private static string Ident(string s)
        {
            var b = new StringBuilder();
            foreach (var ch in s) b.Append(char.IsLetterOrDigit(ch) || ch == '_' || ch == '.' || ch == '$' ? ch : '_');
            return b.ToString();
        }

        private static string Local(ISymbol s) => s is IParameterSymbol p ? "p$" + p.Name : "l$" + s.Name + "$" + s.Locations.FirstOrDefault()?.SourceSpan.Start;

        private static string TypeOf(ITypeSymbol t) => t.SpecialType == SpecialType.System_Boolean ? "bool" : "int";

        private static (string lo, string hi) Range(ITypeSymbol t) => t.SpecialType == SpecialType.System_Int64
            ? (long.MinValue.ToString(CultureInfo.InvariantCulture), long.MaxValue.ToString(CultureInfo.InvariantCulture))
            : (int.MinValue.ToString(CultureInfo.InvariantCulture), int.MaxValue.ToString(CultureInfo.InvariantCulture));

        private static string InRange(string e, ITypeSymbol t)
        {
            var (lo, hi) = Range(t);
            return $"({lo} <= {e} && {e} <= {hi})";
        }

        /// <summary>The definitions every program has: C#'s truncating division and remainder.</summary>
        public void Prelude()
        {
            Line("// C#'s / and % truncate toward zero; Boogie's div and mod are Euclidean");
            Line("function cs#div(a: int, b: int): int { if a >= 0 then (if b > 0 then a div b else -(a div (-b))) else (if b > 0 then -((-a) div b) else (-a) div (-b)) }");
            Line("function cs#rem(a: int, b: int): int { a - b * cs#div(a, b) }");
        }

        // ------------------------------------------------------------------ a method

        /// <summary>The method as a procedure; throws <see cref="NotTranslated"/> for one outside the subset (then nothing is written).</summary>
        public void Procedure(IMethodSymbol m, Contract contract, SyntaxNode decl, SemanticModel model, MethodResult result)
        {
            var body = new Body(this, m, contract, decl, model, result);
            var lines = body.Translate(); // (throws before anything is written)
            foreach (var (text, check) in lines) Line(text, check);
            // (each assert and each call's precondition, and each postcondition)
            Obligations[result] = lines.Count(l => l.check != null && l.check.Id != Aux) + contract.Ensures.Count;
        }

        private sealed class Body
        {
            private readonly BoogieTranslator _t;
            private readonly IMethodSymbol _m;
            private readonly Contract _contract;
            private readonly SyntaxNode _decl;
            private readonly SemanticModel _model;
            private readonly MethodResult _result;
            private readonly List<(string text, Check check)> _out = new List<(string, Check)>();
            private readonly List<string> _locals = new List<string>();
            private int _temps;

            public Body(BoogieTranslator t, IMethodSymbol m, Contract contract, SyntaxNode decl, SemanticModel model, MethodResult result)
            {
                _t = t; _m = m; _contract = contract; _decl = decl; _model = model; _result = result;
            }

            private Check At(string id, SyntaxNode at, string message) =>
                new Check { Id = id, Message = message, Span = at.GetLocation().GetLineSpan(), Method = _result };

            private void Emit(string text, Check check = null) => _out.Add((text, check));

            public List<(string text, Check check)> Translate()
            {
                if (!(_model.GetOperation(_decl) is IMethodBodyOperation bodyOp)) throw new NotTranslated("no body");
                var cfg = ControlFlowGraph.Create(bodyOp);
                // the header: parameters, result, contract
                var ps = string.Join(", ", _m.Parameters.Select(p => $"{Local(p)}: {TypeOf(p.Type)}"));
                var ret = _m.ReturnsVoid ? "" : $" returns (result: {TypeOf(_m.ReturnType)})";
                var header = new List<(string, Check)> { ($"procedure {Name(_m)}({ps}){ret}", null) };
                foreach (var p in _m.Parameters.Where(p => IsIntegral(p.Type))) header.Add(($"  free requires {InRange(Local(p), p.Type)};", null));
                foreach (var r in _contract.Requires)
                    header.Add(($"  requires {Spec(r)};", At(Aux, r.Syntax, $"precondition '{r.Syntax}' of '{_m.Name}'")));
                foreach (var e in _contract.Ensures)
                    header.Add(($"  ensures {Spec(e.Expr, e.ResultParameter)};", At(Aux, e.Syntax, $"postcondition '{e.Syntax}'")));
                if (!_m.ReturnsVoid && IsIntegral(_m.ReturnType)) header.Add(($"  free ensures {InRange("result", _m.ReturnType)};", null));
                header.Add(("{", null));
                // the body: each block, its operations, then where it goes
                var loopHeads = LoopHeads(cfg);
                var invariants = Invariants(cfg, loopHeads);
                var blocks = new List<(string, Check)>();
                foreach (var b in cfg.Blocks)
                {
                    _out.Clear();
                    Emit($"  b{b.Ordinal}:");
                    if (invariants.TryGetValue(b.Ordinal, out var invs))
                        foreach (var inv in invs)
                            Emit($"    assert {Spec(inv)};", At("CSV1005", inv.Syntax, $"loop invariant '{inv.Syntax}'"));
                    if (b.Kind == BasicBlockKind.Exit) { Emit("    return;"); blocks.AddRange(_out); continue; }
                    foreach (var op in b.Operations) Statement(op);
                    Branch(b);
                    blocks.AddRange(_out);
                }
                header.AddRange(_locals.Select(l => ((string)$"  var {l};", (Check)null)));
                header.AddRange(blocks);
                header.Add(("}", null));
                if (cfg.Root.NestedRegions.Any(r => r.Kind != ControlFlowRegionKind.LocalLifetime) ||
                    cfg.Root.NestedRegions.SelectMany(AllRegions).Any(r => r.Kind != ControlFlowRegionKind.LocalLifetime))
                    throw new NotTranslated("try, catch or finally");
                return header;
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
                            // the innermost loop: the latest head before this block whose back edge comes from this block or after it
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

            private void Statement(IOperation op)
            {
                if (op is IExpressionStatementOperation es) op = es.Operation;
                switch (op)
                {
                    case IInvocationOperation inv when SpecSymbols.IsSpecClass(inv.TargetMethod.ContainingType):
                        switch (inv.TargetMethod.Name)
                        {
                            case "Requires": case "Ensures": case "Invariant": return; // (the contract; the loop heads)
                            case "Assert":
                                Emit($"    assert {Spec(SpecArgument(inv))};", At("CSV1004", inv.Syntax, $"assertion '{inv.Arguments[0].Syntax}'"));
                                return;
                            case "Assume":
                                Emit($"    assume {Spec(SpecArgument(inv))};");
                                return;
                            default: throw new NotTranslated("Spec." + inv.TargetMethod.Name);
                        }
                    case IInvocationOperation call:
                        Call(call, discard: true);
                        return;
                    case ISimpleAssignmentOperation a:
                        Emit($"    {Target(a.Target)} := {Expr(a.Value)};");
                        return;
                    case ICompoundAssignmentOperation ca:
                        Emit($"    {Target(ca.Target)} := {Arith(ca.OperatorKind, Expr(ca.Target), Expr(ca.Value), ca.Type, ca.Syntax, ca.IsChecked)};");
                        return;
                    case IIncrementOrDecrementOperation id:
                        Emit($"    {Target(id.Target)} := {Arith(id.Kind == OperationKind.Increment ? BinaryOperatorKind.Add : BinaryOperatorKind.Subtract, Expr(id.Target), "1", id.Type, id.Syntax, id.IsChecked)};");
                        return;
                    case IFlowCaptureOperation fc:
                        Emit($"    {Capture(fc.Id, fc.Value.Type)} := {Expr(fc.Value)};");
                        return;
                    default:
                        throw new NotTranslated(op.Kind.ToString());
                }
            }

            private void Branch(BasicBlock b)
            {
                var fall = b.FallThroughSuccessor;
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
                    Emit("    return;", At(Aux, at, "return"));
                    return;
                }
                Emit($"    goto b{to.Destination.Ordinal};");
            }

            private string Target(IOperation t)
            {
                switch (t)
                {
                    case ILocalReferenceOperation l when InSubset(l.Local.Type): return Declare(Local(l.Local), l.Local.Type);
                    case IParameterReferenceOperation p: throw new NotTranslated("an assignment to a parameter");
                    default: throw new NotTranslated("an assignment to " + t.Kind);
                }
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

            private string Expr(IOperation e)
            {
                switch (e)
                {
                    case ILiteralOperation lit when lit.ConstantValue.HasValue:
                        return Constant(lit.ConstantValue.Value);
                    case { ConstantValue: { HasValue: true } cv } when InSubset(e.Type):
                        return Constant(cv.Value);
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
                    case IInvocationOperation call:
                        return Call(call, discard: false);
                    default:
                        throw new NotTranslated(e.Kind + " '" + e.Syntax + "'");
                }
            }

            private static string Constant(object v) => v switch
            {
                bool x => x ? "true" : "false",
                int x => x < 0 ? $"({x.ToString(CultureInfo.InvariantCulture)})" : x.ToString(CultureInfo.InvariantCulture),
                long x => x < 0 ? $"({x.ToString(CultureInfo.InvariantCulture)})" : x.ToString(CultureInfo.InvariantCulture),
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

            /// <summary>
            /// Integer arithmetic at run time: division by zero is an obligation; overflow is one in the default context
            /// and ends the path in a checked one (it throws), as MinValue / -1 does anywhere. An unchecked context
            /// (modular arithmetic) isn't translated yet.
            /// </summary>
            private string Arith(BinaryOperatorKind k, string l, string r, ITypeSymbol type, SyntaxNode at, bool isChecked)
            {
                if (!IsIntegral(type)) throw new NotTranslated("arithmetic on " + type);
                if (!isChecked && at.AncestorsAndSelf().Any(n => n is CheckedExpressionSyntax ce && ce.IsKind(SyntaxKind.UncheckedExpression) ||
                                                               n is CheckedStatementSyntax cs && cs.IsKind(SyntaxKind.UncheckedStatement)))
                    throw new NotTranslated("unchecked arithmetic");
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
                        value = k == BinaryOperatorKind.Divide ? $"cs#div({l}, {r})" : $"cs#rem({l}, {r})";
                        return value;
                    default: throw new NotTranslated("the operator " + k);
                }
                if (isChecked || !_t._checkOverflow) Emit($"    assume {InRange(value, type)};");
                else Emit($"    assert {InRange(value, type)};", At("CSV1010", at, $"arithmetic '{at}' might overflow {type.Name}"));
                return value;
            }

            private string Call(IInvocationOperation call, bool discard)
            {
                var callee = call.TargetMethod.OriginalDefinition;
                if (!_t._procedures.Contains(callee)) throw new NotTranslated("a call of " + call.TargetMethod.Name);
                var args = call.Arguments.OrderBy(a => a.Parameter.Ordinal).Select(a => Expr(a.Value)).ToList();
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

            private string Spec(IOperation e, IParameterSymbol result = null)
            {
                switch (e)
                {
                    case IDelegateCreationOperation d: return Spec(d.Target, result);
                    case IAnonymousFunctionOperation fn when fn.Body.Operations.Length == 1 && fn.Body.Operations[0] is IReturnOperation ret:
                        return Spec(ret.ReturnedValue, fn.Symbol.Parameters.FirstOrDefault() ?? result);
                    case { ConstantValue: { HasValue: true } cv } when InSubset(e.Type): return Constant(cv.Value);
                    case IParameterReferenceOperation p when result != null && SymbolEqualityComparer.Default.Equals(p.Parameter, result): return "result";
                    case IParameterReferenceOperation p when InSubset(p.Parameter.Type): return Local(p.Parameter);
                    case ILocalReferenceOperation l when InSubset(l.Local.Type): return Declare(Local(l.Local), l.Local.Type);
                    case IParenthesizedOperation par: return Spec(par.Operand, result);
                    case IConversionOperation conv when IsIntegral(conv.Type) && IsIntegral(conv.Operand.Type) || conv.Conversion.IsIdentity: return Spec(conv.Operand, result);
                    case IUnaryOperation u when u.OperatorKind == UnaryOperatorKind.Not: return $"!({Spec(u.Operand, result)})";
                    case IUnaryOperation u when u.OperatorKind == UnaryOperatorKind.Minus: return $"(0 - {Spec(u.Operand, result)})";
                    case IUnaryOperation u when u.OperatorKind == UnaryOperatorKind.Plus: return Spec(u.Operand, result);
                    case IConditionalOperation c when c.WhenFalse != null:
                        return $"(if {Spec(c.Condition, result)} then {Spec(c.WhenTrue, result)} else {Spec(c.WhenFalse, result)})";
                    case IBinaryOperation b when b.OperatorMethod == null:
                    {
                        var l = Spec(b.LeftOperand, result);
                        var r = Spec(b.RightOperand, result);
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
                            BinaryOperatorKind.ConditionalAnd or BinaryOperatorKind.And => $"({l} && {r})",
                            BinaryOperatorKind.ConditionalOr or BinaryOperatorKind.Or => $"({l} || {r})",
                            BinaryOperatorKind.ExclusiveOr => $"({l} != {r})",
                            _ => throw new NotTranslated("the operator " + b.OperatorKind),
                        };
                    }
                    case IInvocationOperation inv when SpecSymbols.IsSpecClass(inv.TargetMethod.ContainingType) && inv.TargetMethod.Name == "Old":
                        return $"old({Spec(inv.Arguments[0].Value, result)})";
                    case IInvocationOperation inv when SpecSymbols.IsSpecClass(inv.TargetMethod.ContainingType) && inv.TargetMethod.Name == "Result":
                        return "result";
                    default:
                        throw new NotTranslated("in a specification: " + e.Kind + " '" + e.Syntax + "'");
                }
            }
        }
    }
}
