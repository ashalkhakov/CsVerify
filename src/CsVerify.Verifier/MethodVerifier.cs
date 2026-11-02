using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.FlowAnalysis;
using Microsoft.CodeAnalysis.Operations;
using Microsoft.CodeAnalysis.Text;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Verifies one method: symbolic execution over its Roslyn control flow graph, a forward computation of the
    /// weakest-precondition verification conditions. Every proof obligation (callee precondition, array bound,
    /// assertion, invariant, termination measure, postcondition) becomes the query "path condition and not goal",
    /// which Z3 must find unsatisfiable. Loops are cut at their head with Spec.Invariant; calls are modular.
    /// </summary>
    internal sealed class MethodVerifier
    {
        private sealed class Loop
        {
            public int Id, Head;
            public SyntaxNode Syntax;
            public List<IOperation> Invariants = new List<IOperation>();
            public IReadOnlyList<IOperation> Decreases;
            public HashSet<ISymbol> Havoc = new HashSet<ISymbol>(SymbolEqualityComparer.Default);
            public HashSet<ISymbol> HavocArrays = new HashSet<ISymbol>(SymbolEqualityComparer.Default);
            public bool HavocHeap;
        }

        private readonly Engine _engine;
        private readonly SmtSolver _z3;
        private readonly Contract _contract;
        private readonly IMethodSymbol _method;
        private readonly SemanticModel _model;
        private readonly MethodResult _result;
        private readonly Dictionary<int, Loop> _loops = new Dictionary<int, Loop>();
        private readonly HashSet<SyntaxNode> _loopSpecStatements = new HashSet<SyntaxNode>();
        private readonly HashSet<SyntaxNode> _contractStatements = new HashSet<SyntaxNode>();
        private readonly HashSet<(string, TextSpan)> _reported = new HashSet<(string, TextSpan)>();
        private Frame _entry;
        private Term[] _entryMeasure;
        private int _paths, _unfoldDepth, _quantDepth;
        private readonly Stack<List<Term>> _quantFacts = new Stack<List<Term>>();

        /// <summary>Assumes a background fact, or inside a quantifier records it as a hypothesis of the quantifier's body.</summary>
        private void AssumeSide(Term fact)
        {
            if (_quantFacts.Count == 0) _z3.Assume(fact);
            else _quantFacts.Peek().Add(fact);
        }
        private bool _codeMode; // obligations are only generated for code, not for specification expressions

        public MethodVerifier(Engine engine, Contract contract, MethodResult result)
        {
            _engine = engine;
            _z3 = engine.Solver;
            _contract = contract;
            _method = contract.Method;
            _model = contract.Model;
            _result = result;
        }

        // ================================================================================== driver

        public void Run()
        {
            var body = _model.GetOperation(_contract.Declaration);
            ControlFlowGraph cfg;
            switch (body)
            {
                case IMethodBodyOperation mb: cfg = ControlFlowGraph.Create(mb); break;
                case IConstructorBodyOperation cb: cfg = ControlFlowGraph.Create(cb); break;
                default: return;
            }
            FindContractStatements();
            FindLoops(cfg);

            _z3.Push();
            try
            {
                var f = new Frame { Heap = _z3.Fresh("heap", Sort.Heap) };
                if (!_method.IsStatic) f.This = _z3.Fresh("this", Sort.Int);
                foreach (var p in _method.Parameters)
                    f.Vars[p] = FreshOf(p.Type, p.Name);
                _entry = f.Clone();
                var spec = new SpecEnv { Old = _entry };
                foreach (var req in _contract.Requires) _z3.Assume(AsBool(EvalSpec(req, f, spec)));
                if (_contract.Decreases != null) _entryMeasure = EvalMeasure(_contract.Decreases, f, spec);
                _entry = f.Clone();
                Exec(cfg.Blocks[0], f, new HashSet<int>());
            }
            finally { _z3.Pop(); }
        }

        private void FindContractStatements()
        {
            BlockSyntax block = (_contract.Declaration as BaseMethodDeclarationSyntax)?.Body;
            if (block == null) return;
            foreach (var s in block.Statements.OfType<ExpressionStatementSyntax>())
                if (s.Expression is InvocationExpressionSyntax inv && SpecName(inv) is string n && (n == "Requires" || n == "Ensures" || n == "Decreases"))
                    _contractStatements.Add(inv);
        }

        private string SpecName(InvocationExpressionSyntax inv) =>
            _model.GetSymbolInfo(inv).Symbol is IMethodSymbol m && SpecSymbols.IsSpecClass(m.ContainingType) ? m.Name : null;

        private void FindLoops(ControlFlowGraph cfg)
        {
            foreach (var stmt in _contract.Declaration.DescendantNodes().OfType<StatementSyntax>())
            {
                StatementSyntax loopBody; ExpressionSyntax cond;
                switch (stmt)
                {
                    case WhileStatementSyntax w: loopBody = w.Statement; cond = w.Condition; break;
                    case ForStatementSyntax fs: loopBody = fs.Statement; cond = fs.Condition; break;
                    case DoStatementSyntax d: loopBody = d.Statement; cond = null; break;
                    case CommonForEachStatementSyntax fe:
                        Warn(fe.ForEachKeyword, "foreach loops are not supported; the body is checked for one iteration only");
                        continue;
                    default: continue;
                }
                var loop = new Loop { Id = _loops.Count, Syntax = stmt };
                var span = cond != null ? cond.Span : loopBody.Span;
                var heads = cfg.Blocks.Where(b => b.Operations.Any(o => span.Contains(o.Syntax.Span)) ||
                                                  (b.BranchValue != null && span.Contains(b.BranchValue.Syntax.Span)));
                if (!heads.Any()) continue;
                loop.Head = heads.Min(b => b.Ordinal);

                var leading = loopBody is BlockSyntax bs ? bs.Statements : new SyntaxList<StatementSyntax>(loopBody);
                foreach (var s in leading)
                {
                    if (!(s is ExpressionStatementSyntax es && es.Expression is InvocationExpressionSyntax inv)) break;
                    var name = SpecName(inv);
                    if (name != "Invariant" && name != "Decreases") break;
                    var args = ((IInvocationOperation)_model.GetOperation(inv)).Arguments;
                    if (name == "Invariant") loop.Invariants.Add(args[0].Value); else loop.Decreases = args.Select(a => a.Value).ToList();
                    _loopSpecStatements.Add(inv);
                }
                CollectHavoc(stmt, loop);
                _loops[loop.Head] = loop;
            }
        }

        private void CollectHavoc(SyntaxNode loopSyntax, Loop loop)
        {
            void Target(ExpressionSyntax e)
            {
                switch (e)
                {
                    case IdentifierNameSyntax _:
                        var s = _model.GetSymbolInfo(e).Symbol;
                        if (s is ILocalSymbol || s is IParameterSymbol) loop.Havoc.Add(s);
                        break;
                    case ElementAccessExpressionSyntax ea when ea.Expression is IdentifierNameSyntax:
                        var a = _model.GetSymbolInfo(ea.Expression).Symbol;
                        if (a is ILocalSymbol || a is IParameterSymbol) loop.HavocArrays.Add(a); else loop.HavocHeap = true;
                        break;
                    case ParenthesizedExpressionSyntax p: Target(p.Expression); break;
                    case DeclarationExpressionSyntax _: break;
                    default: loop.HavocHeap = true; break;
                }
            }
            foreach (var n in loopSyntax.DescendantNodes(n => !(n is AnonymousFunctionExpressionSyntax)))
            {
                switch (n)
                {
                    case AssignmentExpressionSyntax asg: Target(asg.Left); break;
                    case PrefixUnaryExpressionSyntax pre when pre.IsKind(SyntaxKind.PreIncrementExpression) || pre.IsKind(SyntaxKind.PreDecrementExpression): Target(pre.Operand); break;
                    case PostfixUnaryExpressionSyntax post: Target(post.Operand); break;
                    case ArgumentSyntax arg when !arg.RefKindKeyword.IsKind(SyntaxKind.None) && !arg.RefKindKeyword.IsKind(SyntaxKind.InKeyword): Target(arg.Expression); break;
                    case InvocationExpressionSyntax inv when _model.GetSymbolInfo(inv).Symbol is IMethodSymbol m && HavocsHeap(m): loop.HavocHeap = true; break;
                }
            }
            foreach (var a in loop.HavocArrays) if (loop.Havoc.Contains(a)) loop.HavocHeap = true;
        }

        // ================================================================================== CFG walk

        private void Exec(BasicBlock block, Frame f, HashSet<int> onPath)
        {
            if (++_paths > _engine.Options.MaxPaths)
            {
                if (_paths == _engine.Options.MaxPaths + 1)
                    Warn(MethodLocationNode(), $"path limit ({_engine.Options.MaxPaths}) reached; the rest of '{_method.Name}' is not verified");
                return;
            }
            if (block.Kind == BasicBlockKind.Exit) { CheckPostconditions(f); return; }

            if (_loops.TryGetValue(block.Ordinal, out var loop))
            {
                if (f.ActiveLoops.Contains(loop.Id)) { LoopBackEdge(loop, f); return; }
                LoopEntry(loop, f);
            }
            else if (onPath.Contains(block.Ordinal))
            {
                Warn(block.Operations.FirstOrDefault()?.Syntax ?? MethodLocationNode(), "unstructured cycle (goto/foreach) is not supported; path cut");
                return;
            }

            onPath.Add(block.Ordinal);
            _codeMode = true;
            foreach (var op in block.Operations) ExecOperation(op, f);

            var fall = block.FallThroughSuccessor;
            var cond = block.ConditionalSuccessor;
            if (cond != null)
            {
                if (InSpec(block.BranchValue)) Follow(fall, f, onPath);
                else
                {
                    var c = AsBool(Eval(block.BranchValue, f));
                    var taken = block.ConditionKind == ControlFlowConditionKind.WhenTrue ? c : T.Not(c);
                    Branch(cond, f.Clone(), taken, onPath);
                    Branch(fall, f, T.Not(taken), onPath);
                }
            }
            else
            {
                if (block.BranchValue != null && !InSpec(block.BranchValue))
                {
                    var v = Eval(block.BranchValue, f);
                    if (fall?.Semantics == ControlFlowBranchSemantics.Return)
                    {
                        f.Result = v;
                        f.ReturnSyntax = block.BranchValue.Syntax.Parent is ReturnStatementSyntax rs ? rs : block.BranchValue.Syntax;
                    }
                }
                else if (fall?.Semantics == ControlFlowBranchSemantics.Return)
                    f.ReturnSyntax = block.Operations.LastOrDefault()?.Syntax;
                Follow(fall, f, onPath);
            }
            onPath.Remove(block.Ordinal);
        }

        private void Branch(ControlFlowBranch succ, Frame f, Term cond, HashSet<int> onPath)
        {
            _z3.Push();
            _z3.Assume(cond);
            if (_z3.Check(T.True) != "unsat") Follow(succ, f, onPath);
            _z3.Pop();
        }

        private void Follow(ControlFlowBranch succ, Frame f, HashSet<int> onPath)
        {
            if (succ?.Destination == null) return; // throw, rethrow, program termination: no normal exit on this path
            switch (succ.Semantics)
            {
                case ControlFlowBranchSemantics.Regular:
                case ControlFlowBranchSemantics.Return:
                    Exec(succ.Destination, f, onPath);
                    break;
                case ControlFlowBranchSemantics.StructuredExceptionHandling:
                    Warn(MethodLocationNode(), "try/finally is not supported; paths through finally are not verified");
                    break;
            }
        }

        private void LoopEntry(Loop loop, Frame f)
        {
            var spec = new SpecEnv { Old = _entry };
            foreach (var inv in loop.Invariants)
                Prove(AsBool(EvalSpec(inv, f, spec)), "CSV1005", inv.Syntax, $"loop invariant '{inv.Syntax}' might not hold on entry");

            foreach (var s in loop.Havoc)
                f.Vars[s] = FreshOf(TypeOf(s), s.Name);
            if (loop.HavocHeap) f.Heap = _z3.Fresh("heap", Sort.Heap);
            else
                foreach (var a in loop.HavocArrays)
                    f.Heap = T.Store(f.Heap, Read(f, a), _z3.Fresh(a.Name + "$elems", Sort.Row));
            foreach (var key in f.Captures.Keys.ToList()) f.Captures.Remove(key);

            foreach (var inv in loop.Invariants) _z3.Assume(AsBool(EvalSpec(inv, f, spec)));
            if (loop.Decreases != null) f.LoopMeasures[loop.Id] = EvalMeasure(loop.Decreases, f, spec);
            f.ActiveLoops.Add(loop.Id);
        }

        private void LoopBackEdge(Loop loop, Frame f)
        {
            var spec = new SpecEnv { Old = _entry };
            foreach (var inv in loop.Invariants)
                Prove(AsBool(EvalSpec(inv, f, spec)), "CSV1006", inv.Syntax, $"loop invariant '{inv.Syntax}' might not be maintained by the loop");
            if (loop.Decreases != null)
            {
                var before = f.LoopMeasures[loop.Id];
                var after = EvalMeasure(loop.Decreases, f, spec);
                Prove(LexDecreases(after, before), "CSV1007", loop.Decreases[0].Parent.Syntax,
                    $"loop measure '{MeasureText(loop.Decreases)}' might not decrease or might be negative");
            }
        }

        private void CheckPostconditions(Frame f)
        {
            var at = f.ReturnSyntax ?? MethodLocationNode();
            foreach (var post in _contract.Ensures)
            {
                var spec = new SpecEnv { Old = _entry, Result = f.Result, ResultParameter = post.ResultParameter };
                Prove(AsBool(EvalSpec(post.Expr, f, spec)), "CSV1002", at,
                    $"postcondition '{post.Syntax}' might not hold on this return path");
            }
        }

        private SyntaxNode MethodLocationNode() => _contract.Declaration;

        // ================================================================================== statements

        private bool InSpec(IOperation op) => op != null && SpecSymbols.EnclosingSpecCall(op.Syntax, _model) != null;

        private void ExecOperation(IOperation op, Frame f)
        {
            if (op is IExpressionStatementOperation es) op = es.Operation;
            var specCall = SpecSymbols.EnclosingSpecCall(op.Syntax, _model);
            if (specCall == null) { Eval(op, f); return; }
            if (op.Syntax != specCall) return; // a lowered piece of a specification argument: evaluated as a whole below
            if (_contractStatements.Contains(specCall) || _loopSpecStatements.Contains(specCall)) return;

            var inv = (IInvocationOperation)_model.GetOperation(specCall);
            var arg = inv.Arguments.Length > 0 ? inv.Arguments[0].Value : null;
            var spec = new SpecEnv { Old = _entry };
            switch (inv.TargetMethod.Name)
            {
                case "Assert":
                    Prove(AsBool(EvalSpec(arg, f, spec)), "CSV1004", specCall, $"assertion '{arg.Syntax}' might not hold");
                    break;
                case "Assume":
                    _z3.Assume(AsBool(EvalSpec(arg, f, spec)));
                    break;
                case "Invariant":
                case "Decreases":
                    Warn(specCall, $"Spec.{inv.TargetMethod.Name} must be a leading statement of a while/for/do loop body (or of the method body for Decreases); ignored");
                    break;
                default:
                    Warn(specCall, $"Spec.{inv.TargetMethod.Name} must be a top-level statement of the method body; ignored");
                    break;
            }
            _codeMode = true;
        }

        // ================================================================================== obligations

        private void Prove(Term goal, string id, SyntaxNode at, string message)
        {
            bool wasCode = _codeMode;
            _result.Obligations++;
            var r = _z3.Check(T.Not(goal));
            if (r == "unsat") _result.Proved++;
            else
            {
                if (r != "sat") message += $" (solver: {r})";
                Report(id, at, message, isError: true);
            }
            _z3.Assume(goal); // continue as if it held, so one failure does not cascade
            _codeMode = wasCode;
        }

        private void Report(string id, SyntaxNode at, string message, bool isError)
        {
            if (!_reported.Add((id, at.Span))) return;
            _result.Diagnostics.Add(new VerificationDiagnostic(id, isError, message, at.GetLocation().GetLineSpan()));
        }

        private void Warn(SyntaxNode at, string message) => Report("CSV1900", at, message, isError: false);
        private void Warn(SyntaxToken at, string message) => Warn(at.Parent, message);

        private void Unsupported(IOperation op)
        {
            Warn(op.Syntax, $"unsupported construct ({op.Kind}); treated as an unknown value");
        }

        // ================================================================================== values

        private static bool IsIntegral(ITypeSymbol t)
        {
            switch (t?.SpecialType)
            {
                case SpecialType.System_SByte: case SpecialType.System_Byte:
                case SpecialType.System_Int16: case SpecialType.System_UInt16:
                case SpecialType.System_Int32: case SpecialType.System_UInt32:
                case SpecialType.System_Int64: case SpecialType.System_UInt64:
                case SpecialType.System_Char:
                    return true;
                default:
                    return t?.TypeKind == TypeKind.Enum;
            }
        }

        private static (BigInteger lo, BigInteger hi) RangeOf(ITypeSymbol t)
        {
            switch (t.TypeKind == TypeKind.Enum ? ((INamedTypeSymbol)t).EnumUnderlyingType.SpecialType : t.SpecialType)
            {
                case SpecialType.System_SByte: return (sbyte.MinValue, sbyte.MaxValue);
                case SpecialType.System_Byte: return (byte.MinValue, byte.MaxValue);
                case SpecialType.System_Int16: return (short.MinValue, short.MaxValue);
                case SpecialType.System_UInt16: case SpecialType.System_Char: return (ushort.MinValue, ushort.MaxValue);
                case SpecialType.System_UInt32: return (uint.MinValue, uint.MaxValue);
                case SpecialType.System_Int64: return (long.MinValue, long.MaxValue);
                case SpecialType.System_UInt64: return (ulong.MinValue, ulong.MaxValue);
                default: return (int.MinValue, int.MaxValue);
            }
        }

        internal static Sort SortOf(ITypeSymbol t)
        {
            if (SpecSymbols.IsGhostType(t)) return SortOf(((INamedTypeSymbol)t).TypeArguments[0]);
            if (SpecSymbols.IsSeqType(t)) return Sort.Row;
            return t?.SpecialType == SpecialType.System_Boolean ? Sort.Bool : Sort.Int;
        }

        internal static bool IsSequence(ITypeSymbol t) =>
            t is IArrayTypeSymbol || t?.SpecialType == SpecialType.System_String ||
            (t is INamedTypeSymbol n && (n.OriginalDefinition.ToDisplayString() == "System.Span<T>" || n.OriginalDefinition.ToDisplayString() == "System.ReadOnlySpan<T>"));

        private static ITypeSymbol TypeOf(ISymbol s) => s is ILocalSymbol l ? l.Type : ((IParameterSymbol)s).Type;

        private Term FreshOf(ITypeSymbol type, string hint)
        {
            var t = _z3.Fresh(hint, SortOf(type));
            if (IsIntegral(type)) { var (lo, hi) = RangeOf(type); _z3.Assume(T.InRange(t, lo, hi)); }
            if (IsSequence(type)) Len(t);
            return t;
        }

        private Term Len(Term seq)
        {
            var len = _z3.Apply("length", Sort.Int, new[] { seq });
            AssumeSide(T.InRange(len, 0, int.MaxValue));
            return len;
        }

        private Term Read(Frame f, ISymbol s)
        {
            if (f.Vars.TryGetValue(s, out var t)) return t;
            t = FreshOf(TypeOf(s), s.Name);
            f.Vars[s] = t;
            return t;
        }

        private Term Unknown(ITypeSymbol type, string hint = "unknown") => FreshOf(type, hint);

        private static Term AsBool(Term t) => T.Coerce(t, Sort.Bool);

        private Term EvalSpec(IOperation op, Frame f, SpecEnv spec)
        {
            bool wasCode = _codeMode;
            _codeMode = false;
            try { return Eval(op, f, spec); }
            finally { _codeMode = wasCode; }
        }

        private Term Eval(IOperation op, Frame f, SpecEnv spec = null)
        {
            if (op == null) return _z3.Fresh("missing", Sort.Int);
            if (op.ConstantValue.HasValue && !(op is IAssignmentOperation))
            {
                switch (op.ConstantValue.Value)
                {
                    case bool b: return T.Bool(b);
                    case char c: return T.Int(c);
                    case null: return T.Int(0);
                    case ulong ul: return T.Int(new BigInteger(ul));
                    case object o when IsIntegral(op.Type) || o is int || o is long: return T.Int(Convert.ToInt64(o));
                }
            }
            switch (op)
            {
                case IConversionOperation c: return EvalConversion(c, f, spec);
                case ILocalReferenceOperation l: return Read(f, l.Local);
                case IParameterReferenceOperation p:
                    if (spec?.ResultParameter != null && SymbolEqualityComparer.Default.Equals(p.Parameter, spec.ResultParameter))
                        return spec.Result ?? Unknown(p.Type, "result");
                    return Read(f, p.Parameter);
                case IInstanceReferenceOperation _: return f.This ?? (f.This = _z3.Fresh("this", Sort.Int));
                case IFlowCaptureReferenceOperation r: return f.Captures.TryGetValue(r.Id, out var cv) ? cv : Unknown(r.Type, "capture");
                case IFlowCaptureOperation fc: return f.Captures[fc.Id] = Eval(fc.Value, f, spec);
                case IBinaryOperation b: return EvalBinary(b, f, spec);
                case IUnaryOperation u: return EvalUnary(u, f, spec);
                case IConditionalOperation cond when cond.WhenFalse != null:
                    return T.Ite(AsBool(Eval(cond.Condition, f, spec)), Eval(cond.WhenTrue, f, spec), Eval(cond.WhenFalse, f, spec));
                case ISimpleAssignmentOperation a:
                {
                    var v = T.Coerce(Eval(a.Value, f, spec), SortOf(a.Target.Type));
                    Write(a.Target, v, f, spec);
                    return v;
                }
                case IDeconstructionAssignmentOperation da:
                {
                    var v = Eval(da.Value, f, spec);
                    Deconstruct(da.Target, v, f, spec);
                    return v;
                }
                case ICompoundAssignmentOperation ca:
                {
                    var old = Eval(ca.Target, f, spec);
                    var v = Arith(ca.OperatorKind, old, Eval(ca.Value, f, spec), ca.Type, ca.Syntax, ca.OperatorMethod != null);
                    Write(ca.Target, v, f, spec);
                    return v;
                }
                case IIncrementOrDecrementOperation inc:
                {
                    var old = Eval(inc.Target, f, spec);
                    var kind = inc.Kind == OperationKind.Increment ? BinaryOperatorKind.Add : BinaryOperatorKind.Subtract;
                    var v = Arith(kind, old, T.Int(1), inc.Type, inc.Syntax, inc.OperatorMethod != null);
                    Write(inc.Target, v, f, spec);
                    return inc.IsPostfix ? old : v;
                }
                case IArrayElementReferenceOperation ae:
                {
                    if (ae.Indices.Length != 1) { Unsupported(op); return Unknown(op.Type); }
                    var arr = Eval(ae.ArrayReference, f, spec);
                    var idx = Eval(ae.Indices[0], f, spec);
                    BoundsCheck(arr, idx, ae.Syntax);
                    return T.Coerce(T.Select(T.Select(f.Heap, arr, Sort.Row), idx, Sort.Int), SortOf(op.Type));
                }
                case IPropertyReferenceOperation pr: return EvalProperty(pr, f, spec);
                case IFieldReferenceOperation fr when fr.Field.ContainingType?.IsTupleType == true && fr.Instance != null:
                    return T.Coerce(TupleItem(Eval(fr.Instance, f, spec), fr.Field), SortOf(fr.Type));
                case ITupleOperation tuple:
                {
                    // a tuple is a value: a fresh reference whose items are fixed here and never change
                    var elems = tuple.Elements.Select(e => Eval(e, f, spec)).ToArray();
                    var t = _z3.Fresh("tuple", Sort.Int);
                    var fields = ((INamedTypeSymbol)tuple.Type).TupleElements;
                    for (int i = 0; i < elems.Length; i++) AssumeSide(T.Eq(TupleItem(t, fields[i]), elems[i]));
                    return t;
                }
                case IFieldReferenceOperation fr:
                {
                    var args = fr.Instance != null ? new[] { Eval(fr.Instance, f, spec) } : Array.Empty<Term>();
                    if (!fr.Field.IsReadOnly && !fr.Field.IsConst && _codeMode)
                        Warn(fr.Syntax, $"mutable field '{fr.Field.Name}' is modeled as a function of its object; writes to it are not tracked");
                    return T.Coerce(_z3.Apply(fr.Field.OriginalDefinition.ToDisplayString(), SortOf(fr.Field.OriginalDefinition.Type), args), SortOf(fr.Type));
                }
                case IInvocationOperation inv: return EvalInvocation(inv, f, spec);
                case IArrayCreationOperation ac: return EvalArrayCreation(ac, f, spec);
                case IDefaultValueOperation _: return SortOf(op.Type) == Sort.Bool ? T.False : T.Int(0);
                case IDeclarationExpressionOperation d: return Eval(d.Expression, f, spec);
                case IArgumentOperation arg: return Eval(arg.Value, f, spec);
                case IExpressionStatementOperation es: return Eval(es.Operation, f, spec);
                case IObjectCreationOperation oc:
                    foreach (var a in oc.Arguments) Eval(a.Value, f, spec);
                    return Unknown(op.Type, "new");
                case IIsNullOperation isn:
                    Eval(isn.Operand, f, spec);
                    return _z3.Fresh("isnull", Sort.Bool);
                case IFlowAnonymousFunctionOperation _:
                case IDelegateCreationOperation _:
                case IAnonymousFunctionOperation _:
                    return _z3.Fresh("delegate", Sort.Int);
                case ILiteralOperation _:
                    return Unknown(op.Type, "literal");
                default:
                    foreach (var child in op.ChildOperations) Eval(child, f, spec);
                    Unsupported(op);
                    return Unknown(op.Type);
            }
        }

        private Term EvalConversion(IConversionOperation c, Frame f, SpecEnv spec)
        {
            var v = Eval(c.Operand, f, spec);
            var from = c.Operand.Type;
            if (c.OperatorMethod != null)
            {
                // T[] -> Span<T> / ReadOnlySpan<T> keeps the same storage.
                if (from is IArrayTypeSymbol && IsSequence(c.Type)) return v;
                Unsupported(c);
                return Unknown(c.Type);
            }
            if (IsIntegral(c.Type) && IsIntegral(from) && _codeMode && _engine.Options.CheckOverflow)
            {
                var (lo, hi) = RangeOf(c.Type);
                Prove(T.InRange(v, lo, hi), "CSV1010", c.Syntax, $"conversion '{c.Syntax}' to {c.Type.Name} might overflow");
            }
            else if (IsIntegral(c.Type) && !IsIntegral(from) && from?.SpecialType != SpecialType.System_Boolean && !SpecSymbols.IsGhostType(from) && from != null && from.TypeKind != TypeKind.TypeParameter)
            {
                return Unknown(c.Type, "conv");
            }
            return T.Coerce(v, SortOf(c.Type));
        }

        private Term EvalBinary(IBinaryOperation b, Frame f, SpecEnv spec)
        {
            if (b.OperatorMethod != null)
            {
                if (SpecSymbols.IsGhostType(b.OperatorMethod.ContainingType) || SpecSymbols.IsSeqType(b.OperatorMethod.ContainingType))
                {
                    var eq = T.Eq(Eval(b.LeftOperand, f, spec), Eval(b.RightOperand, f, spec));
                    return b.OperatorKind == BinaryOperatorKind.NotEquals ? T.Not(eq) : eq;
                }
                Eval(b.LeftOperand, f, spec); Eval(b.RightOperand, f, spec);
                Unsupported(b);
                return Unknown(b.Type);
            }
            var l = Eval(b.LeftOperand, f, spec);
            if (b.OperatorKind == BinaryOperatorKind.ConditionalAnd) return T.And(AsBool(l), AsBool(Eval(b.RightOperand, f, spec)));
            if (b.OperatorKind == BinaryOperatorKind.ConditionalOr) return T.Or(AsBool(l), AsBool(Eval(b.RightOperand, f, spec)));
            var r = Eval(b.RightOperand, f, spec);
            var opType = b.LeftOperand.Type;
            bool numeric = IsIntegral(opType) || IsIntegral(b.RightOperand.Type) || SpecSymbols.IsGhostType(opType);
            bool boolean = l.Sort == Sort.Bool && r.Sort == Sort.Bool;
            switch (b.OperatorKind)
            {
                case BinaryOperatorKind.Equals: return numeric || boolean || opType?.IsReferenceType == true || SpecSymbols.IsLinear(opType) ? T.Eq(l, r) : Unknown(b.Type);
                case BinaryOperatorKind.NotEquals: return numeric || boolean || opType?.IsReferenceType == true ? T.Not(T.Eq(l, r)) : Unknown(b.Type);
                case BinaryOperatorKind.LessThan: return numeric ? T.Lt(l, r) : Unknown(b.Type);
                case BinaryOperatorKind.LessThanOrEqual: return numeric ? T.Le(l, r) : Unknown(b.Type);
                case BinaryOperatorKind.GreaterThan: return numeric ? T.Gt(l, r) : Unknown(b.Type);
                case BinaryOperatorKind.GreaterThanOrEqual: return numeric ? T.Ge(l, r) : Unknown(b.Type);
                case BinaryOperatorKind.And when boolean: return T.And(l, r);
                case BinaryOperatorKind.Or when boolean: return T.Or(l, r);
                case BinaryOperatorKind.ExclusiveOr when boolean: return T.Xor(l, r);
                default: return Arith(b.OperatorKind, l, r, b.Type, b.Syntax, false);
            }
        }

        private Term Arith(BinaryOperatorKind kind, Term l, Term r, ITypeSymbol type, SyntaxNode at, bool userDefined)
        {
            if (userDefined || !IsIntegral(type) || l.Sort != Sort.Int || r.Sort != Sort.Int)
            {
                if (!userDefined && l.Sort == Sort.Bool && r.Sort == Sort.Bool)
                {
                    if (kind == BinaryOperatorKind.And) return T.And(l, r);
                    if (kind == BinaryOperatorKind.Or) return T.Or(l, r);
                    if (kind == BinaryOperatorKind.ExclusiveOr) return T.Xor(l, r);
                }
                if (_codeMode) Warn(at, $"operator on {type?.Name ?? "?"} is not modeled; result is unknown");
                return Unknown(type);
            }
            Term v;
            switch (kind)
            {
                case BinaryOperatorKind.Add: v = T.Add(l, r); break;
                case BinaryOperatorKind.Subtract: v = T.Sub(l, r); break;
                case BinaryOperatorKind.Multiply: v = T.Mul(l, r); break;
                case BinaryOperatorKind.Divide:
                case BinaryOperatorKind.Remainder:
                    if (_codeMode) Prove(T.Not(T.Eq(r, T.Int(0))), "CSV1009", at, $"possible division by zero in '{at}'");
                    v = kind == BinaryOperatorKind.Divide ? T.Div(l, r) : T.Rem(l, r);
                    break;
                default:
                    if (_codeMode) Warn(at, $"operator {kind} is not modeled; result is unknown");
                    return Unknown(type);
            }
            if (_codeMode && _engine.Options.CheckOverflow)
            {
                var (lo, hi) = RangeOf(type);
                Prove(T.InRange(v, lo, hi), "CSV1010", at, $"arithmetic '{at}' might overflow {type.Name}");
            }
            return v;
        }

        private Term EvalUnary(IUnaryOperation u, Frame f, SpecEnv spec)
        {
            var v = Eval(u.Operand, f, spec);
            switch (u.OperatorKind)
            {
                case UnaryOperatorKind.Not: return T.Not(AsBool(v));
                case UnaryOperatorKind.Plus: return v;
                case UnaryOperatorKind.Minus when v.Sort == Sort.Int && IsIntegral(u.Type):
                    return Arith(BinaryOperatorKind.Subtract, T.Int(0), v, u.Type, u.Syntax, false);
                default:
                    Unsupported(u);
                    return Unknown(u.Type);
            }
        }

        /// <summary><c>(a, b) = t</c> and <c>var (a, b) = t</c>: each target gets the tuple's item at its position.</summary>
        private void Deconstruct(IOperation target, Term tuple, Frame f, SpecEnv spec)
        {
            if (target is IDeclarationExpressionOperation d) target = d.Expression;
            if (!(target is ITupleOperation targets) || !(targets.Type is INamedTypeSymbol type && type.IsTupleType))
            {
                Unsupported(target);
                return;
            }
            var fields = type.TupleElements;
            for (int i = 0; i < targets.Elements.Length; i++)
            {
                var item = TupleItem(tuple, fields[i]);
                var element = targets.Elements[i] is IDeclarationExpressionOperation de ? de.Expression : targets.Elements[i];
                if (element is ITupleOperation) Deconstruct(element, item, f, spec);
                else if (!(element is IDiscardOperation)) Write(element, T.Coerce(item, SortOf(element.Type)), f, spec);
            }
        }

        /// <summary>Item n of a tuple, by position: named elements (<c>r.k</c>) and <c>ItemN</c> are the same function.</summary>
        private Term TupleItem(Term tuple, IFieldSymbol field)
        {
            var item = field.CorrespondingTupleField ?? field;
            return _z3.Apply("tuple." + item.Name, SortOf(item.Type), new[] { tuple });
        }

        private void BoundsCheck(Term seq, Term idx, SyntaxNode at)
        {
            var len = Len(seq);
            if (_codeMode)
                Prove(T.And(T.Le(T.Int(0), idx), T.Lt(idx, len)), "CSV1003", at, $"index in '{at}' might be out of range");
        }

        private void Write(IOperation target, Term v, Frame f, SpecEnv spec)
        {
            switch (target)
            {
                case ILocalReferenceOperation l: f.Vars[l.Local] = v; break;
                case IParameterReferenceOperation p: f.Vars[p.Parameter] = v; break;
                case IDeclarationExpressionOperation d: Write(d.Expression, v, f, spec); break;
                case IArrayElementReferenceOperation ae when ae.Indices.Length == 1:
                {
                    var arr = Eval(ae.ArrayReference, f, spec);
                    var idx = Eval(ae.Indices[0], f, spec);
                    BoundsCheck(arr, idx, ae.Syntax);
                    f.Heap = T.Store(f.Heap, arr, T.Store(T.Select(f.Heap, arr, Sort.Row), idx, T.Coerce(v, Sort.Int)));
                    break;
                }
                case IPropertyReferenceOperation pr when pr.Property.IsIndexer && IsSequence(pr.Instance?.Type) && pr.Arguments.Length == 1:
                {
                    var arr = Eval(pr.Instance, f, spec);
                    var idx = Eval(pr.Arguments[0].Value, f, spec);
                    BoundsCheck(arr, idx, pr.Syntax);
                    f.Heap = T.Store(f.Heap, arr, T.Store(T.Select(f.Heap, arr, Sort.Row), idx, T.Coerce(v, Sort.Int)));
                    break;
                }
                case IFlowCaptureReferenceOperation _:
                    break;
                default:
                    Warn(target.Syntax, $"assignment to {target.Kind} is not tracked by the verifier");
                    break;
            }
        }

        private Term EvalProperty(IPropertyReferenceOperation pr, Frame f, SpecEnv spec)
        {
            var prop = pr.Property;
            if (SpecSymbols.IsGhostType(prop.ContainingType) && prop.Name == "Value") return Eval(pr.Instance, f, spec);
            if (SpecSymbols.IsSeqType(prop.ContainingType) && prop.IsIndexer)
                return T.Coerce(T.Select(Eval(pr.Instance, f, spec), Eval(pr.Arguments[0].Value, f, spec), Sort.Int), SortOf(pr.Type));
            if (pr.Instance != null && IsSequence(pr.Instance.Type))
            {
                if (prop.Name == "Length") return Len(Eval(pr.Instance, f, spec));
                if (prop.IsIndexer && pr.Arguments.Length == 1)
                {
                    var arr = Eval(pr.Instance, f, spec);
                    var idx = Eval(pr.Arguments[0].Value, f, spec);
                    BoundsCheck(arr, idx, pr.Syntax);
                    if (pr.Instance.Type.SpecialType == SpecialType.System_String) return Unknown(pr.Type, "char");
                    return T.Coerce(T.Select(T.Select(f.Heap, arr, Sort.Row), idx, Sort.Int), SortOf(pr.Type));
                }
            }
            var args = new List<Term>();
            if (pr.Instance != null) args.Add(Eval(pr.Instance, f, spec));
            foreach (var a in pr.Arguments) args.Add(Eval(a.Value, f, spec));
            var def = prop.OriginalDefinition;
            return T.Coerce(_z3.Apply(def.ToDisplayString(), SortOf(def.Type), args), SortOf(pr.Type));
        }

        private Term EvalArrayCreation(IArrayCreationOperation ac, Frame f, SpecEnv spec)
        {
            if (ac.DimensionSizes.Length != 1) { Unsupported(ac); return Unknown(ac.Type); }
            var n = Eval(ac.DimensionSizes[0], f, spec);
            if (_codeMode) Prove(T.Le(T.Int(0), n), "CSV1003", ac.Syntax, $"array size in '{ac.Syntax}' might be negative");
            var r = _z3.Fresh("array", Sort.Int);
            _z3.Assume(T.Eq(Len(r), n));
            // A new array is distinct from every array the method can already see.
            foreach (var t in f.Vars.Where(kv => IsSequence(TypeOf(kv.Key))).Select(kv => kv.Value))
                _z3.Assume(T.Not(T.Eq(r, t)));
            var row = T.ZeroRow();
            if (ac.Initializer != null)
                for (int i = 0; i < ac.Initializer.ElementValues.Length; i++)
                    row = T.Store(row, T.Int(i), T.Coerce(Eval(ac.Initializer.ElementValues[i], f, spec), Sort.Int));
            f.Heap = T.Store(f.Heap, r, row);
            return r;
        }

        // ================================================================================== calls

        private bool HavocsHeap(IMethodSymbol m) =>
            !SpecSymbols.IsSpecClass(m.ContainingType) && !SpecSymbols.IsGhostOf(m) && _engine.MayWriteHeap(m);

        private Term EvalInvocation(IInvocationOperation inv, Frame f, SpecEnv spec)
        {
            var m = inv.TargetMethod;
            if (SpecSymbols.IsSpecClass(m.ContainingType))
            {
                switch (m.Name)
                {
                    case "Result":
                        return spec?.Result != null ? T.Coerce(spec.Result, SortOf(inv.Type)) : Unknown(inv.Type, "result");
                    case "Old":
                        return spec?.Old != null ? Eval(inv.Arguments[0].Value, OldFrame(spec.Old, f), spec) : Eval(inv.Arguments[0].Value, f, spec);
                    case "Forall":
                    case "Exists":
                        return Quantifier(inv, f, spec, m.Name == "Forall");
                    default:
                        return T.True;
                }
            }
            if (SpecSymbols.IsGhostOf(m)) return Eval(inv.Arguments[0].Value, f, spec);
            if (SpecSymbols.IsSeqType(m.ContainingType)) return EvalSeq(inv, f, spec);

            var builtin = Builtin(inv, f, spec);
            if (builtin != null) return builtin;

            var callee = _engine.ContractOf(m);
            Term receiver = inv.Instance != null ? Eval(inv.Instance, f, spec) : null;
            var argTerms = new Term[m.Parameters.Length];
            foreach (var a in inv.Arguments)
            {
                int i = a.Parameter.Ordinal;
                argTerms[i] = a.Parameter.RefKind == RefKind.Out ? FreshOf(a.Parameter.Type, a.Parameter.Name + "$unset") : Eval(a.Value, f, spec);
            }

            if (!_codeMode)
            {
                if (callee.IsPure) return PureApply(callee, receiver, argTerms, f.Heap, SortOf(inv.Type));
                Warn(inv.Syntax, $"'{m.Name}' is not [Pure] and cannot be used in a specification; treated as unknown");
                return Unknown(inv.Type);
            }

            var pre = CalleeFrame(callee, receiver, argTerms, f.Heap);
            if (!callee.HasSource)
            {
                foreach (var a in inv.Arguments.Where(a => a.Parameter.RefKind == RefKind.Ref || a.Parameter.RefKind == RefKind.Out))
                    Write(a.Value, FreshOf(a.Parameter.Type, a.Parameter.Name), f, spec);
                if (HavocsHeap(m)) f.Heap = _z3.Fresh("heap", Sort.Heap);
                return m.ReturnsVoid ? T.True : Unknown(inv.Type, m.Name);
            }

            var preEnv = new SpecEnv { Old = pre };
            foreach (var req in callee.Requires)
                Prove(AsBool(EvalSpec(req, pre, preEnv)), "CSV1001", inv.Syntax,
                    $"precondition '{req.Syntax}' of '{m.Name}' might not hold");

            if (_engine.IsRecursiveCall(_method, callee.Method))
            {
                bool self = SymbolEqualityComparer.Default.Equals(callee.Method, _method);
                if (_entryMeasure == null || callee.Decreases == null)
                    Warn(inv.Syntax, self
                        ? $"recursive call without Spec.Decreases in '{_method.Name}'; termination is not checked"
                        : $"mutually recursive call from '{_method.Name}' to '{m.Name}' without Spec.Decreases on both; termination is not checked");
                else if (callee.Decreases.Count != _entryMeasure.Length)
                    Prove(T.False, "CSV1008", inv.Syntax,
                        $"cannot prove termination: '{m.Name}' and '{_method.Name}' call each other but their measures have different numbers of components");
                else
                    Prove(LexDecreases(EvalMeasure(callee.Decreases, pre, preEnv), _entryMeasure), "CSV1008", inv.Syntax,
                        $"cannot prove termination: measure '{MeasureText(callee.Decreases)}' of '{m.Name}' might not decrease or might be negative");
            }

            var post = pre.Clone();
            foreach (var a in inv.Arguments.Where(a => a.Parameter.RefKind == RefKind.Ref || a.Parameter.RefKind == RefKind.Out))
            {
                var nv = FreshOf(a.Parameter.Type, a.Parameter.Name);
                post.Vars[callee.Method.Parameters[a.Parameter.Ordinal]] = nv;
                Write(a.Value, nv, f, spec);
            }
            if (HavocsHeap(m)) f.Heap = post.Heap = _z3.Fresh("heap", Sort.Heap);

            var result = m.ReturnsVoid ? null : FreshOf(m.ReturnType, m.Name);
            if (result != null && callee.IsPure)
                _z3.Assume(T.Eq(result, PureApply(callee, receiver, argTerms, pre.Heap, result.Sort)));
            foreach (var ens in callee.Ensures)
                _z3.Assume(AsBool(EvalSpec(ens.Expr, post, new SpecEnv { Old = pre, Result = result, ResultParameter = ens.ResultParameter })));
            return result ?? T.True;
        }

        /// <summary>Ghost sequences are SMT arrays; Drop and Concat are the array lambdas in <see cref="SeqTheory"/>.</summary>
        private Term EvalSeq(IInvocationOperation inv, Frame f, SpecEnv spec)
        {
            var args = inv.Arguments.Select(a => Eval(a.Value, f, spec)).ToArray();
            var self = inv.Instance != null ? Eval(inv.Instance, f, spec) : null;
            switch (inv.TargetMethod.Name)
            {
                case "Const": return T.ConstRow(T.Coerce(args[0], Sort.Int));
                case "Update": return T.Store(self, args[0], T.Coerce(args[1], Sort.Int));
                case "Drop": return new Term($"(cv_drop {self} {args[0]})", Sort.Row);
                case "Concat": return new Term($"(cv_concat {self} {args[0]} {args[1]})", Sort.Row);
                default: Unsupported(inv); return _z3.Fresh("seq", Sort.Row);
            }
        }

        /// <summary>Drop and Concat as array lambdas: definitions, not quantified axioms, so they cost Z3 nothing until used.</summary>
        public const string SeqTheory =
            "(define-fun cv_drop ((a (Array Int Int)) (n Int)) (Array Int Int) (lambda ((i Int)) (select a (+ n i))))\n" +
            "(define-fun cv_concat ((a (Array Int Int)) (n Int) (b (Array Int Int))) (Array Int Int) (lambda ((i Int)) (ite (< i n) (select a i) (select b (- i n)))))";

        private Frame CalleeFrame(Contract callee, Term receiver, Term[] args, Term heap)
        {
            var frame = new Frame { This = receiver, Heap = heap };
            for (int i = 0; i < args.Length && i < callee.Method.Parameters.Length; i++)
                if (args[i] != null) frame.Vars[callee.Method.Parameters[i]] = args[i];
            return frame;
        }

        /// <summary>
        /// A [Pure] method is a mathematical function: an uninterpreted function whose definition (single return
        /// expression) and postconditions are unfolded once, guarded by its preconditions.
        /// </summary>
        private Term PureApply(Contract callee, Term receiver, Term[] args, Term heap, Sort sort)
        {
            var m = callee.Method;
            var all = new List<Term>();
            if (receiver != null) all.Add(receiver);
            all.AddRange(args.Select(a => a ?? T.Int(0)));
            bool readsHeap = m.Parameters.Any(p => IsSequence(p.Type));
            if (readsHeap) all.Add(heap);
            var app = _z3.Apply("pure:" + m.ToDisplayString(), SortOf(m.ReturnType), all);

            if (_unfoldDepth == 0)
            {
                _unfoldDepth++;
                bool wasCode = _codeMode;
                _codeMode = false;
                try
                {
                    var frame = CalleeFrame(callee, receiver, args, heap);
                    var env = new SpecEnv { Old = frame, Result = app };
                    var pre = T.And(callee.Requires.Select(r => AsBool(Eval(r, frame, env))).ToArray());
                    if (callee.PureBody != null) AssumeSide(T.Implies(pre, T.Eq(app, Eval(callee.PureBody, frame, env))));
                    foreach (var ens in callee.Ensures)
                        AssumeSide(T.Implies(pre, AsBool(Eval(ens.Expr, frame, new SpecEnv { Old = frame, Result = app, ResultParameter = ens.ResultParameter }))));
                }
                finally { _unfoldDepth--; _codeMode = wasCode; }
            }
            return T.Coerce(app, sort);
        }

        private Term[] EvalMeasure(IReadOnlyList<IOperation> measure, Frame f, SpecEnv spec) =>
            measure.Select(m => EvalSpec(m, f, spec)).ToArray();

        private static string MeasureText(IReadOnlyList<IOperation> measure) => string.Join(", ", measure.Select(m => m.Syntax));

        /// <summary>
        /// <paramref name="after"/> &lt; <paramref name="before"/> lexicographically: some component goes down, from a
        /// non-negative value, and every component before it stays the same. Well-founded, as ATS's metrics on nat tuples.
        /// </summary>
        private static Term LexDecreases(Term[] after, Term[] before)
        {
            var cases = new List<Term>();
            for (int i = 0; i < before.Length; i++)
            {
                var same = Enumerable.Range(0, i).Select(j => T.Eq(after[j], before[j]));
                cases.Add(T.And(same.Concat(new[] { T.Le(T.Int(0), before[i]), T.Lt(after[i], before[i]) }).ToArray()));
            }
            return T.Or(cases.ToArray());
        }

        /// <summary>
        /// The state <c>Spec.Old</c> reads: heap and parameters as on entry; locals and quantifier-bound variables,
        /// which the entry state does not have, keep their current values (like Dafny's <c>old</c>).
        /// </summary>
        private static Frame OldFrame(Frame entry, Frame now)
        {
            var old = entry.Clone();
            foreach (var kv in now.Vars)
                if (!old.Vars.ContainsKey(kv.Key)) old.Vars[kv.Key] = kv.Value;
            return old;
        }

        private Term Quantifier(IInvocationOperation inv, Frame f, SpecEnv spec, bool forall)
        {
            var lo = Eval(inv.Arguments[0].Value, f, spec);
            var hi = Eval(inv.Arguments[1].Value, f, spec);
            var fn = (inv.Arguments[2].Value as IDelegateCreationOperation)?.Target as IAnonymousFunctionOperation;
            var bodyOp = fn?.Body.Operations.OfType<IReturnOperation>().FirstOrDefault()?.ReturnedValue;
            if (bodyOp == null) { Unsupported(inv); return _z3.Fresh("quant", Sort.Bool); }
            var name = _z3.FreshName(fn.Symbol.Parameters[0].Name);
            var bound = new Term(name, Sort.Int);
            var inner = f.Clone();
            inner.Vars[fn.Symbol.Parameters[0]] = bound;
            _quantDepth++;
            int factLevels = _quantFacts.Count;
            _quantFacts.Push(new List<Term>());
            try
            {
                var body = AsBool(Eval(bodyOp, inner, spec));
                var range = T.And(T.Le(lo, bound), T.Lt(bound, hi));
                // Side facts about the body's terms (lengths, [Pure] unfoldings) may mention the bound variable. They
                // become an axiom of their own, quantified the same way, and assumed whether this quantifier is a
                // hypothesis or a goal. (As a hypothesis of the body they would be useless where the quantifier is
                // assumed: a model could falsify them and satisfy the implication vacuously.)
                var facts = T.And(_quantFacts.Pop().ToArray());
                if (facts != T.True) AssumeSide(T.Quant("forall", name, T.Implies(range, facts)));
                return forall ? T.Quant("forall", name, T.Implies(range, body))
                              : T.Quant("exists", name, T.And(range, body));
            }
            finally
            {
                while (_quantFacts.Count > factLevels) _quantFacts.Pop();
                _quantDepth--;
            }
        }

        private Term Builtin(IInvocationOperation inv, Frame f, SpecEnv spec)
        {
            var m = inv.TargetMethod;
            if (m.ContainingType?.ToDisplayString() != "System.Math" || !IsIntegral(inv.Type)) return null;
            var args = inv.Arguments.Select(a => Eval(a.Value, f, spec)).ToArray();
            switch (m.Name)
            {
                case "Max" when args.Length == 2: return T.Ite(T.Ge(args[0], args[1]), args[0], args[1]);
                case "Min" when args.Length == 2: return T.Ite(T.Le(args[0], args[1]), args[0], args[1]);
                case "Abs" when args.Length == 1:
                    if (_codeMode && _engine.Options.CheckOverflow)
                        Prove(T.Not(T.Eq(args[0], T.Int(RangeOf(inv.Type).lo))), "CSV1010", inv.Syntax, $"'{inv.Syntax}' overflows for {inv.Type.Name}.MinValue");
                    return T.Abs(args[0]);
                default: return null;
            }
        }
    }
}
