using System;
using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.FlowAnalysis;
using Microsoft.CodeAnalysis.Operations;
using static CsVerify.Verifier.Boogie.KernelTypes;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>
    /// Pass 1: a method's control-flow graph (Roslyn's lowering of C#) to a kernel procedure. Each block is a block, its
    /// operations kernel statements; what C# means is kept in typed nodes (arithmetic in its context, conversions,
    /// array reads and lengths, functions' calls in specifications) for Checks to make obligations of. Specifications
    /// are read whole from the operations the source has, and what the graph lowers their arguments to is left out:
    /// they never run. Throws <see cref="NotTranslated"/> at anything outside the subset.
    /// </summary>
    internal sealed class Lowering
    {
        private readonly IMethodSymbol _m;
        private readonly Contract _contract;
        private readonly SyntaxNode _decl;
        private readonly SemanticModel _model;
        private readonly Func<IMethodSymbol, bool> _isProcedure, _isFunction;
        private readonly KProcedure _p;
        private KBlock _block;
        private int _temps;

        private Lowering(IMethodSymbol m, Contract contract, SyntaxNode decl, SemanticModel model, MethodResult result,
                         Func<IMethodSymbol, bool> isProcedure, Func<IMethodSymbol, bool> isFunction)
        {
            _m = m; _contract = contract; _decl = decl; _model = model; _isProcedure = isProcedure; _isFunction = isFunction;
            _p = new KProcedure
            {
                Method = m.OriginalDefinition, Contract = contract, Result = result, Name = Name(m), Params = m.Parameters.ToList(),
                Ghost = SpecSymbols.IsGhostFunction(m) || contract.IsLemma,
                HasThis = !m.IsStatic, IsCtor = m.MethodKind == MethodKind.Constructor,
                ThisIsView = !m.IsStatic && SpecSymbols.IsOwned(m.ContainingType) && (m.MethodKind == MethodKind.Constructor || !contract.IsPure),
            };
            _p.UsesPerm = _p.ThisIsView || m.Parameters.Any(x => IsView(x.Type));
        }

        public static KProcedure Lower(IMethodSymbol m, Contract contract, SyntaxNode decl, SemanticModel model, MethodResult result,
                                       Func<IMethodSymbol, bool> isProcedure, Func<IMethodSymbol, bool> isFunction) =>
            new Lowering(m, contract, decl, model, result, isProcedure, isFunction).Run();

        /// <summary>A callee's contract alone (its requires and its measure, over its parameters): what a call of it is checked against.</summary>
        public static KProcedure Signature(IMethodSymbol m, Contract contract, Func<IMethodSymbol, bool> isFunction)
        {
            var l = new Lowering(m, contract, null, null, null, _ => false, isFunction);
            foreach (var r in contract.Requires) l._p.Requires.Add(new KSpec { Expr = l.Spec(r, null), At = r.Syntax });
            if (contract.Decreases != null) l._p.Decreases = contract.Decreases.Select(d => l.Spec(d, null)).ToList();
            // (the permissions its postconditions give back, and a predicate's body, for folding and unfolding it)
            foreach (var e in contract.Ensures) l._p.Ensures.Add(new KSpec { Expr = l.Spec(e.Expr, e.ResultParameter), At = e.Syntax });
            if ((SpecSymbols.IsPredicate(m) || isFunction(m) && contract.Requires.Any(HasAtoms)) && contract.PureBody != null) l._p.FunctionBody = l.Spec(contract.PureBody, null);
            return l._p;
        }

        /// <summary>Does a specification name permissions (Spec.Acc, or a predicate)?</summary>
        public static bool HasAtoms(IOperation op) =>
            op != null && op.DescendantsAndSelf().OfType<IInvocationOperation>().Any(i =>
                SpecSymbols.IsPredicate(i.TargetMethod.OriginalDefinition) || SpecSymbols.IsSpecClass(i.TargetMethod.ContainingType) && i.TargetMethod.Name is "Acc" or "AccRead");

        /// <summary>A predicate's own check: its body, its arithmetic as code's (checked), read left to right.</summary>
        private KProcedure Predicate()
        {
            if (!_m.IsStatic || _m.ReturnType.SpecialType != SpecialType.System_Boolean || _contract.PureBody == null)
                throw new NotTranslated("a [Predicate] that isn't a static bool method of one expression");
            // (ghost code: its arithmetic is mathematical, its reads and divisions checked)
            _p.IsPredicate = _p.UsesPerm = _p.Ghost = true;
            _codeArith = true;
            try { _p.FunctionBody = Spec(_contract.PureBody, null); }
            finally { _codeArith = false; }
            _p.Blocks.Add(new KBlock { Label = "b0", Ordinal = 0, Jump = new KStop() });
            return _p;
        }

        /// <summary>In a predicate's own check: arithmetic is code's.</summary>
        private bool _codeArith;

        private KProcedure Run()
        {
            if (SpecSymbols.IsPredicate(_m)) return Predicate();
            // (Viper's functions over predicates read their footprint: not yet)
            _p.UsesPerm |= _contract.Requires.Any(HasAtoms) || _contract.Ensures.Any(e => HasAtoms(e.Expr));
            var cfg = _model.GetOperation(_decl) switch
            {
                IMethodBodyOperation body => ControlFlowGraph.Create(body),
                IConstructorBodyOperation body => ControlFlowGraph.Create(body),
                _ => throw new NotTranslated("no body"),
            };
            if (cfg.Root.NestedRegions.SelectMany(AllRegions).Concat(cfg.Root.NestedRegions).Any(r => r.Kind != ControlFlowRegionKind.LocalLifetime))
                throw new NotTranslated("try, catch or finally");
            foreach (var r in _contract.Requires) _p.Requires.Add(new KSpec { Expr = Spec(r, null), At = r.Syntax });
            foreach (var e in _contract.Ensures) _p.Ensures.Add(new KSpec { Expr = Spec(e.Expr, e.ResultParameter), At = e.Syntax });
            if (_contract.Decreases != null) _p.Decreases = _contract.Decreases.Select(d => Spec(d, null)).ToList();
            if (_isFunction(_m)) _p.FunctionBody = Spec(_contract.PureBody, null);
            var heads = LoopHeads(cfg);
            foreach (var h in heads)
            {
                var hb = cfg.Blocks[h];
                var loop = (hb.BranchValue?.Syntax ?? hb.Operations.FirstOrDefault()?.Syntax)?.AncestorsAndSelf()
                    .FirstOrDefault(n => n is ForStatementSyntax || n is WhileStatementSyntax || n is DoStatementSyntax || n is CommonForEachStatementSyntax);
                if (loop != null) _p.LoopSyntax[h] = loop;
            }
            foreach (var h in heads)
                _p.LoopBodies[h] = cfg.Blocks.Where(x => new[] { x.FallThroughSuccessor, x.ConditionalSuccessor }.Any(s => s?.Destination?.Ordinal == h) && x.Ordinal >= h).Max(x => x.Ordinal);
            ReadLoopSpecs(cfg, heads);
            if (_p.IsCtor) Initializers();
            foreach (var b in cfg.Blocks)
            {
                _block = new KBlock { Label = $"b{b.Ordinal}", Ordinal = b.Ordinal };
                _p.Blocks.Add(_block);
                if (b.Kind == BasicBlockKind.Exit) { _block.Jump = new KStop(); continue; }
                foreach (var op in b.Operations) Statement(op);
                Branch(b);
            }
            return _p;
        }

        /// <summary>
        /// A constructor's start: the field initializers of its class, in order (its fields are their defaults before,
        /// as the caller makes them). One that chains to another (this(...), or base(...) of a class not object) isn't
        /// translated yet.
        /// </summary>
        private void Initializers()
        {
            if (_decl is ConstructorDeclarationSyntax { Initializer: { } chained } && chained.ThisOrBaseKeyword.IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.ThisKeyword))
                throw new NotTranslated("a constructor that calls this(...)");
            _block = new KBlock { Label = "init", Ordinal = -1, Jump = new KGoto("b0") };
            _p.Blocks.Add(_block);
            foreach (var member in _m.ContainingType.GetMembers().Where(x => !x.IsStatic && (x is IFieldSymbol || x is IPropertySymbol)))
                foreach (var syntax in member.DeclaringSyntaxReferences.Select(r => r.GetSyntax()))
                {
                    var init = (SyntaxNode)(syntax as VariableDeclaratorSyntax)?.Initializer ?? (syntax as PropertyDeclarationSyntax)?.Initializer;
                    if (init == null) continue;
                    if (!IsField(member)) throw new NotTranslated("an initializer of " + member.Name);
                    if (init.SyntaxTree != _decl.SyntaxTree) throw new NotTranslated("an initializer in another file");
                    if (!(_model.GetOperation(init) is ISymbolInitializerOperation op)) throw new NotTranslated("the initializer of " + member.Name);
                    var value = Expr(op.Value);
                    _p.Fields.Add(member.OriginalDefinition);
                    Emit(new KFieldStore { Field = member.OriginalDefinition, Instance = new KVar("this"), Value = value, OnThis = true, At = init, InstanceAt = init });
                }
        }

        private static IEnumerable<ControlFlowRegion> AllRegions(ControlFlowRegion r) => r.NestedRegions.Concat(r.NestedRegions.SelectMany(AllRegions));

        // ------------------------------------------------------------------ loops

        /// <summary>The blocks a later block goes back to: loop heads.</summary>
        private static HashSet<int> LoopHeads(ControlFlowGraph cfg)
        {
            var heads = new HashSet<int>();
            foreach (var b in cfg.Blocks)
                foreach (var s in new[] { b.FallThroughSuccessor, b.ConditionalSuccessor })
                    if (s?.Destination != null && s.Destination.Ordinal <= b.Ordinal) heads.Add(s.Destination.Ordinal);
            return heads;
        }

        /// <summary>The innermost loop a block is in: the latest head before it whose back edge comes from it or after it; -1 if none.</summary>
        private static int HeadOf(ControlFlowGraph cfg, HashSet<int> heads, BasicBlock b) =>
            heads.Where(h => h <= b.Ordinal && cfg.Blocks.Any(x => x.Ordinal >= b.Ordinal &&
                new[] { x.FallThroughSuccessor, x.ConditionalSuccessor }.Any(s => s?.Destination?.Ordinal == h))).DefaultIfEmpty(-1).Max();

        /// <summary>Each Spec.Invariant and loop Spec.Decreases, at the head of the innermost loop it is in.</summary>
        private void ReadLoopSpecs(ControlFlowGraph cfg, HashSet<int> heads)
        {
            foreach (var b in cfg.Blocks)
                foreach (var op in b.Operations)
                {
                    if (SpecCall(op, "Decreases") is IInvocationOperation dec && HeadOf(cfg, heads, b) is int h && h >= 0)
                    {
                        var whole = _model.GetOperation(dec.Syntax) as IInvocationOperation ?? throw new NotTranslated("a measure without its operation");
                        var measure = new List<KSpec>();
                        for (int k = 0; k < whole.Arguments.Length; k++)
                        {
                            measure.Add(new KSpec { Expr = Spec(whole.Arguments[k].Value, null), At = whole.Arguments[k].Value.Syntax });
                            Declare($"m${h}${k}", whole.Arguments[k].Value.Type);
                        }
                        _p.Measures[h] = measure;
                    }
                    if (SpecCall(op, "Invariant") is IInvocationOperation inv)
                    {
                        var head = HeadOf(cfg, heads, b);
                        if (head < 0) throw new NotTranslated("an invariant outside a loop");
                        if (!_p.Invariants.TryGetValue(head, out var list)) _p.Invariants[head] = list = new List<KSpec>();
                        var arg = SpecArgument(inv);
                        list.Add(new KSpec { Expr = Spec(arg, null), At = arg.Syntax });
                    }
                }
        }

        /// <summary>
        /// A Spec statement's argument as written: the control-flow graph lowers &amp;&amp; and ?: in it into blocks, but a
        /// specification is one formula.
        /// </summary>
        private IOperation SpecArgument(IInvocationOperation inv) =>
            (_model.GetOperation(inv.Syntax) as IInvocationOperation)?.Arguments[0].Value ?? throw new NotTranslated("a specification without its operation");

        private static IInvocationOperation SpecCall(IOperation op, string name) =>
            (op is IExpressionStatementOperation es ? es.Operation : op) is IInvocationOperation inv &&
            SpecSymbols.IsSpecClass(inv.TargetMethod.ContainingType) && inv.TargetMethod.Name == name ? inv : null;

        /// <summary>
        /// Is this syntax inside a Spec statement's argument? What the graph lowers it to is left out (a specification
        /// argument never runs), and each branch of it is a choice of either way, which meet again at the Spec call.
        /// </summary>
        private bool InSpec(SyntaxNode at) =>
            at != null && at.AncestorsAndSelf().OfType<ArgumentSyntax>().Any(arg => arg.Parent?.Parent is InvocationExpressionSyntax call &&
                _model.GetSymbolInfo(call).Symbol is IMethodSymbol m && SpecSymbols.IsSpecClass(m.ContainingType));

        // ------------------------------------------------------------------ statements

        private void Emit(KStmt s) => _block.Stmts.Add(s);

        private void Statement(IOperation op)
        {
            if (op is IExpressionStatementOperation es) op = es.Operation;
            if (op is IFlowCaptureOperation spec && InSpec(spec.Value.Syntax)) return;
            switch (op)
            {
                case IInvocationOperation baseCall when baseCall.TargetMethod.MethodKind == MethodKind.Constructor &&
                                                        baseCall.TargetMethod.ContainingType.SpecialType == SpecialType.System_Object:
                    return; // (object's constructor does nothing)
                case IInvocationOperation own when SpecSymbols.IsCsVerifyType(own.TargetMethod.ContainingType, "Own"):
                    Own(own);
                    return;
                case IInvocationOperation inv when SpecSymbols.IsSpecClass(inv.TargetMethod.ContainingType):
                    switch (inv.TargetMethod.Name)
                    {
                        case "Requires": case "Ensures": case "Invariant": case "Decreases": return; // (the contract; the loop heads)
                        case "Fold": case "Unfold":
                        {
                            var whole = SpecArgument(inv);
                            if (!(Spec(whole, null) is KInst instance)) throw new NotTranslated("Spec." + inv.TargetMethod.Name + " of what isn't a predicate instance");
                            _p.UsesPerm = true;
                            Emit(new KFold { Inst = instance, Unfold = inv.TargetMethod.Name == "Unfold", At = inv.Syntax, InstAt = whole.Syntax });
                            return;
                        }
                        case "Assert": case "Assume":
                            Emit(new KSpecStmt { Spec = Spec(SpecArgument(inv), null), Assume = inv.TargetMethod.Name == "Assume", At = inv.Syntax, ArgumentAt = inv.Arguments[0].Syntax });
                            return;
                        default: throw new NotTranslated("Spec." + inv.TargetMethod.Name);
                    }
                case IInvocationOperation call:
                    Call(call);
                    return;
                case ISimpleAssignmentOperation a:
                    Assign(a.Target, Expr(a.Value));
                    return;
                case ICompoundAssignmentOperation ca:
                {
                    var v = Operands(ca.Target, ca.Value);
                    Assign(ca.Target, Arith(Op(ca.OperatorKind), v[0], v[1], ca.Type, ca.Syntax, ca.IsChecked));
                    return;
                }
                case IIncrementOrDecrementOperation id:
                    Assign(id.Target, Arith(id.Kind == OperationKind.Increment ? "+" : "-", Expr(id.Target), new KLit("1"), id.Type, id.Syntax, id.IsChecked));
                    return;
                case IFlowCaptureOperation fc:
                    var value = Expr(fc.Value);
                    Emit(new KAssign { Var = Capture(fc.Id, fc.Value.Type), Value = value });
                    return;
                default:
                    throw new NotTranslated(op.Kind.ToString());
            }
        }

        private void Assign(IOperation target, KExpr value)
        {
            switch (target)
            {
                case ILocalReferenceOperation l when IsView(l.Local.Type):
                    throw new NotTranslated("a view moved from one variable to another");
                case ILocalReferenceOperation l when InSubset(l.Local.Type) && l.Local.RefKind == RefKind.None:
                {
                    // (a local of non-nullable type: each write is checked, so it stays not null)
                    bool nonNull = IsRef(l.Local.Type) && NotNullable(l.Local.Type);
                    Emit(new KAssign { Var = Declare(Local(l.Local), l.Local.Type), Value = value,
                                       NotNullAt = nonNull ? l.Syntax.Parent ?? l.Syntax : null, NotNullName = l.Local.Name });
                    return;
                }
                case IFieldReferenceOperation _: case IPropertyReferenceOperation _:
                {
                    var (field, instance, onThis, instanceAt) = FieldOf(target);
                    if (IsOwnedField(field)) _p.UsesPerm = true;
                    Emit(new KFieldStore { Field = field, Instance = instance, OnThis = onThis, Value = value, At = target.Syntax, InstanceAt = instanceAt });
                    return;
                }
                case IArrayElementReferenceOperation e when IsArray(e.ArrayReference.Type) && e.Indices.Length == 1:
                {
                    var v = Operands(e.ArrayReference, e.Indices[0]);
                    Emit(new KStore { Array = v[0], Index = v[1], Value = value, ArrayType = e.ArrayReference.Type, At = e.Syntax, ArrayAt = e.ArrayReference.Syntax });
                    return;
                }
                case IParameterReferenceOperation p when p.Parameter.RefKind is RefKind.Ref or RefKind.Out && InSubset(p.Parameter.Type) && !IsView(p.Parameter.Type):
                {
                    Emit(new KAssign { Var = Local(p.Parameter), Value = value });
                    return;
                }
                case IParameterReferenceOperation: throw new NotTranslated("an assignment to a parameter");
                default: throw new NotTranslated("an assignment to " + target.Kind);
            }
        }

        private void Branch(BasicBlock b)
        {
            var fall = b.FallThroughSuccessor;
            string then = $"b{b.Ordinal}$then", otherwise = $"b{b.Ordinal}$else";
            if (b.ConditionalSuccessor != null)
            {
                bool inSpec = InSpec(b.BranchValue?.Syntax);
                KExpr cond = null;
                if (!inSpec)
                {
                    // (evaluated once, here: each way assumes it, or its negation)
                    var c = Expr(b.BranchValue);
                    var name = Declare($"g${b.Ordinal}", _model.Compilation.GetSpecialType(SpecialType.System_Boolean));
                    Emit(new KAssign { Var = name, Value = c });
                    cond = b.ConditionKind == ControlFlowConditionKind.WhenTrue ? new KVar(name) : new KOp("!", new KVar(name));
                }
                _block.Jump = new KGoto(then, otherwise);
                var thenBlock = new KBlock { Label = then, Ordinal = b.Ordinal };
                var elseBlock = new KBlock { Label = otherwise, Ordinal = b.Ordinal };
                if (cond != null)
                {
                    thenBlock.Stmts.Add(new KAssume { Cond = cond });
                    elseBlock.Stmts.Add(new KAssume { Cond = new KOp("!", cond) });
                }
                thenBlock.Jump = To(b, b.ConditionalSuccessor.Destination);
                elseBlock.Jump = To(b, fall?.Destination);
                _p.Blocks.Add(thenBlock);
                _p.Blocks.Add(elseBlock);
                return;
            }
            if (fall?.Semantics == ControlFlowBranchSemantics.Return && b.BranchValue != null)
                Emit(new KAssign { Var = "result", Value = Expr(b.BranchValue) });
            else if (fall?.Semantics == ControlFlowBranchSemantics.Throw || fall?.Semantics == ControlFlowBranchSemantics.Rethrow)
            {
                // (a path that throws need not meet the postcondition: it ends)
                if (b.BranchValue != null) Expr(b.BranchValue);
                _block.Jump = new KStop();
                return;
            }
            _block.Jump = To(b, fall?.Destination);
        }

        /// <summary>A jump to a block, or a return where it is to the exit.</summary>
        private KJump To(BasicBlock from, BasicBlock to)
        {
            if (to == null) return new KStop();
            if (to.Kind == BasicBlockKind.Exit)
            {
                // (where CsVerify's engine reports a return: the return statement or its value; a return; at its block's
                // last operation; falling off the end, at the method)
                var at = from.BranchValue?.Syntax.Parent as ReturnStatementSyntax as SyntaxNode ?? from.BranchValue?.Syntax ??
                         (from.FallThroughSuccessor?.Semantics == ControlFlowBranchSemantics.Return ? from.Operations.LastOrDefault()?.Syntax : null) ?? _decl;
                return new KReturn { At = at };
            }
            return new KGoto($"b{to.Ordinal}");
        }

        private string Declare(string name, ITypeSymbol type)
        {
            if (!_p.Locals.Any(l => l.Name == name)) _p.Locals.Add(new KLocal { Name = name, Type = type });
            return name;
        }

        private string Capture(CaptureId id, ITypeSymbol type)
        {
            if (type == null || !InSubset(type)) throw new NotTranslated("a capture of " + type);
            return Declare("c$" + id.GetHashCode(), type);
        }

        /// <summary>A field access's field, its object (null for a static field), whether that is this, and where it is.</summary>
        private (ISymbol field, KExpr instance, bool onThis, SyntaxNode at) FieldOf(IOperation access, IParameterSymbol specResult = null, bool spec = false)
        {
            var (symbol, instance) = access switch
            {
                IFieldReferenceOperation f => ((ISymbol)f.Field, f.Instance),
                IPropertyReferenceOperation p when p.Arguments.Length == 0 => (p.Property, p.Instance),
                _ => throw new NotTranslated(access.Kind.ToString()),
            };
            if (!IsField(symbol)) throw new NotTranslated("the member " + symbol.Name);
            symbol = symbol.OriginalDefinition;
            if (symbol.IsStatic && IsRef(FieldType(symbol)) && NotNullable(FieldType(symbol))) throw new NotTranslated("a non-nullable static field");
            _p.Fields.Add(symbol);
            if (symbol.IsStatic) return (symbol, null, false, null);
            if (instance is IInstanceReferenceOperation { ReferenceKind: InstanceReferenceKind.ContainingTypeInstance }) return (symbol, new KVar("this"), true, instance.Syntax);
            return (symbol, spec ? Spec(instance, specResult) : Expr(instance), false, instance.Syntax);
        }

        // ------------------------------------------------------------------ expressions (run time)

        private KMode Mode(SyntaxNode at, bool isChecked) =>
            !isChecked && InUnchecked(at) ? KMode.Unchecked : _p.Ghost ? KMode.Math : isChecked ? KMode.Checked : KMode.Default;

        /// <summary>
        /// Operands, in C#'s order: where a later one is a call (or an allocation), lowered to a statement before the
        /// expression, each earlier one is evaluated into a temporary before it, so its checks (and its reads of
        /// memory) come first, as they do in C#.
        /// </summary>
        private KExpr[] Operands(params IOperation[] ops)
        {
            var values = new KExpr[ops.Length];
            var after = new int[ops.Length];
            for (int k = 0; k < ops.Length; k++)
            {
                values[k] = Expr(ops[k]);
                after[k] = _block.Stmts.Count;
            }
            int end = _block.Stmts.Count;
            for (int k = ops.Length - 2; k >= 0; k--)
            {
                if (after[k] == end || values[k] is KLit || values[k] is KVar || !InSubset(ops[k].Type)) continue;
                var t = Declare("t$" + _temps++, ops[k].Type);
                _block.Stmts.Insert(after[k], new KAssign { Var = t, Value = values[k] });
                values[k] = new KVar(t);
            }
            return values;
        }

        private KExpr Arith(string op, KExpr l, KExpr r, ITypeSymbol type, SyntaxNode at, bool isChecked)
        {
            if (!IsIntegral(type)) throw new NotTranslated("arithmetic on " + type);
            return new KArith { Op = op, Left = l, Right = r, Type = type, Mode = Mode(at, isChecked), At = at };
        }

        private static string Op(BinaryOperatorKind k) => k switch
        {
            BinaryOperatorKind.Add => "+", BinaryOperatorKind.Subtract => "-", BinaryOperatorKind.Multiply => "*",
            BinaryOperatorKind.Divide => "/", BinaryOperatorKind.Remainder => "%",
            _ => throw new NotTranslated("the operator " + k),
        };

        private KExpr Expr(IOperation e)
        {
            switch (e)
            {
                case { ConstantValue: { HasValue: true } cv } when Scalar(e.Type) || IsRef(e.Type): return Constant(cv.Value, e.Type);
                case ILocalReferenceOperation l when InSubset(l.Local.Type) && l.Local.RefKind == RefKind.None: return new KVar(Declare(Local(l.Local), l.Local.Type));
                case IParameterReferenceOperation p when InSubset(p.Parameter.Type) && p.Parameter.RefKind is RefKind.None or RefKind.Ref or RefKind.Out: return new KVar(Local(p.Parameter));
                case IInvocationOperation own when SpecSymbols.IsCsVerifyType(own.TargetMethod.ContainingType, "Own"):
                    return Own(own);
                case IFlowCaptureReferenceOperation r: return new KVar(Capture(r.Id, r.Type));
                case IInstanceReferenceOperation { ReferenceKind: InstanceReferenceKind.ContainingTypeInstance } when !_p.IsCtor:
                    return new KVar("this");
                case IInstanceReferenceOperation _:
                    throw new NotTranslated(_p.IsCtor ? "this, escaping its constructor" : "an instance reference");
                case IFieldReferenceOperation _:
                case IPropertyReferenceOperation pf when !(pf.Property.Name == "Length" && IsArray(pf.Instance?.Type)):
                {
                    var (field, instance, onThis, instanceAt) = FieldOf(e);
                    return new KField { Field = field, Instance = instance, OnThis = onThis, At = e.Syntax, InstanceAt = instanceAt };
                }
                case IObjectCreationOperation oc when IsClass(oc.Type) && oc.Initializer == null && oc.Constructor != null:
                {
                    var ctor = oc.Constructor.OriginalDefinition;
                    bool isImplicit = ctor.IsImplicitlyDeclared;
                    if (!isImplicit && !_isProcedure(ctor)) throw new NotTranslated("a call of " + oc.Type.Name + "'s constructor");
                    if (!isImplicit) _p.Calls.Add(ctor);
                    var ordered = oc.Arguments.OrderBy(a => a.Parameter.Ordinal).ToList();
                    var args = Operands(ordered.Select(a => a.Value).ToArray());
                    var t = Declare("t$" + _temps++, oc.Type);
                    foreach (var f in InstanceFields(oc.Type)) _p.Fields.Add(f);
                    Emit(new KNewObj { Var = t, Type = oc.Type, Ctor = isImplicit ? null : ctor, Args = args, ArgsAt = ordered.Select(a => a.Value.Syntax).ToArray(), At = oc.Syntax });
                    return new KVar(t);
                }
                case IParenthesizedOperation par: return Expr(par.Operand);
                case IConversionOperation conv when conv.Conversion.IsIdentity || conv.IsImplicit && IsIntegral(conv.Type) && IsIntegral(conv.Operand.Type) && conv.Conversion.IsNumeric:
                    return Expr(conv.Operand);
                case IConversionOperation conv when Upcast(conv):
                    return conv.Operand.ConstantValue.HasValue ? new KLit("null") : Expr(conv.Operand);
                case IConversionOperation conv when IsIntegral(conv.Type) && IsIntegral(conv.Operand.Type) && conv.Conversion.IsNumeric:
                    return new KConv { Value = Expr(conv.Operand), From = conv.Operand.Type, To = conv.Type, Mode = Mode(conv.Syntax, conv.IsChecked), At = conv.Syntax };
                case IUnaryOperation u when u.OperatorKind == UnaryOperatorKind.Not: return new KOp("!", Expr(u.Operand));
                case IUnaryOperation u when u.OperatorKind == UnaryOperatorKind.Plus: return Expr(u.Operand);
                case IUnaryOperation u when u.OperatorKind == UnaryOperatorKind.Minus && IsIntegral(u.Type):
                    return Arith("-", new KLit("0"), Expr(u.Operand), u.Type, u.Syntax, u.IsChecked);
                case IBinaryOperation b when b.OperatorMethod == null && (InSubset(b.LeftOperand.Type) && InSubset(b.RightOperand.Type) ||
                                             b.OperatorKind is BinaryOperatorKind.Equals or BinaryOperatorKind.NotEquals && (RefOperand(b.LeftOperand) || RefOperand(b.RightOperand))):
                    return Binary(b);
                case IArrayElementReferenceOperation el when IsArray(el.ArrayReference.Type) && el.Indices.Length == 1:
                {
                    var v = Operands(el.ArrayReference, el.Indices[0]);
                    return new KElem { Array = v[0], Index = v[1], ArrayType = el.ArrayReference.Type, At = el.Syntax, ArrayAt = el.ArrayReference.Syntax };
                }
                case IPropertyReferenceOperation pr when pr.Property.Name == "Length" && IsArray(pr.Instance?.Type):
                    return new KLen { Array = Expr(pr.Instance), At = pr.Syntax, ArrayAt = pr.Instance.Syntax };
                case IArrayCreationOperation ac when IsArray(ac.Type) && ac.DimensionSizes.Length == 1:
                {
                    var v = Operands(new[] { ac.DimensionSizes[0] }.Concat(ac.Initializer?.ElementValues ?? Enumerable.Empty<IOperation>()).ToArray());
                    var size = v[0];
                    var elements = ac.Initializer == null ? null : v.Skip(1).ToArray();
                    var t = Declare("t$" + _temps++, ac.Type);
                    Emit(new KNew { Var = t, ArrayType = ac.Type, Size = size, Elements = elements });
                    return new KVar(t);
                }
                case IInvocationOperation call:
                    return Call(call);
                default:
                    if (e.ConstantValue.HasValue && e.ConstantValue.Value == null && IsRef(e.Type)) return new KLit("null");
                    throw new NotTranslated(e.Kind + " '" + e.Syntax + "'");
            }
        }

        /// <summary>
        /// A reference made an object (to compare it with ==, or null): the same reference. Comparing two objects as
        /// objects is reference equality.
        /// </summary>
        private static bool Upcast(IConversionOperation conv) =>
            conv.IsImplicit && conv.Conversion.IsReference && (IsRef(conv.Operand.Type) || conv.Operand.ConstantValue is { HasValue: true, Value: null });

        private static IOperation Unconverted(IOperation op)
        {
            while (op is IConversionOperation c && c.IsImplicit) op = c.Operand;
            return op;
        }

        private static bool RefOperand(IOperation op) => IsRef(op.Type) || op is IConversionOperation c && Upcast(c) && IsRef(c.Operand.Type);

        private static KExpr Constant(object v, ITypeSymbol type)
        {
            if (v is bool x) return new KLit(x ? "true" : "false");
            if (v == null && IsRef(type)) return new KLit("null");
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
            return Number(n);
        }

        private KExpr Binary(IBinaryOperation b)
        {
            var v = Operands(b.LeftOperand, b.RightOperand);
            var (l, r) = (v[0], v[1]);
            switch (b.OperatorKind)
            {
                case BinaryOperatorKind.Add: case BinaryOperatorKind.Subtract: case BinaryOperatorKind.Multiply:
                case BinaryOperatorKind.Divide: case BinaryOperatorKind.Remainder:
                    return Arith(Op(b.OperatorKind), l, r, b.Type, b.Syntax, b.IsChecked);
                case BinaryOperatorKind.Equals: return new KOp("==", l, r);
                case BinaryOperatorKind.NotEquals: return new KOp("!=", l, r);
                case BinaryOperatorKind.LessThan: return new KOp("<", l, r);
                case BinaryOperatorKind.LessThanOrEqual: return new KOp("<=", l, r);
                case BinaryOperatorKind.GreaterThan: return new KOp(">", l, r);
                case BinaryOperatorKind.GreaterThanOrEqual: return new KOp(">=", l, r);
                case BinaryOperatorKind.And when b.Type.SpecialType == SpecialType.System_Boolean:
                case BinaryOperatorKind.ConditionalAnd: return new KOp("&&", l, r);
                case BinaryOperatorKind.Or when b.Type.SpecialType == SpecialType.System_Boolean:
                case BinaryOperatorKind.ConditionalOr: return new KOp("||", l, r);
                case BinaryOperatorKind.ExclusiveOr when b.Type.SpecialType == SpecialType.System_Boolean: return new KOp("!=", l, r);
                default: throw new NotTranslated("the operator " + b.OperatorKind);
            }
        }

        private KExpr Call(IInvocationOperation call)
        {
            var callee = call.TargetMethod.OriginalDefinition;
            if (!_isProcedure(callee)) throw new NotTranslated("a call of " + call.TargetMethod.Name);
            _p.Calls.Add(callee);
            var ordered = call.Arguments.OrderBy(a => a.Parameter.Ordinal).ToList();
            if (!callee.IsStatic && (call.Instance == null || callee.IsVirtual || callee.IsAbstract || callee.IsOverride)) throw new NotTranslated("a virtual call of " + callee.Name);
            bool onThis = call.Instance is IInstanceReferenceOperation;
            // (a ref or out argument is a variable, which gets what the callee gives back; an out one isn't read)
            var refOuts = ordered.Where(a => a.Parameter.RefKind != RefKind.None).Select(a => (a.Parameter.Ordinal, RefVariable(a))).ToList();
            var ins = ordered.Where(a => a.Parameter.RefKind != RefKind.Out).ToList();
            var operands = (call.Instance == null || onThis ? Enumerable.Empty<IOperation>() : new[] { call.Instance }).Concat(ins.Select(a => a.Value)).ToArray();
            var values = Operands(operands);
            var receiver = call.Instance == null ? null : onThis ? Expr(call.Instance) : values[0];
            var inValues = call.Instance == null || onThis ? values : values.Skip(1).ToArray();
            var args = new KExpr[ordered.Count];
            for (int k = 0; k < ins.Count; k++) args[ins[k].Parameter.Ordinal] = inValues[k];
            foreach (var (ordinal, v) in refOuts) args[ordinal] ??= new KVar(v);
            if (refOuts.Any()) _p.UsesPerm |= ordered.Any(a => IsView(a.Parameter.Type));
            if (ordered.Any(a => IsView(a.Parameter.Type)) || IsOwnedClass(callee.ContainingType) && !callee.IsStatic) _p.UsesPerm = true;
            var result = callee.ReturnsVoid ? null : Declare("t$" + _temps++, callee.ReturnType);
            Emit(new KCall { Callee = callee, Receiver = receiver, ReceiverIsThis = onThis, ReceiverAt = call.Instance?.Syntax, Args = args, ArgsAt = ordered.Select(a => a.Value.Syntax).ToArray(),
                             Result = result, At = call.Syntax, RefOuts = refOuts });
            return result == null ? null : new KVar(result);
        }

        /// <summary>The variable a ref or out argument is: a local (declared there, for out var), or a ref or out parameter.</summary>
        private string RefVariable(IArgumentOperation a)
        {
            var v = a.Value is IDeclarationExpressionOperation d ? d.Expression : a.Value;
            switch (v)
            {
                case ILocalReferenceOperation l when InSubset(l.Local.Type) && l.Local.RefKind == RefKind.None: return Declare(Local(l.Local), l.Local.Type);
                case IParameterReferenceOperation p when InSubset(p.Parameter.Type) && p.Parameter.RefKind is RefKind.Ref or RefKind.Out: return Local(p.Parameter);
                default: throw new NotTranslated("a ref or out argument that isn't a variable");
            }
        }

        /// <summary>Own.New(new C(...), out view): a view of the new object; Own.Drop(view). The rest of Own isn't translated yet.</summary>
        private KExpr Own(IInvocationOperation own)
        {
            _p.UsesPerm = true;
            switch (own.TargetMethod.Name)
            {
                case "New" when own.Arguments[0].Value is IObjectCreationOperation:
                {
                    var obj = Expr(own.Arguments[0].Value);
                    var view = RefVariable(own.Arguments[1]);
                    Emit(new KOwn { Kind = "new", Obj = obj, View = view, Type = own.Arguments[0].Value.Type, At = own.Syntax });
                    return obj;
                }
                case "ToAcc" when IsView(own.Arguments[0].Value.Type):
                    // (the view goes, its permission stays in hand: a view and Spec.Acc are one permission here)
                    Expr(own.Arguments[0].Value);
                    return null;
                case "FromAcc" when IsOwnedClass(own.Arguments[0].Value.Type):
                {
                    var obj = Expr(own.Arguments[0].Value);
                    Emit(new KOwn { Kind = "fromacc", Obj = obj, View = RefVariable(own.Arguments[1]), Type = own.Arguments[0].Value.Type, At = own.Syntax });
                    return null;
                }
                case "Drop" when IsView(own.Arguments[0].Value.Type):
                    Emit(new KOwn { Kind = "drop", Obj = Expr(own.Arguments[0].Value), Type = ViewOf(own.Arguments[0].Value.Type), At = own.Syntax });
                    return null;
                default: throw new NotTranslated("Own." + own.TargetMethod.Name + (own.TargetMethod.Name == "New" ? " of an existing object" : ""));
            }
        }

        // ------------------------------------------------------------------ specifications (mathematical)

        /// <summary>A specification: mathematics, its array reads, lengths, divisions and functions' calls kept for Checks' well-definedness.</summary>
        private KExpr Spec(IOperation e, IParameterSymbol result)
        {
            switch (e)
            {
                case IDelegateCreationOperation d: return Spec(d.Target, result);
                case IAnonymousFunctionOperation fn when fn.Body.Operations.Length == 1 && fn.Body.Operations[0] is IReturnOperation ret:
                    return Spec(ret.ReturnedValue, fn.Symbol.Parameters.FirstOrDefault() ?? result);
                case { ConstantValue: { HasValue: true } cv } when Scalar(e.Type) || IsRef(e.Type): return Constant(cv.Value, e.Type);
                case IParameterReferenceOperation p when result != null && SymbolEqualityComparer.Default.Equals(p.Parameter, result): return new KVar("result");
                case IParameterReferenceOperation p when p.Parameter.ContainingSymbol is IMethodSymbol { MethodKind: MethodKind.AnonymousFunction }:
                    return new KVar("q$" + p.Parameter.Name); // (a quantifier's variable)
                case IParameterReferenceOperation p when InSubset(p.Parameter.Type): return new KVar(Local(p.Parameter));
                case ILocalReferenceOperation l when InSubset(l.Local.Type): return new KVar(Declare(Local(l.Local), l.Local.Type));
                case IInstanceReferenceOperation { ReferenceKind: InstanceReferenceKind.ContainingTypeInstance }: return new KVar("this");
                // (a view's object: v.Obj.Value)
                case IPropertyReferenceOperation { Property.Name: "Value", Instance: IPropertyReferenceOperation { Property.Name: "Obj" } obj } when IsView(obj.Instance?.Type):
                    return Spec(obj.Instance, result);
                case IFieldReferenceOperation _:
                case IPropertyReferenceOperation pf when !(pf.Property.Name == "Length" && IsArray(pf.Instance?.Type)):
                {
                    var (field, instance, onThis, instanceAt) = FieldOf(e, result, spec: true);
                    return new KField { Field = field, Instance = instance, OnThis = onThis, At = e.Syntax, InstanceAt = instanceAt };
                }
                case IParenthesizedOperation par: return Spec(par.Operand, result);
                case IConversionOperation conv when conv.Conversion.IsIdentity || IsIntegral(conv.Type) && IsIntegral(conv.Operand.Type) && conv.Conversion.IsNumeric && conv.IsImplicit:
                    return Spec(conv.Operand, result);
                case IConversionOperation conv when Upcast(conv):
                    return conv.Operand.ConstantValue.HasValue ? new KLit("null") : Spec(conv.Operand, result);
                case IUnaryOperation u when u.OperatorKind == UnaryOperatorKind.Not: return new KOp("!", Spec(u.Operand, result));
                case IUnaryOperation u when u.OperatorKind == UnaryOperatorKind.Minus && _codeArith: return Arith("-", new KLit("0"), Spec(u.Operand, result), u.Type, u.Syntax, u.IsChecked);
                case IUnaryOperation u when u.OperatorKind == UnaryOperatorKind.Minus: return new KOp("-", new KLit("0"), Spec(u.Operand, result));
                case IUnaryOperation u when u.OperatorKind == UnaryOperatorKind.Plus: return Spec(u.Operand, result);
                case IConditionalOperation c when c.WhenFalse != null:
                    return new KOp("ite", Spec(c.Condition, result), Spec(c.WhenTrue, result), Spec(c.WhenFalse, result));
                case IBinaryOperation b when b.OperatorMethod == null:
                {
                    var l = Spec(b.LeftOperand, result);
                    var r = Spec(b.RightOperand, result);
                    return b.OperatorKind switch
                    {
                        BinaryOperatorKind.Add when _codeArith => Arith("+", l, r, b.Type, b.Syntax, b.IsChecked),
                        BinaryOperatorKind.Subtract when _codeArith => Arith("-", l, r, b.Type, b.Syntax, b.IsChecked),
                        BinaryOperatorKind.Multiply when _codeArith => Arith("*", l, r, b.Type, b.Syntax, b.IsChecked),
                        BinaryOperatorKind.Divide when _codeArith => Arith("/", l, r, b.Type, b.Syntax, b.IsChecked),
                        BinaryOperatorKind.Remainder when _codeArith => Arith("%", l, r, b.Type, b.Syntax, b.IsChecked),
                        BinaryOperatorKind.Add => new KOp("+", l, r),
                        BinaryOperatorKind.Subtract => new KOp("-", l, r),
                        BinaryOperatorKind.Multiply => new KOp("*", l, r),
                        BinaryOperatorKind.Divide => new KArith { Op = "/", Left = l, Right = r, Type = b.Type, Mode = KMode.Math, At = b.Syntax },
                        BinaryOperatorKind.Remainder => new KArith { Op = "%", Left = l, Right = r, Type = b.Type, Mode = KMode.Math, At = b.Syntax },
                        BinaryOperatorKind.Equals => new KOp("==", l, r),
                        BinaryOperatorKind.NotEquals => new KOp("!=", l, r),
                        BinaryOperatorKind.LessThan => new KOp("<", l, r),
                        BinaryOperatorKind.LessThanOrEqual => new KOp("<=", l, r),
                        BinaryOperatorKind.GreaterThan => new KOp(">", l, r),
                        BinaryOperatorKind.GreaterThanOrEqual => new KOp(">=", l, r),
                        BinaryOperatorKind.ConditionalAnd => new KOp("&&", l, r),
                        BinaryOperatorKind.ConditionalOr => new KOp("||", l, r),
                        BinaryOperatorKind.And => new KOp("&", l, r),
                        BinaryOperatorKind.Or => new KOp("|", l, r),
                        BinaryOperatorKind.ExclusiveOr => new KOp("!=", l, r),
                        _ => throw new NotTranslated("the operator " + b.OperatorKind),
                    };
                }
                case IArrayElementReferenceOperation el when IsArray(el.ArrayReference.Type) && el.Indices.Length == 1:
                    return new KElem { Array = Spec(el.ArrayReference, result), Index = Spec(el.Indices[0], result), ArrayType = el.ArrayReference.Type, InSpec = true, At = el.Syntax, ArrayAt = el.ArrayReference.Syntax };
                case IPropertyReferenceOperation pr when pr.Property.Name == "Length" && IsArray(pr.Instance?.Type):
                    return new KLen { Array = Spec(pr.Instance, result), InSpec = true, At = pr.Syntax, ArrayAt = pr.Instance.Syntax };
                case IInvocationOperation acc when SpecSymbols.IsSpecClass(acc.TargetMethod.ContainingType) && acc.TargetMethod.Name == "Acc" &&
                                                   acc.Arguments.Length == 1 && IsOwnedClass(Unconverted(acc.Arguments[0].Value).Type):
                {
                    var target = Unconverted(acc.Arguments[0].Value);
                    _p.UsesPerm = true;
                    return new KAcc { Obj = Spec(target, result), Type = target.Type, At = acc.Syntax };
                }
                case IInvocationOperation fa when SpecSymbols.IsSpecClass(fa.TargetMethod.ContainingType) && fa.TargetMethod.Name == "Acc" &&
                                                  fa.Arguments.Length == 2 && IsOwnedClass(Unconverted(fa.Arguments[0].Value).Type):
                {
                    var target = Unconverted(fa.Arguments[0].Value);
                    // (only of a sealed class without an [Invariant], and not an [Owns] field: CsVerify's engine reports the rest)
                    if (!(fa.Arguments[1].Value.ConstantValue is { HasValue: true, Value: string name }) || !(target.Type is INamedTypeSymbol { IsSealed: true } t) ||
                        DataTypes.Invariants(t).Any() || !(WholeFields(t).FirstOrDefault(x => x.Name == name) is ISymbol field))
                        throw new NotTranslated("a Spec.Acc of a field CsVerify's engine rejects");
                    _p.UsesPerm = true;
                    return new KFieldAcc { Obj = Spec(target, result), Field = field, Type = target.Type, At = fa.Syntax };
                }
                case IInvocationOperation pc when SpecSymbols.IsPredicate(pc.TargetMethod.OriginalDefinition) && pc.TargetMethod.IsStatic:
                    _p.UsesPerm = true;
                    _p.Preds.Add(pc.TargetMethod.OriginalDefinition);
                    return new KInst { Pred = pc.TargetMethod.OriginalDefinition, Args = pc.Arguments.OrderBy(a => a.Parameter.Ordinal).Select(a => Spec(a.Value, result)).ToArray(), At = pc.Syntax };
                case IInvocationOperation inv when SpecSymbols.IsSpecClass(inv.TargetMethod.ContainingType):
                    switch (inv.TargetMethod.Name)
                    {
                        case "Old": return new KOp("old", Spec(inv.Arguments[0].Value, result));
                        // (allocated during the call)
                        case "Fresh" when IsRef(Unconverted(inv.Arguments[0].Value).Type):
                            return new KOp("!", new KOp("old", new KOp("sel", new KVar("$Alloc"), Spec(Unconverted(inv.Arguments[0].Value), result))));
                        case "Acc" or "AccRead" when IsArray(Unconverted(inv.Arguments[0].Value).Type) && inv.Arguments.Length is 1 or 3:
                        {
                            var arr = Spec(Unconverted(inv.Arguments[0].Value), result);
                            _p.UsesPerm = true;
                            return new KCells
                            {
                                Arr = arr, Read = inv.TargetMethod.Name == "AccRead", At = inv.Syntax,
                                Lo = inv.Arguments.Length == 1 ? new KLit("0") : Spec(inv.Arguments[1].Value, result),
                                Hi = inv.Arguments.Length == 1 ? new KOp("len", arr) : Spec(inv.Arguments[2].Value, result),
                            };
                        }
                        case "Result": return new KVar("result");
                        case "Forall": case "Exists" when inv.Arguments.Length == 3:
                        {
                            var lo = Spec(inv.Arguments[0].Value, result);
                            var hi = Spec(inv.Arguments[1].Value, result);
                            var fn = (inv.Arguments[2].Value as IDelegateCreationOperation)?.Target as IAnonymousFunctionOperation
                                     ?? throw new NotTranslated("a quantifier without a lambda");
                            if (!(fn.Body.Operations.Length == 1 && fn.Body.Operations[0] is IReturnOperation ret)) throw new NotTranslated("a quantifier's body");
                            var q = "q$" + fn.Symbol.Parameters[0].Name;
                            return new KQuant
                            {
                                Forall = inv.TargetMethod.Name == "Forall", Var = q,
                                Range = new KOp("&&", new KOp("<=", lo, new KVar(q)), new KOp("<", new KVar(q), hi)),
                                Body = Spec(ret.ReturnedValue, result),
                            };
                        }
                        default: throw new NotTranslated("Spec." + inv.TargetMethod.Name + " in a specification");
                    }
                case IInvocationOperation fn when _isFunction(fn.TargetMethod) && (fn.TargetMethod.IsStatic || fn.Instance != null && !fn.TargetMethod.IsVirtual && !fn.TargetMethod.IsAbstract && !fn.TargetMethod.IsOverride):
                {
                    bool onThis = fn.Instance is IInstanceReferenceOperation;
                    return new KFnCall
                    {
                        Callee = fn.TargetMethod.OriginalDefinition, Receiver = fn.Instance == null ? null : Spec(fn.Instance, result), ReceiverIsThis = onThis, ReceiverAt = fn.Instance?.Syntax,
                        Args = fn.Arguments.OrderBy(a => a.Parameter.Ordinal).Select(a => Spec(a.Value, result)).ToArray(), At = fn.Syntax,
                    };
                }
                default:
                    throw new NotTranslated("in a specification: " + e.Kind + " '" + e.Syntax + "'");
            }
        }
    }
}
