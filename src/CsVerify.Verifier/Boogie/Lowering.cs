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
        private readonly Func<string, string> _literal;
        private readonly Func<IMethodSymbol, Contract> _contractOf;
        private readonly KProcedure _p;
        private KBlock _block;
        private int _temps;

        private Lowering(IMethodSymbol m, Contract contract, SyntaxNode decl, SemanticModel model, MethodResult result,
                         Func<IMethodSymbol, bool> isProcedure, Func<IMethodSymbol, bool> isFunction, Func<string, string> literal, Func<IMethodSymbol, Contract> contractOf)
        {
            _m = m; _contract = contract; _decl = decl; _model = model; _isProcedure = isProcedure; _isFunction = isFunction;
            _literal = literal; _contractOf = contractOf;
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
                                       Func<IMethodSymbol, bool> isProcedure, Func<IMethodSymbol, bool> isFunction, Func<string, string> literal = null, Func<IMethodSymbol, Contract> contractOf = null) =>
            new Lowering(m, contract, decl, model, result, isProcedure, isFunction, literal, contractOf).Run();

        /// <summary>
        /// A [Pure] member of string whose stub contract the library gives (its parameters and result in the subset): a
        /// function of its arguments, which its contract describes.
        /// </summary>
        private bool IsStub(IMethodSymbol m) =>
            IsString(m.ContainingType) && _contractOf?.Invoke(m) is Contract c && c.IsStub && c.IsPure && !m.ReturnsVoid && InSubset(m.ReturnType) &&
            m.Parameters.All(x => x.RefKind == RefKind.None && InSubset(x.Type)) && c.Stub.Parameters.All(x => x.RefKind == RefKind.None && InSubset(x.Type));

        /// <summary>A callee's contract alone (its requires and its measure, over its parameters): what a call of it is checked against.</summary>
        public static KProcedure Signature(IMethodSymbol m, Contract contract, Func<IMethodSymbol, bool> isFunction, Func<string, string> literal = null, Func<IMethodSymbol, Contract> contractOf = null)
        {
            var l = new Lowering(m, contract, null, null, null, _ => false, isFunction, literal, contractOf);
            // (the permissions its postconditions give back, and a predicate's body, for folding and unfolding it)
            ContractOf(l, contract);
            if (contract.Modifies != null) l._p.Frame = l.Spec(contract.Modifies, null);
            if ((SpecSymbols.IsPredicate(m) || isFunction(m) && !Engine.IsOverridable(m)) && contract.PureBody != null) l._p.FunctionBody = l.Spec(contract.PureBody, null);
            return l._p;
        }

        /// <summary>
        /// The contract: its requires, its ensures (an inherited one where its precondition was weakened: promised where the
        /// base's held on entry), its measure; an override's own precondition and each base's, and the bases' frames.
        /// </summary>
        private static void ContractOf(Lowering l, Contract contract)
        {
            KExpr And(IEnumerable<KExpr> xs) => xs.DefaultIfEmpty(new KLit("true")).Aggregate((a, b) => new KOp("&&", a, b));
            foreach (var r in contract.Requires) l._p.Requires.Add(new KSpec { Expr = l.Spec(r, null), At = r.Syntax });
            foreach (var e in contract.Ensures)
            {
                var post = l.Spec(e.Expr, e.ResultParameter);
                if (e.Guard != null) post = new KOp("==>", new KOp("old", And(e.Guard.Select(g => l.Spec(g, null)))), post);
                l._p.Ensures.Add(new KSpec { Expr = post, At = e.Syntax });
            }
            if (contract.Decreases != null) l._p.Decreases = contract.Decreases.Select(d => l.Spec(d, null)).ToList();
            if (contract.Reads != null) l._p.ReadsFrame = l.Spec(contract.Reads, null);
            if (contract.OwnRequires.Count > 0)
            {
                l._p.OwnRequires = contract.OwnRequires.Select(r => l.Spec(r, null)).ToList();
                foreach (var b in contract.Bases) l._p.BaseRequires.Add((b.Method, b.Requires.Select(r => l.Spec(r, null)).ToList()));
            }
            foreach (var (b, frame) in contract.BaseModifies.Where(x => !ReferenceEquals(x.Frame, contract.Modifies)))
                l._p.BaseFrames.Add((b.Method, l.Spec(frame, null)));
        }

        /// <summary>
        /// A virtual member called on this: where this class (or a base of it) overrides it and nothing below may again
        /// (the override sealed, or the class), the call is of that override, as CsVerify's engine reads it.
        /// </summary>
        private IMethodSymbol OnThis(IMethodSymbol m, IOperation instance)
        {
            m = m.OriginalDefinition;
            if (!(instance is IInstanceReferenceOperation) || !Engine.IsOverridable(m) || _m.ContainingType == null) return m;
            for (var t = _m.ContainingType; t != null; t = t.BaseType)
                foreach (var o in t.GetMembers(m.Name).OfType<IMethodSymbol>())
                    for (var b = o.OverriddenMethod; b != null; b = b.OverriddenMethod)
                        if (SymbolEqualityComparer.Default.Equals(b.OriginalDefinition, m))
                            return o.IsSealed || _m.ContainingType.IsSealed ? o.OriginalDefinition : m;
            return m;
        }

        /// <summary>A contract class's member means the member it specifies (the one it overrides or implements).</summary>
        private static IPropertySymbol Specified(IPropertySymbol p)
        {
            if (p == null || !SpecSymbols.IsContractsClass(p.ContainingType)) return p;
            if (p.OverriddenProperty != null) return p.OverriddenProperty;
            var target = SpecSymbols.ContractClassTarget(p.ContainingType);
            return target?.GetMembers(p.Name).OfType<IPropertySymbol>().FirstOrDefault() ?? p;
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
            // (Dafny's dynamic frames: what it may write. An [Owned] class's objects are framed by their views instead)
            if (_contract.Modifies != null)
            {
                if (SpecSymbols.IsOwned(_m.ContainingType)) throw new NotTranslated("Spec.Modifies of an [Owned] class's method");
                _p.Frame = Spec(_contract.Modifies, null);
            }
            // (Viper's functions over predicates read their footprint: not yet)
            _p.UsesPerm |= _contract.Requires.Any(HasAtoms) || _contract.Ensures.Any(e => HasAtoms(e.Expr));
            ContractOf(this, _contract);
            // (an abstract member: its contract alone)
            if (_m.IsAbstract) { _p.Abstract = true; return _p; }
            var cfg = _model.GetOperation(_decl) switch
            {
                IMethodBodyOperation body => ControlFlowGraph.Create(body),
                IConstructorBodyOperation body => ControlFlowGraph.Create(body),
                // (an accessor, an expression-bodied property's getter)
                IBlockOperation block => ControlFlowGraph.Create(block),
                _ => throw new NotTranslated("no body"),
            };
            if (cfg.Root.NestedRegions.SelectMany(AllRegions).Concat(cfg.Root.NestedRegions).Any(r => r.Kind != ControlFlowRegionKind.LocalLifetime))
                throw new NotTranslated("try, catch or finally");
            // (a function's definition is its body: not one an override may answer, which is of its contract alone)
            if (_isFunction(_m) && _contract.PureBody != null && !Engine.IsOverridable(_m)) _p.FunctionBody = Spec(_contract.PureBody, null);
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
                case IInvocationOperation chain when chain.TargetMethod.MethodKind == MethodKind.Constructor && chain.Instance is IInstanceReferenceOperation && _p.IsCtor:
                {
                    // base(...): the base class's constructor, on this object
                    var ctor = chain.TargetMethod.OriginalDefinition;
                    // (an implicit one of a class without field initializers does nothing)
                    if (ctor.IsImplicitlyDeclared && !ctor.ContainingType.GetMembers().Any(x => !x.IsStatic && x.DeclaringSyntaxReferences.Any(r =>
                            r.GetSyntax() is VariableDeclaratorSyntax { Initializer: not null } || r.GetSyntax() is PropertyDeclarationSyntax { Initializer: not null }))) return;
                    if (!_isProcedure(ctor)) throw new NotTranslated("a call of " + ctor.ContainingType.Name + "'s constructor");
                    _p.Calls.Add(ctor);
                    var ordered = chain.Arguments.OrderBy(a => a.Parameter.Ordinal).ToList();
                    var args = Operands(ordered.Select(a => a.Value).ToArray());
                    Emit(new KCall { Callee = ctor, Receiver = new KVar("this"), ReceiverIsThis = true, Args = args, ArgsAt = ordered.Select(a => a.Value.Syntax).ToArray(), At = chain.Syntax });
                    return;
                }
                case IInvocationOperation own when SpecSymbols.IsCsVerifyType(own.TargetMethod.ContainingType, "Own"):
                    Own(own);
                    return;
                case IInvocationOperation inv when SpecSymbols.IsSpecClass(inv.TargetMethod.ContainingType):
                    switch (inv.TargetMethod.Name)
                    {
                        case "Requires": case "Ensures": case "Invariant": case "Decreases": case "Modifies": return; // (the contract; the loop heads)
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
                    bool nonNull = IsNullable(l.Local.Type) && NotNullable(l.Local.Type);
                    Emit(new KAssign { Var = Declare(Local(l.Local), l.Local.Type), Value = value,
                                       NotNullAt = nonNull ? l.Syntax.Parent ?? l.Syntax : null, NotNullName = l.Local.Name });
                    return;
                }
                // (a computed property: its setter, called with the value)
                case IPropertyReferenceOperation sp when IsComputed(sp.Property) && sp.Property.SetMethod != null:
                    Invoke(sp.Property.SetMethod, sp.Instance, sp.Arguments, sp.Syntax, value);
                    return;
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
            if (symbol.IsStatic && IsNullable(FieldType(symbol)) && NotNullable(FieldType(symbol))) throw new NotTranslated("a non-nullable static field");
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
                case { ConstantValue: { HasValue: true } cv } when Scalar(e.Type) || IsNullable(e.Type): return Constant(cv.Value, e.Type);
                case ILocalReferenceOperation l when InSubset(l.Local.Type) && l.Local.RefKind == RefKind.None: return new KVar(Declare(Local(l.Local), l.Local.Type));
                case IParameterReferenceOperation p when InSubset(p.Parameter.Type) && p.Parameter.RefKind is RefKind.None or RefKind.Ref or RefKind.Out: return new KVar(Local(p.Parameter));
                case IInvocationOperation own when SpecSymbols.IsCsVerifyType(own.TargetMethod.ContainingType, "Own"):
                    return Own(own);
                // (a quantifier in code, a [Pure] or ghost function's body: mathematics, its reads checked over its range)
                case IInvocationOperation q when SpecSymbols.IsSpecClass(q.TargetMethod.ContainingType) && q.TargetMethod.Name is "Forall" or "Exists" && q.Arguments.Length == 3:
                    // (read as the source has it: the graph lowers its lambda)
                    return Spec(_model.GetOperation(q.Syntax) as IInvocationOperation ?? q, null);
                case IFlowCaptureReferenceOperation r: return new KVar(Capture(r.Id, r.Type));
                case IInstanceReferenceOperation { ReferenceKind: InstanceReferenceKind.ContainingTypeInstance } when !_p.IsCtor:
                    return new KVar("this");
                case IInstanceReferenceOperation _:
                    throw new NotTranslated(_p.IsCtor ? "this, escaping its constructor" : "an instance reference");
                // (a computed property: its getter, called)
                case IPropertyReferenceOperation cp when IsComputed(cp.Property) && cp.Property.GetMethod != null:
                    return Invoke(cp.Property.GetMethod, cp.Instance, cp.Arguments, cp.Syntax, null);
                case IFieldReferenceOperation _:
                case IPropertyReferenceOperation pf when !(pf.Property.Name == "Length" && IsArray(pf.Instance?.Type)) && !IsString(pf.Instance?.Type):
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
                case IPropertyReferenceOperation sl when sl.Property.Name == "Length" && IsString(sl.Instance?.Type):
                    return new KLen { String = true, Array = Expr(sl.Instance), At = sl.Syntax, ArrayAt = sl.Instance.Syntax };
                case IPropertyReferenceOperation sc when sc.Property.IsIndexer && IsString(sc.Instance?.Type) && sc.Arguments.Length == 1:
                {
                    var v = Operands(sc.Instance, sc.Arguments[0].Value);
                    return new KElem { String = true, Array = v[0], Index = v[1], At = sc.Syntax, ArrayAt = sc.Instance.Syntax };
                }
                case IBinaryOperation sb when IsString(sb.LeftOperand.Type) && IsString(sb.RightOperand.Type) &&
                                             (sb.OperatorMethod == null || IsString(sb.OperatorMethod.ContainingType)) &&
                                             sb.OperatorKind is BinaryOperatorKind.Equals or BinaryOperatorKind.NotEquals or BinaryOperatorKind.Add:
                {
                    var v = Operands(sb.LeftOperand, sb.RightOperand);
                    return StringBinary(sb.OperatorKind, v[0], v[1]);
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
                    if (e.ConstantValue.HasValue && e.ConstantValue.Value == null && IsNullable(e.Type)) return new KLit("null");
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

        private KExpr Constant(object v, ITypeSymbol type)
        {
            if (v is bool x) return new KLit(x ? "true" : "false");
            if (v == null && IsNullable(type)) return new KLit("null");
            // (a string literal: one value per contents)
            if (v is string str) return new KVar(_literal?.Invoke(str) ?? throw new NotTranslated("a string literal"));
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

        /// <summary>== != and + of strings: equality of values (characters), and concatenation (null counts as empty).</summary>
        private static KExpr StringBinary(BinaryOperatorKind k, KExpr l, KExpr r) => k switch
        {
            BinaryOperatorKind.Equals => new KOp("streq", l, r),
            BinaryOperatorKind.NotEquals => new KOp("!", new KOp("streq", l, r)),
            _ => new KOp("scat", l, r),
        };

        /// <summary>string.Equals(a, b), a.Equals(b), ordinally (StringComparison.Ordinal, or none); null for any other call.</summary>
        private (IOperation a, IOperation b)? StringEquals(IInvocationOperation inv)
        {
            var m = inv.TargetMethod;
            if (m.Name != "Equals" || !IsString(m.ContainingType)) return null;
            var strings = m.Parameters.TakeWhile(p => IsString(p.Type)).Count();
            var rest = m.Parameters.Skip(strings).ToList();
            if (rest.Count > 1 || rest.Count == 1 && !(rest[0].Type.Name == "StringComparison" &&
                inv.Arguments.First(a => a.Parameter.Ordinal == rest[0].Ordinal).Value.ConstantValue is { HasValue: true, Value: 4 })) return null;
            if (m.IsStatic && strings == 2) return (inv.Arguments.First(a => a.Parameter.Ordinal == 0).Value, inv.Arguments.First(a => a.Parameter.Ordinal == 1).Value);
            if (!m.IsStatic && strings == 1 && inv.Instance != null) return (inv.Instance, inv.Arguments.First(a => a.Parameter.Ordinal == 0).Value);
            return null;
        }

        /// <summary>A stub's call: its receiver (not null) and arguments; its precondition checked, its value the function's.</summary>
        private KFnCall StubCall(IInvocationOperation call, Func<IOperation, KExpr> eval)
        {
            _p.Stubs.Add(call.TargetMethod.OriginalDefinition);
            var ordered = call.Arguments.OrderBy(a => a.Parameter.Ordinal).Select(a => a.Value).ToList();
            KExpr receiver = null;
            KExpr[] args;
            if (eval == null)
            {
                var v = Operands((call.Instance == null ? new IOperation[0] : new[] { call.Instance }).Concat(ordered).ToArray());
                receiver = call.Instance == null ? null : v[0];
                args = call.Instance == null ? v : v.Skip(1).ToArray();
            }
            else
            {
                receiver = call.Instance == null ? null : eval(call.Instance);
                args = ordered.Select(eval).ToArray();
            }
            return new KFnCall { Callee = call.TargetMethod.OriginalDefinition, Receiver = receiver, ReceiverAt = call.Instance?.Syntax, Args = args, At = call.Syntax, Stub = true };
        }

        private KExpr Call(IInvocationOperation call)
        {
            var callee = call.TargetMethod.OriginalDefinition;
            if (StringEquals(call) is (IOperation ea, IOperation eb))
            {
                var v = Operands(ea, eb);
                if (call.Instance == null) return new KOp("streq", v[0], v[1]);
                // (a.Equals(b) dereferences a: its length, read, is checked not null, and is never negative)
                var deref = new KLen { String = true, Array = v[0], At = call.Syntax, ArrayAt = call.Instance.Syntax };
                return new KOp("&&", new KOp(">=", deref, new KLit("0")), new KOp("streq", v[0], v[1]));
            }
            if (!_isProcedure(callee) && IsStub(callee)) return StubCall(call, null);
            return Invoke(callee, call.Instance, call.Arguments, call.Syntax, null);
        }

        /// <summary>
        /// A call of a procedure: a method, or a property's accessor (its indices the arguments, and a setter's value
        /// after them). A virtual one is of the member as bound here, whose contract every override keeps.
        /// </summary>
        private KExpr Invoke(IMethodSymbol callee, IOperation instance, IReadOnlyList<IArgumentOperation> arguments, SyntaxNode at, KExpr value)
        {
            callee = callee.OriginalDefinition;
            if (!_isProcedure(callee)) throw new NotTranslated("a call of " + callee.Name);
            _p.Calls.Add(callee);
            var ordered = arguments.OrderBy(a => a.Parameter.Ordinal).ToList();
            if (!callee.IsStatic && instance == null) throw new NotTranslated("a call of " + callee.Name + " without its receiver");
            var call = (Instance: instance, Syntax: at);
            bool onThis = call.Instance is IInstanceReferenceOperation;
            // (a ref or out argument is a variable, which gets what the callee gives back; an out one isn't read)
            var refOuts = ordered.Where(a => a.Parameter.RefKind != RefKind.None).Select(a => (a.Parameter.Ordinal, RefVariable(a))).ToList();
            var ins = ordered.Where(a => a.Parameter.RefKind != RefKind.Out).ToList();
            var operands = (call.Instance == null || onThis ? Enumerable.Empty<IOperation>() : new[] { call.Instance }).Concat(ins.Select(a => a.Value)).ToArray();
            var values = Operands(operands);
            var receiver = call.Instance == null ? null : onThis ? Expr(call.Instance) : values[0];
            var inValues = call.Instance == null || onThis ? values : values.Skip(1).ToArray();
            var args = new KExpr[ordered.Count + (value == null ? 0 : 1)];
            for (int k = 0; k < ins.Count; k++) args[ins[k].Parameter.Ordinal] = inValues[k];
            if (value != null) args[ordered.Count] = value;
            foreach (var (ordinal, v) in refOuts) args[ordinal] ??= new KVar(v);
            if (refOuts.Any()) _p.UsesPerm |= ordered.Any(a => IsView(a.Parameter.Type));
            if (ordered.Any(a => IsView(a.Parameter.Type)) || IsOwnedClass(callee.ContainingType) && !callee.IsStatic) _p.UsesPerm = true;
            var result = callee.ReturnsVoid ? null : Declare("t$" + _temps++, callee.ReturnType);
            Emit(new KCall { Callee = callee, Receiver = receiver, ReceiverIsThis = onThis, ReceiverAt = call.Instance?.Syntax,
                             Args = args, ArgsAt = ordered.Select(a => a.Value.Syntax).Concat(value == null ? new SyntaxNode[0] : new[] { at }).ToArray(),
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
            // (ObjSet.Empty: no objects)
            if ((e is IFieldReferenceOperation { Field.Name: "Empty", Instance: null } || e is IPropertyReferenceOperation { Property.Name: "Empty", Instance: null }) && IsObjSet(e.Type))
                return new KLit("(lambda r$: Ref :: false)");
            switch (e)
            {
                case IDelegateCreationOperation d: return Spec(d.Target, result);
                case IAnonymousFunctionOperation fn when fn.Body.Operations.Length == 1 && fn.Body.Operations[0] is IReturnOperation ret:
                    return Spec(ret.ReturnedValue, fn.Symbol.Parameters.FirstOrDefault() ?? result);
                case { ConstantValue: { HasValue: true } cv } when Scalar(e.Type) || IsNullable(e.Type): return Constant(cv.Value, e.Type);
                case IParameterReferenceOperation p when result != null && SymbolEqualityComparer.Default.Equals(p.Parameter, result): return new KVar("result");
                case IParameterReferenceOperation p when p.Parameter.ContainingSymbol is IMethodSymbol { MethodKind: MethodKind.AnonymousFunction }:
                    return new KVar("q$" + p.Parameter.Name); // (a quantifier's variable)
                // (a base's contract, inherited: its parameters are this method's, by position)
                case IParameterReferenceOperation p when InSubset(p.Parameter.Type) && !_contract.IsStub && p.Parameter.ContainingSymbol is IMethodSymbol pm &&
                                                         _contract.Aliases.Any(a => SymbolEqualityComparer.Default.Equals(a.OriginalDefinition, pm.OriginalDefinition)) &&
                                                         p.Parameter.Ordinal < _m.Parameters.Length:
                    return new KVar(Local(_m.Parameters[p.Parameter.Ordinal]));
                case IParameterReferenceOperation p when InSubset(p.Parameter.Type): return new KVar(Local(p.Parameter));
                case ILocalReferenceOperation l when InSubset(l.Local.Type): return new KVar(Declare(Local(l.Local), l.Local.Type));
                case IInstanceReferenceOperation { ReferenceKind: InstanceReferenceKind.ContainingTypeInstance }: return new KVar("this");
                // (a view's object: v.Obj.Value)
                case IPropertyReferenceOperation { Property.Name: "Value", Instance: IPropertyReferenceOperation { Property.Name: "Obj" } obj } when IsView(obj.Instance?.Type):
                    return Spec(obj.Instance, result);
                // (a [Pure] computed property: its getter, a function; in a contract class, the member it specifies)
                case IPropertyReferenceOperation cp when Specified(cp.Property) is IPropertySymbol sp && IsComputed(sp) && sp.GetMethod != null && _isFunction(sp.GetMethod):
                    return new KFnCall
                    {
                        Callee = OnThis(Specified(cp.Property).GetMethod, cp.Instance), Receiver = cp.Instance == null ? null : Spec(cp.Instance, result),
                        ReceiverIsThis = cp.Instance is IInstanceReferenceOperation, ReceiverAt = cp.Instance?.Syntax,
                        Args = cp.Arguments.OrderBy(a => a.Parameter.Ordinal).Select(a => Spec(a.Value, result)).ToArray(), At = cp.Syntax,
                    };
                case IFieldReferenceOperation _:
                case IPropertyReferenceOperation pf when !(pf.Property.Name == "Length" && IsArray(pf.Instance?.Type)) && !IsString(pf.Instance?.Type):
                {
                    var (field, instance, onThis, instanceAt) = FieldOf(e, result, spec: true);
                    return new KField { Field = field, Instance = instance, OnThis = onThis, At = e.Syntax, InstanceAt = instanceAt };
                }
                case IParenthesizedOperation par: return Spec(par.Operand, result);
                case IConversionOperation conv when conv.Conversion.IsIdentity || IsIntegral(conv.Type) && IsIntegral(conv.Operand.Type) && conv.Conversion.IsNumeric &&
                                                    (conv.IsImplicit || Range(conv.Operand.Type).lo >= Range(conv.Type).lo && Range(conv.Operand.Type).hi <= Range(conv.Type).hi):
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
                case IPropertyReferenceOperation sl when sl.Property.Name == "Length" && IsString(sl.Instance?.Type):
                    return new KLen { String = true, Array = Spec(sl.Instance, result), InSpec = true, At = sl.Syntax, ArrayAt = sl.Instance.Syntax };
                case IPropertyReferenceOperation sc when sc.Property.IsIndexer && IsString(sc.Instance?.Type) && sc.Arguments.Length == 1:
                    return new KElem { String = true, Array = Spec(sc.Instance, result), Index = Spec(sc.Arguments[0].Value, result), InSpec = true, At = sc.Syntax, ArrayAt = sc.Instance.Syntax };
                case IBinaryOperation sb when IsString(sb.LeftOperand.Type) && IsString(sb.RightOperand.Type) &&
                                             (sb.OperatorMethod == null || IsString(sb.OperatorMethod.ContainingType)) &&
                                             sb.OperatorKind is BinaryOperatorKind.Equals or BinaryOperatorKind.NotEquals or BinaryOperatorKind.Add:
                    return StringBinary(sb.OperatorKind, Spec(sb.LeftOperand, result), Spec(sb.RightOperand, result));
                case IInvocationOperation se when StringEquals(se) is (IOperation ea, IOperation eb):
                    return new KOp("streq", Spec(ea, result), Spec(eb, result));
                case IInvocationOperation st when !_isFunction(st.TargetMethod) && IsStub(st.TargetMethod.OriginalDefinition):
                    return StubCall(st, x => Spec(x, result));
                case IPropertyReferenceOperation pr when pr.Property.Name == "Length" && IsArray(pr.Instance?.Type):
                    return new KLen { Array = Spec(pr.Instance, result), InSpec = true, At = pr.Syntax, ArrayAt = pr.Instance.Syntax };
                // (ghost sets of objects)
                case IPropertyReferenceOperation { Property.Name: "Empty" } empty when IsObjSet(empty.Type) && empty.Instance == null:
                    return new KLit("(lambda r$: Ref :: false)");
                case IInvocationOperation of when IsObjSet(of.TargetMethod.ContainingType) && of.TargetMethod.Name == "Of" && of.Arguments.Length == 1 &&
                                                  (IsRef(Unconverted(of.Arguments[0].Value).Type) || Unconverted(of.Arguments[0].Value) is IInstanceReferenceOperation):
                    return new KOp("set.of", Spec(Unconverted(of.Arguments[0].Value), result));
                case IInvocationOperation add when IsObjSet(add.TargetMethod.ContainingType) && add.TargetMethod.Name == "Add" && add.Instance != null && IsRef(Unconverted(add.Arguments[0].Value).Type):
                    return new KOp("set.add", Spec(add.Instance, result), Spec(Unconverted(add.Arguments[0].Value), result));
                case IInvocationOperation has when IsObjSet(has.TargetMethod.ContainingType) && has.TargetMethod.Name == "Contains" && has.Instance != null && IsRef(Unconverted(has.Arguments[0].Value).Type):
                    return new KOp("sel", Spec(has.Instance, result), Spec(Unconverted(has.Arguments[0].Value), result));
                case IInvocationOperation union when IsObjSet(union.TargetMethod.ContainingType) && union.TargetMethod.Name == "Union" && union.Instance != null:
                    return new KOp("set.union", Spec(union.Instance, result), Spec(union.Arguments[0].Value, result));
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
                            // (its argument read now: only the allocated set is as it was)
                            return new KOp("&&", new KOp("!=", Spec(Unconverted(inv.Arguments[0].Value), result), new KLit("null")),
                                new KOp("!", new KOp("sel", new KOp("old", new KVar("$Alloc")), Spec(Unconverted(inv.Arguments[0].Value), result))));
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
