using System;
using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Operations;
using static CsVerify.Verifier.Boogie.KernelTypes;
using static CsVerify.Verifier.Boogie.KOp;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>Contracts: a method's requires, ensures, frames and measures as kernel specifications; callees' signatures; predicates and invariants.</summary>
    internal sealed partial class Lowering
    {
        /// <summary>
        /// A data type's invariant's body, of the value "this" (its own fields only: an invariant that calls anything, or
        /// reads anything but its fields, isn't translated).
        /// </summary>
        public static KExpr InvariantBody(IMethodSymbol inv, Func<IMethodSymbol, bool> isFunction, Func<string, string> literal, Func<IMethodSymbol, Contract> contractOf)
        {
            var c = contractOf(inv);
            if (c.PureBody == null)
            {
                throw new NotTranslated("an invariant without an expression body: " + inv.Name);
            }
            if (c.PureBody.DescendantsAndSelf().Any(o => o is IInvocationOperation call && !IsOfValues(call, isFunction) || o is IFieldReferenceOperation ||
                                                       o is IPropertyReferenceOperation pr && !(pr.Instance != null && IsData(pr.Instance.Type) && DataTypes.IsPositional(pr.Property.OriginalDefinition)) &&
                                                       !IsViewsObject(pr) && !(pr.Property.Name == "Value" && pr.Instance is IPropertyReferenceOperation inner && IsViewsObject(inner))))
            {
                // (one that reads mutable state is reported, from its declaration, by StaticChecks;
                // a value's validity then says nothing of it, which is sound, and a construction still checks it)
                return KLit.True;
            }
            var l = new Lowering(inv, c, null, c.Model, null, _ => false, isFunction, literal, contractOf);
            return l.Spec(c.PureBody, null);
        }

        // (a function it calls is of values alone: static, its parameters data or scalars, as the record's are)
        private static bool IsOfValues(IInvocationOperation call, Func<IMethodSymbol, bool> isFunction) => IntegerMath(call) ||
            isFunction(call.TargetMethod) && call.TargetMethod.IsStatic && call.TargetMethod.Parameters.All(x => x.RefKind == RefKind.None && (Scalar(x.Type) || IsData(x.Type)));

        /// <summary>
        /// A data case's field that its base record has: the argument its record header gives the base's primary
        /// constructor, over the case's own constructor parameters (Ind(Fact Prev) : Fact(Prev.N + 1, ...)).
        /// </summary>
        public static KExpr BaseArgument(INamedTypeSymbol c, IPropertySymbol prop, Func<IMethodSymbol, bool> isFunction, Func<string, string> literal, Func<IMethodSymbol, Contract> contractOf)
        {
            var def = DataTypes.Def(c);
            var decl = def.DeclaringSyntaxReferences.Select(r => r.GetSyntax()).OfType<RecordDeclarationSyntax>().FirstOrDefault();
            var baseType = decl?.BaseList?.Types.OfType<PrimaryConstructorBaseTypeSyntax>().FirstOrDefault() ?? throw new NotTranslated("a base field without its argument: " + prop.Name);
            var ctor = DataTypes.PrimaryConstructor(def);
            var model = KernelTypes.Compilation.GetSemanticModel(decl.SyntaxTree);
            var call = model.GetOperation(baseType)?.DescendantsAndSelf().OfType<IInvocationOperation>().FirstOrDefault(i => i.TargetMethod.MethodKind == MethodKind.Constructor)
                       ?? throw new NotTranslated("a base constructor call not found: " + c.Name);
            var arg = call.Arguments.FirstOrDefault(a => a.Parameter?.Name == prop.Name) ?? throw new NotTranslated("a base field not given by name: " + prop.Name);
            var l = new Lowering(ctor, contractOf(ctor), decl, model, null, _ => false, isFunction, literal, contractOf);
            return l.Spec(arg.Value, null);
        }

        /// <summary>A callee's contract alone (its requires and its measure, over its parameters): what a call of it is checked against.</summary>
        public static KProcedure Signature(IMethodSymbol m, Contract contract, Func<IMethodSymbol, bool> isFunction, Func<string, string> literal = null, Func<IMethodSymbol, Contract> contractOf = null)
        {
            var l = new Lowering(m, contract, null, null, null, _ => false, isFunction, literal, contractOf);
            // (a local function's: what it captures, inputs of its own, which its contract may name)
            if (IsNested(m) && KernelTypes.NestedGraphs != null && KernelTypes.NestedGraphs.TryGetValue(m.OriginalDefinition, out var lg))
            {
                l.Captures(lg);
            }
            // (the permissions its postconditions give back, and a predicate's body, for folding and unfolding it)
            ContractOf(l, contract);
            if (contract.Modifies != null)
            {
                l._p.Frame = l.Spec(contract.Modifies, null);
                l.LentRoots(contract.Modifies);
            }
            if ((SpecSymbols.IsPredicate(m) || isFunction(m) && !Engine.IsOverridable(m)) && contract.PureBody != null)
            {
                l._p.FunctionBody = l.Spec(contract.PureBody, null);
            }
            else if (isFunction(m) && !Engine.IsOverridable(m) && contract.PureStatements != null)
            {
                l._p.FunctionBody = l.PureStatements(contract.PureStatements, 0);
            }
            return l._p;
        }

        /// <summary>
        /// The contract: its requires, its ensures (an inherited one where its precondition was weakened: promised where the
        /// base's held on entry), its measure; an override's own precondition and each base's, and the bases' frames.
        /// </summary>
        private static void ContractOf(Lowering l, Contract contract)
        {
            foreach (var r in contract.Requires)
            {
                l._p.Requires.Add(KSpec.Of(l.Spec(r, null), r.Syntax));
            }
            foreach (var (type, cond, at) in contract.ThrowEnsures)
            {
                if (!IsException(type))
                {
                    throw new NotTranslated("Spec.EnsuresOnThrow of " + type);
                }
                l._p.ThrowEnsures.Add((type, l.Spec(cond, null), at));
                l._p.ExceptionTypes.Add(type);
            }
            foreach (var e in contract.Ensures)
            {
                var post = l.Spec(e.Expr, e.ResultParameter);
                if (e.Guard != null)
                {
                    post = Implies(Old(AndAll(e.Guard.Select(g => l.Spec(g, null)))), post);
                }
                l._p.Ensures.Add(KSpec.Of(post, e.Syntax));
            }
            // (a function over a predicate, with its body: its procedure gives its value, of the instance's snapshot, as
            // the body says where it unfolds it; so a call of it in code tells what a specification's use of it reads)
            if (l._m.IsStatic && l._isFunction(l._m) && contract.PureBody != null && contract.Requires.Any(HasAtoms) && l._m.DeclaringSyntaxReferences.Length > 0 &&
                l._m.DeclaringSyntaxReferences[0].GetSyntax().DescendantNodes().OfType<InvocationExpressionSyntax>().Any(i => i.Expression.ToString() == "Spec.Unfold"))
            {
                l._p.Ensures.Add(KSpec.Of(
                    at: l._m.DeclaringSyntaxReferences[0].GetSyntax(),
                    expr: Eq(new KVar("result"),
                   new KFnCall
                   {
                       Callee = l._m.OriginalDefinition,
                       Args = l._m.Parameters.Select(x => (KExpr)new KVar(Local(x))).ToArray(),
                       At = l._m.DeclaringSyntaxReferences[0].GetSyntax(),
                   })));
            }
            if (contract.Decreases != null)
            {
                l._p.Decreases = contract.Decreases.Select(d => l.Measure(d)).ToList();
            }
            // (a memory view parameter holds its cells: a Spec.Acc of them, taken, and given back where it's lent)
            var decl = l._m.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax();
            foreach (var p in l._m.Parameters.Where(x => IsMemView(x.Type)))
            {
                if (p.RefKind != RefKind.Out)
                {
                    foreach (var c in MemCells(new KVar(Local(p)), p.Type, decl))
                    {
                        l._p.Requires.Add(KSpec.Of(c, decl));
                    }
                }
                if (p.RefKind != RefKind.None)
                {
                    foreach (var c in MemCells(new KVar(Local(p)), p.Type, decl))
                    {
                        l._p.Ensures.Add(KSpec.Of(c, decl));
                    }
                }
            }
            if (Returns(l._m) is ITypeSymbol rt && IsMemView(rt))
            {
                foreach (var c in MemCells(new KVar("result"), rt, decl))
                {
                    l._p.Ensures.Add(KSpec.Of(c, decl));
                }
            }
            if (contract.Reads != null)
            {
                l._p.ReadsFrame = l.Spec(contract.Reads, null);
            }
            if (contract.OwnRequires.Count > 0)
            {
                l._p.OwnRequires = contract.OwnRequires.Select(r => l.Spec(r, null)).ToList();
                foreach (var b in contract.Bases)
                {
                    l._p.BaseRequires.Add((b.Method, b.Requires.Select(r => l.Spec(r, null)).ToList()));
                }
            }
            foreach (var (b, frame) in contract.BaseModifies.Where(x => !ReferenceEquals(x.Frame, contract.Modifies)))
            {
                l._p.BaseFrames.Add((b.Method, l.Spec(frame, null)));
            }
        }

        /// <summary>
        /// A virtual member called on this: where this class (or a base of it) overrides it and nothing below may again
        /// (the override sealed, or the class), the call is of that override.
        /// </summary>
        private IMethodSymbol OnThis(IMethodSymbol m, IOperation instance)
        {
            m = m.OriginalDefinition;
            if (!(instance is IInstanceReferenceOperation) || !Engine.IsOverridable(m) || _m.ContainingType == null)
            {
                return m;
            }
            for (var t = _m.ContainingType; t != null; t = t.BaseType)
            {
                foreach (var o in t.GetMembers(m.Name).OfType<IMethodSymbol>())
                {
                    for (var b = o.OverriddenMethod; b != null; b = b.OverriddenMethod)
                    {
                        if (SymbolEqualityComparer.Default.Equals(b.OriginalDefinition, m))
                        {
                            return o.IsSealed || _m.ContainingType.IsSealed ? o.OriginalDefinition : m;
                        }
                    }
                }
            }
            return m;
        }

        /// <summary>A contract class's member means the member it specifies (the one it overrides or implements).</summary>
        private static IPropertySymbol Specified(IPropertySymbol p)
        {
            if (p == null || !SpecSymbols.IsContractsClass(p.ContainingType))
            {
                return p;
            }
            if (p.OverriddenProperty != null)
            {
                return p.OverriddenProperty;
            }
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
            {
                throw new NotTranslated("a [Predicate] that isn't a static bool method of one expression");
            }
            // (ghost code: its arithmetic is mathematical, its reads and divisions checked)
            _p.IsPredicate = _p.UsesPerm = _p.Ghost = true;
            _codeArith = true;
            try
            {
                _p.FunctionBody = Spec(_contract.PureBody, null);
            }
            finally
            {
                _codeArith = false;
            }
            _p.Blocks.Add(KBlock.Of("b0", 0, jump: new KStop()));
            return _p;
        }

        /// <summary>In a predicate's own check: arithmetic is code's.</summary>
        private bool _codeArith;

        private bool _ownedModifies;

        /// <summary>Inside Spec.Old: a parameter the body assigns is the parameter, as it came in.</summary>
        private int _inOld;

        /// <summary>In a specification, a?.m's receiver, as m reads it.</summary>
        private readonly Stack<KExpr> _conditionalInstances = new Stack<KExpr>();

        /// <summary>A measure: a number, or a data value's rank (how deep it is).</summary>
        private KExpr Measure(IOperation d)
        {
            var v = Spec(d, null);
            return IsData(d.Type) ? new KOp("$rank", v) : v;
        }

        /// <summary>
        /// A [Pure] body of more than one expression, as one: local declarations
        /// bound in what follows, ifs as ?:, returns; Spec statements and lemmas skipped. Null where it's anything else
        /// (the function is then of its contract alone).
        /// </summary>
        private KExpr PureStatements(IReadOnlyList<IOperation> ops, int i)
        {
            if (i >= ops.Count)
            {
                return null;
            }
            var op = ops[i];
            try
            {
                switch (op)
                {
                    case IReturnOperation ret when ret.ReturnedValue != null:
                        return Spec(ret.ReturnedValue, null);
                    case IBlockOperation block:
                        return PureStatements(OperationsAfter(block, ops, i), 0);
                    case IVariableDeclarationGroupOperation group:
                    {
                        var binds = new List<(string, KExpr)>();
                        foreach (var decl in group.Declarations)
                        {
                            foreach (var v in decl.Declarators)
                            {
                                var init = v.Initializer?.Value ?? decl.Initializer?.Value;
                                if (init == null || !InSubset(v.Symbol.Type))
                                {
                                    return null;
                                }
                                binds.Add((Local(v.Symbol), Spec(init, null)));
                            }
                        }
                        var rest = PureStatements(ops, i + 1);
                        if (rest == null)
                        {
                            return null;
                        }
                        for (int k = binds.Count - 1; k >= 0; k--)
                        {
                            rest = KLet.Of(binds[k].Item1, binds[k].Item2, rest);
                        }
                        return rest;
                    }
                    case IConditionalOperation cond when cond.Type == null || cond.Type.SpecialType == SpecialType.System_Void:
                    {
                        var c = Spec(cond.Condition, null);
                        var yes = PureStatements(OperationsAfter(cond.WhenTrue, ops, i), 0);
                        var no = cond.WhenFalse != null ? PureStatements(OperationsAfter(cond.WhenFalse, ops, i), 0) : PureStatements(ops, i + 1);
                        return yes == null || no == null ? null : Ite(c, yes, no);
                    }
                    case IExpressionStatementOperation es when es.Operation is IInvocationOperation inv &&
                                                              (SpecSymbols.IsSpecClass(inv.TargetMethod.ContainingType) || _contractOf?.Invoke(inv.TargetMethod) is Contract lc && lc.IsLemma):
                        return PureStatements(ops, i + 1);
                    default:
                        return null;
                }
            }
            catch (NotTranslated)
            {
                return null;
            }
        }

        private IReadOnlyList<IOperation> OperationsAfter(IOperation first, IReadOnlyList<IOperation> ops, int i) =>
            (first is IBlockOperation b ? b.Operations : (IEnumerable<IOperation>)new[] { first }).Concat(ops.Skip(i + 1)).ToList();

        /// <summary>The trees a frame borrows: the roots of its Own.Tree(x).</summary>
        private void LentRoots(IOperation modifies)
        {
            foreach (var t in modifies.DescendantsAndSelf().OfType<IInvocationOperation>())
            {
                if (SpecSymbols.IsCsVerifyType(t.TargetMethod.ContainingType, "Own") && t.TargetMethod.Name == "Tree" && t.Arguments.Length == 1)
                {
                    _p.LentRoots.Add(Spec(Unconverted(t.Arguments[0].Value), null));
                }
            }
        }

        /// <summary>
        /// A call of a procedure: a method, or a property's accessor (its indices the arguments, and a setter's value
        /// after them). A virtual one is of the member as bound here, whose contract every override keeps.
        /// </summary>
        // ------------------------------------------------------------------ delegates

        /// <summary>
        /// The Func and Action parameters whose Spec.Pre, Spec.Post or Spec.Total a method's specifications speak of: it
        /// takes them to be the same in every state, and its callers must give such ones (a lambda reading no state, or
        /// one of their own such parameters).
        /// </summary>
        private HashSet<IParameterSymbol> SteadyParams(IMethodSymbol m)
        {
            var named = new HashSet<IParameterSymbol>(SymbolEqualityComparer.Default);
            var reading = new HashSet<IParameterSymbol>(SymbolEqualityComparer.Default);
            var c = _contractOf?.Invoke(m);
            if (c == null)
            {
                return named;
            }
            foreach (var op in c.Requires.Concat(c.Ensures.Select(e => e.Expr)).Where(x => x != null).SelectMany(x => x.DescendantsAndSelf()).OfType<IInvocationOperation>())
            {
                if (SpecSymbols.IsSpecClass(op.TargetMethod.ContainingType) && op.Arguments.Length > 0 && Unconverted(op.Arguments[0].Value) is IParameterReferenceOperation pr)
                {
                    switch (op.TargetMethod.Name)
                    {
                        case "Pre": case "Post": case "Total":
                            named.Add(pr.Parameter.OriginalDefinition);
                            break;
                        case "Reads" when op.Arguments.Length == 2:
                            reading.Add(pr.Parameter.OriginalDefinition);
                            break;
                        case "ReadsOf":
                            reading.Add(pr.Parameter.OriginalDefinition);
                            break;
                    }
                }
            }
            named.ExceptWith(reading);
            return named;
        }

        /// <summary>
        /// A lambda or a local function knows what the method it is in requires of what never changes:
        /// its steady delegates, and its Spec.Pre and Spec.Total preconditions of them.
        /// </summary>
        private void EnclosingFacts()
        {
            if (!IsNested(_m))
            {
                return;
            }
            if (!(Enclosing(_m) is IMethodSymbol outer))
            {
                return;
            }
            foreach (var sp in SteadyParams(outer).Where(x => IsFunc(x.Type) && NeverWritten(x)))
            {
                if (_capturedParams.FirstOrDefault(c => SymbolEqualityComparer.Default.Equals(c.OriginalDefinition, sp)) is IParameterSymbol cp)
                {
                    _p.DelegateKeys.Add(FuncKey(cp.Type));
                    Emit(KAssume.Of(new KOp("$steady", new KVar(_capturedIn[cp]))));
                }
            }
            foreach (var req in _contractOf?.Invoke(outer)?.Requires ?? Enumerable.Empty<IOperation>())
            {
                if (req.DescendantsAndSelf().OfType<IInvocationOperation>().Any(i => SpecSymbols.IsSpecClass(i.TargetMethod.ContainingType) && i.TargetMethod.Name is "Pre" or "Total") &&
                    req.DescendantsAndSelf().All(o => o.ConstantValue.HasValue || o switch
                    {
                        IInvocationOperation i => SpecSymbols.IsSpecClass(i.TargetMethod.ContainingType) && i.TargetMethod.Name is "Pre" or "Total",
                        IParameterReferenceOperation x => _capturedParams.Contains(x.Parameter) && NeverWritten(x.Parameter),
                        IArgumentOperation or IBinaryOperation or IUnaryOperation or IParenthesizedOperation or IConversionOperation => true,
                        _ => false,
                    }))
                {
                    Emit(KAssume.Of(Spec(req, null)));
                }
            }
        }

        /// <summary>At a call: what the callee takes to be steady must be (CSV1001).</summary>
        private void SteadyArguments(IMethodSymbol callee, KExpr[] args, SyntaxNode at)
        {
            foreach (var p in SteadyParams(callee).Where(p => p.Ordinal < args.Length && args[p.Ordinal] != null))
            {
                Emit(KCheck.Of(
                    new KOp("$steady", args[p.Ordinal]),
                    "CSV1001",
                    at,
                    $"'{callee.Name}' takes what '{p.Name}' accepts and gives to be the same in every state, but this might depend on state: " +
                    $"say what it reads with Spec.Requires(Spec.Reads({p.Name}, ...)) in '{callee.Name}'"));
            }
        }
    }
}
