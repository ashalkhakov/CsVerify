using System.Collections.Generic;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.FlowAnalysis;
using Microsoft.CodeAnalysis.Operations;
using static CsVerify.Verifier.Boogie.KernelTypes;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>ref and out: arguments by reference, ref locals, array cells lent to a call and written back.</summary>
    internal sealed partial class Lowering
    {
        /// <summary>The variable a ref or out argument is: a local (declared there, for out var), or a ref or out parameter.</summary>
        private readonly Dictionary<IArgumentOperation, string> _refVariables = new Dictionary<IArgumentOperation, string>();

        /// <summary>The cells and struct members lent to the call being lowered: written back after it.</summary>
        private readonly List<(IOperation target, string var)> _writeBacks = new List<(IOperation, string)>();

        /// <summary>The array cells lent: their array and index, for the check that two aren't the same (CSV1020).</summary>
        private readonly Dictionary<string, (KExpr array, KExpr index)> _lentCells = new Dictionary<string, (KExpr, KExpr)>();

        /// <summary>
        /// An array's cell lent by ref to a callee that may itself touch arrays: not supported, CSV1901
        /// (the callee's parameter and the cell would disagree); it is lent as a copy, written back after.
        /// </summary>
        private void ArrayCellLent(IArgumentOperation a, IMethodSymbol callee) =>
            Emit(KCheck.Of(
                KLit.False,
                "CSV1901",
                a.Syntax,
                notAssumedAfter: true,
                message: $"passing the array cell '{a.Value.Syntax}' by {a.Parameter.RefKind.ToString().ToLowerInvariant()} to '{callee.Name}', which may touch arrays itself, is not supported: the cell and the parameter would disagree (copy the element into a local)"));

        /// <summary>What each ref local names: a variable (its kernel name), or an array's cell (the array and the index, as they were bound).</summary>
        private readonly Dictionary<ILocalSymbol, (string Var, KExpr Array, KExpr Index, ITypeSymbol ArrayType)> _refAlias =
            new Dictionary<ILocalSymbol, (string, KExpr, KExpr, ITypeSymbol)>(SymbolEqualityComparer.Default);

        /// <summary>
        /// ref T r = ref x: r names x, a local or a parameter's variable, or an array's cell, its array and index fixed
        /// where it is bound (and checked there, as reading it would be). A field, or binding r again, is not supported
        /// (CSV1901).
        /// </summary>
        private void BindRef(ILocalSymbol r, IOperation target, SyntaxNode at)
        {
            target = target is IFlowCaptureReferenceOperation fc && _captured.TryGetValue(fc.Id, out var cv) ? cv : target;
            if (!InSubset(r.Type))
            {
                throw new NotTranslated("a ref local of " + r.Type);
            }
            if (_refAlias.ContainsKey(r))
            {
                Emit(KCheck.Of(
                    KLit.False,
                    "CSV1901",
                    at,
                    notAssumedAfter: true,
                    message: $"binding the ref local '{r.Name}' again is not supported: it names one variable or cell"));
            }
            switch (target)
            {
                case ILocalReferenceOperation l when l.Local.RefKind == RefKind.None && InSubset(l.Local.Type):
                    _refAlias[r] = (Declare(Local(l.Local), l.Local.Type), null, null, null);
                    return;
                case ILocalReferenceOperation l2 when _refAlias.TryGetValue(l2.Local, out var other):
                    _refAlias[r] = other;
                    return;
                case IParameterReferenceOperation ap when _assigned.TryGetValue(ap.Parameter, out var apLocal):
                    _refAlias[r] = (apLocal, null, null, null);
                    return;
                case IParameterReferenceOperation p when InSubset(p.Parameter.Type) && p.Parameter.RefKind is RefKind.Ref or RefKind.Out:
                    _refAlias[r] = (Local(p.Parameter), null, null, null);
                    return;
                case IArrayElementReferenceOperation e when IsArray(e.ArrayReference.Type) && e.Indices.Length == 1:
                {
                    var v = Operands(e.ArrayReference, e.Indices[0]);
                    var arr = Declare("t$" + _temps++, e.ArrayReference.Type);
                    var idx = Declare("t$" + _temps++, e.Indices[0].Type);
                    Emit(KAssign.Of(arr, v[0]));
                    Emit(KAssign.Of(idx, v[1]));
                    // (its checks: not null, within bounds, as reading it)
                    var probe = Declare("t$" + _temps++, e.Type);
                    HeldCell(new KVar(arr), e.Syntax, write: false);
                    Emit(KAssign.Of(
                        probe,
                        new KElem
                {
                    Array = new KVar(arr),
                    Index = new KVar(idx),
                    ArrayType = e.ArrayReference.Type,
                    At = e.Syntax,
                    ArrayAt = e.ArrayReference.Syntax,
                }));
                    _refAlias[r] = (null, new KVar(arr), new KVar(idx), e.ArrayReference.Type);
                    return;
                }
                case IFieldReferenceOperation:
                {
                    Emit(KCheck.Of(
                        KLit.False,
                        "CSV1901",
                        at,
                        notAssumedAfter: true,
                        message: $"a ref local to the field '{target.Syntax}' is not supported: only locals, parameters and array elements"));
                    var t = Declare("t$" + _temps++, r.Type);
                    Emit(KHavoc.Of(t));
                    _refAlias[r] = (t, null, null, null);
                    return;
                }
                default: throw new NotTranslated("a ref local bound to " + target.Kind);
            }
        }

        /// <summary>What a cell or struct member lent by reference is in: an array's cell, or a local or parameter (a struct's); else null.</summary>
        private static IOperation CellRoot(IOperation v) => v switch
        {
            IArrayElementReferenceOperation ae when IsArray(ae.ArrayReference.Type) && ae.Indices.Length == 1 || IsMultiArray(ae.ArrayReference.Type) => ae,
            ILocalReferenceOperation { Local.RefKind: RefKind.None } l => l,
            IParameterReferenceOperation { Parameter.RefKind: RefKind.Ref or RefKind.Out } p => p,
            _ when StructMember(v) is (IOperation inner, int _) => CellRoot(inner),
            _ => null,
        };

        private string RefVariableName(IArgumentOperation a) => _refVariables.TryGetValue(a, out var v) ? v : null;

        private string RefVariable(IArgumentOperation a) => _refVariables[a] = RefVariableOf(a);

        private string RefVariableOf(IArgumentOperation a)
        {
            var v = a.Value is IDeclarationExpressionOperation d ? d.Expression : a.Value;
            // (a variable the flow graph captured before an argument after it branches, Add(ref x, c ? 2 : 3): the variable
            // itself, as it is at the call)
            if (v is IFlowCaptureReferenceOperation fc && _captured.TryGetValue(fc.Id, out var cv) && cv is ILocalReferenceOperation or IParameterReferenceOperation)
            {
                v = cv;
            }
            switch (v)
            {
                // (out _: a variable of its own, never read)
                case IDiscardOperation discard when InSubset(discard.Type): return Declare("t$" + _temps++, discard.Type);
                case ILocalReferenceOperation l when InSubset(l.Local.Type) && l.Local.RefKind == RefKind.None: return Declare(Local(l.Local), l.Local.Type);
                case ILocalReferenceOperation rl when _refAlias.TryGetValue(rl.Local, out var ral) && ral.Var != null: return ral.Var;
                case ILocalReferenceOperation rc when _refAlias.TryGetValue(rc.Local, out var rca):
                {
                    if (a.Parameter?.ContainingSymbol is IMethodSymbol rcallee && (KernelTypes.MayTouchArrays == null || KernelTypes.MayTouchArrays(rcallee.OriginalDefinition)))
                    {
                        ArrayCellLent(a, rcallee);
                    }
                    var t = Declare("t$" + _temps++, v.Type);
                    _lentCells[t] = (rca.Array, rca.Index);
                    if (a.Parameter.RefKind != RefKind.Out)
                    {
                        Emit(KAssign.Of(t, Expr(rc)));
                    }
                    _writeBacks.Add((rc, t));
                    return t;
                }
                case IParameterReferenceOperation ap when _assigned.TryGetValue(ap.Parameter, out var apLocal): return apLocal;
                case IParameterReferenceOperation p when InSubset(p.Parameter.Type) && p.Parameter.RefKind is RefKind.Ref or RefKind.Out: return Local(p.Parameter);
                // (an array's cell, or a struct's member: a variable of the callee's, copied in, and written back after the
                // call; which is what happens where the callee doesn't look at arrays itself)
                case IArrayElementReferenceOperation or IFieldReferenceOperation or IPropertyReferenceOperation when InSubset(v.Type) && CellRoot(v) is IOperation root:
                {
                    if (root is IArrayElementReferenceOperation && a.Parameter?.ContainingSymbol is IMethodSymbol callee && (KernelTypes.MayTouchArrays == null || KernelTypes.MayTouchArrays(callee.OriginalDefinition)))
                    {
                        ArrayCellLent(a, callee);
                    }
                    var t = Declare("t$" + _temps++, v.Type);
                    if (v is IArrayElementReferenceOperation { Indices.Length: 1 } ce && IsArray(ce.ArrayReference.Type))
                    {
                        var at = Operands(ce.ArrayReference, ce.Indices[0]);
                        _lentCells[t] = (at[0], at[1]);
                    }
                    // (an out one isn't read, but its place must be one)
                    if (a.Parameter.RefKind == RefKind.Out)
                    {
                        Emit(KAssign.Of(t, Expr(v)));
                    }
                    _writeBacks.Add((v, t));
                    return t;
                }
                // (a field by ref: not supported, CSV1901; a variable of the callee's, unknown after)
                case IFieldReferenceOperation rfr when InSubset(v.Type):
                {
                    Emit(KCheck.Of(
                        KLit.False,
                        "CSV1901",
                        a.Syntax,
                        notAssumedAfter: true,
                        message: $"passing '{a.Value.Syntax}' by {a.Parameter.RefKind.ToString().ToLowerInvariant()} is not supported: only locals, parameters, array elements and their structs' members"));
                    var t = Declare("t$" + _temps++, v.Type);
                    if (a.Parameter.RefKind != RefKind.Out)
                    {
                        Emit(KAssign.Of(t, Expr(rfr)));
                    }
                    return t;
                }
                default: throw new NotTranslated("a ref or out argument that isn't a variable");
            }
        }
    }
}
