using System.Collections.Generic;
using System.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.FlowAnalysis;
using Microsoft.CodeAnalysis.Operations;
using CsVerify.Analyzers;
using static CsVerify.Verifier.Boogie.KernelTypes;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>
    /// How a method is encoded, decided from its text before it is lowered: whether it keeps permissions (views,
    /// predicates, Spec.Acc) and whether it holds memory views. Lowering and Checks read these; neither sets them.
    /// </summary>
    internal sealed partial class Lowering
    {
        /// <summary>Does the method keep permissions? Of its parameters, its contract, and what its body does.</summary>
        private bool KeepsPermissions(IEnumerable<IOperation> body)
        {
            if (_p.ThisIsView || _m.Parameters.Any(x => IsView(x.Type) || IsShare(x.Type) || IsPackage(x.Type)))
            {
                return true;
            }
            if (_contract.Requires.Any(HasAtoms) || _contract.Ensures.Any(e => HasAtoms(e.Expr)))
            {
                return true;
            }
            return body.Any(KeepsPermissions);
        }

        /// <summary>Does this operation need permissions kept?</summary>
        private bool KeepsPermissions(IOperation op)
        {
            switch (op)
            {
                case IDeconstructionAssignmentOperation d when IsPackage(d.Value.Type):
                    return true;
                case IObjectCreationOperation pk when IsPackage(pk.Type) && !InSpec(pk.Syntax):
                    return true;
                case IAssignmentOperation { Target: IMemberReferenceOperation { Member: var f } } when IsOwnedField(f):
                case IIncrementOrDecrementOperation { Target: IMemberReferenceOperation { Member: var g } } when IsOwnedField(g):
                    return true;
                case IInvocationOperation i:
                {
                    var m = i.TargetMethod;
                    // (Spec.Fold and Spec.Unfold; Own's operations; Spec.Acc of an object or a field; a predicate instance)
                    if (SpecSymbols.IsSpecClass(m.ContainingType) && m.Name is "Fold" or "Unfold")
                    {
                        return true;
                    }
                    if (SpecSymbols.IsCsVerifyType(m.ContainingType, "Own"))
                    {
                        return true;
                    }
                    if (SpecSymbols.IsSpecClass(m.ContainingType) && m.Name is "Acc" or "AccRead")
                    {
                        return true;
                    }
                    if (SpecSymbols.IsPredicate(m.OriginalDefinition) && m.IsStatic)
                    {
                        return true;
                    }
                    // (a call that gives or takes views, shares or packages, of an [Owned] object's, or that borrows a tree)
                    if (InSpec(i.Syntax))
                    {
                        return false;
                    }
                    if (m.Parameters.Any(x => IsView(x.Type) || IsShare(x.Type) || IsPackage(x.Type)) || IsPackage(Returns(m)) || IsOwnedClass(m.ContainingType) && !m.IsStatic)
                    {
                        return true;
                    }
                    return _contractOf?.Invoke(m.OriginalDefinition) is Contract c && c.Modifies != null &&
                           c.Modifies.DescendantsAndSelf().OfType<IInvocationOperation>().Any(t => SpecSymbols.IsCsVerifyType(t.TargetMethod.ContainingType, "Own") && t.TargetMethod.Name == "Tree");
                }
                default:
                    return false;
            }
        }

        /// <summary>Does the method hold memory views (ATS's)? A view parameter, or a call of Mem's.</summary>
        private bool HoldsMemViews(IEnumerable<IOperation> body) =>
            _m.Parameters.Any(x => IsMemView(x.Type)) || Returns(_m) is ITypeSymbol r && IsMemView(r) ||
            body.OfType<IInvocationOperation>().Any(i => i.TargetMethod.Name == "Offset" && SpecSymbols.IsCsVerifyType(i.TargetMethod.ContainingType, "Ptr`1") ||
                                                        SpecSymbols.IsCsVerifyType(i.TargetMethod.ContainingType, "Mem") && i.TargetMethod.IsGenericMethod);

        /// <summary>The operations of a method's contract, and of its body as its flow graph has them (none: its contract alone).</summary>
        private IEnumerable<IOperation> OperationsOf(ControlFlowGraph cfg) =>
            (cfg == null ? Enumerable.Empty<IOperation>() : cfg.Blocks.SelectMany(b => b.Operations.Concat(b.BranchValue == null ? new IOperation[0] : new[] { b.BranchValue })))
               .Concat(_contract.Requires).Concat(_contract.Ensures.Select(e => e.Expr)).Concat(new[] { _contract.Modifies, _contract.Reads, _contract.PureBody })
               .Where(o => o != null).SelectMany(o => o.DescendantsAndSelf());

        /// <summary>Both modes, of the contract and (where there is one) the body: set once, before anything is lowered.</summary>
        private void DecideModes(ControlFlowGraph cfg)
        {
            var ops = OperationsOf(cfg).ToList();
            _p.UsesPerm = KeepsPermissions(ops);
            _p.MemViews = HoldsMemViews(ops);
        }
    }
}
