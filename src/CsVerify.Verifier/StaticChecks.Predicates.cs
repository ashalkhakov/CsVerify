using System;
using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Predicates (Viper's, ATS's dataviews) over the permission mask. <c>Spec.Acc(o)</c> is write permission to an
    /// [Owned] object; a [Predicate] packages permissions and facts under a name, as an instance <c>P(args)</c>:
    /// <list type="bullet">
    /// <item>an instance has an identity (an injective function of its arguments) and an amount held (Frame.Inst);
    /// the objects of its footprint record it as their owner (Frame.Owner), with their ownership trees;</item>
    /// <item><c>Spec.Fold(P(args))</c> gives up the body's permissions (each must be in hand, the facts must hold) for
    /// the instance; <c>Spec.Unfold</c> trades it back, and the facts hold again: nobody can write a folded footprint,
    /// and a body reads only what it has permission to (checked where the predicate is declared), so they cannot
    /// have changed;</item>
    /// <item>in a contract, permissions are given up by the caller (exhaled) and received by the callee (inhaled),
    /// and back for postconditions; a call changes only what it got; in a loop invariant, they go round the loop;</item>
    /// <item>as a condition anywhere else, <c>Spec.Acc(o)</c> and <c>P(args)</c> say "in hand".</item>
    /// </list>
    /// Iso-recursive: an instance is never unfolded except by Spec.Unfold, so predicates may be recursive.
    /// </summary>
    internal sealed partial class StaticChecks
    {

        internal static bool IsAccCall(IOperation op, out IInvocationOperation inv)
        {
            inv = Unconverted(op) as IInvocationOperation;
            return inv != null && SpecSymbols.IsSpecClass(inv.TargetMethod.ContainingType) && (inv.TargetMethod.Name == "Acc" || inv.TargetMethod.Name == "AccRead");
        }

    }
}
