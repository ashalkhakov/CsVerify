using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Spec.Acc and Spec.AccRead calls, as the started delegates' permission checks find them (StartedDelegates).
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
