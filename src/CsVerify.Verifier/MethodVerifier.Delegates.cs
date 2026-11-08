using System.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Contracts of delegates. A delegate type of the program gets one as an interface does, from a [ContractClassFor]
    /// class whose Invoke says Spec.Requires and Spec.Ensures. A call of such a delegate proves the precondition and
    /// assumes the postcondition; a lambda made one is proved against it, as an override is (CSV1018 if it requires
    /// more). What it may change is anything, since which body runs isn't known. A method group made a contracted
    /// delegate is reported (CSV1029): its contract isn't compared with the type's, and a lambda that calls it says the
    /// same thing, checked. On a type without a contract (Func, Action), see Spec.Pre and Spec.Post (MethodVerifier.HigherOrder).
    /// </summary>
    internal sealed partial class MethodVerifier
    {
        /// <summary>A lambda made a contracted delegate is checked against the type's (CSV1018); one made a plain delegate is partial (MethodVerifier.HigherOrder).</summary>
        private void CheckDelegateContract() { }

        private void CheckMethodGroup(IDelegateCreationOperation dc)
        {
            if (!_codeMode || !(dc.Target is IMethodReferenceOperation group) || !_engine.HasDelegateContract(dc.Type)) return;
            var invoke = ((INamedTypeSymbol)dc.Type).DelegateInvokeMethod;
            var args = string.Join(", ", invoke.Parameters.Select(p => p.Name));
            Report("CSV1029", dc.Syntax,
                $"'{group.Method.Name}' is made a '{dc.Type.Name}' here, but its contract isn't compared with the type's: say ({args}) => {group.Method.Name}({args}) instead", isError: true);
        }
    }
}
