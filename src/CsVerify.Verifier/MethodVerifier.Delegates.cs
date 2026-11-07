using System.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Contracts of delegates. A delegate type of the program gets one as an interface does, from a [ContractClassFor]
    /// class whose Invoke says Spec.Requires and Spec.Ensures. A call of such a delegate proves the precondition and
    /// assumes the postcondition; a lambda made one is proved against it, as an override is (CSV1018 if it requires
    /// more). What it may change is anything, since which body runs isn't known. A lambda's own precondition is checked
    /// at calls only through its type's: on a type without a contract (Func, Action) it would be checked nowhere, so it
    /// is reported (CSV1029). So is a method group made a contracted delegate: its contract isn't compared with the
    /// type's, and a lambda that calls it says the same thing checked.
    /// </summary>
    internal sealed partial class MethodVerifier
    {
        private void CheckDelegateContract()
        {
            if (_method.MethodKind != MethodKind.AnonymousFunction || _contract.OwnRequires.Count == 0) return;
            var type = _engine.DelegateTypeOf(_method);
            if (type != null && _engine.HasDelegateContract(type)) return;
            Report("CSV1029", _contract.OwnRequires[0].Syntax,
                $"this lambda's precondition isn't checked where it's called: its type '{type?.ToDisplayString() ?? "?"}' has no contract. " +
                "Declare a delegate type and give it the contract with [ContractClassFor], or drop the precondition", isError: true);
        }

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
