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
    /// same thing, checked. On a type without a contract (Func, Action), see Spec.Pre and Spec.Post (StaticChecks.HigherOrder).
    /// </summary>
    internal sealed partial class StaticChecks
    {
        /// <summary>A lambda made a contracted delegate is checked against the type's (CSV1018); one made a plain delegate is partial (StaticChecks.HigherOrder).</summary>
        private void CheckDelegateContract() { }
    }
}
