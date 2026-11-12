using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Contracts for code without sources ([ContractsFor] stubs, see <see cref="ContractStubs"/>): a stubbed member is
    /// called like a source method with its stub's contract, which is trusted. Its preconditions are proved at the
    /// call; its postconditions are assumed, and so counted among the run's assumptions. [Model] functions are ghost
    /// fields of the external objects (<see cref="FieldEffects"/>): a stub's Spec.Modifies frames them like any field.
    /// </summary>
    internal sealed partial class StaticChecks
    {
    }
}
