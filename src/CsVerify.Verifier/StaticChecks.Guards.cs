using System.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// What applications check their arguments with. The generic guard clauses of ArgumentOutOfRangeException
    /// (<c>ThrowIfNegative(i)</c>, <c>ThrowIfGreaterThanOrEqual(i, n)</c>, ...) throw unless the relation holds, so a
    /// call that returns gives it, for integer types (a stub could not compare a T). <c>Debug.Assert(c)</c> and
    /// <c>Trace.Assert(c)</c> are proved like <c>Spec.Assert</c> (CSV1004), and assumed after; at run time they are
    /// unchanged.
    /// </summary>
    internal sealed partial class StaticChecks
    {

        /// <summary>Is this member's stub async: does awaiting it give its contract's result?</summary>
        private bool IsAsyncStubbed(IMethodSymbol m) => _engine.ContractOf(m) is Contract c && c.IsStub && c.Stub.IsAsync;

        /// <summary>The T an await of a call to <paramref name="m"/> gives: an async method's, or an async stub's.</summary>
        private ITypeSymbol AwaitedType(IMethodSymbol m) =>
            AsyncResultType(m) ?? (IsAsyncStubbed(m) && m.ReturnType is INamedTypeSymbol rt && rt.TypeArguments.Length == 1 ? rt.TypeArguments[0] : null);
    }
}
