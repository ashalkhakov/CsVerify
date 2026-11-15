using Microsoft.CodeAnalysis;

namespace CsVerify.Verifier
{
    /// <summary>
    /// What an await of a call gives: an async method's result, or an async stub's (Stream.ReadAsync's), for the
    /// lock checks of a method's result.
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
