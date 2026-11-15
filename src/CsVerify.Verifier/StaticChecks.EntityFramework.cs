using System.Linq;
using Microsoft.CodeAnalysis;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Entity Framework Core, as the concurrency checks of contexts read it (StaticChecks.EfConcurrency; EfModel has the
    /// model): its members, its contexts, its transactions. Queries and the change tracker are the Boogie engine's
    /// (Lowering.Ef, Lowering.EfTracker).
    /// </summary>
    internal partial class StaticChecks
    {
        private EfModel Ef => _engine.Ef;

        private static bool IsEfMethod(IMethodSymbol m) =>
            m.ContainingNamespace?.ToDisplayString() is string ns && (ns == "Microsoft.EntityFrameworkCore" || ns.StartsWith("Microsoft.EntityFrameworkCore."));

        private static bool IsTransactionType(ITypeSymbol t) =>
            t != null && (t.Name == "IDbContextTransaction" || t.AllInterfaces.Any(i => i.Name == "IDbContextTransaction"));
    }
}
