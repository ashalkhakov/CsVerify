using System.Collections.Generic;
using System.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Entity Framework Core's change tracker, transactions and bulk updates, over the ghost state CsVerify.Ef.Tracker
    /// declares (a context's tracked entities and their states, its unsaved changes, its transaction, a failed save):
    /// - Add, Attach, Update and Remove (and Entry(e).State) must not meet another tracked instance with the same key,
    ///   which EF refuses (CSV1033); Update must not take along what the entity's navigations hold (CSV1033).
    /// - SaveChanges writes what is pending; after one that failed, or a rollback, the context is done with (CSV1033).
    ///   It must not write an entity ExecuteUpdate or ExecuteDelete changed behind the tracker (CSV1033).
    /// - Attach or Update of an entity this context read must find its concurrency token as it was read, and a row
    ///   version is never written by the program (CSV1034).
    /// - BeginTransaction needs none open; Commit needs the changes saved; two saves on one context need one
    ///   transaction around them (CSV1035).
    /// </summary>
    internal partial class StaticChecks
    {
        internal const string TrackerId = "CSV1033", TokenId = "CSV1034", TransactionId = "CSV1035";

        private const int EfDetached = 0, Unchanged = 1, Deleted = 2, Modified = 3, Added = 4;

        private static bool IsTransactionType(ITypeSymbol t) =>
            t != null && (t.Name == "IDbContextTransaction" || t.AllInterfaces.Any(i => i.Name == "IDbContextTransaction"));
    }
}
