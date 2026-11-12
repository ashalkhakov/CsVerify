using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// A collection changed while it is enumerated. List, Dictionary, HashSet, Stack and Queue have a version (a
    /// [Model], Version()) that a change of the collection may change, and an enumerator remembers the collection and
    /// its version from GetEnumerator. Each MoveNext requires the version to be the same still: else it throws
    /// InvalidOperationException ("Collection was modified"), and that is reported (CSV1001). Changing the collection
    /// and leaving the loop at once (break) is fine: the next MoveNext is what fails. Dictionary.Remove keeps the
    /// version (as .NET Core 3.0 and later do).
    /// </summary>
    internal sealed partial class StaticChecks
    {
    }
}
