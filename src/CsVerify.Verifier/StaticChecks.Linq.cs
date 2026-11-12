using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// The sequences LINQ's definitions (StaticChecks.Queries) are compiled into, and their encodings: a source the
    /// verifier indexes (a List, an array, an IReadOnlyList or IList: StaticChecks.Interfaces), a range, a filter (a
    /// running count of the matches, one step at a time), sequences one after another (running offsets), a stable
    /// sort (a permutation in key order), and folds (running values). Lambdas passed to LINQ are inlined where they
    /// are pure (an expression with no assignments, calling only [Pure] members); their own obligations are checked
    /// where each lambda is verified, as a unit of its own. ToList and ToArray copy a sequence into a new object.
    /// </summary>
    internal sealed partial class StaticChecks
    {
    }
}
