using System.Collections.Generic;
using System.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Lists seen through their interfaces (<c>IReadOnlyList&lt;T&gt;</c>, <c>IList&lt;T&gt;</c>,
    /// <c>IReadOnlyCollection&lt;T&gt;</c>, <c>ICollection&lt;T&gt;</c>), by what the object is: a <c>List&lt;T&gt;</c>
    /// (its models, so its facts cross the interface and changes through the list are seen), an array (its length and
    /// cells), or else a library collection the verifier does not model (a function of the heap and the model state,
    /// which changes whenever they might). If a class of the program implements one of these interfaces, that last case
    /// is an unknown value at each read: the program's own list could change in ways no model follows.
    ///
    /// Reads: <c>Count</c>, the indexer, <c>Contains</c>, <c>IndexOf</c>. Writes (the indexer, <c>Add</c>, <c>Insert</c>,
    /// <c>RemoveAt</c>, <c>Remove</c>, <c>Clear</c>) change, by what the object is, a list's models as its contract says,
    /// an array's cells (an array is fixed-size: the others throw NotSupportedException), or anything (a library call
    /// without a contract). A foreach over an IReadOnlyList or IList whose loop changes no state runs over the indexer,
    /// like a foreach over an array.
    /// </summary>
    internal sealed partial class StaticChecks
    {
    }
}
