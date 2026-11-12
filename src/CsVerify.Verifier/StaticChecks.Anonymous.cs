using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Tuples and anonymous objects (<c>new { x, y = x * 2 }</c>, and what query syntax makes for <c>let</c> and a second
    /// <c>from</c>) as values: one constructor per anonymous type, applied to the members' values, which selectors read
    /// back. Objects with equal members are the same term, as their Equals has them equal (so GroupBy and Distinct by
    /// one work); <c>==</c> between two anonymous objects compares references, which is not modeled (unknown); they are
    /// not null. A tuple's constructor is its type's (without its names), read by <c>tuple.ItemN</c>. (A value made by a
    /// constructor, not a fresh constant: in a lambda a query applies, a constant would be one for every element. Its
    /// parts are read back by side facts where it is made, as a fresh tuple's were.)
    /// </summary>
    internal sealed partial class StaticChecks
    {
    }
}
