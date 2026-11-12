using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// ATS-style ownership of [Owned] objects. A view <c>Own&lt;C&gt;</c> is linear (the analyzer sees to that), so at
    /// most one piece of code holds an object's view at a time, and only that code may write the object's fields.
    /// A view's value is the object it owns. Consequences the verifier uses:
    /// <list type="bullet">
    /// <item>a write to an owned field needs a live view of the object in hand (CSV1016);</item>
    /// <item>a call changes an owned object only if its view goes in (by <c>ref</c> or by value), comes out, or the
    /// object is the receiver of one of its class's methods: no other object's fields need to be forgotten;</item>
    /// <item>the class's [Invariant] travels with the view: assumed where a view is received, proved where it is
    /// handed over or given back (CSV1015).</item>
    /// </list>
    /// Reads need no view: objects are garbage-collected, and while this code runs nobody else holds a view it lent.
    /// </summary>
    internal sealed partial class StaticChecks
    {
    }
}
