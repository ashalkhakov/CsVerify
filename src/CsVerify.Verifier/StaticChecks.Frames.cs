using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Dafny-style dynamic frames for ordinary mutable classes. An object keeps a ghost set of the objects it is
    /// made of (<c>Ghost&lt;ObjSet&gt; Repr</c>) and a [Pure] <c>Valid()</c> that reads only them (Spec.Reads).
    /// <list type="bullet">
    /// <item>A method with <c>Spec.Modifies(W)</c> writes fields and array cells only of objects in W (on entry) or
    /// allocated since (CSV1017); a call to it changes nothing else, every other object's fields and array's cells are
    /// as before.</item>
    /// <item>A [Pure] function with <c>Spec.Reads(R)</c> reads fields only of objects in R (CSV1017); a change
    /// touching nothing in R leaves its value as it was, so <c>Valid()</c> of one object survives updates of
    /// another whose representation is disjoint.</item>
    /// <item><c>Spec.Fresh(x)</c> in a postcondition: x was allocated by the method.</item>
    /// </list>
    /// [Owned] classes are framed by their views instead; a class is one or the other.
    /// </summary>
    internal sealed partial class StaticChecks
    {
    }
}
