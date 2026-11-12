using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// References to variables and array cells:
    /// <list type="bullet">
    /// <item>an array element passed by <c>ref</c>/<c>out</c>/<c>in</c> is copied in and out of the callee's parameter.
    /// That is exactly what happens when nothing else looks at the cell during the call: so a callee given one by
    /// ref or out must not touch array contents at all (Engine.MayTouchArrays), and one given one by in must not
    /// write them. Two arguments by reference, one of them ref or out, must not be the same cell or variable
    /// (CSV1020): the callee's parameters are variables of their own.</item>
    /// <item>a ref local is bound to a location, a variable or an array cell (the array and the index as they were
    /// when it was bound); reading and writing it read and write the location. A loop that writes through one
    /// havocs every location it is ever bound to.</item>
    /// </list>
    /// </summary>
    internal sealed partial class StaticChecks
    {
    }
}
