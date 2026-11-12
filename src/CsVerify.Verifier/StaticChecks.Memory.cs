using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// ATS's manual memory (<c>Mem</c>, <c>Ptr&lt;T&gt;</c>) on the same model as C# arrays: its cells are a row of the
    /// heap, the one at null (array code never reads or writes there: it proves its arrays non-null first), and the
    /// views <c>PointsTo&lt;T&gt;</c> (<c>T @ l</c>), <c>ArrayView&lt;T&gt;</c> (<c>array_v</c>) and <c>ArrayHole&lt;T&gt;</c>
    /// hold permissions to cells of it, like Spec.Acc to an array's cells:
    /// <list type="bullet">
    /// <item>a view in hand holds its cells (Frame.ArrPerm at row 0): two views in hand are of disjoint cells;</item>
    /// <item>what a view says (<c>Elems</c>, <c>Value</c>) is what its cells hold: a view's contents are its own ghost
    /// value, as in ATS, tied to the heap whenever it comes into hand (nobody changes cells held, so it stays true);</item>
    /// <item>a call changes only the cells it may: none of those whose views stay in hand, and anything else (the
    /// views it got, memory it allocates or frees); the proof functions (Split, Join, TakeOut, PutBack, Get, Read) none.</item>
    /// </list>
    /// </summary>
    internal sealed partial class StaticChecks
    {
    }
}
