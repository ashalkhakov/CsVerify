using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.FlowAnalysis;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Loops that are not while/for/do statements:
    /// <list type="bullet">
    /// <item><c>foreach</c> over a one-dimensional array is what C# compiles it to, a loop over a hidden index
    /// <c>i</c> from 0 to the array's length, reading <c>a[i]</c> into the iteration variable (the array is evaluated
    /// once; the enumerator and its finally do not exist). <c>Spec.Index(x)</c> is that index: in an invariant, the
    /// number of elements gone through, and in the body, the index of <c>x</c>. The loop terminates by itself.</item>
    /// <item><c>foreach</c> over anything else is the enumerator pattern the flow graph shows: GetEnumerator, then
    /// MoveNext and Current in each iteration, and Dispose in a finally, each an ordinary (modular) call.</item>
    /// <item>a cycle made by <c>goto</c> is cut at the head of each natural loop of the flow graph (a block that
    /// dominates the blocks that jump back to it), like a loop statement. Its invariants and measure are the
    /// Spec.Invariant/Decreases statements right after the label. A cycle with no such head (a goto into the middle
    /// of a loop) is still rejected.</item>
    /// </list>
    /// </summary>
    internal sealed partial class StaticChecks
    {
    }
}
