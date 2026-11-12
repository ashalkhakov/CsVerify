using System.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Spans (<c>Span&lt;T&gt;</c>, <c>ReadOnlySpan&lt;T&gt;</c>) are views of memory: a base (an array, or memory the
    /// verifier knows only as some array's cells), an offset into it, and a length. <c>s[i]</c> is the base's cell at
    /// offset + i, read from and written to the heap like an array's, so what code writes through one span (or the
    /// array) a span over the same cells sees. A span made from an array (a conversion, <c>new Span&lt;T&gt;(a, start,
    /// length)</c>, <c>a.AsSpan(...)</c>) has the array as its base. <c>Slice</c> keeps the base and moves the offset;
    /// <c>CopyTo</c>, <c>Fill</c> and <c>Clear</c> write cells; <c>stackalloc</c> makes a new base. A span from
    /// elsewhere (a parameter, a library call) has some base and offset, its cells within the base's length.
    /// Under array permissions (Spec.Acc), spans are as before: their reads unknown, their writes refused.
    /// </summary>
    internal sealed partial class StaticChecks
    {
    }
}
