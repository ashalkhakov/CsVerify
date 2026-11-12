using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Values and equality. A string is its value: two strings with the same characters are the same term, so
    /// <c>==</c>, <c>Equals</c>, a switch on strings, <c>Length</c> and a dictionary's string keys compare contents, as
    /// .NET does (ordinally), and a literal is the same value wherever it appears (different literals are different
    /// values). Comparing strings as objects (<c>ReferenceEquals</c>, <c>(object)a == (object)b</c>) is unknown, since
    /// equal strings may or may not be one object. The characters themselves are not modeled.
    ///
    /// <c>Spec.Equal(a, b)</c> is what <c>EqualityComparer&lt;T&gt;.Default.Equals(a, b)</c> gives, for T as the call
    /// instantiates it: the verifier's own equality where T's is known (numbers, chars, bools, enums, strings, classes
    /// that do not override Equals, data records), else a relation the verifier knows nothing of, fixed within one call's
    /// contract. A ghost Map's keys are compared the same way: by value where T's equality is known, else through a key
    /// function (as .NET's dictionaries require: a key does not change while it is one).
    /// </summary>
    internal sealed partial class StaticChecks
    {
    }
}
