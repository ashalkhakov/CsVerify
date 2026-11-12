using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Properties with code: a getter or setter with a body (or an abstract, virtual or interface accessor, specified
    /// by its contract) is a method, called where the property is read or written. A [Pure] property is a function,
    /// usable in specifications; others are calls in code, with their contracts checked and assumed.
    /// </summary>
    internal sealed partial class StaticChecks
    {
    }
}
