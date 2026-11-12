using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.FlowAnalysis;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Mutable fields (and settable auto-properties) of the program's structs. A struct is a value: each member is an
    /// uninterpreted function of it, as a readonly field is, and <c>s.X = v</c> makes s a new value whose X is v and
    /// whose other members are s's. That is value semantics exactly: a copy (<c>var t = s</c>, an argument) is the
    /// old value and does not change. The value is written back to where it lives: a local or parameter (a ref
    /// parameter is the caller's variable), a ref local, an array cell, an enclosing struct's member, or
    /// <c>this</c> in the struct's constructor. A struct held in a class's field, and a struct method other than a
    /// constructor that writes <c>this</c>, are not supported (the caller would not see the change).
    /// </summary>
    internal sealed partial class StaticChecks
    {
    }
}
