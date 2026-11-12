using System.Collections.Generic;
using System.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Data types and object invariants. A value of a data record (see <see cref="DataTypes"/>) is its constructor
    /// applied to its fields: <c>new Cons(h, t)</c> is the term <c>mk:Cons(h, t)</c>, whose fields read back, whose
    /// tag is Cons's and whose size is one more than its parts'. A type test is a test of the tag, and on the
    /// matching branch the value is that constructor applied to its own fields, so equal fields mean equal values.
    /// Identity is not observable: a data value is its contents.
    /// </summary>
    internal sealed partial class StaticChecks
    {

        private DataTypes Data => _engine.Data;
    }
}
