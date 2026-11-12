using System.Collections.Generic;
using System.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// The program's data types (see <see cref="DataTypes"/>), as the checks of an [Invariant]'s dependence read them.
    /// </summary>
    internal sealed partial class StaticChecks
    {

        private DataTypes Data => _engine.Data;
    }
}
