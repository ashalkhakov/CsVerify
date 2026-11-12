using System.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// <c>Nullable&lt;T&gt;</c> (<c>int?</c>): a value with two functions of it, whether it has a value
    /// (<c>nullable.has</c>) and the value (<c>nullable.value</c>, meaningful only when it has one). <c>some(x)</c> and
    /// <c>none</c> build them. Conversions wrap and unwrap (an explicit unwrap of null throws:
    /// CSV1013), <c>HasValue</c>/<c>Value</c>/<c>GetValueOrDefault</c> read them, <c>x == null</c> and patterns test
    /// them, and lifted operators (<c>x + 1</c>, <c>x &lt; y</c>, <c>x == y</c>) work on the values where both have
    /// one, as C# defines them.
    /// </summary>
    internal sealed partial class StaticChecks
    {

    }
}
