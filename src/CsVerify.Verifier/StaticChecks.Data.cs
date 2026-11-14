
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
