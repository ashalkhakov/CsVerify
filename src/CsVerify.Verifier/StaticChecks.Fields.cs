using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Permissions to single fields of [Owned] objects (Viper's <c>acc(o.f)</c>): <c>Spec.Acc(o, nameof(C.F))</c>.
    /// The whole-object mask (Frame.Perm: views, Spec.Acc(o)) stays as it is; Frame.FPerm holds fields one by one,
    /// object -> field -> amount. Writing o.F needs either. Giving a field out of a whole object splits it (the
    /// other fields stay, one by one); holding every field again makes the object whole. A folded field records
    /// its instance in Frame.FOwner (object -> field -> instance), so a call changes only the fields it gets.
    /// Fields of sealed classes without an [Invariant] only, and not [Owns] fields: invariants and ownership trees
    /// are about whole objects.
    /// </summary>
    internal sealed partial class StaticChecks
    {
    }
}
