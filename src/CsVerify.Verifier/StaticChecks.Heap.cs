using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Heap fields (see <see cref="FieldEffects"/>): each is an SMT array from object to value. A frame holds the
    /// maps changed on its path; an unchanged one is the map as of the frame's epoch (the method's entry state,
    /// or the state after a call that may have written anything), shared by every path and by <c>Spec.Old</c>.
    /// </summary>
    internal sealed partial class StaticChecks
    {

        /// <summary>
        /// <paramref name="map"/>, or, if it is built (an ite of paths, a cv_frame), a constant equal to it: a trigger must
        /// select from a name, since Z3 drops one with ite, or or distinct in it (cv_frame's included, as it is inlined).
        /// </summary>
    }
}
