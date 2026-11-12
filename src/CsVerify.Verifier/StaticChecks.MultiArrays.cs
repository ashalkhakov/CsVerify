using System.Collections.Generic;
using System.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Rectangular (multi-dimensional) arrays, <c>int[,]</c>: a reference like any array, with a length per
    /// dimension (<c>GetLength(d)</c>, fixed when the array is created) and its cells in the same heap row as a
    /// one-dimensional array's. Cell <c>[i, j]</c> is at <c>cv_cell(i, j)</c>, <c>[i, j, k]</c> at
    /// <c>cv_cell(cv_cell(i, j), k)</c>: an injective pairing (its inverses <c>cv_row</c>/<c>cv_col</c> are an axiom),
    /// so two cells are the same exactly when their indices are, without the nonlinear <c>i * n + j</c>.
    /// <c>Length</c> is the product of the lengths. Spec.Acc permissions cover one-dimensional arrays only.
    /// </summary>
    internal sealed partial class StaticChecks
    {
        public const string CellTheory =
            "(declare-fun cv_cell (Int Int) Int)\n" +
            "(declare-fun cv_row (Int) Int)\n" +
            "(declare-fun cv_col (Int) Int)\n" +
            "(assert (forall ((i Int) (j Int)) (! (and (= (cv_row (cv_cell i j)) i) (= (cv_col (cv_cell i j)) j)) :pattern ((cv_cell i j)))))";
    }
}
