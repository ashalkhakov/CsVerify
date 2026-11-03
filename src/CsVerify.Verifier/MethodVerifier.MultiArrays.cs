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
    internal sealed partial class MethodVerifier
    {
        public const string CellTheory =
            "(declare-fun cv_cell (Int Int) Int)\n" +
            "(declare-fun cv_row (Int) Int)\n" +
            "(declare-fun cv_col (Int) Int)\n" +
            "(assert (forall ((i Int) (j Int)) (! (and (= (cv_row (cv_cell i j)) i) (= (cv_col (cv_cell i j)) j)) :pattern ((cv_cell i j)))))";

        private static int RankOf(ITypeSymbol t) => t is IArrayTypeSymbol at ? at.Rank : 1;

        /// <summary>The length of dimension <paramref name="d"/> of a multi-dimensional array.</summary>
        private Term DimLength(Term arr, int d)
        {
            var len = _z3.Apply("dimLength", Sort.Int, new[] { arr, T.Int(d) });
            AssumeSide(T.InRange(len, 0, int.MaxValue));
            return len;
        }

        /// <summary><c>Length</c> of a multi-dimensional array: the product of its lengths.</summary>
        private void LengthIsProduct(Term arr, int rank)
        {
            var product = DimLength(arr, 0);
            for (int d = 1; d < rank; d++) product = T.Mul(product, DimLength(arr, d));
            AssumeSide(T.Eq(Len(arr), product));
        }

        private static Term Cell(IReadOnlyList<Term> indices)
        {
            var cell = indices[0];
            for (int d = 1; d < indices.Count; d++) cell = new Term($"(cv_cell {cell.S} {indices[d].S})", Sort.Int);
            return cell;
        }

        /// <summary>The cell <c>a[i, j, ...]</c> names (a not null, each index within its dimension).</summary>
        private Term CellOf(IArrayElementReferenceOperation ae, Term arr, Frame f, SpecEnv spec)
        {
            var indices = ae.Indices.Select(i => Eval(i, f, spec)).ToList();
            Deref(ae.ArrayReference, arr, ae.Syntax);
            if (indices.Count == 1)
            {
                BoundsCheck(arr, indices[0], ae.Syntax);
                return indices[0];
            }
            for (int d = 0; d < indices.Count; d++)
                Require(T.And(T.Le(T.Int(0), indices[d]), T.Lt(indices[d], DimLength(arr, d))), "CSV1003", ae.Syntax,
                    $"index {d} in '{ae.Syntax}' might be out of range");
            return Cell(indices);
        }

        /// <summary><c>new T[n, m]</c> (rank 2 or more): the lengths, and the cells an initializer gives.</summary>
        private Term NewMultiArray(IArrayCreationOperation ac, Term r, IReadOnlyList<Term> sizes, Frame f, SpecEnv spec)
        {
            for (int d = 0; d < sizes.Count; d++) _z3.Assume(T.Eq(DimLength(r, d), sizes[d]));
            LengthIsProduct(r, sizes.Count);
            var row = T.ZeroRow();
            void Fill(IArrayInitializerOperation init, List<Term> prefix)
            {
                for (int i = 0; i < init.ElementValues.Length; i++)
                {
                    var at = new List<Term>(prefix) { T.Int(i) };
                    if (at.Count < sizes.Count) Fill((IArrayInitializerOperation)init.ElementValues[i], at);
                    else row = T.Store(row, Cell(at), T.Coerce(Eval(init.ElementValues[i], f, spec), Sort.Int));
                }
            }
            if (ac.Initializer != null) Fill(ac.Initializer, new List<Term>());
            return row;
        }

        /// <summary><c>a.GetLength(d)</c>, defined for 0 &lt;= d &lt; a.Rank.</summary>
        private Term GetLength(IInvocationOperation inv, Frame f, SpecEnv spec)
        {
            var instance = Unconverted(inv.Instance);
            int rank = RankOf(instance.Type);
            var arr = Eval(instance, f, spec);
            Deref(instance, arr, inv.Syntax);
            var d = Eval(inv.Arguments[0].Value, f, spec);
            Require(T.And(T.Le(T.Int(0), d), T.Lt(d, T.Int(rank))), "CSV1003", inv.Syntax, $"dimension in '{inv.Syntax}' might be out of range");
            if (rank == 1) return Len(arr);
            var len = DimLength(arr, rank - 1);
            for (int k = rank - 2; k >= 0; k--) len = T.Ite(T.Eq(d, T.Int(k)), DimLength(arr, k), len);
            return len;
        }

        private static bool IsGetLength(IInvocationOperation inv) =>
            inv.TargetMethod.Name == "GetLength" && inv.TargetMethod.ContainingType?.SpecialType == SpecialType.System_Array &&
            inv.Instance != null && Unconverted(inv.Instance).Type is IArrayTypeSymbol && inv.Arguments.Length == 1;
    }
}
