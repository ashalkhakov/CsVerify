using System.Diagnostics;
using CsVerify;

namespace Samples
{
    /// <summary>
    /// Two more INT2PROGINATS programs, rewritten in C#: taking one cell out of an array view (CHAP_DATAVIEW,
    /// array_v_takeout) and row-major matrix access justified by a multiplication lemma (CHAP_PRGTHMPRV, matget;
    /// also matrixSub in Xi's ICFP'05 paper "Combining Programming with Theorem Proving").
    /// </summary>
    public static class AtsMatrixAndTakeOut
    {
        // ---- array_v_takeout ----------------------------------------------------------------------------------

        /// <summary>
        /// Increments cell i in place by lending it out of the array view as a plain <c>int @ (l + i)</c>, working
        /// on it with the single-cell Read/Write, and putting it back: no array-specific access at all.
        /// </summary>
        public static void IncrementAt(ref ArrayView<int> view, Ptr<int> p, int i)
        {
            Spec.Requires(view.Addr == p.Addr && 0 <= i && i < view.Length.Value);
            Spec.Requires(view.Elems[i].Value < 1000);
            Spec.Ensures(view.Addr == Spec.Old(view).Addr && view.Length == Spec.Old(view).Length);
            Spec.Ensures(view.Elems == Spec.Old(view).Elems.Update(i, Ghost.Of(Spec.Old(view).Elems[i].Value + 1)));
            Mem.TakeOut(view, Ghost.Of(i), out PointsTo<int> cell, out ArrayHole<int> rest);  // int @ (l + i), plus the hole
            Ptr<int> q = p.Offset(i);
            int x = Mem.Read(in cell, q);
            Mem.Write(ref cell, q, x + 1);
            Mem.PutBack(cell, rest, out view);                                                  // the hole is filled again
        }

        public static int TakeOutDemo()
        {
            Spec.Ensures<int>(r => r == 4 + 3);
            var p = Mem.AllocArray(5, 3, out ArrayView<int> view, out FreeGc<int> gc);
            IncrementAt(ref view, p, 2);
            int changed = Mem.Get(in view, p, 2);
            int untouched = Mem.Get(in view, p, 4);
            Mem.FreeArray(gc, view, p);
            return changed + untouched;
        }

        // ---- matrices in row-major order ----------------------------------------------------------------------

        /// <summary>
        /// The MUL lemma matget needs: multiplication by a natural is monotone, a &lt;= b ⇒ a n &lt;= b n. By induction
        /// on b - a, each step adding n.
        /// </summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void MulMonotone(int a, int b, int n)
        {
            Spec.Requires(0 <= a && a <= b && n >= 0);
            Spec.Ensures(a * n <= b * n);
            Spec.Decreases(b - a);
            if (a < b) MulMonotone(a + 1, b, n);
        }

        /// <summary>i &lt; m and j &lt; n place i n + j inside an m × n matrix: i n + j &lt; (i + 1) n &lt;= m n.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void RowMajorInBounds(int m, int n, int i, int j)
        {
            Spec.Requires(0 <= i && i < m && 0 <= j && j < n);
            Spec.Ensures(0 <= i * n + j && i * n + j < m * n);
            MulMonotone(0, i, n);
            MulMonotone(i + 1, m, n);
        }

        /// <summary>
        /// <c>fun matget {m,n:nat} {i,j:nat | i &lt; m; j &lt; n} (A: arrayref(a, m*n), n: int n, i: int i, j: int j): a</c>.
        /// The subscript is nonlinear: ATS's constraint solver handles only linear arithmetic, so the bound needs the
        /// lemma. Z3's nonlinear arithmetic happens to prove this one even without it; the call keeps the proof
        /// explicit and independent of solver heuristics.
        /// </summary>
        public static int MatGet(int[] a, int m, int n, int i, int j)
        {
            Spec.Requires(a.Length == m * n);
            Spec.Requires(0 <= i && i < m && 0 <= j && j < n);
            Spec.Ensures<int>(r => r == a[i * n + j]);
            RowMajorInBounds(m, n, i, j);
            return a[i * n + j];
        }

        /// <summary>Sets every cell of an m × n matrix to its row number, through nested loops.</summary>
        public static void FillRows(int[] a, int m, int n)
        {
            Spec.Requires(m >= 0 && n >= 0 && a.Length == m * n);
            for (int i = 0; i < m; i++)
            {
                Spec.Invariant(0 <= i && i <= m);
                Spec.Decreases(m - i);
                for (int j = 0; j < n; j++)
                {
                    Spec.Invariant(0 <= j && j <= n);
                    Spec.Decreases(n - j);
                    RowMajorInBounds(m, n, i, j);
                    a[i * n + j] = i;
                }
            }
        }
    }
}
