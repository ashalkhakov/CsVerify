using CsVerify;

namespace Samples
{
    // ATS's manual memory on the same model as C# arrays: Mem's cells are cells of the heap, and a view of them
    // (T @ l, array_v) holds permissions to them, like Spec.Acc to an array's cells. Two views in hand are views of
    // different cells; a call changes only the cells whose views it gets, and arrays only as their cells allow.
    public static class MemoryModel
    {
        /// <summary>Two non-empty views in hand never overlap (ATS knows it from linearity; here it is a fact).</summary>
        public static void Apart(in ArrayView<int> a, in ArrayView<int> b)
        {
            Spec.Requires(a.Length.Value > 0 && b.Length.Value > 0);
            Spec.Assert(a.Addr.Value + a.Length.Value <= b.Addr.Value || b.Addr.Value + b.Length.Value <= a.Addr.Value);
        }

        /// <summary>A cell in hand is none of an array view's cells.</summary>
        public static void CellOutside(in PointsTo<int> cell, in ArrayView<int> view)
        {
            Spec.Assert(cell.Addr.Value < view.Addr.Value || cell.Addr.Value >= view.Addr.Value + view.Length.Value);
        }

        /// <summary>The first n cells of an array hold what a view's first n cells hold.</summary>
        [GhostFunction]
        public static bool Holds(int[] a, Seq<int> s, int n)
        {
            Spec.Requires(0 <= n && n <= a.Length);
            return Spec.Forall(0, n, j => a[j] == s[j].Value);
        }

        /// <summary>
        /// Copies a view's cells into a C# array it has permission to: memory and arrays are one heap, and each
        /// write changes only its own cells (the view's contents stay, the array's other cells too).
        /// </summary>
        public static void ToArray(in ArrayView<int> view, Ptr<int> p, int[] target, int n)
        {
            Spec.Requires(view.Addr == p.Addr && view.Length.Value == n && n >= 0 && target.Length == n + 1 && Spec.Acc(target));
            Spec.Ensures(Spec.Acc(target) && Holds(target, view.Elems, n) && target[n] == Spec.Old(target[n]));
            for (int i = 0; i < n; i++)
            {
                Spec.Invariant(0 <= i && i <= n && Holds(target, view.Elems, i) && target[n] == Spec.Old(target[n]));
                Spec.Decreases(n - i);
                target[i] = Mem.Get(in view, p, i);
            }
        }

        public static int Demo()
        {
            Spec.Ensures((int r) => r == 3 + 9);
            var p = Mem.AllocArray(2, 3, out ArrayView<int> view, out FreeGc<int> gc);
            var c = Mem.Alloc(7, out PointsTo<int> cell);
            CellOutside(in cell, in view);
            var target = new int[3];
            target[2] = 9;
            ToArray(in view, p, target, 2);
            Mem.Write(ref cell, c, 1);            // the view's cells are not this one
            int r = target[1] + target[2] + Mem.Get(in view, p, 0) - Mem.Read(in cell, c) - 2;
            Mem.Free(cell, c);
            Mem.FreeArray(gc, view, p);
            return r;
        }
    }
}
