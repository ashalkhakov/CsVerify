namespace CsVerify
{
    using System.Collections.Generic;
    using System.Runtime.CompilerServices;

    /// <summary>
    /// The array view <c>array_v(T, n, l)</c>: a linear token proving that the <see cref="Length"/> cells starting at
    /// <see cref="Addr"/> hold the elements <see cref="Elems"/>. Split it to hand parts of an array to different code,
    /// join it to get the whole back; the analyzers make sure no part is lost or used twice.
    /// </summary>
    [Linear]
    public readonly struct ArrayView<T>
    {
        public Ghost<int> Addr => default;
        public Ghost<int> Length => default;
        public Seq<T> Elems => default;
    }

    /// <summary>
    /// ATS's <c>mfree_gc_v(l)</c>: the right to free the allocation at <see cref="Addr"/>. Freeing needs it and the
    /// whole view, so an array can only be freed after all its parts are joined back.
    /// </summary>
    [Linear]
    public readonly struct FreeGc<T>
    {
        public Ghost<int> Addr => default;
        public Ghost<int> Length => default;
    }

    /// <summary>
    /// An array view with one cell taken out: what is left of <c>array_v(T, n, l)</c> once <c>T @ (l + i)</c> is lent
    /// out. ATS's <c>array_v_takeout</c> returns the cell's view and a linear function
    /// <c>T @ (l + i) -&lt;lin&gt; array_v(T, n, l)</c> that puts it back; this token is that function, and
    /// <see cref="Mem.PutBack{T}"/> applies it.
    /// </summary>
    [Linear]
    public readonly struct ArrayHole<T>
    {
        public Ghost<int> Addr => default;
        public Ghost<int> Length => default;
        public Ghost<int> Index => default;
        public Seq<T> Elems => default;
    }

    public static partial class Mem
    {
        private static readonly Dictionary<int, int> ArraySizes = new Dictionary<int, int>();

        [Trusted]
        public static Ptr<T> AllocArray<T>(int length, T fill, out ArrayView<T> view, out FreeGc<T> gc)
        {
            view = default;
            gc = default;
            Spec.Requires(length >= 0);
            Spec.Ensures(view.Addr == Spec.Result<Ptr<T>>().Addr && view.Length.Value == length && view.Elems == Seq.Const(fill));
            Spec.Ensures(gc.Addr == view.Addr && gc.Length == view.Length);
            lock (Cells)
            {
                int handle = Cells.Count;
                for (int i = 0; i < length; i++) Cells.Add(fill);
                ArraySizes[handle] = length;
                return new Ptr<T>(handle);
            }
        }

        /// <summary>A view's length is a natural number (ATS: <c>array_v(T, n:nat, l)</c>).</summary>
        [Lemma, System.Diagnostics.Conditional(Spec.Symbol), Trusted]
        public static void LengthIsNatural<T>(in ArrayView<T> view)
        {
            Spec.Ensures(view.Length.Value >= 0);
        }

        /// <summary><c>p->[i]</c> under <c>!array_v(T, n, l)</c>.</summary>
        [Trusted]
        public static T Get<T>(in ArrayView<T> view, Ptr<T> p, int i)
        {
            Spec.Requires(view.Addr == p.Addr && 0 <= i && i < view.Length.Value);
            Spec.Ensures(Ghost.Of(Spec.Result<T>()) == view.Elems[i]);
            lock (Cells) return (T)Cells[p.Handle + i];
        }

        [Trusted]
        public static void Set<T>(ref ArrayView<T> view, Ptr<T> p, int i, T value)
        {
            Spec.Requires(view.Addr == p.Addr && 0 <= i && i < view.Length.Value);
            Spec.Ensures(view.Addr == Spec.Old(view).Addr && view.Length == Spec.Old(view).Length);
            Spec.Ensures(view.Elems == Spec.Old(view).Elems.Update(i, Ghost.Of(value)));
            lock (Cells) Cells[p.Handle + i] = value;
        }

        [Trusted]
        public static void FreeArray<T>(FreeGc<T> gc, ArrayView<T> view, Ptr<T> p)
        {
            Spec.Requires(gc.Addr == view.Addr && gc.Addr == p.Addr && gc.Length == view.Length);
            lock (Cells)
            {
                int n = ArraySizes[p.Handle];
                ArraySizes.Remove(p.Handle);
                for (int i = 0; i < n; i++) Cells[p.Handle + i] = null;
            }
        }

        /// <summary>
        /// <c>array_v(T, n, l) -o array_v(T, i, l) * array_v(T, n - i, l + i)</c>. A proof axiom (ATS <c>praxi</c>):
        /// C# forbids out parameters on [Conditional] methods, so instead of being erased it is an empty method on
        /// data-less structs, inlined away.
        /// </summary>
        [Trusted, MethodImpl(MethodImplOptions.AggressiveInlining)]
        public static void Split<T>(ArrayView<T> whole, Ghost<int> at, out ArrayView<T> left, out ArrayView<T> right)
        {
            left = default;
            right = default;
            Spec.Requires(0 <= at.Value && at.Value <= whole.Length.Value);
            Spec.Ensures(left.Addr == whole.Addr && left.Length == at && left.Elems == whole.Elems && right.Length.Value >= 0);
            Spec.Ensures(right.Addr.Value == whole.Addr.Value + at.Value && right.Length.Value == whole.Length.Value - at.Value);
            Spec.Ensures(right.Elems == whole.Elems.Drop(at.Value));
        }

        /// <summary>
        /// ATS's <c>array_v_takeout</c>: lends out cell i of the view as a plain <c>T @ (l + i)</c>, which
        /// <see cref="Read{T}"/> and <see cref="Write{T}"/> work on; the rest stays behind as a hole.
        /// </summary>
        [Trusted, MethodImpl(MethodImplOptions.AggressiveInlining)]
        public static void TakeOut<T>(ArrayView<T> whole, Ghost<int> i, out PointsTo<T> cell, out ArrayHole<T> rest)
        {
            cell = default;
            rest = default;
            Spec.Requires(0 <= i.Value && i.Value < whole.Length.Value);
            Spec.Ensures(cell.Addr.Value == whole.Addr.Value + i.Value && cell.Value == whole.Elems[i.Value]);
            Spec.Ensures(rest.Addr == whole.Addr && rest.Length == whole.Length && rest.Index == i && rest.Elems == whole.Elems);
        }

        /// <summary>Puts a taken-out cell back into its hole, with whatever value it now holds.</summary>
        [Trusted, MethodImpl(MethodImplOptions.AggressiveInlining)]
        public static void PutBack<T>(PointsTo<T> cell, ArrayHole<T> rest, out ArrayView<T> whole)
        {
            whole = default;
            Spec.Requires(cell.Addr.Value == rest.Addr.Value + rest.Index.Value);
            Spec.Ensures(whole.Addr == rest.Addr && whole.Length == rest.Length);
            Spec.Ensures(whole.Elems == rest.Elems.Update(rest.Index.Value, cell.Value));
        }

        /// <summary><c>array_v(T, i, l) * array_v(T, m, l + i) -o array_v(T, i + m, l)</c>.</summary>
        [Trusted, MethodImpl(MethodImplOptions.AggressiveInlining)]
        public static void Join<T>(ArrayView<T> left, ArrayView<T> right, out ArrayView<T> whole)
        {
            whole = default;
            Spec.Requires(right.Addr.Value == left.Addr.Value + left.Length.Value);
            Spec.Ensures(whole.Addr == left.Addr && whole.Length.Value == left.Length.Value + right.Length.Value);
            Spec.Ensures(whole.Elems == left.Elems.Concat(left.Length.Value, right.Elems));
        }
    }
}
