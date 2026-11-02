using System.Collections.Generic;

namespace CsVerify
{
    /// <summary>A pointer (ATS <c>ptr l</c>). Its ghost <see cref="Addr"/> is the static address <c>l</c>.</summary>
    public readonly struct Ptr<T>
    {
        internal readonly int Handle;
        internal Ptr(int handle) { Handle = handle; }
        public Ghost<int> Addr => default;

        /// <summary>Pointer arithmetic, <c>l + i</c>: the address of the <paramref name="offset"/>-th cell after this one.</summary>
        [Trusted]
        public Ptr<T> Offset(int offset)
        {
            Spec.Ensures(Spec.Result<Ptr<T>>().Addr.Value == Addr.Value + offset);
            return new Ptr<T>(Handle + offset);
        }
    }

    /// <summary>
    /// The view <c>T @ l</c>: a zero-size linear token proving that <see cref="Addr"/> holds a <typeparamref name="T"/>
    /// equal to <see cref="Value"/>. Only <see cref="Mem"/> creates or destroys one.
    /// </summary>
    [Linear]
    public readonly struct PointsTo<T>
    {
        public Ghost<int> Addr => default;
        public Ghost<T> Value => default;
    }

    /// <summary>Manual memory with views. Trusted: the bodies are not verified, the contracts are the axioms.</summary>
    public static partial class Mem
    {
        private static readonly List<object> Cells = new List<object>();
        private static readonly Stack<int> FreeList = new Stack<int>();

        [Trusted]
        public static Ptr<T> Alloc<T>(T init, out PointsTo<T> view)
        {
            view = default; // an out parameter must be assigned before a postcondition can mention it
            Spec.Ensures(view.Addr == Spec.Result<Ptr<T>>().Addr && view.Value == Ghost.Of(init));
            int handle;
            lock (Cells)
            {
                if (FreeList.Count > 0) { handle = FreeList.Pop(); Cells[handle] = init; }
                else { handle = Cells.Count; Cells.Add(init); }
            }
            return new Ptr<T>(handle);
        }

        [Trusted]
        public static T Read<T>(in PointsTo<T> view, Ptr<T> p)
        {
            Spec.Requires(view.Addr == p.Addr);
            Spec.Ensures(Ghost.Of(Spec.Result<T>()) == view.Value);
            lock (Cells) return (T)Cells[p.Handle];
        }

        [Trusted]
        public static void Write<T>(ref PointsTo<T> view, Ptr<T> p, T value)
        {
            Spec.Requires(view.Addr == p.Addr);
            Spec.Ensures(view.Addr == Spec.Old(view).Addr && view.Value == Ghost.Of(value));
            lock (Cells) Cells[p.Handle] = value;
        }

        [Trusted]
        public static void Free<T>(PointsTo<T> view, Ptr<T> p)
        {
            Spec.Requires(view.Addr == p.Addr);
            lock (Cells) { Cells[p.Handle] = null; FreeList.Push(p.Handle); }
        }
    }
}
