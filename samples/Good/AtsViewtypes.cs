using CsVerify;

namespace Samples
{
    // Ports from INT2PROGINATS part IV, "Programming with Views and Viewtypes" (Xi), rewritten in C#: linear lists
    // and trees as ownership trees (dataviewtypes, ch. 15) and abstract viewtypes as [Owned] classes (ch. 16).

    /// <summary>
    /// A node of a linear list, list_vt(int, n): the node owns the rest of the list. Len is the list's length (the
    /// type's index); Ord says this list is sorted, which the book's insertion sort does not prove and this one does.
    /// </summary>
    [Owned]
    public sealed class LNode
    {
        public int Val;
        [Owns] public LNode? Next;
        public Ghost<int> Len;
        public Ghost<bool> Ord;

        [Invariant, GhostFunction]
        public bool Valid() =>
            Len.Value >= 1 && (Next == null ? Len.Value == 1 : Len.Value == Next.Len.Value + 1) &&
            (!Ord.Value || Next == null || Next.Ord.Value && Val <= Next.Val);

        public LNode(int v)
        {
            Spec.Ensures(Val == v && Next == null && Len.Value == 1 && Ord.Value);
            Val = v;
            Len = Ghost.Of(1);
            Ord = Ghost.Of(true);
        }
    }

    /// <summary>A linear list: an owned, possibly empty chain of nodes.</summary>
    [Owned]
    public sealed class LList
    {
        [Owns] public LNode? Head;
        public Ghost<int> Len;

        [Invariant, GhostFunction]
        public bool Valid() => Head == null ? Len.Value == 0 : Len.Value == Head.Len.Value && Head.Len.Value >= 1;

        public LList() { Spec.Ensures(Head == null && Len.Value == 0); Len = Ghost.Of(0); }

        public void Push(int v)
        {
            Spec.Ensures(Len.Value == Spec.Old(Len.Value) + 1);
            var n = Own.New(new LNode(v), out var nv);
            if (Head != null)
            {
                var rest = Own.Take(ref Head, out var rv);
                Own.Give(ref n.Next, rest, rv);
                n.Len = Ghost.Of(rest.Len.Value + 1);
                n.Ord = Ghost.Of(false);
            }
            Own.Give(ref Head, n, nv);
            Len = Ghost.Of(Len.Value + 1);
        }
    }

    /// <summary>A node of a linear binary search tree, bstree_vt(int, n): it owns both subtrees; Size is n.</summary>
    [Owned]
    public sealed class BNode
    {
        public int Key;
        [Owns] public BNode? Left, Right;
        public Ghost<int> Size;

        [Invariant, GhostFunction]
        public bool Valid() =>
            Size.Value == 1 + (Left == null ? 0 : Left.Size.Value) + (Right == null ? 0 : Right.Size.Value) &&
            (Left == null || Left.Size.Value >= 1) && (Right == null || Right.Size.Value >= 1) &&
            (Left == null || Left.Key <= Key) && (Right == null || Key <= Right.Key);

        public BNode(int key)
        {
            Spec.Ensures(Key == key && Left == null && Right == null && Size.Value == 1);
            Key = key;
            Size = Ghost.Of(1);
        }

        /// <summary>insert: the new key becomes a leaf, and the size index grows by one.</summary>
        public void Insert(int key)
        {
            Spec.Decreases(Size.Value);
            Spec.Ensures(Key == Spec.Old(Key) && Size.Value == Spec.Old(Size.Value) + 1);
            if (key < Key)
            {
                if (Left == null) Own.Give(ref Left, Own.New(new BNode(key), out var nv), nv);
                else
                {
                    var l = Own.Take(ref Left, out var lv);
                    Spec.Assert(Size.Value == 1 + l.Size.Value + (Right == null ? 0 : Right.Size.Value)); // the size, unfolded
                    l.Insert(key);
                    Own.Give(ref Left, l, lv);
                }
            }
            else
            {
                if (Right == null) Own.Give(ref Right, Own.New(new BNode(key), out var nv), nv);
                else
                {
                    var r = Own.Take(ref Right, out var rv);
                    Spec.Assert(Size.Value == 1 + (Left == null ? 0 : Left.Size.Value) + r.Size.Value);
                    r.Insert(key);
                    Own.Give(ref Right, r, rv);
                }
            }
            Size = Ghost.Of(Size.Value + 1);
        }
    }

    /// <summary>
    /// The array-based circular buffer, cbufObj(a, m, n): capacity m, size n. The book's implementations skip the
    /// proofs ("too costly"); here the bounds are the object's invariant and every index is checked.
    /// </summary>
    [Owned]
    public sealed class CircularBuffer
    {
        private readonly int[]? _items;
        private int _first, _count;

        [Invariant, Pure]
        public bool Valid() => _items != null && _items.Length > 0 && 0 <= _count && _count <= _items.Length && 0 <= _first && _first < _items.Length;

        public CircularBuffer(int capacity)
        {
            Spec.Requires(capacity > 0);
            Spec.Ensures(_items != null && _items.Length == capacity && _count == 0);
            _items = new int[capacity];
        }

        [Pure] public int Capacity() { Spec.Requires(_items != null); return _items.Length; }
        [Pure] public int Size() => _count;

        /// <summary>cbufObj_insert: {n &lt; m} n becomes n + 1.</summary>
        public void Insert(int x)
        {
            Spec.Requires(_count < Capacity());
            Spec.Ensures(_count == Spec.Old(_count) + 1 && _items == Spec.Old(_items));
            int last = _first + _count;
            if (last >= _items!.Length) last -= _items.Length;
            _items[last] = x;
            _count++;
        }

        /// <summary>cbufObj_remove: {n &gt; 0} n becomes n - 1, and the oldest element comes out.</summary>
        public int Remove()
        {
            Spec.Requires(_count > 0);
            Spec.Ensures(_count == Spec.Old(_count) - 1 && _items == Spec.Old(_items));
            int x = _items![_first];
            _first++;
            if (_first == _items.Length) _first = 0;
            _count--;
            return x;
        }
    }

    /// <summary>
    /// The stopwatch timer of ch. 16 ("simple linear objects"): made by Own.New, borrowed by every operation, gone
    /// with Own.Drop. The clock is passed in, so the sample is deterministic.
    /// </summary>
    [Owned]
    public sealed class Timer
    {
        private bool _started, _running;
        private long _resumedAt, _ticks;

        [Invariant, Pure] public bool Valid() => _ticks >= 0 && (!_running || _started);

        public void Start(long now) { Spec.Ensures(_running && _resumedAt == now && _ticks == 0); _started = true; _running = true; _resumedAt = now; _ticks = 0; }

        public void Pause(long now)
        {
            Spec.Requires(!_running || now >= _resumedAt);
            Spec.Ensures(!_running && _started == Spec.Old(_started) && _ticks == Spec.Old(Ticks(now)));
            if (_running) { _ticks += now - _resumedAt; _running = false; }
        }

        public void Resume(long now)
        {
            Spec.Requires(_started && !_running);
            Spec.Ensures(_running && _resumedAt == now && _ticks == Spec.Old(_ticks));
            _running = true;
            _resumedAt = now;
        }

        /// <summary>The ticks counted so far, the running interval included.</summary>
        [Pure] public long Ticks(long now) => _running ? _ticks + (now - _resumedAt) : _ticks;
    }

    public static class AtsViewtypes
    {
        /// <summary>insord: x goes into the sorted list xs, after every element not greater (stable); nodes are only relinked.</summary>
        public static LNode Insord(LNode xs, Own<LNode> xsView, LNode x, Own<LNode> xView, out Own<LNode> result)
        {
            Spec.Requires(xsView.Obj.Value == xs && xView.Obj.Value == x && xs.Ord.Value && x.Next == null);
            Spec.Decreases(xs.Len.Value);
            // (a lambda cannot capture the out parameter, so the result is Spec.Result)
            Spec.Ensures(result.Obj.Value == Spec.Result<LNode>() && Spec.Result<LNode>().Ord.Value &&
                         Spec.Result<LNode>().Len.Value == Spec.Old(xs.Len.Value) + 1 &&
                         (Spec.Result<LNode>() == x && x.Val == Spec.Old(x.Val) || Spec.Result<LNode>() == xs && xs.Val == Spec.Old(xs.Val)));
            if (x.Val < xs.Val)
            {
                Own.Give(ref x.Next, xs, xsView);
                x.Len = Ghost.Of(xs.Len.Value + 1);
                x.Ord = Ghost.Of(true);
                result = xView;
                return x;
            }
            if (xs.Next == null)
            {
                x.Ord = Ghost.Of(true);
                Own.Give(ref xs.Next, x, xView);
                xs.Len = Ghost.Of(2);
                result = xsView;
                return xs;
            }
            var rest = Own.Take(ref xs.Next, out var restView);
            var r = Insord(rest, restView, x, xView, out var rView);
            Own.Give(ref xs.Next, r, rView);
            xs.Len = Ghost.Of(r.Len.Value + 1);
            result = xsView;
            return xs;
        }

        /// <summary>
        /// insertionSort: takes the nodes of <paramref name="input"/> one by one and inserts each into
        /// <paramref name="sorted"/>. No node is allocated or freed; the total length is preserved (list_vt(a, n)).
        /// </summary>
        public static void InsertionSort(LList input, ref Own<LList> inView, LList sorted, ref Own<LList> outView)
        {
            Spec.Requires(inView.Obj.Value == input && outView.Obj.Value == sorted);
            Spec.Requires(sorted.Head == null || sorted.Head.Ord.Value);
            Spec.Decreases(input.Len.Value);
            Spec.Ensures(inView.Obj.Value == input && outView.Obj.Value == sorted); // the same views come back
            Spec.Ensures(input.Len.Value == 0 && sorted.Len.Value == Spec.Old(input.Len.Value) + Spec.Old(sorted.Len.Value));
            Spec.Ensures(sorted.Head == null || sorted.Head.Ord.Value);
            if (input.Head == null) return;
            var x = Own.Take(ref input.Head, out var xv);
            if (x.Next != null)
            {
                var rest = Own.Take(ref x.Next, out var rv);
                Own.Give(ref input.Head, rest, rv);
            }
            input.Len = Ghost.Of(input.Len.Value - 1);
            x.Len = Ghost.Of(1);
            if (sorted.Head == null)
            {
                x.Ord = Ghost.Of(true);
                Own.Give(ref sorted.Head, x, xv);
            }
            else
            {
                var s = Own.Take(ref sorted.Head, out var sv);
                var r = Insord(s, sv, x, xv, out var rv);
                Own.Give(ref sorted.Head, r, rv);
            }
            sorted.Len = Ghost.Of(sorted.Len.Value + 1);
            InsertionSort(input, ref inView, sorted, ref outView);
        }

        /// <summary>The list's values in order, as digits (first value lowest), to check what the run time built.</summary>
        public static int Digits(LNode n, ref Own<LNode> v)
        {
            Spec.Requires(v.Obj.Value == n);
            Spec.Decreases(n.Len.Value);
            Spec.Ensures(v.Obj.Value == n && n.Len.Value == Spec.Old(n.Len.Value));
            if (n.Next == null) return n.Val;
            var next = Own.Take(ref n.Next, out var nv);
            int rest = Digits(next, ref nv);
            Own.Give(ref n.Next, next, nv);
            return n.Val + 10 * rest;
        }

        /// <summary>A linear list 3 1 4 1 5 sorted in place; its values read back as digits.</summary>
        public static int SortDemo()
        {
            var input = Own.New(new LList(), out var iv);
            input.Push(5); input.Push(1); input.Push(4); input.Push(1); input.Push(3);
            var sorted = Own.New(new LList(), out var sv);
            InsertionSort(input, ref iv, sorted, ref sv);
            Spec.Assert(sorted.Len.Value == 5 && input.Head == null);
            int digits = 0;
            if (sorted.Head != null)
            {
                var h = Own.Take(ref sorted.Head, out var hv);
                digits = Digits(h, ref hv);
                Own.Give(ref sorted.Head, h, hv);
            }
            Own.Drop(iv);
            Own.Drop(sv);
            return digits;
        }

        public static int TreeDemo()
        {
            Spec.Ensures((int r) => r == 4);
            var t = Own.New(new BNode(5), out var tv);
            t.Insert(3); t.Insert(8); t.Insert(4);
            var size = Ghost.Of(t.Size.Value);
            Spec.Assert(size.Value == 4);
            Own.Drop(tv);
            return 4;
        }

        /// <summary>A buffer of capacity 2 that wraps around: 7 and 8 in, 7 out, 9 in, 8 out.</summary>
        public static int BufferDemo()
        {
            var b = Own.New(new CircularBuffer(2), out var bv);
            b.Insert(7); b.Insert(8);
            int first = b.Remove();
            b.Insert(9);
            int second = b.Remove();
            Spec.Assert(b.Size() == 1);
            Own.Drop(bv);
            return first * 10 + second;
        }

        /// <summary>A timer started at 100, paused at 130, resumed at 500: at 510 it has counted 40.</summary>
        public static long TimerDemo()
        {
            Spec.Ensures((long r) => r == 40);
            var timer = Own.New(new Timer(), out var timerView);
            timer.Start(100);
            timer.Pause(130);
            timer.Resume(500);
            long ticks = timer.Ticks(510);
            Own.Drop(timerView);
            return ticks;
        }

        public static long Demo() => SortDemo() * 10000L + BufferDemo() * 100 + TimerDemo() + TreeDemo() * 1000;
    }
}
