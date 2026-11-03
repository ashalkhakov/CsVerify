using CsVerify;

namespace Samples.Buggy
{
    [Owned]
    public sealed class Ring
    {
        private readonly int[]? _items;
        private int _first, _count;

        [Invariant, Pure]
        public bool Valid() => _items != null && _items.Length > 0 && 0 <= _count && _count <= _items.Length && 0 <= _first && _first < _items.Length;

        public Ring(int capacity) { Spec.Requires(capacity > 0); _items = new int[capacity]; }

        // BUG: forgets to wrap around the end of the array (CSV1003)
        public void Insert(int x)
        {
            Spec.Requires(_count < _items!.Length);
            _items[_first + _count] = x;
            _count++;
        }

        // BUG: removes from an empty ring: the size would go negative (CSV1015)
        public void Clear1()
        {
            _count--;
        }
    }

    [Owned]
    public sealed class SizedTree
    {
        public int Key;
        [Owns] public SizedTree? Left;
        public Ghost<int> Size;

        [Invariant, GhostFunction]
        public bool Valid() => Size.Value == 1 + (Left == null ? 0 : Left.Size.Value);

        public SizedTree(int key) { Spec.Ensures(Key == key && Left == null && Size.Value == 1); Key = key; Size = Ghost.Of(1); }

        // BUG: adds a leaf but not to the size index (CSV1015)
        public void AddLeft(int key)
        {
            Spec.Requires(Left == null);
            Own.Give(ref Left, Own.New(new SizedTree(key), out var nv), nv);
        }
    }
}
