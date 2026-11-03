namespace CsVerify
{
    /// <summary>
    /// A ghost multiset of integers (Dafny's <c>multiset&lt;int&gt;</c>): how many times each value occurs.
    /// <see cref="Spec.Multiset"/> gives the multiset of an array prefix, so "a is a permutation of what it was" is
    /// <c>Spec.Multiset(a, n) == Spec.Old(Spec.Multiset(a, n))</c>. Only usable inside specifications and ghost
    /// code; every member throws at run time.
    /// </summary>
    public readonly struct Bag
    {
        public static Bag Empty => throw GhostException.Instance;
        public static Bag Of(int item) => throw GhostException.Instance;

        /// <summary>How many times <paramref name="item"/> occurs.</summary>
        public int Count(int item) => throw GhostException.Instance;
        public bool Contains(int item) => throw GhostException.Instance;
        public Bag Add(int item) => throw GhostException.Instance;
        public Bag Union(Bag other) => throw GhostException.Instance;

        public static bool operator ==(Bag left, Bag right) => throw GhostException.Instance;
        public static bool operator !=(Bag left, Bag right) => throw GhostException.Instance;
        public override bool Equals(object obj) => throw GhostException.Instance;
        public override int GetHashCode() => 0;
    }
}
