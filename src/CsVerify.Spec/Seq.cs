namespace CsVerify
{
    /// <summary>
    /// A ghost mathematical sequence, the contents of an <see cref="ArrayView{T}"/> (ATS's static lists of
    /// elements). Indices outside the view's length are unconstrained. Only usable inside specifications and
    /// [GhostFunction] bodies; every member throws at run time.
    /// </summary>
    public readonly struct Seq<T>
    {
        public Ghost<T> this[int index] => throw GhostException.Instance;

        /// <summary>This sequence with element <paramref name="index"/> replaced.</summary>
        public Seq<T> Update(int index, Ghost<T> value) => throw GhostException.Instance;

        /// <summary>The sequence starting at <paramref name="count"/>: Drop(n)[i] == this[n + i].</summary>
        public Seq<T> Drop(int count) => throw GhostException.Instance;

        /// <summary>The first <paramref name="count"/> elements of this sequence followed by <paramref name="rest"/>.</summary>
        public Seq<T> Concat(int count, Seq<T> rest) => throw GhostException.Instance;

        public static bool operator ==(Seq<T> left, Seq<T> right) => throw GhostException.Instance;
        public static bool operator !=(Seq<T> left, Seq<T> right) => throw GhostException.Instance;
        public override bool Equals(object obj) => throw GhostException.Instance;
        public override int GetHashCode() => 0;
    }

    public static class Seq
    {
        /// <summary>The sequence with every element equal to <paramref name="value"/>.</summary>
        public static Seq<T> Const<T>(T value) => throw GhostException.Instance;

        /// <summary>
        /// The elements of an array of any type, as the verifier stores them (for contracts over <see cref="System.Array"/>,
        /// whose elements C# cannot index): compare them with each other, not with typed values.
        /// </summary>
        public static Seq<object> Contents(System.Array array) => throw GhostException.Instance;
    }
}
