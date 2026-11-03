namespace CsVerify
{
    /// <summary>
    /// A ghost set of objects (Dafny's <c>set&lt;object&gt;</c>), for dynamic frames: an object's representation
    /// <c>Ghost&lt;ObjSet&gt; Repr</c>, a method's <see cref="Spec.Modifies"/> and a [Pure] function's
    /// <see cref="Spec.Reads"/>. Only usable inside specifications and ghost code; every member throws at run time.
    /// </summary>
    public readonly struct ObjSet
    {
        public static ObjSet Empty => throw GhostException.Instance;
        public static ObjSet Of(object item) => throw GhostException.Instance;

        public bool Contains(object item) => throw GhostException.Instance;
        public ObjSet Add(object item) => throw GhostException.Instance;
        public ObjSet Union(ObjSet other) => throw GhostException.Instance;
        public bool IsSubsetOf(ObjSet other) => throw GhostException.Instance;
        public bool IsDisjointFrom(ObjSet other) => throw GhostException.Instance;

        public static bool operator ==(ObjSet left, ObjSet right) => throw GhostException.Instance;
        public static bool operator !=(ObjSet left, ObjSet right) => throw GhostException.Instance;
        public override bool Equals(object obj) => throw GhostException.Instance;
        public override int GetHashCode() => 0;
    }
}
