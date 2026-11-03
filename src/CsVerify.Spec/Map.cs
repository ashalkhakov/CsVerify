namespace CsVerify
{
    /// <summary>
    /// A ghost total map from keys to values (an SMT array), such as a dictionary's contents (<c>CsVerify.Bcl</c>'s
    /// models). Keys compare as the verifier compares values of their type (references by identity). Only usable inside
    /// specifications and [GhostFunction] bodies; every member throws at run time.
    /// </summary>
    public readonly struct Map<K, V>
    {
        public Ghost<V> this[K key] => throw GhostException.Instance;

        /// <summary>This map with <paramref name="key"/> mapped to <paramref name="value"/>.</summary>
        public Map<K, V> Update(K key, Ghost<V> value) => throw GhostException.Instance;

        public static bool operator ==(Map<K, V> left, Map<K, V> right) => throw GhostException.Instance;
        public static bool operator !=(Map<K, V> left, Map<K, V> right) => throw GhostException.Instance;
        public override bool Equals(object obj) => throw GhostException.Instance;
        public override int GetHashCode() => 0;
    }

    public static class Map
    {
        /// <summary>The map taking every key to <paramref name="value"/>.</summary>
        public static Map<K, V> Const<K, V>(V value) => throw GhostException.Instance;
    }
}
