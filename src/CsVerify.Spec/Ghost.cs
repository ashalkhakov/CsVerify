using System;

namespace CsVerify
{
    /// <summary>
    /// A static index (ATS <c>{n:int}</c>): a value that exists only for the verifier. Zero size at run time;
    /// <see cref="Value"/> may only be read inside specifications, lemma arguments and lemma bodies.
    /// </summary>
    public readonly struct Ghost<T> : IEquatable<Ghost<T>>
    {
        public T Value => throw GhostException.Instance;

        public static bool operator ==(Ghost<T> left, Ghost<T> right) => throw GhostException.Instance;
        public static bool operator !=(Ghost<T> left, Ghost<T> right) => throw GhostException.Instance;
        public bool Equals(Ghost<T> other) => throw GhostException.Instance;
        public override bool Equals(object obj) => throw GhostException.Instance;
        public override int GetHashCode() => 0;
    }

    public static class Ghost
    {
        /// <summary>Makes a ghost value. The argument is ghost context; nothing is stored.</summary>
        public static Ghost<T> Of<T>(T value) => default;
    }
}
