namespace CsVerify
{
    /// <summary>
    /// A sealed value (DiskSec's sealed blocks, Ileri et al., OSDI '18): code may store it and pass it around, but not
    /// look inside, so nothing it does depends on what it holds. <see cref="Sealed.Unseal{T}"/> is the only way in, and
    /// only a method marked <see cref="UnsealsAttribute"/> may call it: its preconditions are the access check, which
    /// the verifier proves at each of its calls. What comes out is <see cref="SensitiveAttribute"/>, followed to the
    /// logs by the taint analysis (CSV0030). Its text is a redaction.
    /// </summary>
    public sealed class Sealed<T>
    {
        internal readonly T Value;

        internal Sealed(T value)
        {
            Value = value;
        }

        /// <summary>What it holds, for specifications.</summary>
        public Ghost<T> Content => default;

        public override string ToString() => "(sealed)";
    }

    public static class Sealed
    {
        /// <summary>Seals a value: from here on, only an [Unseals] method can read it.</summary>
        [Trusted]
        public static Sealed<T> Seal<T>(T value)
        {
            Spec.Ensures(Spec.Result<Sealed<T>>() != null && Spec.Result<Sealed<T>>().Content == Ghost.Of(value));
            return new Sealed<T>(value);
        }

        /// <summary>What a sealed value holds: callable only in a method marked [Unseals] (CSV0031).</summary>
        [Trusted]
        public static T Unseal<T>(Sealed<T> sealedValue)
        {
            Spec.Requires(sealedValue != null);
            Spec.Ensures(Ghost.Of(Spec.Result<T>()) == sealedValue.Content);
            return sealedValue.Value;
        }
    }
}
