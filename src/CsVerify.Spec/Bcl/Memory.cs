#nullable enable
namespace CsVerify.Bcl
{
    using System;
    using System.Buffers.Binary;

    /// <summary>
    /// Contracts for searching spans (<see cref="MemoryExtensions"/>): where a result can be, for every T. What it says
    /// of the elements (that span[r] equals value) depends on T's Equals, so it is not said here. (A span cannot be
    /// captured by a lambda: the postconditions name Spec.Result.)
    /// </summary>
    [ContractsFor(typeof(MemoryExtensions))]
    public static class MemoryExtensionsContracts
    {
        [Pure]
        public static int IndexOf<T>(ReadOnlySpan<T> span, T value) where T : IEquatable<T>?
        {
            Spec.Ensures(-1 <= Spec.Result<int>() && Spec.Result<int>() < span.Length);
            throw null!;
        }

        [Pure]
        public static int IndexOf<T>(Span<T> span, T value) where T : IEquatable<T>?
        {
            Spec.Ensures(-1 <= Spec.Result<int>() && Spec.Result<int>() < span.Length);
            throw null!;
        }

        [Pure]
        public static int LastIndexOf<T>(ReadOnlySpan<T> span, T value) where T : IEquatable<T>?
        {
            Spec.Ensures(-1 <= Spec.Result<int>() && Spec.Result<int>() < span.Length);
            throw null!;
        }

        [Pure]
        public static int IndexOfAny<T>(ReadOnlySpan<T> span, T value0, T value1) where T : IEquatable<T>?
        {
            Spec.Ensures(-1 <= Spec.Result<int>() && Spec.Result<int>() < span.Length);
            throw null!;
        }

        [Pure]
        public static int IndexOfAny<T>(ReadOnlySpan<T> span, T value0, T value1, T value2) where T : IEquatable<T>?
        {
            Spec.Ensures(-1 <= Spec.Result<int>() && Spec.Result<int>() < span.Length);
            throw null!;
        }

        [Pure]
        public static bool SequenceEqual<T>(ReadOnlySpan<T> span, ReadOnlySpan<T> other) where T : IEquatable<T>?
        {
            Spec.Ensures(!Spec.Result<bool>() || span.Length == other.Length);
            throw null!;
        }

        [Pure]
        public static bool StartsWith<T>(ReadOnlySpan<T> span, ReadOnlySpan<T> value) where T : IEquatable<T>?
        {
            Spec.Ensures(!Spec.Result<bool>() || value.Length <= span.Length);
            throw null!;
        }
    }

    /// <summary>Contracts for <see cref="BinaryPrimitives"/>' reads: the span holds the value's bytes (they throw otherwise).</summary>
    [ContractsFor(typeof(BinaryPrimitives))]
    public static class BinaryPrimitivesContracts
    {
        [Pure] public static short ReadInt16BigEndian(ReadOnlySpan<byte> source) { Spec.Requires(source.Length >= 2); throw null!; }
        [Pure] public static short ReadInt16LittleEndian(ReadOnlySpan<byte> source) { Spec.Requires(source.Length >= 2); throw null!; }
        [Pure] public static ushort ReadUInt16BigEndian(ReadOnlySpan<byte> source) { Spec.Requires(source.Length >= 2); throw null!; }
        [Pure] public static ushort ReadUInt16LittleEndian(ReadOnlySpan<byte> source) { Spec.Requires(source.Length >= 2); throw null!; }
        [Pure] public static int ReadInt32BigEndian(ReadOnlySpan<byte> source) { Spec.Requires(source.Length >= 4); throw null!; }
        [Pure] public static int ReadInt32LittleEndian(ReadOnlySpan<byte> source) { Spec.Requires(source.Length >= 4); throw null!; }
        [Pure] public static uint ReadUInt32BigEndian(ReadOnlySpan<byte> source) { Spec.Requires(source.Length >= 4); throw null!; }
        [Pure] public static uint ReadUInt32LittleEndian(ReadOnlySpan<byte> source) { Spec.Requires(source.Length >= 4); throw null!; }
        [Pure] public static long ReadInt64BigEndian(ReadOnlySpan<byte> source) { Spec.Requires(source.Length >= 8); throw null!; }
        [Pure] public static long ReadInt64LittleEndian(ReadOnlySpan<byte> source) { Spec.Requires(source.Length >= 8); throw null!; }
    }
}
