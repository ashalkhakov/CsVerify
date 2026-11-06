#nullable enable
namespace CsVerify.Bcl
{
    using System;

    /// <summary>Contracts for <see cref="string"/>: lengths (a string's characters are not modeled).</summary>
    [ContractsFor(typeof(string))]
    public static class StringContracts
    {
        [Pure]
        public static bool IsNullOrEmpty(string? value)
        {
            Spec.Ensures<bool>(r => r == (value == null || value.Length == 0));
            throw null!;
        }

        [Pure]
        public static string Substring(string @this, int startIndex)
        {
            Spec.Requires(0 <= startIndex && startIndex <= @this.Length);
            Spec.Ensures<string>(r => r.Length == @this.Length - startIndex);
            Spec.Ensures<string>(r => Spec.Forall(0, @this.Length - startIndex, i => r[i] == @this[startIndex + i]));
            throw null!;
        }

        [Pure]
        public static string Substring(string @this, int startIndex, int length)
        {
            Spec.Requires(0 <= startIndex && 0 <= length && startIndex <= @this.Length - length);
            Spec.Ensures<string>(r => r.Length == length);
            Spec.Ensures<string>(r => Spec.Forall(0, length, i => r[i] == @this[startIndex + i]));
            throw null!;
        }

        public static string Concat(string? str0, string? str1)
        {
            Spec.Ensures<string>(r => r.Length == (str0 == null ? 0 : str0.Length) + (str1 == null ? 0 : str1.Length));
            Spec.Ensures<string>(r => str0 == null || Spec.Forall(0, str0.Length, i => r[i] == str0[i]));
            Spec.Ensures<string>(r => str1 == null || Spec.Forall(0, str1.Length, i => r[(str0 == null ? 0 : str0.Length) + i] == str1[i]));
            throw null!;
        }

        // (StartsWith, EndsWith and IndexOf of a string without a StringComparison compare by culture, where a character
        // may be ignorable: "a".StartsWith("a\u00AD") holds. Nothing is known of them, not even of the lengths.)
        [Pure]
        public static bool StartsWith(string @this, string value)
        {
            throw null!;
        }

        [Pure]
        public static bool EndsWith(string @this, string value)
        {
            throw null!;
        }

        [Pure]
        public static bool StartsWith(string @this, string value, StringComparison comparisonType)
        {
            Spec.Ensures<bool>(r => comparisonType != StringComparison.Ordinal ||
                r == (value.Length <= @this.Length && Spec.Forall(0, value.Length, i => @this[i] == value[i])));
            throw null!;
        }

        [Pure]
        public static bool EndsWith(string @this, string value, StringComparison comparisonType)
        {
            Spec.Ensures<bool>(r => comparisonType != StringComparison.Ordinal ||
                r == (value.Length <= @this.Length && Spec.Forall(0, value.Length, i => @this[@this.Length - value.Length + i] == value[i])));
            throw null!;
        }

        [Pure]
        public static bool StartsWith(string @this, char value)
        {
            Spec.Ensures<bool>(r => r == (@this.Length > 0 && @this[0] == value));
            throw null!;
        }

        [Pure]
        public static bool EndsWith(string @this, char value)
        {
            Spec.Ensures<bool>(r => r == (@this.Length > 0 && @this[@this.Length - 1] == value));
            throw null!;
        }

        // (Contains compares ordinally, unlike StartsWith)
        [Pure]
        public static bool Contains(string @this, string value)
        {
            Spec.Ensures<bool>(r => !r || value.Length <= @this.Length);
            Spec.Ensures<bool>(r => r == Spec.Exists(0, @this.Length - value.Length + 1, i => Spec.Forall(0, value.Length, j => @this[i + j] == value[j])));
            throw null!;
        }

        [Pure]
        public static bool Contains(string @this, char value)
        {
            Spec.Ensures<bool>(r => r == Spec.Exists(0, @this.Length, i => @this[i] == value));
            throw null!;
        }

        [Pure]
        public static int IndexOf(string @this, char value)
        {
            Spec.Ensures<int>(r => -1 <= r && r < @this.Length);
            Spec.Ensures<int>(r => r == -1 || @this[r] == value);
            Spec.Ensures<int>(r => Spec.Forall(0, r == -1 ? @this.Length : r, i => @this[i] != value));
            throw null!;
        }

        [Pure]
        public static int LastIndexOf(string @this, char value)
        {
            Spec.Ensures<int>(r => -1 <= r && r < @this.Length);
            Spec.Ensures<int>(r => r == -1 || @this[r] == value);
            Spec.Ensures<int>(r => Spec.Forall(r + 1, @this.Length, i => @this[i] != value));
            throw null!;
        }

        public static string Trim(string @this)
        {
            Spec.Ensures<string>(r => r.Length <= @this.Length);
            throw null!;
        }

        // (invariant casing maps character by character)
        public static string ToUpperInvariant(string @this)
        {
            Spec.Ensures<string>(r => r.Length == @this.Length);
            throw null!;
        }

        public static string ToLowerInvariant(string @this)
        {
            Spec.Ensures<string>(r => r.Length == @this.Length);
            throw null!;
        }
    }

    /// <summary>Contracts for <see cref="int"/>'s parsing.</summary>
    [ContractsFor(typeof(int))]
    public static class Int32Contracts
    {
        // (it throws FormatException or OverflowException on bad input: when it returns, there were digits)
        public static int Parse(string s)
        {
            Spec.Ensures(s.Length > 0);
            throw null!;
        }

        public static bool TryParse(string? s, out int result)
        {
            result = 0; // (C# wants it set before the postconditions name it; a stub's body never runs)
            Spec.Ensures(!Spec.Result<bool>() || s != null && s.Length > 0);
            Spec.Ensures(Spec.Result<bool>() || result == 0);
            throw null!;
        }
    }

    /// <summary>
    /// Contracts for <see cref="Math"/>'s integer functions beyond Min, Max and Abs (which the verifier builds in:
    /// it must see their definitions everywhere, inside the definitions of [Pure] functions too).
    /// </summary>
    [ContractsFor(typeof(Math))]
    public static class MathContracts
    {
        [Pure]
        public static int Clamp(int value, int min, int max)
        {
            Spec.Requires(min <= max);
            Spec.Ensures<int>(r => r == (value < min ? min : value > max ? max : value));
            throw null!;
        }

        [Pure]
        public static long Clamp(long value, long min, long max)
        {
            Spec.Requires(min <= max);
            Spec.Ensures<long>(r => r == (value < min ? min : value > max ? max : value));
            throw null!;
        }

        [Pure]
        public static int Sign(int value)
        {
            Spec.Ensures<int>(r => r == (value < 0 ? -1 : value > 0 ? 1 : 0));
            throw null!;
        }

        [Pure]
        public static int Sign(long value)
        {
            Spec.Ensures<int>(r => r == (value < 0 ? -1 : value > 0 ? 1 : 0));
            throw null!;
        }
    }
}
