#nullable enable
namespace CsVerify.Bcl
{
    using System;
    using System.IO;
    using System.Text;

    /// <summary>The model function of a <see cref="StringBuilder"/>: its length (its characters are not modeled).</summary>
    public static class TextModels
    {
        /// <summary>How many characters a builder holds (its Length).</summary>
        [Model]
        public static int Size(this StringBuilder builder)
        {
            Spec.Ensures<int>(r => r >= 0);
            throw null!;
        }
    }

    /// <summary>
    /// Contracts for <see cref="StringBuilder"/>: how its length changes. Each Append returns the builder itself.
    /// Formatting a number gives at least one character; how many more depends on the culture, so it is not given.
    /// </summary>
    [ContractsFor(typeof(StringBuilder))]
    public static class StringBuilderContracts
    {
        public static StringBuilder @new()
        {
            Spec.Ensures<StringBuilder>(r => r.Size() == 0);
            throw null!;
        }

        public static StringBuilder @new(int capacity)
        {
            Spec.Requires(capacity >= 0);
            Spec.Ensures<StringBuilder>(r => r.Size() == 0);
            throw null!;
        }

        public static StringBuilder @new(string? value)
        {
            Spec.Ensures<StringBuilder>(r => r.Size() == (value == null ? 0 : value.Length));
            throw null!;
        }

        [Pure]
        public static int get_Length(StringBuilder @this)
        {
            Spec.Ensures<int>(r => r == @this.Size());
            throw null!;
        }

        public static void set_Length(StringBuilder @this, int value)
        {
            Spec.Requires(value >= 0);
            Spec.Modifies(ObjSet.Of(@this));
            Spec.Ensures(@this.Size() == value);
            throw null!;
        }

        // (the character itself is not modeled; the index is in range)
        [Pure]
        public static char get_Chars(StringBuilder @this, int index)
        {
            Spec.Requires(0 <= index && index < @this.Size());
            throw null!;
        }

        public static StringBuilder Append(StringBuilder @this, char value)
        {
            Spec.Modifies(ObjSet.Of(@this));
            Spec.Ensures<StringBuilder>(r => r == @this && @this.Size() == Spec.Old(@this.Size()) + 1);
            throw null!;
        }

        public static StringBuilder Append(StringBuilder @this, char value, int repeatCount)
        {
            Spec.Requires(repeatCount >= 0);
            Spec.Modifies(ObjSet.Of(@this));
            Spec.Ensures<StringBuilder>(r => r == @this && @this.Size() == Spec.Old(@this.Size()) + repeatCount);
            throw null!;
        }

        public static StringBuilder Append(StringBuilder @this, string? value)
        {
            Spec.Modifies(ObjSet.Of(@this));
            Spec.Ensures<StringBuilder>(r => r == @this && @this.Size() == Spec.Old(@this.Size()) + (value == null ? 0 : value.Length));
            throw null!;
        }

        public static StringBuilder Append(StringBuilder @this, string? value, int startIndex, int count)
        {
            Spec.Requires(0 <= startIndex && 0 <= count);
            Spec.Requires(value == null ? startIndex == 0 && count == 0 : startIndex <= value.Length - count);
            Spec.Modifies(ObjSet.Of(@this));
            Spec.Ensures<StringBuilder>(r => r == @this && @this.Size() == Spec.Old(@this.Size()) + count);
            throw null!;
        }

        public static StringBuilder Append(StringBuilder @this, StringBuilder? value)
        {
            Spec.Modifies(ObjSet.Of(@this));
            Spec.Ensures<StringBuilder>(r => r == @this && @this.Size() == Spec.Old(@this.Size()) + (value == null ? 0 : Spec.Old(value.Size())));
            throw null!;
        }

        public static StringBuilder Append(StringBuilder @this, int value)
        {
            Spec.Modifies(ObjSet.Of(@this));
            Spec.Ensures<StringBuilder>(r => r == @this && @this.Size() > Spec.Old(@this.Size()));
            throw null!;
        }

        public static StringBuilder Append(StringBuilder @this, long value)
        {
            Spec.Modifies(ObjSet.Of(@this));
            Spec.Ensures<StringBuilder>(r => r == @this && @this.Size() > Spec.Old(@this.Size()));
            throw null!;
        }

        // (an object's ToString may be anything, null or empty included)
        public static StringBuilder Append(StringBuilder @this, object? value)
        {
            Spec.Modifies(ObjSet.Of(@this));
            Spec.Ensures<StringBuilder>(r => r == @this && @this.Size() >= Spec.Old(@this.Size()));
            throw null!;
        }

        // (Environment.NewLine is one or two characters)
        public static StringBuilder AppendLine(StringBuilder @this)
        {
            Spec.Modifies(ObjSet.Of(@this));
            Spec.Ensures<StringBuilder>(r => r == @this && Spec.Old(@this.Size()) + 1 <= @this.Size() && @this.Size() <= Spec.Old(@this.Size()) + 2);
            throw null!;
        }

        public static StringBuilder AppendLine(StringBuilder @this, string? value)
        {
            Spec.Modifies(ObjSet.Of(@this));
            Spec.Ensures<StringBuilder>(r => r == @this && Spec.Old(@this.Size()) + (value == null ? 0 : value.Length) + 1 <= @this.Size() &&
                                             @this.Size() <= Spec.Old(@this.Size()) + (value == null ? 0 : value.Length) + 2);
            throw null!;
        }

        public static StringBuilder Insert(StringBuilder @this, int index, string? value)
        {
            Spec.Requires(0 <= index && index <= @this.Size());
            Spec.Modifies(ObjSet.Of(@this));
            Spec.Ensures<StringBuilder>(r => r == @this && @this.Size() == Spec.Old(@this.Size()) + (value == null ? 0 : value.Length));
            throw null!;
        }

        public static StringBuilder Remove(StringBuilder @this, int startIndex, int length)
        {
            Spec.Requires(0 <= startIndex && 0 <= length && startIndex <= @this.Size() - length);
            Spec.Modifies(ObjSet.Of(@this));
            Spec.Ensures<StringBuilder>(r => r == @this && @this.Size() == Spec.Old(@this.Size()) - length);
            throw null!;
        }

        public static StringBuilder Clear(StringBuilder @this)
        {
            Spec.Modifies(ObjSet.Of(@this));
            Spec.Ensures<StringBuilder>(r => r == @this && @this.Size() == 0);
            throw null!;
        }

        public static string ToString(StringBuilder @this)
        {
            Spec.Ensures<string>(r => r.Length == @this.Size());
            throw null!;
        }

        public static string ToString(StringBuilder @this, int startIndex, int length)
        {
            Spec.Requires(0 <= startIndex && 0 <= length && startIndex <= @this.Size() - length);
            Spec.Ensures<string>(r => r.Length == length);
            throw null!;
        }
    }

    /// <summary>
    /// Contracts for <see cref="TextWriter"/>: writing changes nothing the verifier models (only the writer's output,
    /// which is not modeled), and writes no arrays or fields of yours. A writer's overrides in the library (StreamWriter,
    /// StringWriter) keep these contracts; yours are checked against them. A write may throw (an IOException).
    /// </summary>
    [ContractsFor(typeof(TextWriter))]
    public static class TextWriterContracts
    {
        public static void Write(TextWriter @this, string? value) { throw null!; }
        public static void Write(TextWriter @this, char value) { throw null!; }
        public static void Write(TextWriter @this, int value) { throw null!; }
        public static void Write(TextWriter @this, long value) { throw null!; }
        public static void Write(TextWriter @this, bool value) { throw null!; }
        public static void Write(TextWriter @this, object? value) { throw null!; }
        public static void Write(TextWriter @this, string format, object? arg0) { throw null!; }
        public static void Write(TextWriter @this, string format, object? arg0, object? arg1) { throw null!; }
        public static void Write(TextWriter @this, string format, params object?[] arg) { throw null!; }

        public static void Write(TextWriter @this, char[] buffer, int index, int count)
        {
            Spec.Requires(0 <= index && 0 <= count && index <= buffer.Length - count);
            throw null!;
        }

        public static void WriteLine(TextWriter @this) { throw null!; }
        public static void WriteLine(TextWriter @this, string? value) { throw null!; }
        public static void WriteLine(TextWriter @this, char value) { throw null!; }
        public static void WriteLine(TextWriter @this, int value) { throw null!; }
        public static void WriteLine(TextWriter @this, long value) { throw null!; }
        public static void WriteLine(TextWriter @this, bool value) { throw null!; }
        public static void WriteLine(TextWriter @this, object? value) { throw null!; }
        public static void WriteLine(TextWriter @this, string format, object? arg0) { throw null!; }
        public static void WriteLine(TextWriter @this, string format, object? arg0, object? arg1) { throw null!; }
        public static void WriteLine(TextWriter @this, string format, params object?[] arg) { throw null!; }
        public static void Flush(TextWriter @this) { throw null!; }
    }
}
