#nullable enable
namespace CsVerify.Bcl
{
    using System;
    using System.IO;
    using System.Threading.Tasks;

    /// <summary>
    /// Contracts for the guard clauses of <see cref="ArgumentException"/>: each returns only if its argument passes.
    /// (ArgumentNullException.ThrowIfNull needs none: its [NotNull] says it. ArgumentOutOfRangeException's generic
    /// ThrowIf… are built into the verifier, since a stub cannot compare a T.)
    /// </summary>
    [ContractsFor(typeof(ArgumentException))]
    public static class ArgumentExceptionContracts
    {
        public static void ThrowIfNullOrEmpty(string? argument, string? paramName)
        {
            Spec.Ensures(argument != null && argument.Length > 0);
            throw null!;
        }

        public static void ThrowIfNullOrWhiteSpace(string? argument, string? paramName)
        {
            Spec.Ensures(argument != null && argument.Length > 0);
            throw null!;
        }
    }

    /// <summary>
    /// Contracts for <see cref="Stream"/>'s reads into an array: the range must be in the buffer, only the buffer
    /// changes, and at most count bytes are read (0 at the end). The stream's own state is not modeled. The async one
    /// is an async stub: its postcondition is of what the task gives when awaited.
    /// </summary>
    [ContractsFor(typeof(Stream))]
    public static class StreamContracts
    {
        public static int Read(Stream @this, byte[] buffer, int offset, int count)
        {
            Spec.Requires(0 <= offset && 0 <= count && offset <= buffer.Length - count);
            Spec.Modifies(ObjSet.Of(buffer));
            Spec.Ensures<int>(r => 0 <= r && r <= count);
            throw null!;
        }

#pragma warning disable CS1998 // (a stub's body never runs)
        public static async Task<int> ReadAsync(Stream @this, byte[] buffer, int offset, int count)
        {
            Spec.Requires(0 <= offset && 0 <= count && offset <= buffer.Length - count);
            Spec.Modifies(ObjSet.Of(buffer));
            Spec.Ensures<int>(r => 0 <= r && r <= count);
            throw null!;
        }
#pragma warning restore CS1998
    }
}
