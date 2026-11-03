using CsVerify;

namespace Samples
{
    /// <summary>
    /// Null references are proved absent, not hoped absent. A non-nullable reference type is a contract (callers
    /// prove arguments, the method proves its result); <c>T?</c> must be checked before use; <c>!</c> proves nothing.
    /// </summary>
    public static class Nulls
    {
        public static int LengthOr(int[]? a, int d)
        {
            Spec.Ensures((int r) => a == null ? r == d : r == a.Length);
            if (a == null) return d;
            return a.Length;
        }

        public static int[] OrEmpty(int[]? a)
        {
            Spec.Ensures((int[] r) => a == null ? r.Length == 0 : r == a);
            return a ?? new int[0];
        }

        /// <summary>C# lets a string[] hold nulls (new string[n] is all nulls): the precondition rules them out.</summary>
        public static int TotalLength(string[] words)
        {
            Spec.Requires(Spec.Forall(0, words.Length, i => words[i] != null));
            int total = 0;
            for (int i = 0; i < words.Length; i++)
            {
                Spec.Invariant(0 <= i && i <= words.Length);
                total = checked(total + words[i].Length);
            }
            return total;
        }

        public static int CountPresent(string?[] xs)
        {
            Spec.Ensures((int r) => 0 <= r && r <= xs.Length);
            int n = 0;
            for (int i = 0; i < xs.Length; i++)
            {
                Spec.Invariant(0 <= i && i <= xs.Length && 0 <= n && n <= i);
                if (xs[i] is not null) n++;
            }
            return n;
        }

        public static int Demo()
        {
            Spec.Ensures((int r) => r == 7 + 2);
            TotalLength(new[] { "ab", "c" }); // its precondition: no element is null
            return LengthOr(null, 7) + OrEmpty(new[] { 1, 2 }).Length;
        }
    }
}
