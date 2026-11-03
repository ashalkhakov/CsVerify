using System;
using CsVerify;

namespace Samples
{
    // Exceptions: methods are verified for partial correctness (any call may throw), Spec.EnsuresOnThrow says what
    // holds if one does, and try/catch/finally handlers are verified on every path that reaches them.
    public static class ExceptionSamples
    {
        /// <summary>A digit's value; anything else is rejected with an exception, which says why.</summary>
        public static int Digit(char c)
        {
            Spec.Ensures((int r) => '0' <= c && c <= '9' && r == c - '0');
            Spec.EnsuresOnThrow<ArgumentException>(c < '0' || c > '9');
            if (c < '0' || c > '9') throw new ArgumentException("not a digit");
            return c - '0';
        }

        /// <summary>The TryParse pattern over Digit: no exception escapes, and -1 means "not a digit".</summary>
        public static int DigitOrMinusOne(char c)
        {
            Spec.Ensures((int r) => r == -1 || 0 <= r && r <= 9);
            try { return Digit(c); }
            catch (ArgumentException) { return -1; }
        }

        /// <summary>Adds the cells, saturating instead of overflowing: checked arithmetic throws, and is caught.</summary>
        public static int SaturatingSum(int[] a)
        {
            Spec.Ensures((int r) => r == int.MaxValue || r == int.MinValue || r == Spec.Old(Sum(a, a.Length)));
            try
            {
                int s = 0;
                for (int i = 0; i < a.Length; i++)
                {
                    Spec.Invariant(0 <= i && i <= a.Length && s == Sum(a, i));
                    Spec.Decreases(a.Length - i);
                    s = checked(s + a[i]);
                }
                return s;
            }
            catch (OverflowException) { return a.Length > 0 && a[0] < 0 ? int.MinValue : int.MaxValue; }
        }

        /// <summary>The sum of a[0..n), mathematically.</summary>
        [GhostFunction]
        public static int Sum(int[] a, int n)
        {
            Spec.Requires(0 <= n && n <= a.Length);
            Spec.Decreases(n);
            return n == 0 ? 0 : Sum(a, n - 1) + a[n - 1];
        }

        /// <summary>
        /// A two-step update that may fail halfway: the catch rolls the first step back, so on a failure the
        /// array is as it was (rethrown, with that promise).
        /// </summary>
        public static void Update(int[] a, char c)
        {
            Spec.Requires(a.Length == 2);
            Spec.Ensures(a[0] == Spec.Old(a[0]) + 1 && 0 <= a[1] && a[1] <= 9);
            Spec.EnsuresOnThrow<Exception>(a[0] == Spec.Old(a[0]) && a[1] == Spec.Old(a[1]));
            int before = a[0];
            a[0] = checked(a[0] + 1);
            try { a[1] = Digit(c); }
            catch (Exception) { a[0] = before; throw; }
        }

        /// <summary>A finally runs on every way out: here it marks the work done whether it finished or threw.</summary>
        public static int Guarded(bool[] done, char c)
        {
            Spec.Requires(done.Length == 1);
            Spec.Ensures((int r) => done[0] && 0 <= r && r <= 9);
            Spec.EnsuresOnThrow<Exception>(done[0]);
            done[0] = false;
            try { return Digit(c); }
            finally { done[0] = true; }
        }
    }
}
