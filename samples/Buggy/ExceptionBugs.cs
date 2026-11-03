using System;
using CsVerify;

namespace Samples.Buggy
{
    public static class ExceptionBugs
    {
        public static int PositiveOnly(int x)
        {
            Spec.Ensures((int r) => r == x && x > 0);
            Spec.EnsuresOnThrow<ArgumentOutOfRangeException>(x <= 0);
            if (x <= 0) throw new ArgumentOutOfRangeException(nameof(x));
            return x;
        }

        // BUG: the catch returns 0, which the postcondition rules out (CSV1002)
        public static int AtLeastOne(int x)
        {
            Spec.Ensures((int r) => r >= 1);
            try { return PositiveOnly(x); }
            catch (ArgumentOutOfRangeException) { return 0; }
        }

        // BUG: forgets to roll back the first step before the failure escapes (CSV1002)
        public static void NoRollback(int[] a, int x)
        {
            Spec.Requires(a.Length == 1 && a[0] < 1000);
            Spec.EnsuresOnThrow<Exception>(a[0] == Spec.Old(a[0]));
            a[0] = a[0] + 1;
            PositiveOnly(x);
        }

        // BUG: throws something other than what it promised about (CSV1002)
        public static void WrongKind(int x)
        {
            Spec.EnsuresOnThrow<Exception>(x > 0);
            if (x <= 0) throw new InvalidOperationException();
        }

        // BUG: throws null (CSV1013)
        public static void ThrowsNull(Exception? e)
        {
            throw e!;
        }
    }
}
