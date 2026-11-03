using System;
using CsVerify;

namespace Samples.Buggy
{
    public static class FloatBugs
    {
        // BUG: with both ends +infinity, hi - lo is NaN (CSV1002)
        public static float Length(float lo, float hi)
        {
            Spec.Requires(lo <= hi);
            Spec.Ensures((float r) => r >= 0);
            return hi - lo;
        }

        // BUG: x + 1 is not above x for NaN, the infinities, or large x (CSV1004)
        public static void Successor(double x)
        {
            Spec.Assert(x + 1.0 > x);
        }

        // BUG: d may be NaN, infinite or out of range (CSV1010)
        public static int Truncated(double d)
        {
            return (int)d;
        }

        // BUG: NaN is not equal to itself, so this is not reflexive (CSV1004)
        public static void Reflexive(double x)
        {
            Spec.Assert(x == x);
        }
    }
}
