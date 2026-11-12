using System;
using System.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// <c>float</c> and <c>double</c> exactly as IEEE 754 binary32 and binary64 (Z3's floating-point theory): every
    /// operation rounds as .NET does (to nearest, ties to even), and NaN, the infinities and -0.0 are values like
    /// any other. What verifies is true of the program as it runs:
    /// <list type="bullet">
    /// <item><c>==</c> is IEEE equality (NaN is not equal to itself, -0.0 equals 0.0); <c>&lt;</c> and the rest are false
    /// when an operand is NaN;</item>
    /// <item>overflow goes to an infinity, as it does at run time, so it is not an error; a cast to an integer
    /// type that does not fit (NaN, an infinity, too big) is (CSV1010), or throws in a checked context;</item>
    /// <item>Math.Min/Max follow .NET (NaN if either is; -0.0 below 0.0), Abs, Sqrt, Floor, Ceiling, Round, Truncate,
    /// FusedMultiplyAdd are exact; Sin, Exp and the like are unknown values;</item>
    /// <item>in the heap (fields, array cells, sequences) a float is stored through an injective encoding.</item>
    /// </list>
    /// </summary>
    internal sealed partial class StaticChecks
    {

        /// <summary>Background: floats in the heap are encoded as integers (injectively; +0.0 as 0, the default cell).</summary>
        public const string FloatTheory =
            "(declare-fun cv_enc32 ((_ FloatingPoint 8 24)) Int)\n" +
            "(declare-fun cv_dec32 (Int) (_ FloatingPoint 8 24))\n" +
            "(assert (forall ((x (_ FloatingPoint 8 24))) (! (= (cv_dec32 (cv_enc32 x)) x) :pattern ((cv_enc32 x)))))\n" +
            "(assert (= (cv_enc32 (_ +zero 8 24)) 0))\n" +
            "(declare-fun cv_enc64 ((_ FloatingPoint 11 53)) Int)\n" +
            "(declare-fun cv_dec64 (Int) (_ FloatingPoint 11 53))\n" +
            "(assert (forall ((x (_ FloatingPoint 11 53))) (! (= (cv_dec64 (cv_enc64 x)) x) :pattern ((cv_enc64 x)))))\n" +
            "(assert (= (cv_enc64 (_ +zero 11 53)) 0))";
    }
}
