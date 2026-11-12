using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Bitwise operators and shifts, as integer arithmetic. A value's bits are its two's complement ones, and SMT-LIB's
    /// <c>div</c> and <c>mod</c> by a power of two read them for a negative value too (they floor). So with one operand
    /// constant, each is exact and linear: <c>x &gt;&gt; k</c> is <c>x div 2^k</c>, a mask is a sum of runs of bits, and
    /// <c>x | C</c> is <c>(x &amp; ~C) + C</c>. Bitvectors would make the solver convert between Int and BitVec, which
    /// timed out on a Base64 block's round trip that this form proves at once.
    ///
    /// With neither operand constant, the result is a function of the operands (<c>cv_bit</c>), with what is known of
    /// it: if one has no bits where the other may (a shift by k, and a value under 2^k, as when a word is packed), it
    /// is their sum; and bit by bit, which is exact but costly. The candidates for "no bits below k" are only suggestions:
    /// each is checked by the solver as a condition of the fact it gives.
    /// </summary>
    internal sealed partial class StaticChecks
    {
    }
}
