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
    internal sealed partial class MethodVerifier
    {
        /// <summary>Terms known by their form to have no bits below some position.</summary>
        private readonly Dictionary<string, int> _lowZeros = new Dictionary<string, int>();

        private static BigInteger Pow2(int k) => BigInteger.One << k;

        private static BigInteger? ConstOf(Term t)
        {
            var s = t.S;
            if (s.Length > 0 && char.IsDigit(s[0]) && BigInteger.TryParse(s, out var v)) return v;
            if (s.StartsWith("(- ") && s.EndsWith(")") && BigInteger.TryParse(s.Substring(3, s.Length - 4), out var n)) return -n;
            return null;
        }

        private static (int width, bool signed) WidthOf(ITypeSymbol type)
        {
            var (lo, hi) = RangeOf(type);
            return ((int)(hi - lo + 1).GetBitLength() - 1, lo < 0);
        }

        private static BigInteger Unsigned(BigInteger v, int width)
        {
            var m = v % Pow2(width);
            return m < 0 ? m + Pow2(width) : m;
        }

        private static BigInteger Signed(BigInteger u, int width) => u >= Pow2(width - 1) ? u - Pow2(width) : u;

        private static Term Mod(Term a, int k) => new Term($"(mod {a.S} {Pow2(k)})", Sort.Int);
        private static Term Shifted(Term a, int k) => k == 0 ? a : new Term($"(div {a.S} {Pow2(k)})", Sort.Int);

        /// <summary>An operand's name, where it would be repeated (not under a quantifier: its variable has no definition).</summary>
        private Term Once(Term t) => _quantFacts.Count == 0 ? _z3.Define("bits", t) : t;

        /// <summary>An unsigned image of the given width, as a value of the type.</summary>
        private static Term AsTyped(Term u, int width, bool signed) =>
            signed ? new Term($"(- (mod (+ {u.S} {Pow2(width - 1)}) {Pow2(width)}) {Pow2(width - 1)})", Sort.Int) : u;

        /// <summary>The bits of x where the mask (a constant, unsigned) has them: a sum of runs of bits, so non-negative.</summary>
        private static Term Masked(Term x, BigInteger mask, int width)
        {
            var runs = new List<Term>();
            for (int i = 0; i < width; i++)
            {
                if ((mask >> i).IsEven) continue;
                int from = i;
                while (i + 1 < width && !(mask >> (i + 1)).IsEven) i++;
                var run = Mod(Shifted(x, from), i + 1 - from);
                runs.Add(from == 0 ? run : new Term($"(* {Pow2(from)} {run.S})", Sort.Int));
            }
            return runs.Count == 0 ? T.Int(0) : runs.Count == 1 ? runs[0] : new Term("(+ " + string.Join(" ", runs.Select(r => r.S)) + ")", Sort.Int);
        }

        private Term Complement(Term x, ITypeSymbol type)
        {
            var (width, signed) = WidthOf(type);
            return signed ? T.Sub(T.Int(-1), x) : T.Sub(T.Int(Pow2(width) - 1), x);
        }

        private Term Bitwise(BinaryOperatorKind kind, Term l, Term r, ITypeSymbol type)
        {
            var (width, signed) = WidthOf(type);
            if (width >= 32) return Bitwise(kind, l, r, type, width, signed);
            // (x op= y of a smaller type: computed as int, then narrowed)
            var promoted = Bitwise(kind, l, r, _model.Compilation.GetSpecialType(SpecialType.System_Int32), 32, true);
            return signed ? AsTyped(promoted, width, true) : Mod(promoted, width);
        }

        private Term Bitwise(BinaryOperatorKind kind, Term l, Term r, ITypeSymbol type, int width, bool signed)
        {
            switch (kind)
            {
                case BinaryOperatorKind.LeftShift:
                case BinaryOperatorKind.RightShift:
                case BinaryOperatorKind.UnsignedRightShift:
                    return Shift(kind, l, r, width, signed);
            }
            BigInteger? cl = ConstOf(l), cr = ConstOf(r);
            if (cl != null && cr != null)
            {
                BigInteger a = Unsigned(cl.Value, width), b = Unsigned(cr.Value, width);
                var u = kind == BinaryOperatorKind.And ? a & b : kind == BinaryOperatorKind.Or ? a | b : a ^ b;
                return T.Int(signed ? Signed(u, width) : u);
            }
            if (cl != null || cr != null)
                return WithConstant(kind, cl != null ? r : l, Unsigned((cl ?? cr).Value, width), width, signed);
            return Variables(kind, Once(l), Once(r), type, width, signed);
        }

        private Term Shift(BinaryOperatorKind kind, Term l, Term r, int width, bool signed)
        {
            bool logical = kind == BinaryOperatorKind.UnsignedRightShift && signed;
            if (ConstOf(r) is BigInteger count)
            {
                // (the count is taken modulo the width)
                int k = (int)Unsigned(count, width == 64 ? 6 : 5);
                if (k == 0) return l;
                if (kind == BinaryOperatorKind.LeftShift)
                {
                    var shifted = AsTyped(new Term($"(mod (* {l.S} {Pow2(k)}) {Pow2(width)})", Sort.Int), width, signed);
                    _lowZeros[shifted.S] = k;
                    return shifted;
                }
                return Shifted(logical ? Mod(l, width) : l, k);
            }
            // the count is unknown: a power of two chosen by its low bits
            var power = new Term($"(cv_pow{width} (mod {r.S} {width}))", Sort.Int);
            if (kind == BinaryOperatorKind.LeftShift)
                return AsTyped(new Term($"(mod (* {l.S} {power.S}) {Pow2(width)})", Sort.Int), width, signed);
            var value = new Term($"(div {(logical ? Mod(l, width) : l).S} {power.S})", Sort.Int);
            // (a logical shift by 0 of a negative value: its unsigned image is not its value)
            return logical ? AsTyped(value, width, true) : value;
        }

        private Term WithConstant(BinaryOperatorKind kind, Term x, BigInteger c, int width, bool signed)
        {
            BigInteger all = Pow2(width) - 1;
            x = Once(x);
            Term result;
            switch (kind)
            {
                case BinaryOperatorKind.And:
                    if (c == all) return x;
                    result = Masked(x, c, width);
                    // (the sign bit is in no run unless the mask has it: else the value is the image)
                    if (signed && c >= Pow2(width - 1)) result = AsTyped(result, width, true);
                    NoteLowZeros(result, c);
                    return result;
                case BinaryOperatorKind.Or:
                    if (c == 0) return x;
                    return AsTyped(T.Add(Masked(x, all ^ c, width), T.Int(c)), width, signed);
                default:
                    if (c == 0) return x;
                    return AsTyped(T.Add(Masked(x, all ^ c, width), T.Sub(T.Int(c), Masked(x, c, width))), width, signed);
            }
        }

        private void NoteLowZeros(Term t, BigInteger mask)
        {
            if (mask.IsZero || !mask.IsEven) return;
            int k = 0;
            while ((mask >> k).IsEven) k++;
            _lowZeros[t.S] = k;
        }

        private int LowZeros(Term t)
        {
            if (ConstOf(t) is BigInteger c)
            {
                if (c.IsZero) return 64;
                int k = 0;
                while ((c >> k).IsEven) k++;
                return k;
            }
            return _lowZeros.TryGetValue(t.S, out var n) ? n : 0;
        }

        private Term Variables(BinaryOperatorKind kind, Term x, Term y, ITypeSymbol type, int width, bool signed)
        {
            string op = kind == BinaryOperatorKind.And ? "and" : kind == BinaryOperatorKind.Or ? "or" : "xor";
            var app = _z3.Apply("cv_bit:" + op + ":" + width, Sort.Int, new[] { T.Coerce(x, Sort.Int), T.Coerce(y, Sort.Int) });
            InRangeOf(app, type);
            int xz = LowZeros(x), yz = LowZeros(y);
            if (xz == 0 && yz == 0)
            {
                // nothing suggests how they fit together: bit by bit (not under a quantifier: it would be a fact per bit per value)
                if (_quantFacts.Count == 0) _z3.AssumeOnce("bits:" + app.S, () => BitFacts(op, x, y, app, width));
                return app;
            }
            _z3.AssumeOnce("bitrange:" + app.S, () => RangeFacts(op, x, y, app));
            Term Disjoint(Term zeros, int k, Term low) => T.And(T.Eq(Mod(zeros, System.Math.Min(k, width)), T.Int(0)), T.Le(T.Int(0), low), T.Lt(low, T.Int(Pow2(System.Math.Min(k, width)))));
            var disjoint = kind == BinaryOperatorKind.And ? T.Int(0) : T.Add(x, y);
            var value = app;
            if (yz > 0) value = T.Ite(Disjoint(y, yz, x), disjoint, value);
            if (xz > 0) value = T.Ite(Disjoint(x, xz, y), disjoint, value);
            value = Once(value);
            _lowZeros[value.S] = System.Math.Min(xz, yz);
            return value;
        }

        /// <summary>What holds of any non-negative operands: their results' ranges.</summary>
        private static Term RangeFacts(string op, Term x, Term y, Term r)
        {
            var nonNegative = T.And(T.Le(T.Int(0), x), T.Le(T.Int(0), y));
            var fact = op == "and" ? T.And(T.Le(T.Int(0), r), T.Le(r, x), T.Le(r, y))
                     : op == "or" ? T.And(T.Le(x, r), T.Le(y, r), T.Le(r, T.Add(x, y)))
                     : T.And(T.Le(T.Int(0), r), T.Le(r, T.Add(x, y)));
            return T.Implies(nonNegative, fact);
        }

        /// <summary>The result, bit by bit.</summary>
        private static Term BitFacts(string op, Term x, Term y, Term r, int width)
        {
            Term Bit(Term t, int i) => T.Eq(Mod(Shifted(t, i), 1), T.Int(1));
            var facts = new List<Term> { RangeFacts(op, x, y, r) };
            for (int i = 0; i < width; i++)
                facts.Add(T.Eq(Bit(r, i), op == "and" ? T.And(Bit(x, i), Bit(y, i)) : op == "or" ? T.Or(Bit(x, i), Bit(y, i)) : T.Xor(Bit(x, i), Bit(y, i))));
            // (and the value those bits add up to: else the solver knows every bit of it, but not what it is)
            var sum = string.Join(" ", Enumerable.Range(0, width).Select(i => $"(ite {Bit(r, i).S} {Pow2(i)} 0)"));
            facts.Add(T.Eq(Mod(r, width), new Term($"(+ {sum})", Sort.Int)));
            return T.And(facts.ToArray());
        }
    }
}
