using System.Collections.Generic;
using System.Globalization;
using System.Linq;
using System.Numerics;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.Operations;
using static CsVerify.Verifier.Boogie.KernelTypes;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>
    /// Bitwise operators and shifts: integer arithmetic over a
    /// value's two's complement bits, which Boogie's Euclidean <c>div</c> and <c>mod</c> by a power of two read for a
    /// negative value too. With one operand constant each is exact and linear (<c>x &gt;&gt; k</c> is <c>x div 2^k</c>, a mask a
    /// sum of runs of bits, <c>x | C</c> is <c>(x &amp; ~C) + C</c>). With neither constant, the result is a function of the
    /// operands (<c>$bit.and32</c>, ...) with what is known of it: their sum if they have no bits in common (a value
    /// shifted by k, and one below 2^k), and else bit by bit.
    /// </summary>
    internal sealed partial class Lowering
    {
        /// <summary>Values known by their form to have no bits below some position.</summary>
        private readonly Dictionary<KExpr, int> _lowZeros = new Dictionary<KExpr, int>(ReferenceEqualityComparer.Instance);

        private static BigInteger Pow2(int k) => BigInteger.One << k;

        private static BigInteger? ConstOf(KExpr e)
        {
            if (!(e is KLit l)) return null;
            var s = l.Text.Trim('(', ')');
            return BigInteger.TryParse(s, NumberStyles.AllowLeadingSign, CultureInfo.InvariantCulture, out var v) ? v : (BigInteger?)null;
        }

        private static (int width, bool signed) WidthOf(ITypeSymbol type) => (Widths[Sp(type)].bits, Widths[Sp(type)].signed);

        private static BigInteger Unsigned(BigInteger v, int width)
        {
            var m = v % Pow2(width);
            return m < 0 ? m + Pow2(width) : m;
        }

        private static BigInteger Signed(BigInteger u, int width) => u >= Pow2(width - 1) ? u - Pow2(width) : u;

        private static KExpr Mod(KExpr a, int k) => new KOp("emod", a, Number(Pow2(k)));
        private static KExpr Shifted(KExpr a, int k) => k == 0 ? a : new KOp("ediv", a, Number(Pow2(k)));
        private static KExpr Plus(KExpr a, KExpr b) => new KOp("+", a, b);
        private static KExpr Minus(KExpr a, KExpr b) => new KOp("-", a, b);

        /// <summary>An operand that is repeated: in code, a temporary (in a specification, the expression itself).</summary>
        private KExpr Once(KExpr e, bool inSpec)
        {
            if (inSpec || e is KLit || e is KVar) return e;
            var t = Declare("t$" + _temps++, _model.Compilation.GetSpecialType(SpecialType.System_Int64));
            Emit(new KAssign { Var = t, Value = e });
            var v = new KVar(t);
            if (_lowZeros.TryGetValue(e, out var z)) _lowZeros[v] = z;
            return v;
        }

        /// <summary>An unsigned image of the given width, as a value of the type.</summary>
        private static KExpr AsTyped(KExpr u, int width, bool signed) =>
            signed ? Minus(Mod(Plus(u, Number(Pow2(width - 1))), width), Number(Pow2(width - 1))) : u;

        /// <summary>The bits of x where the mask (a constant, unsigned) has them: a sum of runs of bits, so non-negative.</summary>
        private static KExpr Masked(KExpr x, BigInteger mask, int width)
        {
            var runs = new List<KExpr>();
            for (int i = 0; i < width; i++)
            {
                if ((mask >> i).IsEven) continue;
                int from = i;
                while (i + 1 < width && !(mask >> (i + 1)).IsEven) i++;
                var run = Mod(Shifted(x, from), i + 1 - from);
                runs.Add(from == 0 ? run : new KOp("*", Number(Pow2(from)), run));
            }
            return runs.Count == 0 ? Number(0) : runs.Aggregate(Plus);
        }

        /// <summary>~x.</summary>
        private static KExpr Complement(KExpr x, ITypeSymbol type)
        {
            var (width, signed) = WidthOf(type);
            return signed ? Minus(Number(-1), x) : Minus(Number(Pow2(width) - 1), x);
        }

        private static bool IsBitwise(BinaryOperatorKind k) =>
            k is BinaryOperatorKind.And or BinaryOperatorKind.Or or BinaryOperatorKind.ExclusiveOr or BinaryOperatorKind.LeftShift or BinaryOperatorKind.RightShift or BinaryOperatorKind.UnsignedRightShift;

        /// <summary>l op r of an integral type (a smaller one's computed as int, then narrowed, as x op= y is).</summary>
        private KExpr Bitwise(BinaryOperatorKind kind, KExpr l, KExpr r, ITypeSymbol type, bool inSpec)
        {
            var (width, signed) = WidthOf(type);
            if (width >= 32) return Bitwise(kind, l, r, type, width, signed, inSpec);
            var promoted = Bitwise(kind, l, r, _model.Compilation.GetSpecialType(SpecialType.System_Int32), 32, true, inSpec);
            return signed ? AsTyped(promoted, width, true) : Mod(promoted, width);
        }

        private KExpr Bitwise(BinaryOperatorKind kind, KExpr l, KExpr r, ITypeSymbol type, int width, bool signed, bool inSpec)
        {
            if (kind is BinaryOperatorKind.LeftShift or BinaryOperatorKind.RightShift or BinaryOperatorKind.UnsignedRightShift)
                return Shift(kind, l, r, width, signed, inSpec);
            BigInteger? cl = ConstOf(l), cr = ConstOf(r);
            if (cl != null && cr != null)
            {
                BigInteger a = Unsigned(cl.Value, width), b = Unsigned(cr.Value, width);
                var u = kind == BinaryOperatorKind.And ? a & b : kind == BinaryOperatorKind.Or ? a | b : a ^ b;
                return Number(signed ? Signed(u, width) : u);
            }
            if (cl != null || cr != null)
                return WithConstant(kind, cl != null ? r : l, Unsigned((cl ?? cr).Value, width), width, signed, inSpec);
            // (in a specification read where it stands, as Spec.Assert's is, its facts go just before it; not of a
            // quantifier's variable, nor in a contract)
            if (inSpec && (_block == null || Bound(l) || Bound(r))) throw new NotTranslated("a bitwise operator of two variables in a specification");
            return Variables(kind, Once(l, inSpec), Once(r, inSpec), type, width);
        }

        private KExpr Shift(BinaryOperatorKind kind, KExpr l, KExpr r, int width, bool signed, bool inSpec)
        {
            bool logical = kind == BinaryOperatorKind.UnsignedRightShift && signed;
            if (ConstOf(r) is BigInteger count)
            {
                // (the count is taken modulo the width)
                int k = (int)Unsigned(count, width == 64 ? 6 : 5);
                if (k == 0) return l;
                if (kind == BinaryOperatorKind.LeftShift)
                {
                    var shifted = AsTyped(Mod(new KOp("*", l, Number(Pow2(k))), width), width, signed);
                    _lowZeros[shifted] = k;
                    return shifted;
                }
                return Shifted(logical ? Mod(l, width) : l, k);
            }
            // the count is unknown: a power of two chosen by its low bits
            var power = new KOp("$pow" + width, new KOp("emod", r, Number(width)));
            if (kind == BinaryOperatorKind.LeftShift)
                return AsTyped(Mod(new KOp("*", l, power), width), width, signed);
            var value = new KOp("ediv", logical ? Mod(l, width) : l, power);
            // (a logical shift by 0 of a negative value: its unsigned image is not its value)
            return logical ? AsTyped(value, width, true) : value;
        }

        private KExpr WithConstant(BinaryOperatorKind kind, KExpr x, BigInteger c, int width, bool signed, bool inSpec)
        {
            BigInteger all = Pow2(width) - 1;
            x = Once(x, inSpec);
            switch (kind)
            {
                case BinaryOperatorKind.And:
                {
                    if (c == all) return x;
                    var result = Masked(x, c, width);
                    // (the sign bit is in no run unless the mask has it: else the value is the image)
                    if (signed && c >= Pow2(width - 1)) result = AsTyped(result, width, true);
                    if (!c.IsZero && c.IsEven)
                    {
                        int k = 0;
                        while ((c >> k).IsEven) k++;
                        _lowZeros[result] = k;
                    }
                    return result;
                }
                case BinaryOperatorKind.Or:
                    if (c == 0) return x;
                    return AsTyped(Plus(Masked(x, all ^ c, width), Number(c)), width, signed);
                default:
                    if (c == 0) return x;
                    return AsTyped(Plus(Masked(x, all ^ c, width), Minus(Number(c), Masked(x, c, width))), width, signed);
            }
        }

        private static bool Bound(KExpr e) => e switch
        {
            KVar v => v.Name.StartsWith("q$"),
            KOp op => op.Args.Any(Bound),
            KLit => false,
            _ => true,
        };

        private int LowZeros(KExpr e)
        {
            if (ConstOf(e) is BigInteger c)
            {
                if (c.IsZero) return 64;
                int k = 0;
                while ((c >> k).IsEven) k++;
                return k;
            }
            return _lowZeros.TryGetValue(e, out var n) ? n : 0;
        }

        private KExpr Variables(BinaryOperatorKind kind, KExpr x, KExpr y, ITypeSymbol type, int width)
        {
            string op = kind == BinaryOperatorKind.And ? "and" : kind == BinaryOperatorKind.Or ? "or" : "xor";
            var app = new KVar(Declare("t$" + _temps++, _model.Compilation.GetSpecialType(SpecialType.System_Int64)));
            Emit(new KAssign { Var = app.Name, Value = new KOp($"$bit.{op}{width}", x, y) });
            Emit(new KAssume { Cond = InRange(app, type) });
            int xz = LowZeros(x), yz = LowZeros(y);
            if (xz == 0 && yz == 0)
            {
                // nothing suggests how they fit together: bit by bit
                Emit(new KAssume { Cond = BitFacts(op, x, y, app, width) });
                return app;
            }
            Emit(new KAssume { Cond = RangeFacts(op, x, y, app) });
            KExpr Disjoint(KExpr zeros, int k, KExpr low) => new KOp("&&", new KOp("&&",
                new KOp("==", Mod(zeros, System.Math.Min(k, width)), Number(0)), new KOp("<=", Number(0), low)), new KOp("<", low, Number(Pow2(System.Math.Min(k, width)))));
            KExpr disjoint = kind == BinaryOperatorKind.And ? Number(0) : Plus(x, y);
            KExpr value = app;
            if (yz > 0) value = new KOp("ite", Disjoint(y, yz, x), disjoint, value);
            if (xz > 0) value = new KOp("ite", Disjoint(x, xz, y), disjoint, value);
            var v = Once(value, false);
            _lowZeros[v] = System.Math.Min(xz, yz);
            return v;
        }

        /// <summary>What holds of any non-negative operands: their results' ranges.</summary>
        private static KExpr RangeFacts(string op, KExpr x, KExpr y, KExpr r)
        {
            KExpr Le(KExpr a, KExpr b) => new KOp("<=", a, b);
            KExpr And(params KExpr[] xs) => xs.Aggregate((a, b) => new KOp("&&", a, b));
            var nonNegative = And(Le(Number(0), x), Le(Number(0), y));
            var fact = op == "and" ? And(Le(Number(0), r), Le(r, x), Le(r, y))
                     : op == "or" ? And(Le(x, r), Le(y, r), Le(r, Plus(x, y)))
                     : And(Le(Number(0), r), Le(r, Plus(x, y)));
            return new KOp("==>", nonNegative, fact);
        }

        /// <summary>The result, bit by bit, and the value those bits add up to.</summary>
        private static KExpr BitFacts(string op, KExpr x, KExpr y, KExpr r, int width)
        {
            KExpr Bit(KExpr t, int i) => new KOp("==", Mod(Shifted(t, i), 1), Number(1));
            var facts = new List<KExpr> { RangeFacts(op, x, y, r) };
            for (int i = 0; i < width; i++)
                facts.Add(new KOp("==", Bit(r, i), op == "and" ? new KOp("&&", Bit(x, i), Bit(y, i)) : op == "or" ? new KOp("||", Bit(x, i), Bit(y, i)) : new KOp("!=", Bit(x, i), Bit(y, i))));
            var sum = Enumerable.Range(0, width).Select(i => (KExpr)new KOp("ite", Bit(r, i), Number(Pow2(i)), Number(0))).Aggregate(Plus);
            facts.Add(new KOp("==", Mod(r, width), sum));
            return facts.Aggregate((a, b) => new KOp("&&", a, b));
        }
    }
}
