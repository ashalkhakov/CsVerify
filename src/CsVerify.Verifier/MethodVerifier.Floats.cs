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
    internal sealed partial class MethodVerifier
    {
        internal static bool IsFloating(ITypeSymbol t) =>
            t?.SpecialType == SpecialType.System_Single || t?.SpecialType == SpecialType.System_Double;

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

        private static string FpSort(Sort s) => s == Sort.F32 ? "8 24" : "11 53";

        /// <summary>An exact literal: the value's own bits.</summary>
        internal static Term FloatLiteral(object value)
        {
            if (value is float x)
            {
                var bits = BitConverter.SingleToInt32Bits(x);
                return new Term($"(fp #b{Bits((uint)bits >> 31, 1)} #b{Bits(((uint)bits >> 23) & 0xFF, 8)} #b{Bits((uint)bits & 0x7FFFFF, 23)})", Sort.F32);
            }
            var b = (ulong)BitConverter.DoubleToInt64Bits(Convert.ToDouble(value));
            return new Term($"(fp #b{Bits(b >> 63, 1)} #b{Bits((b >> 52) & 0x7FF, 11)} #b{Bits(b & 0xFFFFFFFFFFFFFUL, 52)})", Sort.F64);
        }

        private static string Bits(ulong v, int width) => Convert.ToString((long)v, 2).PadLeft(width, '0');

        private static Term Zero(Sort s) => new Term($"(_ +zero {FpSort(s)})", s);
        private static Term NaN(Sort s) => new Term($"(_ NaN {FpSort(s)})", s);

        private static Term Fp(string op, Sort sort, params Term[] args) =>
            new Term($"({op} {string.Join(" ", args.Select(a => T.Coerce(a, sort).S))})", sort);

        private static Term FpRounded(string op, Sort sort, params Term[] args) =>
            new Term($"({op} RNE {string.Join(" ", args.Select(a => T.Coerce(a, sort).S))})", sort);

        private static Term FpTest(string op, Sort sort, params Term[] args) =>
            new Term($"({op} {string.Join(" ", args.Select(a => T.Coerce(a, sort).S))})", Sort.Bool);

        /// <summary>A binary operation on floats (both operands already of the result's type, as C# promotes them).</summary>
        private Term FloatBinary(BinaryOperatorKind kind, Term l, Term r, ITypeSymbol operandType, SyntaxNode at, ITypeSymbol resultType)
        {
            var s = SortOf(operandType);
            switch (kind)
            {
                case BinaryOperatorKind.Add: return FpRounded("fp.add", s, l, r);
                case BinaryOperatorKind.Subtract: return FpRounded("fp.sub", s, l, r);
                case BinaryOperatorKind.Multiply: return FpRounded("fp.mul", s, l, r);
                case BinaryOperatorKind.Divide: return FpRounded("fp.div", s, l, r);
                case BinaryOperatorKind.Equals: return FpTest("fp.eq", s, l, r);
                case BinaryOperatorKind.NotEquals: return T.Not(FpTest("fp.eq", s, l, r));
                case BinaryOperatorKind.LessThan: return FpTest("fp.lt", s, l, r);
                case BinaryOperatorKind.LessThanOrEqual: return FpTest("fp.leq", s, l, r);
                case BinaryOperatorKind.GreaterThan: return FpTest("fp.gt", s, l, r);
                case BinaryOperatorKind.GreaterThanOrEqual: return FpTest("fp.geq", s, l, r);
                default:
                    // % is C's fmod, not IEEE's remainder: not modeled
                    Warn(at, $"'{at}': this floating-point operation is not modeled; the result is unknown");
                    return Unknown(resultType);
            }
        }

        private static Term FloatNegate(Term v, ITypeSymbol type) => Fp("fp.neg", SortOf(type), v);

        /// <summary>
        /// A conversion to or from a float type. Integer to float, and float to float, round to nearest; float to an
        /// integer type truncates, and must fit (CSV1010), or throws if checked.
        /// </summary>
        private Term FloatConversion(Term v, ITypeSymbol from, ITypeSymbol to, IConversionOperation c)
        {
            if (IsFloating(from) && IsFloating(to))
            {
                if (from.SpecialType == to.SpecialType) return T.Coerce(v, SortOf(to));
                return new Term($"((_ to_fp {FpSort(SortOf(to))}) RNE {T.Coerce(v, SortOf(from)).S})", SortOf(to));
            }
            if (IsFloating(to))
            {
                if (from.SpecialType == SpecialType.System_Char || IsIntegral(from))
                {
                    // through the integer's bits (the solver rounds those well), and exact below 2^24 (2^53)
                    var i = T.Coerce(v, Sort.Int);
                    var (ilo, ihi) = RangeOf(from);
                    int bits = (int)System.Numerics.BigInteger.Log(ihi - ilo + 1, 2);
                    var intBits = $"((_ int2bv {bits}) {i.S})";
                    var result = new Term($"((_ {(ilo < 0 ? "to_fp" : "to_fp_unsigned")} {FpSort(SortOf(to))}) RNE {intBits})", SortOf(to));
                    var exact = SortOf(to) == Sort.F32 ? 1L << 24 : 1L << 53;
                    AssumeSide(T.Implies(T.And(T.Le(T.Int(-exact), i), T.Le(i, T.Int(exact))),
                        new Term($"(= (fp.to_real {result.S}) (to_real {i.S}))", Sort.Bool)));
                    return result;
                }
                return Unknown(to, "conv");
            }
            // float to integer: toward zero; it fits if it is finite and its integral part is in range (the
            // bounds are powers of two, exact in every float type)
            var s = SortOf(from);
            var x = T.Coerce(v, s);
            var (lo, hi) = RangeOf(to);
            bool signed = lo < 0;
            int width = (int)System.Numerics.BigInteger.Log(hi - lo + 1, 2) + (((hi - lo + 1) & (hi - lo)) == 0 ? 0 : 1);
            var t = new Term($"(fp.roundToIntegral RTZ {x.S})", s);
            var fits = T.And(T.Not(FpTest("fp.isNaN", s, x)), T.Not(FpTest("fp.isInfinite", s, x)),
                new Term($"(fp.geq {t.S} ((_ to_fp {FpSort(s)}) RNE {RealLiteral(lo)}))", Sort.Bool),
                new Term($"(fp.lt {t.S} ((_ to_fp {FpSort(s)}) RNE {RealLiteral(hi + 1)}))", Sort.Bool));
            var bv = $"((_ {(signed ? "fp.to_sbv" : "fp.to_ubv")} {width}) RTZ {x.S})";
            var asInt = signed
                ? new Term($"(ite (>= (bv2int {bv}) {T.Int(hi + 1)}) (- (bv2int {bv}) {T.Int(hi - lo + 1)}) (bv2int {bv}))", Sort.Int)
                : new Term($"(bv2int {bv})", Sort.Int);
            // (the same number, as the solver's integer arithmetic sees it: a bridge from the bits to the bounds)
            AssumeSide(T.Implies(fits, new Term($"(= (to_real {asInt.S}) (fp.to_real {t.S}))", Sort.Bool)));
            if (!_codeMode || InGhostCode || !_engine.Options.CheckOverflow)
                return T.Ite(fits, asInt, Unknown(to, "conv"));
            if (c.IsChecked && !ProofCode)
            {
                if (_current != null) MayRaise(T.Not(fits), _current, KnownType("System.OverflowException"));
                _z3.Assume(fits);
                return asInt;
            }
            Prove(fits, "CSV1010", c.Syntax, $"conversion '{c.Syntax}' to {to.Name} might not fit (it might be NaN, infinite, or out of range)");
            return asInt;
        }

        private static string RealLiteral(System.Numerics.BigInteger v) => v < 0 ? $"(- {-v}.0)" : $"{v}.0";

        /// <summary>Math, MathF, double and float members on floats; null if it is not one of them.</summary>
        private Term FloatBuiltin(IInvocationOperation inv, Frame f, SpecEnv spec)
        {
            var m = inv.TargetMethod;
            var owner = m.ContainingType?.ToDisplayString();
            bool math = owner == "System.Math" || owner == "System.MathF";
            bool number = owner == "double" || owner == "float" || owner == "System.Double" || owner == "System.Single";
            if (!math && !number) return null;
            var p = m.Parameters.FirstOrDefault()?.Type;
            if (!IsFloating(p)) return null;
            var s = SortOf(p);
            var args = inv.Arguments.Select(a => T.Coerce(Eval(a.Value, f, spec), s)).ToArray();
            if (number)
                switch (m.Name)
                {
                    case "IsNaN": return FpTest("fp.isNaN", s, args[0]);
                    case "IsInfinity": return FpTest("fp.isInfinite", s, args[0]);
                    case "IsFinite": return T.Not(T.Or(FpTest("fp.isNaN", s, args[0]), FpTest("fp.isInfinite", s, args[0])));
                    case "IsPositiveInfinity": return T.And(FpTest("fp.isInfinite", s, args[0]), FpTest("fp.isPositive", s, args[0]));
                    case "IsNegativeInfinity": return T.And(FpTest("fp.isInfinite", s, args[0]), FpTest("fp.isNegative", s, args[0]));
                    case "IsNormal": return FpTest("fp.isNormal", s, args[0]);
                    case "IsSubnormal": return FpTest("fp.isSubnormal", s, args[0]);
                    default: return null;
                }
            switch (m.Name)
            {
                case "Abs" when args.Length == 1: return Fp("fp.abs", s, args[0]);
                case "Sqrt" when args.Length == 1: return FpRounded("fp.sqrt", s, args[0]);
                case "Floor" when args.Length == 1: return new Term($"(fp.roundToIntegral RTN {args[0].S})", s);
                case "Ceiling" when args.Length == 1: return new Term($"(fp.roundToIntegral RTP {args[0].S})", s);
                case "Truncate" when args.Length == 1: return new Term($"(fp.roundToIntegral RTZ {args[0].S})", s);
                case "Round" when args.Length == 1: return new Term($"(fp.roundToIntegral RNE {args[0].S})", s); // to even, .NET's default
                case "FusedMultiplyAdd" when args.Length == 3: return FpRounded("fp.fma", s, args[0], args[1], args[2]);
                case "Min" when args.Length == 2: return MinMax(args[0], args[1], s, min: true);
                case "Max" when args.Length == 2: return MinMax(args[0], args[1], s, min: false);
                default:
                    // Sin, Exp, Pow, ...: their results are not modeled
                    return Unknown(inv.Type, m.Name);
            }
        }

        /// <summary>.NET's Math.Min/Max on floats: NaN if either is NaN; between 0.0 and -0.0, Min is -0.0 and Max 0.0.</summary>
        private static Term MinMax(Term a, Term b, Sort s, bool min)
        {
            var nan = T.Or(FpTest("fp.isNaN", s, a), FpTest("fp.isNaN", s, b));
            var less = FpTest(min ? "fp.lt" : "fp.gt", s, a, b);
            var more = FpTest(min ? "fp.lt" : "fp.gt", s, b, a);
            // equal: the same value, or zeros of either sign: the negative one for Min, the positive one for Max
            var keepA = FpTest(min ? "fp.isNegative" : "fp.isPositive", s, a);
            return T.Ite(nan, NaN(s), T.Ite(less, a, T.Ite(more, b, T.Ite(keepA, a, b))));
        }
    }
}
