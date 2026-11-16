using System.Numerics;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.Operations;
using static CsVerify.Verifier.Boogie.KernelTypes;
using static CsVerify.Verifier.Boogie.KOp;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>
    /// decimal, exactly: a value is an integer number of 10^-28 units (every decimal is m / 10^e, |m| &lt; 2^96, 0 &lt;= e
    /// &lt;= 28). + and - are the exact result where it is representable ($drep: m / 10^e for some e), else the result
    /// rounded ($dround, a function of the exact result alone, which keeps its sign); past MaxValue they throw an
    /// OverflowException. Comparisons are exact. * and / are not translated.
    /// </summary>
    internal sealed partial class Lowering
    {
        /// <summary>10^28: a decimal 1, in units.</summary>
        internal static readonly BigInteger DecimalOne = BigInteger.Pow(10, 28);

        /// <summary>decimal.MaxValue, 2^96 - 1, in units.</summary>
        internal static readonly BigInteger DecimalMax = ((BigInteger.One << 96) - 1) * DecimalOne;

        /// <summary>A decimal's value in units.</summary>
        internal static BigInteger DecimalUnits(decimal d)
        {
            var bits = decimal.GetBits(d);
            var m = (new BigInteger((uint)bits[2]) << 64) | (new BigInteger((uint)bits[1]) << 32) | new BigInteger((uint)bits[0]);
            var scale = (bits[3] >> 16) & 0xFF;
            return (bits[3] < 0 ? -m : m) * BigInteger.Pow(10, 28 - scale);
        }

        /// <summary>A decimal operation, in code or in a specification; null where e is none.</summary>
        private KExpr DecimalExpr(IOperation e, LowerMode mode)
        {
            if (IsDecimal(e.Type) && e.ConstantValue is { HasValue: true, Value: decimal d })
            {
                return Number(DecimalUnits(d));
            }
            switch (e)
            {
                // (an integer as a decimal: exact)
                case IConversionOperation c when IsDecimal(c.Type) && IsIntegral(c.Operand.Type):
                    return new KOp("*", Lower(c.Operand, mode), Number(DecimalOne));
                case IBinaryOperation b when IsDecimal(b.LeftOperand.Type) && IsDecimal(b.RightOperand.Type):
                {
                    if (b.OperatorKind is BinaryOperatorKind.Multiply or BinaryOperatorKind.Divide or BinaryOperatorKind.Remainder)
                    {
                        throw new NotTranslated("decimal " + b.OperatorKind);
                    }
                    var (l, r) = mode.InSpec ? (Lower(b.LeftOperand, mode), Lower(b.RightOperand, mode)) : (Operands(b.LeftOperand, b.RightOperand) is var v ? (v[0], v[1]) : default);
                    return b.OperatorKind switch
                    {
                        BinaryOperatorKind.Add => DecimalArith("+", l, r, b.Syntax, mode.InSpec),
                        BinaryOperatorKind.Subtract => DecimalArith("-", l, r, b.Syntax, mode.InSpec),
                        BinaryOperatorKind.Equals => Eq(l, r),
                        BinaryOperatorKind.NotEquals => Ne(l, r),
                        BinaryOperatorKind.LessThan => Lt(l, r),
                        BinaryOperatorKind.LessThanOrEqual => Le(l, r),
                        BinaryOperatorKind.GreaterThan => Gt(l, r),
                        BinaryOperatorKind.GreaterThanOrEqual => Ge(l, r),
                        _ => throw new NotTranslated("decimal " + b.OperatorKind),
                    };
                }
                case IUnaryOperation u when IsDecimal(u.Type) && u.OperatorKind == UnaryOperatorKind.Minus:
                    return Minus(KLit.Zero, Lower(u.Operand, mode));
                case IUnaryOperation u when IsDecimal(u.Type) && u.OperatorKind == UnaryOperatorKind.Plus:
                    return Lower(u.Operand, mode);
                default:
                    return null;
            }
        }

        /// <summary>l + r or l - r of decimals: rounded where not representable; in code, an OverflowException past MaxValue.</summary>
        private KExpr DecimalArith(string op, KExpr l, KExpr r, SyntaxNode at, bool inSpec)
        {
            if (op is not ("+" or "-"))
            {
                throw new NotTranslated("decimal " + op);
            }
            var exact = new KOp(op, l, r);
            if (!inSpec && _cfgBlock != null)
            {
                // (it throws where the result, rounded to an integer, is past MaxValue: half a unit of 1 beyond it)
                var bound = Number(DecimalMax + DecimalOne / 2);
                var fits = AndAlso(Lt(Minus(KLit.Zero, bound), exact), Lt(exact, bound));
                if (ThrowTarget(_cfgBlock.EnclosingRegion) is string to)
                {
                    _p.AddExceptionType(_model.Compilation.GetTypeByMetadataName("System.OverflowException"));
                    Emit(new KFork { Overflow = fits, Target = to });
                }
                Emit(KAssume.Of(fits));
            }
            return new KOp("$dround", exact);
        }
    }
}
