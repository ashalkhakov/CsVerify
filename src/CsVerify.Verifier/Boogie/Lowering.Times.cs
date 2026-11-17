using System.Numerics;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.Operations;
using static CsVerify.Verifier.Boogie.KernelTypes;
using static CsVerify.Verifier.Boogie.KOp;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>
    /// DateTime and TimeSpan arithmetic, on their ticks: DateTime ± TimeSpan, DateTime - DateTime, TimeSpan ± TimeSpan.
    /// A DateTime past its range throws an ArgumentOutOfRangeException, a TimeSpan past long's an OverflowException,
    /// as .NET's operators do.
    /// </summary>
    internal sealed partial class Lowering
    {
        /// <summary>DateTime.MaxValue's ticks.</summary>
        internal static readonly BigInteger MaxTicks = 3155378975999999999;

        /// <summary>DateTime's MinValue and MaxValue, TimeSpan's Zero, MinValue and MaxValue: their ticks; else null.</summary>
        private static KExpr TimeConstant(IFieldReferenceOperation f)
        {
            if (f.Instance != null || !IsOpaqueTicks(f.Field.ContainingType))
            {
                return null;
            }
            var dateTime = f.Field.ContainingType.ToDisplayString() == "System.DateTime";
            return f.Field.Name switch
            {
                "MinValue" => Number(dateTime ? BigInteger.Zero : long.MinValue),
                "MaxValue" => Number(dateTime ? MaxTicks : long.MaxValue),
                "Zero" when !dateTime => KLit.Zero,
                _ => null,
            };
        }

        /// <summary>a ± b of a DateTime's or a TimeSpan's own operator; null where e is none.</summary>
        private KExpr TimeArith(IOperation e, LowerMode mode)
        {
            if (!(e is IBinaryOperation { OperatorMethod: { } m } b) || !OpaqueOperator(m) || !IsOpaqueTicks(b.Type) ||
                b.OperatorKind is not (BinaryOperatorKind.Add or BinaryOperatorKind.Subtract))
            {
                return null;
            }
            var (l, r) = mode.InSpec ? (Lower(b.LeftOperand, mode), Lower(b.RightOperand, mode)) : Operands(b.LeftOperand, b.RightOperand) is var v ? (v[0], v[1]) : default;
            var ticks = new KOp(b.OperatorKind == BinaryOperatorKind.Add ? "+" : "-", l, r);
            if (!mode.InSpec && _cfgBlock != null)
            {
                var dateTime = b.Type.ToDisplayString() == "System.DateTime";
                var (lo, hi) = dateTime ? (BigInteger.Zero, MaxTicks) : (new BigInteger(long.MinValue), new BigInteger(long.MaxValue));
                var fits = AndAlso(Le(Number(lo), ticks), Le(ticks, Number(hi)));
                if (ThrowTarget(_cfgBlock.EnclosingRegion) is string to)
                {
                    var thrown = _model.Compilation.GetTypeByMetadataName(dateTime ? "System.ArgumentOutOfRangeException" : "System.OverflowException");
                    _p.AddExceptionType(thrown);
                    Emit(new KFork { Overflow = fits, Target = to, Exception = TypeConst(thrown) });
                }
                Emit(KAssume.Of(fits));
            }
            return ticks;
        }
    }
}
