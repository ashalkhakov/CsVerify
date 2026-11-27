using System.Numerics;
using CsVerify.Analyzers;
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

        /// <summary>
        /// A property of a DateTime, a TimeSpan, a DateOnly or a TimeOnly that the kernel has no model of (Year, Days,
        /// DayOfWeek): a function of the value, which is all there is to it, within its type's range. Not a DateTime's
        /// Kind, which its ticks don't say. Its function's name, declared; null where p is none.
        /// </summary>
        private string ValueProperty(IPropertyReferenceOperation p)
        {
            if (p.Instance == null || !IsOpaqueTicks(p.Instance.Type) || p.Property.IsIndexer || !InSubset(p.Type) || TypeOf(p.Type) == "Ref" ||
                p.Property.Name == "Kind" && p.Instance.Type.ToDisplayString() == "System.DateTime")
            {
                return null;
            }
            var name = "$vp." + Ident(p.Instance.Type.ToDisplayString() + "." + p.Property.Name);
            _p.AddFunction($"function {name}(v: int): {TypeOf(p.Type)};");
            (BigInteger lo, BigInteger hi)? range =
                IsIntegral(p.Type) ? Range(p.Type)
                : p.Type.ToDisplayString() == "System.DateTime" ? (BigInteger.Zero, MaxTicks)
                : p.Type.ToDisplayString() == "System.TimeSpan" ? (long.MinValue, long.MaxValue) : ((BigInteger, BigInteger)?)null;
            if (range is { } r)
            {
                _p.AddFunction($"axiom (forall v: int :: {{ {name}(v) }} {r.lo} <= {name}(v) && {name}(v) <= {r.hi});");
            }
            return name;
        }

        /// <summary>
        /// a ± b of a DateTime's or a TimeSpan's own operator, or of the method the operator is (d.Add(t), d.Subtract(t),
        /// d.AddTicks(n): SpecSymbols.IsTickArithmetic); null where e is none.
        /// </summary>
        private KExpr TimeArith(IOperation e, LowerMode mode)
        {
            IOperation left, right;
            bool add;
            switch (e)
            {
                case IBinaryOperation { OperatorMethod: { } m } b when OpaqueOperator(m) && IsOpaqueTicks(b.Type) && b.OperatorKind is BinaryOperatorKind.Add or BinaryOperatorKind.Subtract:
                    (left, right, add) = (b.LeftOperand, b.RightOperand, b.OperatorKind == BinaryOperatorKind.Add);
                    break;
                case IInvocationOperation { Instance: { } receiver } call when SpecSymbols.IsTickArithmetic(call.TargetMethod):
                    (left, right, add) = (receiver, call.Arguments[0].Value, call.TargetMethod.Name != "Subtract");
                    break;
                default:
                    return null;
            }
            var (l, r) = mode.InSpec ? (Lower(left, mode), Lower(right, mode)) : Operands(left, right) is var v ? (v[0], v[1]) : default;
            var ticks = new KOp(add ? "+" : "-", l, r);
            if (!mode.InSpec && _cfgBlock != null)
            {
                var dateTime = e.Type.ToDisplayString() == "System.DateTime";
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
