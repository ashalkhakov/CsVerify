using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.Operations;
using static CsVerify.Verifier.Boogie.KernelTypes;
using static CsVerify.Verifier.Boogie.KOp;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>float and double: Math's members and conversions, as IEEE 754.</summary>
    internal sealed partial class Lowering
    {
        /// <summary>A Math, MathF, double or float member on floats, by what it is (null for any other).</summary>
        private static string FloatMember(IMethodSymbol m)
        {
            var owner = m.ContainingType?.ToDisplayString();
            if (m.Parameters.Length == 0 || !IsFloating(m.Parameters[0].Type))
            {
                return null;
            }
            if (owner is "double" or "float" or "System.Double" or "System.Single")
            {
                return m.Name is "IsNaN" or "IsInfinity" or "IsFinite" or "IsPositiveInfinity" or "IsNegativeInfinity" or "IsNormal" or "IsSubnormal" ? m.Name : null;
            }
            return owner is "System.Math" or "System.MathF" ? m.Name : null;
        }

        /// <summary>.NET's float members as IEEE's: Min and Max NaN if either is (and -0.0 below 0.0); Sin, Exp and the like unknown values.</summary>
        private KExpr FloatCall(string name, ITypeSymbol t, KExpr[] a, ITypeSymbol result, bool inSpec)
        {
            var n = FloatSize(t);
            KExpr Op(string f, params KExpr[] xs) => new KOp("$fp." + f + n, xs);
            switch (name)
            {
                case "IsNaN": return Op("isNaN", a[0]);
                case "IsInfinity": return Op("isInf", a[0]);
                case "IsFinite": return Not(OrElse(Op("isNaN", a[0]), Op("isInf", a[0])));
                case "IsPositiveInfinity": return AndAlso(Op("isInf", a[0]), Op("isPos", a[0]));
                case "IsNegativeInfinity": return AndAlso(Op("isInf", a[0]), Op("isNeg", a[0]));
                case "IsNormal": return Op("isNormal", a[0]);
                case "IsSubnormal": return Op("isSubnormal", a[0]);
                case "Abs" when a.Length == 1: return Op("abs", a[0]);
                case "Sqrt" when a.Length == 1: return Op("sqrt", a[0]);
                case "Floor" when a.Length == 1: return Op("floor", a[0]);
                case "Ceiling" when a.Length == 1: return Op("ceil", a[0]);
                case "Truncate" when a.Length == 1: return Op("trunc", a[0]);
                case "Round" when a.Length == 1: return Op("round", a[0]);
                case "FusedMultiplyAdd" when a.Length == 3: return Op("fma", a[0], a[1], a[2]);
                case "Min" or "Max" when a.Length == 2:
                {
                    bool min = name == "Min";
                    var nan = OrElse(Op("isNaN", a[0]), Op("isNaN", a[1]));
                    var less = Op(min ? "lt" : "gt", a[0], a[1]);
                    var more = Op(min ? "lt" : "gt", a[1], a[0]);
                    var keepA = Op(min ? "isNeg" : "isPos", a[0]);
                    return new KOp("ite", nan, FloatLiteral(t.SpecialType == SpecialType.System_Single ? (object)float.NaN : double.NaN, t),
                        new KOp("ite", less, a[0], new KOp("ite", more, a[1], new KOp("ite", keepA, a[0], a[1]))));
                }
                default:
                    if (inSpec || !InSubset(result))
                    {
                        throw new NotTranslated("Math." + name + " of floats");
                    }
                    var r = Declare("t$" + _temps++, result);
                    Emit(new KHavoc { Var = r });
                    return new KVar(r);
            }
        }

        /// <summary>
        /// A conversion to or from a float type: integer to float and float to float round to nearest; float to an
        /// integer type truncates, and must fit (CSV1010), or its value isn't known.
        /// </summary>
        private KExpr FloatConversion(IConversionOperation c, KExpr v, bool inSpec)
        {
            ITypeSymbol from = c.Operand.Type, to = c.Type;
            if (IsFloating(from) && IsFloating(to))
            {
                return from.SpecialType == to.SpecialType ? v : to.SpecialType == SpecialType.System_Double ? new KOp("$fp.widen", v) : new KOp("$fp.narrow", v);
            }
            if (IsFloating(to))
            {
                if (!IsIntegral(from))
                {
                    throw new NotTranslated("a conversion of " + from + " to " + to);
                }
                return new KOp("$fp.ofReal" + FloatSize(to), new KOp("$toreal", v));
            }
            if (!IsIntegral(to))
            {
                throw new NotTranslated("a conversion of " + from + " to " + to);
            }
            var n = FloatSize(from);
            var (lo, hi) = Range(to);
            var t = new KOp("$fp.trunc" + n, v);
            var fits = AndAlso(AndAlso(Not(new KOp("$fp.isNaN" + n, v)), Not(new KOp("$fp.isInf" + n, v))),
                AndAlso(new KOp("$fp.geq" + n, t, new KOp("$fp.ofReal" + n, new KLit(lo + ".0"))), new KOp("$fp.lt" + n, t, new KOp("$fp.ofReal" + n, new KLit((hi + 1) + ".0")))));
            var value = new KOp("$toint", new KOp("$fp.real" + n, t));
            // (in a specification, a cast that doesn't fit has no value: it must be shown to fit, as a divisor isn't zero)
            // (where it doesn't, a value of the type all the same, which nothing is then concluded from)
            if (inSpec)
            {
                return new KOp("$need", fits, new KOp("ite", AndAlso(fits, AndAlso(new KOp("<=", Number(lo), value), new KOp("<=", value, Number(hi)))), value, Number(lo)));
            }
            var mode = Mode(c.Syntax, c.IsChecked);
            // (checked: where it doesn't fit, it throws an OverflowException, which the handlers may catch; in a proof, it may not)
            if (mode == KMode.Checked)
            {
                if (_contract.IsPure || _contract.IsLemma)
                {
                    Emit(new KCheck
                    {
                        Cond = fits,
                        Id = "CSV1010",
                        At = c.Syntax,
                        Message = $"conversion '{c.Syntax}' to {to.Name} might not fit (it might be NaN, infinite, or out of range)",
                    });
                }
                else
                {
                    if (_cfgBlock != null && ThrowTarget(_cfgBlock.EnclosingRegion) is string overflowTo)
                    {
                        Emit(new KFork
                        {
                            Overflow = fits,
                            Target = overflowTo,
                            Exception = null,
                        });
                    }
                    Emit(new KAssume { Cond = fits });
                }
                return value;
            }
            if (mode == KMode.Default)
            {
                Emit(new KCheck
                {
                    Cond = fits,
                    Id = "CSV1010",
                    At = c.Syntax,
                    Message = $"conversion '{c.Syntax}' to {to.Name} might not fit (it might be NaN, infinite, or out of range)",
                });
            }
            if (mode == KMode.Default)
            {
                return value;
            }
            var r = Declare("t$" + _temps++, to);
            Emit(new KHavoc { Var = r });
            return new KOp("ite", fits, value, new KVar(r));
        }
    }
}
