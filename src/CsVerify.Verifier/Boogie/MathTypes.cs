using System.Globalization;
using System.Linq;
using System.Numerics;
using Microsoft.CodeAnalysis;
using static CsVerify.Verifier.Boogie.KernelTypes;
using static CsVerify.Verifier.Boogie.MOp;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>
    /// What C#'s types mean, as level 2's mathematics: a type's default value, its range, a value wrapped into it, a
    /// collection read through an interface. Those of no expression are the kernel's too (KernelTypes embeds them).
    /// </summary>
    internal static class MathTypes
    {
        public static MExpr Number(BigInteger n) => new MLit(n < 0 ? $"({n.ToString(CultureInfo.InvariantCulture)})" : n.ToString(CultureInfo.InvariantCulture));

        public static MExpr Default(ITypeSymbol t) =>
            IsGhost(t) ? Default(GhostOf(t)) : IsStruct(t) ? StructDefault(t) : IsObjSet(t) ? new MLit("(lambda r$: Ref :: false)") : IsFloating(t) ? FloatLiteral(0.0, t)
            : new MLit(IsNullable(t) || TypeOf(t) == "Ref" ? "null" : t.SpecialType == SpecialType.System_Boolean ? "false" : "0");

        /// <summary>A struct's default value: each element its type's.</summary>
        public static MExpr StructDefault(ITypeSymbol t) => new MOp(TupleMaker(t), StructFields(t).Select(f => Default(f.Type)).ToArray());

        /// <summary>A float's value, exactly: its bits.</summary>
        public static MExpr FloatLiteral(object v, ITypeSymbol t)
        {
            if (t.SpecialType == SpecialType.System_Single)
            {
                return new MOp("$fp.bits32", new MLit(((uint)System.BitConverter.SingleToInt32Bits(System.Convert.ToSingle(v))).ToString() + "bv32"));
            }
            return new MOp("$fp.bits64", new MLit(((ulong)System.BitConverter.DoubleToInt64Bits(System.Convert.ToDouble(v))).ToString() + "bv64"));
        }

        /// <summary>lo &lt;= e &lt;= hi of t.</summary>
        public static MExpr InRange(MExpr e, ITypeSymbol t)
        {
            var (lo, hi) = Range(t);
            return AndAlso(new MOp("<=", Number(lo), e), new MOp("<=", e, Number(hi)));
        }

        /// <summary>e wrapped around into t's range: two's complement, as Euclidean mod.</summary>
        public static MExpr Wrap(MExpr e, ITypeSymbol t)
        {
            var (lo, _) = Range(t);
            return new MOp("wrap", e, Number(lo), Number(BigInteger.Pow(2, Widths[Sp(t)].bits)));
        }

        /// <summary>A tuple's element i.</summary>
        public static MExpr TupleItem(MExpr v, ITypeSymbol tuple, int i) => new MOp($"$tup.{i}.{TypeOf(PartsOf(tuple)[i]).Replace("[", "_").Replace("]", "_")}", v);

        /// <summary>A data value is of this type: not null, and its tag one of the type's cases'.</summary>
        public static MExpr IsCase(MExpr v, ITypeSymbol type)
        {
            // (an open type's values: of any case, those the program has or others)
            if (Data.IsOpen(DataTypes.Def(type)))
            {
                return NotNull(v);
            }
            var tags = Data.Cases(DataTypes.Def(type)).Select(c => (MExpr)new MOp("$is." + CaseName(c).Substring(3), v)).ToList();
            var any = tags.Count == 0 ? MLit.False : tags.Aggregate((a, b) => OrElse(a, b));
            return AndAlso(NotNull(v), any);
        }

        /// <summary>A value as a box (where generic code takes it).</summary>
        public static MExpr Box(MExpr v, ITypeSymbol def, ITypeSymbol actual) =>
            IsTypeParameter(def) && !IsTypeParameter(actual) && actual != null ? new MOp("$box." + BoxKind(actual), v) : v;

        /// <summary>A collection interface's Count or element, as an expression: an array's, a modeled collection's (Size, Items), or the state's.</summary>
        public static MExpr IfcRead(MExpr x, MExpr index, ITypeSymbol element)
        {
            var list = (INamedTypeSymbol)KernelTypes.Compilation.GetTypeByMetadataName("System.Collections.Generic.List`1").Construct(element);
            var kind = Kind(element);
            if (index == null)
            {
                return new MOp("ite", new MOp("$arr", x), new MOp("len", x), new MOp("ite", new MOp("$coll", x), Sel(SizeMap, x), new MOp("$ocount", x, new MOp("$state"))));
            }
            var array = (IArrayTypeSymbol)KernelTypes.Compilation.CreateArrayTypeSymbol(element);
            return new MOp("ite", new MOp("$arr", x), Sel(Elements(array), x, index),
                new MOp("ite", new MOp("$coll", x), Sel(ModelOf("Items", list).Name, x, index), new MOp("$oitem." + kind, x, index, new MOp("$state"))));
        }
    }
}
