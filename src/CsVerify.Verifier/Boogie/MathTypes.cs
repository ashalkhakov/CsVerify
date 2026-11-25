using System.Collections.Generic;
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
        /// <summary>A struct's or a tuple's parts, at any depth (a struct's struct's fields too), each with its type.</summary>
        public static IEnumerable<(MExpr part, ITypeSymbol type)> Parts(MExpr v, ITypeSymbol t, int depth = 0)
        {
            // (a nullable struct's: its value's, whatever it is where it has none)
            if (depth <= 8 && IsNullableStruct(t))
            {
                foreach (var inner in Parts(new MOp("$nv." + NullableKey(t), v), Underlying(t), depth + 1))
                {
                    yield return inner;
                }
                yield break;
            }
            if (depth > 8 || !(IsStruct(t) || IsTuple(t)))
            {
                yield break;
            }
            var parts = IsTuple(t) ? PartsOf(t) : StructFields(t).Select(f => f.Type).ToList();
            for (int k = 0; k < parts.Count; k++)
            {
                var item = TupleItem(v, t, k);
                yield return (item, parts[k]);
                foreach (var inner in Parts(item, parts[k], depth + 1))
                {
                    yield return inner;
                }
            }
        }

        /// <summary>A tuple's or an anonymous object's members of a non-nullable reference type.</summary>
        public static IEnumerable<MExpr> NotNullParts(MExpr v, ITypeSymbol t)
        {
            if (!IsTuple(t))
            {
                yield break;
            }
            var parts = PartsOf(t);
            for (int k = 0; k < parts.Count; k++)
            {
                if (IsNullable(parts[k]) && NotNullable(parts[k]))
                {
                    yield return TupleItem(v, t, k);
                }
            }
        }

        public static MExpr StructDefault(ITypeSymbol t) =>
            new MOp(TupleMaker(t), StructFields(t).Select((f, k) => Box(Default(f.Type), LayoutOf(t)[k], f.Type)).ToArray());

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
            return AndAlso(Le(Number(lo), e), Le(e, Number(hi)));
        }

        /// <summary>e wrapped around into t's range: two's complement, as Euclidean mod.</summary>
        public static MExpr Wrap(MExpr e, ITypeSymbol t)
        {
            var (lo, _) = Range(t);
            return new MOp("wrap", e, Number(lo), Number(BigInteger.Pow(2, Widths[Sp(t)].bits)));
        }

        /// <summary>A tuple's element i.</summary>
        public static MExpr TupleItem(MExpr v, ITypeSymbol tuple, int i) =>
            Unbox(new MOp($"$tup.{i}.{TypeOf(LayoutOf(tuple)[i]).Replace("[", "_").Replace("]", "_")}", v), LayoutOf(tuple)[i], PartsOf(tuple)[i]);

        /// <summary>A data value is of this type: not null, and its tag one of the type's cases'.</summary>
        public static MExpr IsCase(MExpr v, ITypeSymbol type)
        {
            // (an open type's values: of any case, those the program has or others)
            if (Data.IsOpen(DataTypes.Def(type)))
            {
                return NotNull(v);
            }
            var tags = Data.Cases(DataTypes.Def(type)).Select(c => (MExpr)new MOp("$is." + CaseName(c).Substring(3), v)).ToList();
            var any = tags.Count == 0 ? MLit.False : OrAny(tags);
            return AndAlso(NotNull(v), any);
        }

        /// <summary>
        /// v is a value of t, as far as t says: a data value one of its cases (or null, where t is nullable), an integer
        /// in its range; null where t says no more.
        /// </summary>
        public static MExpr OfType(MExpr v, ITypeSymbol t) =>
            IsGhost(t) ? OfType(v, GhostOf(t))
            : IsData(t) ? (NotNullable(t) ? IsCase(v, t) : OrElse(IsNull(v), IsCase(v, t)))
            : IsIntegral(t) ? InRange(v, t)
            : IsDecimal(t) ? AndAlso(Le(Number(-Lowering.DecimalMax), v), Le(v, Number(Lowering.DecimalMax)))
            // (a DateTime's ticks within its range, a TimeSpan's within long's)
            : t?.ToDisplayString() == "System.DateTime" ? AndAlso(Le(MLit.Zero, v), Le(v, Number(Lowering.MaxTicks)))
            : t?.ToDisplayString() == "System.TimeSpan" ? AndAlso(Le(Number(long.MinValue), v), Le(v, Number(long.MaxValue))) : null;

        /// <summary>A value as a box (where generic code takes it), and back.</summary>
        public static MExpr Box(MExpr v, ITypeSymbol def, ITypeSymbol actual) =>
            IsTypeParameter(def) && !IsTypeParameter(actual) && actual != null ? new MOp("$box." + BoxKind(actual), v) : v;
        public static MExpr Unbox(MExpr v, ITypeSymbol def, ITypeSymbol actual) =>
            IsTypeParameter(def) && !IsTypeParameter(actual) && actual != null ? new MOp("$unbox." + BoxKind(actual), v) : v;

        /// <summary>A collection interface's Count or element, as an expression: an array's, a modeled collection's (Size, Items), or the state's.</summary>
        public static MExpr IfcRead(MExpr x, MExpr index, ITypeSymbol element)
        {
            var list = (INamedTypeSymbol)KernelTypes.Compilation.GetTypeByMetadataName("System.Collections.Generic.List`1").Construct(element);
            var kind = Kind(element);
            if (index == null)
            {
                return Ite(new MOp("$arr", x), Length(x), Ite(new MOp("$coll", x), Sel(SizeMap, x), new MOp("$ocount", x, new MOp("$state"))));
            }
            var array = (IArrayTypeSymbol)KernelTypes.Compilation.CreateArrayTypeSymbol(element);
            return Ite(new MOp("$arr", x), Sel(Elements(array), x, index),
                Ite(new MOp("$coll", x), Sel(ModelOf("Items", list).Name, x, index), new MOp("$oitem." + kind, x, index, new MOp("$state"))));
        }
    }
}
