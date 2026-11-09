using System.Collections.Generic;
using System.Globalization;
using System.Linq;
using System.Numerics;
using System.Text;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>The C# types the kernel has, and how each is named and bounded in Boogie (every pass's vocabulary).</summary>
    internal static class KernelTypes
    {
        /// <summary>Each C# integer type: its bits, and whether it is signed (char is an unsigned 16-bit integer here).</summary>
        public static readonly Dictionary<SpecialType, (int bits, bool signed)> Widths = new Dictionary<SpecialType, (int, bool)>
        {
            [SpecialType.System_SByte] = (8, true), [SpecialType.System_Byte] = (8, false),
            [SpecialType.System_Int16] = (16, true), [SpecialType.System_UInt16] = (16, false), [SpecialType.System_Char] = (16, false),
            [SpecialType.System_Int32] = (32, true), [SpecialType.System_UInt32] = (32, false),
            [SpecialType.System_Int64] = (64, true), [SpecialType.System_UInt64] = (64, false),
        };

        /// <summary>The element types of arrays: each integer type, and bool.</summary>
        public static readonly SpecialType[] ElementTypes = Widths.Keys.Append(SpecialType.System_Boolean).ToArray();

        public static bool IsIntegral(ITypeSymbol t) => t != null && Widths.ContainsKey(t.SpecialType);

        public static bool Scalar(ITypeSymbol t) => IsIntegral(t) || t?.SpecialType == SpecialType.System_Boolean;

        public static bool IsArray(ITypeSymbol t) => t is IArrayTypeSymbol a && a.IsSZArray && Scalar(a.ElementType);

        public static bool InSubset(ITypeSymbol t) => Scalar(t) || IsArray(t);

        public static bool NotNullable(ITypeSymbol t) => t.NullableAnnotation != NullableAnnotation.Annotated;

        public static string TypeOf(ITypeSymbol t) => IsArray(t) ? "Ref" : t.SpecialType == SpecialType.System_Boolean ? "bool" : "int";

        public static string ElementMap(SpecialType t) => "$E." + t.ToString().Substring("System_".Length);

        /// <summary>The map of an array type's elements.</summary>
        public static string Elements(ITypeSymbol array) => ElementMap(((IArrayTypeSymbol)array).ElementType.SpecialType);

        public static (BigInteger lo, BigInteger hi) Range(SpecialType t)
        {
            var (bits, signed) = Widths[t];
            var size = BigInteger.Pow(2, bits);
            return signed ? (-(size / 2), size / 2 - 1) : (0, size - 1);
        }

        public static (BigInteger lo, BigInteger hi) Range(ITypeSymbol t) => Range(t.SpecialType);

        public static KExpr Number(BigInteger n) => new KLit(n < 0 ? $"({n.ToString(CultureInfo.InvariantCulture)})" : n.ToString(CultureInfo.InvariantCulture));

        /// <summary>lo &lt;= e &lt;= hi of t.</summary>
        public static KExpr InRange(KExpr e, ITypeSymbol t)
        {
            var (lo, hi) = Range(t);
            return new KOp("&&", new KOp("<=", Number(lo), e), new KOp("<=", e, Number(hi)));
        }

        /// <summary>e wrapped around into t's range: two's complement, as Euclidean mod.</summary>
        public static KExpr Wrap(KExpr e, ITypeSymbol t)
        {
            var (lo, _) = Range(t);
            return new KOp("wrap", e, Number(lo), Number(BigInteger.Pow(2, Widths[t.SpecialType].bits)));
        }

        public static string Name(IMethodSymbol m) =>
            Ident(m.ContainingType.ToDisplayString() + "." + m.Name + "$" + string.Join("$", m.Parameters.Select(p => p.Type.ToDisplayString())));

        public static string FunctionName(IMethodSymbol m) => "f$" + Name(m);

        public static string Ident(string s)
        {
            var b = new StringBuilder();
            foreach (var ch in s) b.Append(char.IsLetterOrDigit(ch) || ch == '_' || ch == '.' || ch == '$' ? ch : '_');
            return b.ToString();
        }

        public static string Local(ISymbol s) => s is IParameterSymbol p ? "p$" + p.Name : "l$" + s.Name + "$" + s.Locations.FirstOrDefault()?.SourceSpan.Start;

        /// <summary>Is this syntax in an unchecked context (the innermost checked or unchecked around it)?</summary>
        public static bool InUnchecked(SyntaxNode at) =>
            at.AncestorsAndSelf().Select(n => n is CheckedExpressionSyntax ce ? ce.Kind() : n is CheckedStatementSyntax cs ? cs.Kind() : SyntaxKind.None)
                .FirstOrDefault(k => k != SyntaxKind.None) is SyntaxKind.UncheckedExpression or SyntaxKind.UncheckedStatement;
    }
}
