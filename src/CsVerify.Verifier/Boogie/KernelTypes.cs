using System.Collections.Generic;
using System.Globalization;
using System.Linq;
using System.Numerics;
using System.Text;
using CsVerify.Analyzers;
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

        public static bool InSubset(ITypeSymbol t) => Scalar(t) || IsArray(t) || IsClass(t) || IsView(t) || IsString(t) || IsException(t) || IsDelegate(t) || IsList(t);

        /// <summary>A delegate of the subset's values: a Func or an Action, or a non-generic delegate type of the program's.</summary>
        public static bool IsDelegate(ITypeSymbol t) =>
            IsFunc(t) || t is INamedTypeSymbol { TypeKind: TypeKind.Delegate, Arity: 0 } d && d.DeclaringSyntaxReferences.Length > 0 &&
            d.DelegateInvokeMethod is IMethodSymbol inv && inv.Parameters.All(p => p.RefKind == RefKind.None && FuncValue(p.Type)) && (inv.ReturnsVoid || FuncValue(inv.ReturnType));

        /// <summary>A Func or an Action of the subset's values: a reference, which Spec.Pre and Spec.Post speak of.</summary>
        public static bool IsFunc(ITypeSymbol t) =>
            t is INamedTypeSymbol { TypeKind: TypeKind.Delegate } d && d.ContainingNamespace?.ToDisplayString() == "System" && d.Name is "Func" or "Action" &&
            d.DelegateInvokeMethod is IMethodSymbol inv && inv.Parameters.All(p => p.RefKind == RefKind.None && FuncValue(p.Type)) && (inv.ReturnsVoid || FuncValue(inv.ReturnType));

        private static bool FuncValue(ITypeSymbol t) => Scalar(t) || IsArray(t) || IsClass(t) || IsString(t);

        /// <summary>A Func's or an Action's signature, as Boogie's types: its parameters', then its result's (or void).</summary>
        public static string FuncKey(ITypeSymbol t)
        {
            var inv = ((INamedTypeSymbol)t).DelegateInvokeMethod;
            string Of(ITypeSymbol x) => Scalar(x) ? x.SpecialType.ToString().Substring("System_".Length) : "Ref";
            return string.Join(".", inv.Parameters.Select(p => Of(p.Type)).Append(inv.ReturnsVoid ? "void" : Of(inv.ReturnType)));
        }

        /// <summary>A string: a value (its length, its characters), a Ref only so that null is one; never allocated.</summary>
        public static bool IsString(ITypeSymbol t) => t?.SpecialType == SpecialType.System_String;

        /// <summary>A ghost set of objects (Spec.Modifies, Spec.Reads): a [Ref]bool.</summary>
        public static bool IsObjSet(ITypeSymbol t) => SpecSymbols.IsCsVerifyType(t, "ObjSet");

        /// <summary>An exception: a reference of a type derived from System.Exception (its fields aren't the kernel's).</summary>
        public static bool IsException(ITypeSymbol t)
        {
            for (var c = t as INamedTypeSymbol; c != null; c = c.BaseType)
                if (c.OriginalDefinition.ToDisplayString() == "System.Exception") return t is INamedTypeSymbol n && n.Arity == 0;
            return false;
        }

        /// <summary>An exception type's constant (Ty).</summary>
        public static string TypeConst(ITypeSymbol t) => "T#" + Ident(t.OriginalDefinition.ToDisplayString());

        /// <summary>What may be null: a reference or a string.</summary>
        public static bool IsNullable(ITypeSymbol t) => IsRef(t) || IsString(t) || IsException(t) || IsDelegate(t);

        /// <summary>An [Owned] class of the subset: its objects are written only by whoever holds their view.</summary>
        public static bool IsOwnedClass(ITypeSymbol t) => IsClass(t) && SpecSymbols.IsOwned(t);

        /// <summary>A view, Own&lt;C&gt; of an [Owned] class: its value is the object it owns (a Ref, never null).</summary>
        public static bool IsView(ITypeSymbol t) => SpecSymbols.IsOwnType(t) && IsOwnedClass(((INamedTypeSymbol)t).TypeArguments[0]);

        public static ITypeSymbol ViewOf(ITypeSymbol view) => ((INamedTypeSymbol)view).TypeArguments[0];

        /// <summary>The fields a whole object of this type has: those a split hands out one by one.</summary>
        public static List<ISymbol> WholeFields(ITypeSymbol type) =>
            FieldEffects.FieldsOf(type).Where(x => FieldEffects.IsHeapField(x) && !x.IsStatic).Select(FieldEffects.Key).Distinct(SymbolEqualityComparer.Default).ToList();

        /// <summary>A field of an [Owned] class's objects: written only with the object's view.</summary>
        public static bool IsOwnedField(ISymbol field) => !field.IsStatic && SpecSymbols.IsOwned(field.ContainingType);

        /// <summary>A reference: an array or an object.</summary>
        public static bool IsRef(ITypeSymbol t) => IsArray(t) || IsClass(t) || IsInterface(t) || IsList(t);

        /// <summary>A List&lt;T&gt; of the subset's values: an object, its contents the model CsVerify.Bcl's contracts speak of.</summary>
        public static bool IsList(ITypeSymbol t) =>
            t is INamedTypeSymbol { Arity: 1 } n && n.OriginalDefinition.ToDisplayString() == "System.Collections.Generic.List<T>" && FuncValue(n.TypeArguments[0]);

        /// <summary>A list's elements' kind, as Boogie keeps them: an integer type's name, Boolean, or Ref.</summary>
        public static string ListKey(ITypeSymbol list)
        {
            var e = ((INamedTypeSymbol)list).TypeArguments[0];
            return Scalar(e) ? e.SpecialType.ToString().Substring("System_".Length) : "Ref";
        }

        /// <summary>The model's maps: how many elements (Size), the version (Version), and the elements (Items, of a kind).</summary>
        public const string SizeMap = "$F.$M.Size", VersionMap = "$F.$M.Version";
        public static string ItemsMap(string key) => "$F.$M.Items." + key;
        public static string ItemsType(string key) => key == "Ref" ? "[Ref][int]Ref" : key == "Boolean" ? "[Ref][int]bool" : "[Ref][int]int";

        /// <summary>An interface of the program's, not generic, of abstract members only (their contracts from a contract class).</summary>
        public static bool IsInterface(ITypeSymbol t) =>
            t is INamedTypeSymbol n && n.TypeKind == TypeKind.Interface && n.Arity == 0 && n.DeclaringSyntaxReferences.Length > 0 &&
            n.ContainingNamespace?.ToDisplayString() != SpecSymbols.Namespace && !CsVerifyAttributes(n) &&
            n.GetMembers().All(m => m.IsAbstract && !m.IsStatic && !CsVerifyAttributes(m)) && n.AllInterfaces.All(IsInterface);

        /// <summary>
        /// A property computed by code (or an abstract or an interface one, specified by its contract): its getter and
        /// setter are methods, called where it is read and written. Not an auto-property's, which is a field.
        /// </summary>
        public static bool IsComputed(IPropertySymbol p) =>
            p != null && !FieldEffects.IsHeapField(p) && p.DeclaringSyntaxReferences.Length > 0 && p.ContainingNamespace?.ToDisplayString() != SpecSymbols.Namespace;

        /// <summary>
        /// A class of the program whose objects are plain mutable state: not generic, not static, not a record (a data
        /// type), derived from object, with no virtual members, interfaces or overrides (which run code a call can't
        /// see), and none of CsVerify's attributes on it or its fields ([Owned], [Invariant], locks, atomics, models).
        /// </summary>
        public static bool IsClass(ITypeSymbol t) =>
            t is INamedTypeSymbol n && n.TypeKind == TypeKind.Class && !n.IsStatic && !n.IsRecord && n.Arity == 0 &&
            (n.ContainingType == null || !n.ContainingType.IsGenericType) && n.DeclaringSyntaxReferences.Length > 0 &&
            // (derived from object, or from a class of the subset; an [Owned] one from object)
            (n.BaseType?.SpecialType == SpecialType.System_Object || !SpecSymbols.IsOwned(n) && IsClass(n.BaseType)) && n.ContainingNamespace?.ToDisplayString() != SpecSymbols.Namespace &&
            n.AllInterfaces.All(i => IsInterface(i) || i.ToDisplayString() == "System.IDisposable") && !SpecSymbols.IsContractsClass(n) &&
            !n.GetAttributes().Any(a => a.AttributeClass?.ContainingNamespace?.ToDisplayString() == SpecSymbols.Namespace && a.AttributeClass.Name != "OwnedAttribute") &&
            // (virtual members, of methods: an override only of a member of the program's, whose contract it inherits)
            n.GetMembers().All(m => (m is IMethodSymbol mm ? !mm.IsOverride || mm.OverriddenMethod?.DeclaringSyntaxReferences.Length > 0
                                     : m is IPropertySymbol pp ? !pp.IsOverride || pp.OverriddenProperty?.DeclaringSyntaxReferences.Length > 0
                                     : !m.IsVirtual && !m.IsAbstract && !m.IsOverride) &&
                                    !(m is IFieldSymbol && CsVerifyAttributes(m)) &&
                                    // (a property may be [Pure]: a function)
                                    !(m is IPropertySymbol && m.GetAttributes().Any(a => a.AttributeClass?.ContainingNamespace?.ToDisplayString() == SpecSymbols.Namespace && a.AttributeClass.Name != "PureAttribute"))) &&
            // (an invariant of an [Owned] class travels with its view; any other's is a data type's, assumed of every object)
            (SpecSymbols.IsOwned(n) || !n.GetMembers().OfType<IMethodSymbol>().Any(m => m.GetAttributes().Any(a => a.AttributeClass?.Name == "InvariantAttribute")));

        private static bool CsVerifyAttributes(ISymbol s) =>
            s.GetAttributes().Any(a => a.AttributeClass?.ContainingNamespace?.ToDisplayString() == SpecSymbols.Namespace);

        /// <summary>A field the kernel has: a heap field (an instance field or auto-property, or a mutable static field) of a class in the subset, of a type in it.</summary>
        public static bool IsField(ISymbol s) =>
            s != null && FieldEffects.IsHeapField(s) && InSubset(FieldType(s)) &&
            (s.IsStatic ? s.ContainingType.Arity == 0 && s.ContainingType.ContainingType == null && !CsVerifyAttributes(s) : IsClass(s.ContainingType));

        public static ITypeSymbol FieldType(ISymbol s) => s.OriginalDefinition is IFieldSymbol f ? f.Type : ((IPropertySymbol)s.OriginalDefinition).Type;

        /// <summary>A field's map: object (null for a static field's one object) to value.</summary>
        public static string FieldMap(ISymbol s) => "$F." + Ident(s.ContainingType.ToDisplayString() + "." + s.Name);

        /// <summary>The fields of a class an object of it has (the static ones aren't its).</summary>
        public static IEnumerable<ISymbol> InstanceFields(ITypeSymbol t)
        {
            // (its base classes' too)
            for (var c = t as INamedTypeSymbol; c != null && c.SpecialType != SpecialType.System_Object; c = c.BaseType)
                foreach (var m in c.GetMembers().Where(m => !m.IsStatic && IsField(m))) yield return m.OriginalDefinition;
        }

        public static KExpr Default(ITypeSymbol t) => new KLit(IsNullable(t) ? "null" : t.SpecialType == SpecialType.System_Boolean ? "false" : "0");

        /// <summary>A non-nullable reference type, in an enabled nullable context (an oblivious one promises nothing).</summary>
        public static bool NotNullable(ITypeSymbol t) => t.IsReferenceType && t.NullableAnnotation == NullableAnnotation.NotAnnotated;

        public static string TypeOf(ITypeSymbol t) => IsRef(t) || IsView(t) || IsString(t) || IsException(t) || IsDelegate(t) ? "Ref" : t.SpecialType == SpecialType.System_Boolean ? "bool" : "int";

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
