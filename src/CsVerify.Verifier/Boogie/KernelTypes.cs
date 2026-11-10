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

        public static bool InSubset(ITypeSymbol t) => Scalar(t) || IsArray(t) || IsClass(t) || t?.SpecialType == SpecialType.System_Object || IsView(t) || IsShare(t) || IsString(t) || IsException(t) || IsDelegate(t) || IsCollection(t) || IsPair(t) ||
                                                    IsData(t) || IsTypeParameter(t) || IsGhost(t) && InSubset(GhostOf(t)) || IsToken(t);

        /// <summary>A CancellationToken: a value nothing is known of (whether it's cancelled is a new answer at every read).</summary>
        public static bool IsToken(ITypeSymbol t) => t?.ToDisplayString() == "System.Threading.CancellationToken";

        /// <summary>The program's data types (closed hierarchies of positional records), for the run this thread is in.</summary>
        [System.ThreadStatic] public static DataTypes Data;
        [System.ThreadStatic] public static Compilation Compilation;

        /// <summary>A data record (Dafny's datatype): a value is its constructor applied to its fields; null too, as a reference.</summary>
        public static bool IsData(ITypeSymbol t) =>
            Data != null && t is INamedTypeSymbol n && Data.IsData(n) && Data.Cases(DataTypes.Def(n)) != null &&
            (!n.IsGenericType || n.TypeArguments.All(a => IsTypeParameter(a) || FuncValue(a) || IsData(a)));

        /// <summary>A type parameter without constraints: its values are boxes (Box), as Dafny's are.</summary>
        public static bool IsTypeParameter(ITypeSymbol t) =>
            t is ITypeParameterSymbol tp && !tp.HasReferenceTypeConstraint && !tp.HasValueTypeConstraint && !tp.HasUnmanagedTypeConstraint &&
            !tp.HasNotNullConstraint && !tp.HasConstructorConstraint && tp.ConstraintTypes.Length == 0;

        /// <summary>A ghost value (Ghost&lt;T&gt;): erased, the value itself.</summary>
        public static bool IsGhost(ITypeSymbol t) => SpecSymbols.IsCsVerifyType(t, "Ghost`1");
        public static ITypeSymbol GhostOf(ITypeSymbol t) => ((INamedTypeSymbol)t).TypeArguments[0];

        /// <summary>A data type's names: its case's constructor function, a field's function.</summary>
        public static string CaseName(INamedTypeSymbol c) => "mk." + Ident(DataTypes.Def(c).ToDisplayString());
        public static string FieldFunction(IPropertySymbol p) => "$d." + Ident(p.OriginalDefinition.ContainingType.OriginalDefinition.ToDisplayString() + "." + p.Name);

        /// <summary>A data type with [Invariant]s (its own or its bases'): its values are valid ($valid.T).</summary>
        /// <summary>A data type with invariants: its own, or (a base's) one of its cases'.</summary>
        public static bool HasInvariants(ITypeSymbol t) => IsData(t) && (DataTypes.Invariants(DataTypes.Def(t)).Any() ||
            (Data.Cases(DataTypes.Def(t))?.Any(c => !SymbolEqualityComparer.Default.Equals(c, DataTypes.Def(t)) && DataTypes.Invariants(c).Any()) ?? false));
        public static string ValidName(ITypeSymbol t) => "$valid." + Ident(DataTypes.Def(t).ToDisplayString());

        /// <summary>A data value is of this type: not null, and its tag one of the type's cases'.</summary>
        public static KExpr IsCase(KExpr v, ITypeSymbol type)
        {
            var tags = Data.Cases(DataTypes.Def(type)).Select(c => (KExpr)new KOp("$is." + CaseName(c).Substring(3), v)).ToList();
            var any = tags.Count == 0 ? new KLit("false") : tags.Aggregate((a, b) => new KOp("||", a, b));
            return new KOp("&&", new KOp("!=", v, new KLit("null")), any);
        }

        /// <summary>A value as a box (where generic code takes it), and back.</summary>
        public static KExpr Box(KExpr v, ITypeSymbol def, ITypeSymbol actual) =>
            def is ITypeParameterSymbol && !(actual is ITypeParameterSymbol) && actual != null ? new KOp("$box." + BoxKind(actual), v) : v;
        public static KExpr Unbox(KExpr v, ITypeSymbol def, ITypeSymbol actual) =>
            def is ITypeParameterSymbol && !(actual is ITypeParameterSymbol) && actual != null ? new KOp("$unbox." + BoxKind(actual), v) : v;
        public static string BoxKind(ITypeSymbol t) => t.SpecialType == SpecialType.System_Boolean ? "bool" : Scalar(t) ? "int" : "Ref";

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
        public static bool IsNullable(ITypeSymbol t) => IsRef(t) || IsString(t) || IsException(t) || IsDelegate(t) || IsData(t);

        /// <summary>An [Owned] class of the subset: its objects are written only by whoever holds their view.</summary>
        public static bool IsOwnedClass(ITypeSymbol t) => IsClass(t) && SpecSymbols.IsOwned(t);

        /// <summary>A view, Own&lt;C&gt; of an [Owned] class: its value is the object it owns (a Ref, never null).</summary>
        public static bool IsView(ITypeSymbol t) => SpecSymbols.IsOwnType(t) && IsOwnedClass(((INamedTypeSymbol)t).TypeArguments[0]);

        public static ITypeSymbol ViewOf(ITypeSymbol view) => ((INamedTypeSymbol)view).TypeArguments[0];

        /// <summary>A read share, Shared&lt;C&gt; of an [Owned] class: its value is the object (a Ref, never null).</summary>
        public static bool IsShare(ITypeSymbol t) => t != null && SpecSymbols.IsSharedType(t) && t is INamedTypeSymbol n && n.TypeArguments.Length == 1 && IsOwnedClass(n.TypeArguments[0]);

        /// <summary>A parameter that holds a read share: a Shared&lt;C&gt;, or a view lent read-only (in).</summary>
        public static bool HoldsShare(IParameterSymbol p) => IsShare(p.Type) && p.RefKind is RefKind.None or RefKind.In || IsView(p.Type) && p.RefKind == RefKind.In;

        /// <summary>A package: a [Linear] positional readonly record struct, which holds views (and anything else) together.</summary>
        public static bool IsPackage(ITypeSymbol t) => t != null && SpecSymbols.IsLinearPackage(t) && IsData(t);

        /// <summary>A package's views: its positional fields that are views.</summary>
        public static IEnumerable<IPropertySymbol> PackageViews(ITypeSymbol t) => Data.Fields((INamedTypeSymbol)t).Where(p => IsView(p.Type));

        /// <summary>A parameter that holds a whole view (by value or ref; out only gives one back).</summary>
        public static bool HoldsView(IParameterSymbol p) => IsView(p.Type) && p.RefKind is RefKind.None or RefKind.Ref;

        /// <summary>The fields a whole object of this type has: those a split hands out one by one.</summary>
        public static List<ISymbol> WholeFields(ITypeSymbol type) =>
            FieldEffects.FieldsOf(type).Where(x => FieldEffects.IsHeapField(x) && !x.IsStatic).Select(FieldEffects.Key).Distinct(SymbolEqualityComparer.Default).ToList();

        /// <summary>A field of an [Owned] class's objects: written only with the object's view.</summary>
        public static bool IsOwnedField(ISymbol field) => !field.IsStatic && SpecSymbols.IsOwned(field.ContainingType);

        /// <summary>A reference: an array or an object.</summary>
        /// <summary>A task type (Task, Task&lt;T&gt;, ValueTask, ValueTask&lt;T&gt;).</summary>
        public static bool IsTaskLike(ITypeSymbol t) =>
            t is INamedTypeSymbol n && n.ContainingNamespace?.ToDisplayString() == "System.Threading.Tasks" && n.Name is "Task" or "ValueTask";

        /// <summary>What a method gives back: an async one's task's result (null for none); else its return type (null for void).</summary>
        public static ITypeSymbol Returns(IMethodSymbol m) =>
            m.IsAsync && IsTaskLike(m.ReturnType) ? ((INamedTypeSymbol)m.ReturnType).TypeArguments.FirstOrDefault() : m.ReturnsVoid ? null : m.ReturnType;

        /// <summary>A lock's object (readonly, of type object): no state of the kernel's.</summary>
        public static bool IsLockObject(ISymbol s) => s is IFieldSymbol { IsReadOnly: true } f && (f.Type.SpecialType == SpecialType.System_Object || IsSemaphore(f.Type));

        public static bool IsSemaphore(ITypeSymbol t) => t?.ToDisplayString() == "System.Threading.SemaphoreSlim";

        /// <summary>What runs concurrently (CsVerify's engine's: marked, or started alongside), for the run this thread is in.</summary>
        [System.ThreadStatic] public static StartedDelegates Started;

        /// <summary>The locks' levels and what code takes (CsVerify's engine's static analysis), for the run this thread is in.</summary>
        [System.ThreadStatic] public static LockLevels Levels;

        /// <summary>The program has ownership trees ([Owns] fields): each object's tree root is the ghost map $root.</summary>
        [System.ThreadStatic] public static bool Trees;

        /// <summary>The locks of the program (CsVerify's engine's: what guards what, the locks' invariants), for the run this thread is in.</summary>
        [System.ThreadStatic] public static LockGuards Locks;

        public static bool IsRef(ITypeSymbol t) => IsArray(t) || IsClass(t) || IsInterface(t) || IsCollection(t) || t?.SpecialType == SpecialType.System_Object;

        /// <summary>The BCL collections whose contents CsVerify.Bcl's models are (their stub contracts speak of them).</summary>
        private static readonly string[] Collections =
        {
            "System.Collections.Generic.List<T>", "System.Collections.Generic.Dictionary<TKey, TValue>",
            "System.Collections.Generic.HashSet<T>", "System.Collections.Generic.Stack<T>", "System.Collections.Generic.Queue<T>",
        };

        /// <summary>The collection's kind: List, Dictionary, HashSet, Stack, Queue (null: not one).</summary>
        public static string CollectionKind(ITypeSymbol t) =>
            t is INamedTypeSymbol n && n.IsGenericType && Collections.Contains(n.OriginalDefinition.ToDisplayString()) ? n.Name : null;

        /// <summary>
        /// A collection of the subset's values: an object, its contents its models. The keys of a dictionary and the
        /// members of a set are compared as the verifier compares them, as values or by reference: not strings.
        /// </summary>
        public static bool IsCollection(ITypeSymbol t) =>
            CollectionKind(t) is string kind && ((INamedTypeSymbol)t).TypeArguments.All(FuncValue) &&
            (kind is "List" or "Stack" or "Queue" || !IsString(((INamedTypeSymbol)t).TypeArguments[0]));

        public static bool IsList(ITypeSymbol t) => CollectionKind(t) == "List" && IsCollection(t);

        /// <summary>A dictionary's pair (a foreach's): a value whose Key and Value are functions of it.</summary>
        public static bool IsPair(ITypeSymbol t) =>
            t is INamedTypeSymbol { Arity: 2 } n && n.OriginalDefinition.ToDisplayString() == "System.Collections.Generic.KeyValuePair<TKey, TValue>" &&
            n.TypeArguments.All(FuncValue) && !IsString(n.TypeArguments[0]);

        /// <summary>A value's kind, as Boogie keeps it: an integer type's name, Boolean, or Ref.</summary>
        public static string Kind(ITypeSymbol t) => Scalar(t) ? t.SpecialType.ToString().Substring("System_".Length) : "Ref";

        /// <summary>A kind's Boogie type.</summary>
        public static string BoogieOf(string kind) => kind == "Ref" ? "Ref" : kind == "Boolean" ? "bool" : "int";

        /// <summary>A model map: its name, its Boogie type, and the kind of what it holds where that has a range (else null).</summary>
        public sealed class ModelMap
        {
            public string Name, Type, Range;
        }

        public const string SizeMap = "$F.$M.Size", VersionMap = "$F.$M.Version";

        /// <summary>A collection's model by name (Size, Version, Items, Members, Domain, Entries), for its type's kinds.</summary>
        public static ModelMap ModelOf(string model, INamedTypeSymbol collection)
        {
            var args = collection.TypeArguments.Select(Kind).ToArray();
            return model switch
            {
                "Size" => new ModelMap { Name = SizeMap, Type = "[Ref]int" },
                "Version" => new ModelMap { Name = VersionMap, Type = "[Ref]int" },
                "Items" => new ModelMap { Name = "$F.$M.Items." + args[0], Type = $"[Ref][int]{BoogieOf(args[0])}", Range = args[0] },
                "Members" => new ModelMap { Name = "$F.$M.Members." + args[0], Type = $"[Ref][{BoogieOf(args[0])}]bool" },
                "Domain" => new ModelMap { Name = "$F.$M.Domain." + args[0], Type = $"[Ref][{BoogieOf(args[0])}]bool" },
                "Entries" => new ModelMap { Name = $"$F.$M.Entries.{args[0]}.{args[1]}", Type = $"[Ref][{BoogieOf(args[0])}]{BoogieOf(args[1])}", Range = args[1] },
                _ => null,
            };
        }

        /// <summary>All of a collection's models (what a member that changes it may change).</summary>
        public static IEnumerable<ModelMap> ModelsOf(INamedTypeSymbol collection) =>
            (CollectionKind(collection) switch
            {
                "Dictionary" => new[] { "Size", "Version", "Domain", "Entries" },
                "HashSet" => new[] { "Size", "Version", "Members" },
                _ => new[] { "Size", "Version", "Items" },
            }).Select(x => ModelOf(x, collection));

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
            !n.GetAttributes().Any(a => a.AttributeClass?.ContainingNamespace?.ToDisplayString() == SpecSymbols.Namespace && a.AttributeClass.Name is not ("OwnedAttribute" or "RunsConcurrentlyAttribute" or "LockLevelAttribute" or "TakesNoLocksAttribute")) &&
            // (virtual members, of methods: an override only of a member of the program's, whose contract it inherits)
            n.GetMembers().All(m => (m is IMethodSymbol mm ? !mm.IsOverride || mm.OverriddenMethod?.DeclaringSyntaxReferences.Length > 0
                                     : m is IPropertySymbol pp ? !pp.IsOverride || pp.OverriddenProperty?.DeclaringSyntaxReferences.Length > 0
                                     : !m.IsVirtual && !m.IsAbstract && !m.IsOverride) &&
                                    !(m is IFieldSymbol && CsVerifyAttributes(m) && !OnlyGuardedBy(m)) &&
                                    // (a property may be [Pure]: a function)
                                    !(m is IPropertySymbol && m.GetAttributes().Any(a => a.AttributeClass?.ContainingNamespace?.ToDisplayString() == SpecSymbols.Namespace && a.AttributeClass.Name is not ("PureAttribute" or "GuardedByAttribute")))) &&
            // (an invariant of an [Owned] class travels with its view; any other's is an immutable object's, assumed of every one)
            (SpecSymbols.IsOwned(n) || !HasInvariantMethods(n) || Immutable(n));

        private static bool HasInvariantMethods(INamedTypeSymbol n) =>
            n.GetMembers().OfType<IMethodSymbol>().Any(m => m.GetAttributes().Any(a => a.AttributeClass?.Name == "InvariantAttribute"));

        /// <summary>A class whose fields never change once it is built (each readonly, or an auto-property without a setter).</summary>
        private static bool Immutable(INamedTypeSymbol n) =>
            n.GetMembers().OfType<IFieldSymbol>().Where(f => !f.IsStatic && !f.IsConst).All(f => f.IsReadOnly);

        /// <summary>
        /// An immutable class with invariants (not [Owned]): proved where each object is built, and assumed of every
        /// object of it after, as its fields never change (as CsVerify's engine has a data type's).
        /// </summary>
        public static bool HasObjectInvariant(ITypeSymbol t) =>
            t is INamedTypeSymbol n && IsClass(n) && !SpecSymbols.IsOwned(n) && HasInvariantMethods(n) && Immutable(n);

        /// <summary>Guarded by a lock, and nothing else of CsVerify's.</summary>
        private static bool OnlyGuardedBy(ISymbol s) =>
            s.GetAttributes().Where(a => a.AttributeClass?.ContainingNamespace?.ToDisplayString() == SpecSymbols.Namespace).All(a => a.AttributeClass.Name is "GuardedByAttribute" or "LockLevelAttribute" or "AtomicAttribute" or "OwnsAttribute");

        private static bool CsVerifyAttributes(ISymbol s) =>
            s.GetAttributes().Any(a => a.AttributeClass?.ContainingNamespace?.ToDisplayString() == SpecSymbols.Namespace);

        /// <summary>A field the kernel has: a heap field (an instance field or auto-property, or a mutable static field) of a class in the subset, of a type in it.</summary>
        public static bool IsField(ISymbol s) =>
            s != null && FieldEffects.IsHeapField(s) && InSubset(FieldType(s)) && !IsLockObject(s) && // (a lock's object: no state of the kernel's)
           
            (s.IsStatic ? s.ContainingType.Arity == 0 && s.ContainingType.ContainingType == null && (!CsVerifyAttributes(s) || OnlyGuardedBy(s)) : IsClass(s.ContainingType));

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

        public static KExpr Default(ITypeSymbol t) => IsGhost(t) ? Default(GhostOf(t)) : new KLit(IsNullable(t) ? "null" : t.SpecialType == SpecialType.System_Boolean ? "false" : "0");

        /// <summary>A non-nullable reference type, in an enabled nullable context (an oblivious one promises nothing).</summary>
        public static bool NotNullable(ITypeSymbol t) => t.IsReferenceType && t.NullableAnnotation == NullableAnnotation.NotAnnotated;

        public static string TypeOf(ITypeSymbol t) =>
            IsGhost(t) ? TypeOf(GhostOf(t)) : IsTypeParameter(t) ? "Box" :
            IsRef(t) || IsView(t) || IsShare(t) || IsString(t) || IsException(t) || IsDelegate(t) || IsPair(t) || IsData(t) || IsToken(t) ? "Ref" : t.SpecialType == SpecialType.System_Boolean ? "bool" : "int";

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
