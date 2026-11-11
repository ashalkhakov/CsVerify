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

        /// <summary>The element types of arrays: each integer type, bool, and references (object's map, of every reference element type).</summary>
        public static SpecialType[] ElementTypes => (RefArrays ? WithReferences : Scalars).Concat(FloatArrays ? Floats : new SpecialType[0]).ToArray();
        private static readonly SpecialType[] Floats = { SpecialType.System_Single, SpecialType.System_Double };

        /// <summary>The program has arrays of floats (their maps declared), for the run this thread is in.</summary>
        [System.ThreadStatic] public static bool FloatArrays;

        /// <summary>float and double: IEEE 754 binary32 and binary64, Boogie's float24e8 and float53e11.</summary>
        public static bool IsFloating(ITypeSymbol t) => t?.SpecialType is SpecialType.System_Single or SpecialType.System_Double;
        public static string FloatType(ITypeSymbol t) => t.SpecialType == SpecialType.System_Single ? "float24e8" : "float53e11";
        public static string FloatSize(ITypeSymbol t) => t.SpecialType == SpecialType.System_Single ? "32" : "64";

        /// <summary>A float's value, exactly: its bits.</summary>
        public static KExpr FloatLiteral(object v, ITypeSymbol t)
        {
            if (t.SpecialType == SpecialType.System_Single)
                return new KOp("$fp.bits32", new KLit(((uint)System.BitConverter.SingleToInt32Bits(System.Convert.ToSingle(v))).ToString() + "bv32"));
            return new KOp("$fp.bits64", new KLit(((ulong)System.BitConverter.DoubleToInt64Bits(System.Convert.ToDouble(v))).ToString() + "bv64"));
        }
        private static readonly SpecialType[] Scalars = Widths.Keys.Append(SpecialType.System_Boolean).ToArray();
        private static readonly SpecialType[] WithReferences = Scalars.Append(SpecialType.System_Object).ToArray();

        /// <summary>The program has arrays of references (its references' map, $E.Object, is declared), for the run this thread is in.</summary>
        [System.ThreadStatic] public static bool RefArrays;

        /// <summary>Does the program name an array of references (a type, or an array it makes)?</summary>
        public static bool NamesFloatArrays(Compilation c) =>
            c.SyntaxTrees.Any(t =>
            {
                var model = c.GetSemanticModel(t);
                return t.GetRoot().DescendantNodes().Any(n =>
                    (n is Microsoft.CodeAnalysis.CSharp.Syntax.ArrayTypeSyntax || n is Microsoft.CodeAnalysis.CSharp.Syntax.ImplicitArrayCreationExpressionSyntax ||
                     n is Microsoft.CodeAnalysis.CSharp.Syntax.CollectionExpressionSyntax) &&
                    (model.GetTypeInfo(n).Type ?? model.GetTypeInfo(n).ConvertedType) is IArrayTypeSymbol a && IsFloating(a.ElementType));
            });

        public static bool NamesRefArrays(Compilation c) =>
            c.SyntaxTrees.Any(t =>
            {
                var model = c.GetSemanticModel(t);
                return t.GetRoot().DescendantNodes().Any(n =>
                    (n is Microsoft.CodeAnalysis.CSharp.Syntax.ArrayTypeSyntax || n is Microsoft.CodeAnalysis.CSharp.Syntax.ImplicitArrayCreationExpressionSyntax ||
                     n is Microsoft.CodeAnalysis.CSharp.Syntax.CollectionExpressionSyntax) &&
                    (model.GetTypeInfo(n).Type ?? model.GetTypeInfo(n).ConvertedType) is IArrayTypeSymbol a && !Scalar(a.ElementType));
            });

        /// <summary>An element map's Boogie type of value.</summary>
        public static string ElementValue(SpecialType t) => t == SpecialType.System_Boolean ? "bool" : t == SpecialType.System_Object ? "Ref" :
            t == SpecialType.System_Single ? "float24e8" : t == SpecialType.System_Double ? "float53e11" : "int";
        public static string ElementValue(string map) => ElementValue(ElementTypes.First(t => ElementMap(t) == map));

        /// <summary>An array's element type: a scalar, or a reference (an object, an interface's, a string, object).</summary>
        public static bool IsElement(ITypeSymbol t) => Scalar(t) || FloatArrays && IsFloating(t) || RefArrays && (IsClass(t) || IsInterface(t) || IsString(t) || t?.SpecialType == SpecialType.System_Object);

        public static bool IsIntegral(ITypeSymbol t) => t != null && Widths.ContainsKey(t.SpecialType);

        public static bool Scalar(ITypeSymbol t) => IsIntegral(t) || t?.SpecialType == SpecialType.System_Boolean;

        /// <summary>
        /// A nullable value of a scalar (int?, bool?): a reference, null where it has no value, $nmk.U(v) where it has v,
        /// one reference per value (so == is the lifted operator's); $nv.U reads the value.
        /// </summary>
        public static bool IsNullableValue(ITypeSymbol t) => t is INamedTypeSymbol { OriginalDefinition.SpecialType: SpecialType.System_Nullable_T } n && Scalar(n.TypeArguments[0]);

        public static ITypeSymbol Underlying(ITypeSymbol nullable) => ((INamedTypeSymbol)nullable).TypeArguments[0];

        public static KExpr NullableValue(KExpr v, ITypeSymbol nullable) => new KOp("$nv." + Underlying(nullable).SpecialType.ToString().Substring("System_".Length), v);

        public static KExpr NullableOf(KExpr v, ITypeSymbol nullable) => new KOp("$nmk." + Underlying(nullable).SpecialType.ToString().Substring("System_".Length), v);

        public static bool IsArray(ITypeSymbol t) => t is IArrayTypeSymbol a && a.IsSZArray && IsElement(a.ElementType);

        /// <summary>An array of references (Shape[], string?[]): its elements in $E.Object, null where it's made.</summary>
        public static bool IsRefArray(ITypeSymbol t) => IsArray(t) && !Scalar(((IArrayTypeSymbol)t).ElementType) && !IsFloating(((IArrayTypeSymbol)t).ElementType);

        public static bool InSubset(ITypeSymbol t) => Scalar(t) || IsArray(t) || IsClass(t) || IsInterface(t) || IsCollectionInterface(t) || t?.SpecialType == SpecialType.System_Object || IsView(t) || IsShare(t) || IsString(t) || IsException(t) || IsDelegate(t) || IsCollection(t) || IsPair(t) ||
                                                    IsData(t) || IsGenericParameter(t) || IsGhost(t) && InSubset(GhostOf(t)) || IsToken(t) || IsObjSet(t) || IsMemValue(t) || IsSeqValue(t) || IsGivenTask(t) || IsTuple(t) || IsFloating(t) || IsLinqGroup(t) || IsLibraryObject(t) || IsNullableValue(t);

        /// <summary>A GroupBy's group (IGrouping): the index in its source of its key's first element.</summary>
        public static bool IsLinqGroup(ITypeSymbol t) => t is INamedTypeSymbol { Name: "IGrouping", Arity: 2 } g && g.ContainingNamespace?.ToDisplayString() == "System.Linq";

        /// <summary>A tuple of the subset's values: a value whose elements are functions of it ($tup.i.Kind).</summary>
        public static bool IsTuple(ITypeSymbol t) => t is INamedTypeSymbol n && (n.IsTupleType || n.IsAnonymousType) && PartsOf(t).All(e => InSubset(e) && !IsTuple(e));

        /// <summary>A tuple's elements' types, or an anonymous object's members', in order (an anonymous object is a tuple of its members).</summary>
        public static List<ITypeSymbol> PartsOf(ITypeSymbol t) =>
            ((INamedTypeSymbol)t).IsTupleType ? ((INamedTypeSymbol)t).TupleElements.Select(e => e.Type).ToList()
            : t.GetMembers().OfType<IPropertySymbol>().Select(p => p.Type).ToList();

        /// <summary>An anonymous object's member's position.</summary>
        public static int PartIndex(ITypeSymbol t, string name) => t.GetMembers().OfType<IPropertySymbol>().Select(p => p.Name).ToList().IndexOf(name);

        /// <summary>The function making a tuple of this type from its elements ($tupmk.int_int): its elements are its arguments.</summary>
        public static string TupleMaker(ITypeSymbol tuple) =>
            "$tupmk." + string.Join("_", PartsOf(tuple).Select(e => TypeOf(e).Replace("[", "-").Replace("]", "-")));

        /// <summary>A tuple's element i.</summary>
        public static KExpr TupleItem(KExpr v, ITypeSymbol tuple, int i) => new KOp($"$tup.{i}.{TypeOf(PartsOf(tuple)[i]).Replace("[", "_").Replace("]", "_")}", v);

        /// <summary>A task one is given (Task, Task&lt;T&gt; of the subset's values): a reference to work running elsewhere.</summary>
        public static bool IsGivenTask(ITypeSymbol t) =>
            t is INamedTypeSymbol n && n.ContainingNamespace?.ToDisplayString() == "System.Threading.Tasks" && n.Name == "Task" &&
            (n.Arity == 0 || n.Arity == 1 && (Scalar(n.TypeArguments[0]) || IsRef(n.TypeArguments[0]) || IsString(n.TypeArguments[0]) || IsGenericParameter(n.TypeArguments[0])));

        /// <summary>
        /// ATS's manual memory: a pointer (Ptr&lt;T&gt;), a view (PointsTo, ArrayView, ArrayHole) or a token (FreeGc) of
        /// scalars: a value, its ghost properties functions of it ($mem.Addr, $mem.Elems.Int32, ...).
        /// </summary>
        public static bool IsMemValue(ITypeSymbol t) =>
            (IsMemView(t) || SpecSymbols.IsCsVerifyType(t, "Ptr`1") || SpecSymbols.IsCsVerifyType(t, "FreeGc`1")) && Scalar(((INamedTypeSymbol)t).TypeArguments[0]);

        /// <summary>A view of memory cells, which holds them while in hand.</summary>
        public static bool IsMemView(ITypeSymbol t) =>
            (SpecSymbols.IsCsVerifyType(t, "PointsTo`1") || SpecSymbols.IsCsVerifyType(t, "ArrayView`1") || SpecSymbols.IsCsVerifyType(t, "ArrayHole`1")) &&
            Scalar(((INamedTypeSymbol)t).TypeArguments[0]);

        /// <summary>A ghost sequence of scalars (Seq&lt;int&gt;): a Boogie map from index to value.</summary>
        public static bool IsSeqValue(ITypeSymbol t) => SpecSymbols.IsCsVerifyType(t, "Seq`1") && Scalar(((INamedTypeSymbol)t).TypeArguments[0]);

        /// <summary>A memory value's ghost property (Addr, Length, Index; Value and Elems of its kind of element).</summary>
        public static KExpr MemProp(string name, KExpr v, ITypeSymbol type) =>
            new KOp(name is "Value" or "Elems" ? $"$mem.{name}.{Kind(((INamedTypeSymbol)type).TypeArguments[0])}" : "$mem." + name, v);

        /// <summary>The memory's map of a view's kind of element: the row at null of that element map.</summary>
        public static string MemMap(ITypeSymbol type) => ElementMap(((INamedTypeSymbol)type).TypeArguments[0].SpecialType);

        /// <summary>The cells a view holds: [Addr, Addr + Length) (one for PointsTo), a hole's all but its index.</summary>
        public static List<KCells> MemCells(KExpr v, ITypeSymbol type, SyntaxNode at)
        {
            var addr = MemProp("Addr", v, type);
            KCells Of(KExpr lo, KExpr hi) => new KCells { Arr = new KLit("null"), Lo = lo, Hi = hi, At = at };
            if (SpecSymbols.IsCsVerifyType(type, "PointsTo`1")) return new List<KCells> { Of(addr, new KOp("+", addr, new KLit("1"))) };
            var end = new KOp("+", addr, MemProp("Length", v, type));
            if (SpecSymbols.IsCsVerifyType(type, "ArrayView`1")) return new List<KCells> { Of(addr, end) };
            var hole = new KOp("+", addr, MemProp("Index", v, type));
            return new List<KCells> { Of(addr, hole), Of(new KOp("+", hole, new KLit("1")), end) };
        }

        /// <summary>What a view says is what its cells hold (true while it's in hand: nobody else writes them).</summary>
        public static KExpr MemTie(KExpr v, ITypeSymbol type)
        {
            var map = new KVar(MemMap(type));
            var addr = MemProp("Addr", v, type);
            if (SpecSymbols.IsCsVerifyType(type, "PointsTo`1"))
                return new KOp("==", new KOp("sel", map, new KLit("null"), addr), MemProp("Value", v, type));
            var i = new KVar("m$i");
            KExpr range = new KOp("&&", new KOp("<=", new KLit("0"), i), new KOp("<", i, MemProp("Length", v, type)));
            KExpr body = new KOp("==", new KOp("sel", map, new KLit("null"), new KOp("+", addr, i)), new KOp("sel", MemProp("Elems", v, type), i));
            // (a hole's: all but its index)
            if (SpecSymbols.IsCsVerifyType(type, "ArrayHole`1")) body = new KOp("==>", new KOp("!=", i, MemProp("Index", v, type)), body);
            return new KQuant { Forall = true, Var = "m$i", Range = range, Body = body };
        }

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

        /// <summary>
        /// A type parameter constrained to references (where T : class, or to interfaces and classes of the subset's): its
        /// values are references, as its instantiations must be.
        /// </summary>
        public static bool IsRefParameter(ITypeSymbol t) =>
            t is ITypeParameterSymbol tp && !tp.HasValueTypeConstraint && !tp.HasUnmanagedTypeConstraint && !tp.HasConstructorConstraint &&
            (tp.HasReferenceTypeConstraint || tp.ConstraintTypes.Length > 0) && tp.ConstraintTypes.All(c => IsInterface(c) || IsClass(c));

        /// <summary>A type parameter the subset has: unconstrained (boxes), or constrained to references.</summary>
        public static bool IsGenericParameter(ITypeSymbol t) => IsTypeParameter(t) || IsRefParameter(t);

        /// <summary>A type argument for a type parameter: any that boxes for an unconstrained one, a reference for a constrained one.</summary>
        public static bool Instantiates(ITypeParameterSymbol p, ITypeSymbol a) =>
            IsTypeParameter(p) ? IsGenericParameter(a) || Scalar(a) || IsString(a) || IsData(a) || IsRef(a) : IsRefParameter(p) && (IsRefParameter(a) || IsRef(a) && !(a is ITypeParameterSymbol));

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
            IsTypeParameter(def) && !IsTypeParameter(actual) && actual != null ? new KOp("$box." + BoxKind(actual), v) : v;
        public static KExpr Unbox(KExpr v, ITypeSymbol def, ITypeSymbol actual) =>
            IsTypeParameter(def) && !IsTypeParameter(actual) && actual != null ? new KOp("$unbox." + BoxKind(actual), v) : v;
        public static string BoxKind(ITypeSymbol t) => t.SpecialType == SpecialType.System_Boolean ? "bool" : Scalar(t) ? "int" : "Ref";

        /// <summary>A delegate of the subset's values: a Func or an Action, or a non-generic delegate type of the program's.</summary>
        public static bool IsDelegate(ITypeSymbol t) =>
            IsFunc(t) || t is INamedTypeSymbol { TypeKind: TypeKind.Delegate, Arity: 0 } d && d.DeclaringSyntaxReferences.Length > 0 &&
            d.DelegateInvokeMethod is IMethodSymbol inv && inv.Parameters.All(p => p.RefKind == RefKind.None && FuncValue(p.Type)) && (inv.ReturnsVoid || FuncValue(inv.ReturnType));

        /// <summary>
        /// A class's type arguments: none, or a generic class's (Box&lt;T&gt;) whose type parameters are unconstrained (its
        /// values of T are boxes, as generic data's are), given values that box: scalars, references, its own parameters.
        /// </summary>
        private static bool GenericClassArguments(INamedTypeSymbol n) =>
            n.Arity == 0 || n.OriginalDefinition.TypeParameters.All(IsGenericParameter) &&
            n.OriginalDefinition.TypeParameters.Zip(n.TypeArguments).All(x => !(x.Second is INamedTypeSymbol an && SymbolEqualityComparer.Default.Equals(an.OriginalDefinition, n.OriginalDefinition)) && Instantiates(x.First, x.Second));

        /// <summary>A Func or an Action of the subset's values: a reference, which Spec.Pre and Spec.Post speak of.</summary>
        public static bool IsFunc(ITypeSymbol t) =>
            t is INamedTypeSymbol { TypeKind: TypeKind.Delegate } d && d.ContainingNamespace?.ToDisplayString() == "System" && d.Name is "Func" or "Action" &&
            d.DelegateInvokeMethod is IMethodSymbol inv && inv.Parameters.All(p => p.RefKind == RefKind.None && FuncValue(p.Type)) && (inv.ReturnsVoid || FuncValue(inv.ReturnType));

        private static bool FuncValue(ITypeSymbol t) => Scalar(t) || IsArray(t) || IsClass(t) || IsString(t) || IsToken(t) || IsGivenTask(t);

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
        public static bool IsNullable(ITypeSymbol t) => IsRef(t) || IsString(t) || IsException(t) || IsDelegate(t) || IsData(t) || IsNullableValue(t);

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

        /// <summary>A method whose call is a task: an async one, or an abstract one (an interface's) that returns a task.</summary>
        public static bool IsTaskMethod(IMethodSymbol m) => (m.IsAsync || m.IsAbstract && m.DeclaringSyntaxReferences.Length > 0) && IsTaskLike(m.ReturnType);

        /// <summary>What a method gives back: an async one's task's result (null for none); else its return type (null for void).</summary>
        public static ITypeSymbol Returns(IMethodSymbol m) =>
            IsTaskMethod(m) ? ((INamedTypeSymbol)m.ReturnType).TypeArguments.FirstOrDefault() : m.ReturnsVoid ? null : m.ReturnType;

        /// <summary>A lock's object (readonly, of type object): no state of the kernel's.</summary>
        public static bool IsLockObject(ISymbol s) => s is IFieldSymbol { IsReadOnly: true } f && (f.Type.SpecialType == SpecialType.System_Object || IsSemaphore(f.Type));

        public static bool IsSemaphore(ITypeSymbol t) => t?.ToDisplayString() == "System.Threading.SemaphoreSlim";

        /// <summary>What runs concurrently (CsVerify's engine's: marked, or started alongside), for the run this thread is in.</summary>
        [System.ThreadStatic] public static StartedDelegates Started;

        /// <summary>The locks' levels and what code takes (CsVerify's engine's static analysis), for the run this thread is in.</summary>
        [System.ThreadStatic] public static LockLevels Levels;

        /// <summary>CsVerify's engine's judgments of a library call without a stub: may it write arrays (MayWriteHeap), fields (WritesFieldsAt)?</summary>
        [System.ThreadStatic] public static System.Func<IMethodSymbol, bool> MayWriteHeap;
        [System.ThreadStatic] public static System.Func<Microsoft.CodeAnalysis.Operations.IInvocationOperation, bool> WritesFieldsAt;
        /// <summary>May a library member run the program's code (what it is handed, its receiver)? A stub's call changes what it says, and, where it may, anything.</summary>
        [System.ThreadStatic] public static System.Func<IMethodSymbol, bool> RunsUserCode;
        /// <summary>CsVerify's engine's effects of a library member with a stub: the fields it writes, reads, and whether it may use arrays.</summary>
        [System.ThreadStatic] public static System.Func<IMethodSymbol, IEnumerable<ISymbol>> FieldWrites, FieldReads;
        [System.ThreadStatic] public static System.Func<IMethodSymbol, bool> MayTouchArrays;

        /// <summary>An object of a library class the program has no model of (Random, TextWriter): a reference, whose members are library calls.</summary>
        public static bool IsLibraryObject(ITypeSymbol t) =>
            t is INamedTypeSymbol { TypeKind: TypeKind.Class } n && n.DeclaringSyntaxReferences.Length == 0 && n.SpecialType == SpecialType.None &&
            n.ContainingNamespace?.ToDisplayString() is string ns && ns != SpecSymbols.Namespace && !ns.StartsWith("CsVerify") &&
            !IsCollection(t) && !IsException(t) && !IsDelegate(t) && !IsString(t) && !IsGivenTask(t) && !IsTaskLike(t) && !IsSemaphore(t) && CollectionKind(t) == null &&
            !(n.IsGenericType && n.ContainingNamespace?.ToDisplayString() == "System.Collections.Generic");

        /// <summary>The program has ownership trees ([Owns] fields): each object's tree root is the ghost map $root.</summary>
        [System.ThreadStatic] public static bool Trees;

        /// <summary>The locks of the program (CsVerify's engine's: what guards what, the locks' invariants), for the run this thread is in.</summary>
        [System.ThreadStatic] public static LockGuards Locks;

        public static bool IsRef(ITypeSymbol t) => IsArray(t) || IsClass(t) || IsInterface(t) || IsRefParameter(t) || IsCollection(t) || IsCollectionInterface(t) || IsLibraryObject(t) || t?.SpecialType == SpecialType.System_Object;

        /// <summary>A collection's interface (IList, IReadOnlyList, ICollection, IReadOnlyCollection) of the subset's values.</summary>
        public static bool IsCollectionInterface(ITypeSymbol t) =>
            t is INamedTypeSymbol { TypeKind: TypeKind.Interface, Arity: 1 } n && n.ContainingNamespace?.ToDisplayString() == "System.Collections.Generic" &&
            n.Name is "IList" or "IReadOnlyList" or "ICollection" or "IReadOnlyCollection" && FuncValue(n.TypeArguments[0]);

        /// <summary>The program's own classes or structs that implement a collection interface: then a read through it is unknown at each read.</summary>
        public static bool ImplementedHere(INamedTypeSymbol ifc)
        {
            if (Compilation == null) return true;
            if (!_implemented.TryGetValue(Compilation, out var set))
            {
                set = new HashSet<string>();
                void Walk(INamespaceOrTypeSymbol ns)
                {
                    foreach (var m in ns.GetMembers())
                        if (m is INamespaceSymbol sub) Walk(sub);
                        else if (m is INamedTypeSymbol nt && nt.DeclaringSyntaxReferences.Length > 0)
                        {
                            foreach (var i in nt.AllInterfaces) set.Add(i.OriginalDefinition.ToDisplayString());
                            Walk(nt);
                        }
                }
                Walk(Compilation.Assembly.GlobalNamespace);
                _implemented.Add(Compilation, set);
            }
            return set.Contains(ifc.OriginalDefinition.ToDisplayString());
        }
        private static readonly System.Runtime.CompilerServices.ConditionalWeakTable<Compilation, HashSet<string>> _implemented = new System.Runtime.CompilerServices.ConditionalWeakTable<Compilation, HashSet<string>>();

        /// <summary>A collection interface's Count or element, as an expression: an array's, a modeled collection's (Size, Items), or the state's.</summary>
        public static KExpr IfcRead(KExpr x, KExpr index, ITypeSymbol element)
        {
            var list = (INamedTypeSymbol)Compilation.GetTypeByMetadataName("System.Collections.Generic.List`1").Construct(element);
            var kind = Kind(element);
            if (index == null)
                return new KOp("ite", new KOp("$arr", x), new KOp("len", x), new KOp("ite", new KOp("$coll", x), new KOp("sel", new KVar(SizeMap), x), new KOp("$ocount", x, new KOp("$state"))));
            var array = (IArrayTypeSymbol)Compilation.CreateArrayTypeSymbol(element);
            return new KOp("ite", new KOp("$arr", x), new KOp("sel", new KVar(Elements(array)), x, index),
                new KOp("ite", new KOp("$coll", x), new KOp("sel", new KVar(ModelOf("Items", list).Name), x, index), new KOp("$oitem." + kind, x, index, new KOp("$state"))));
        }

        /// <summary>The BCL collections whose contents CsVerify.Bcl's models are (their stub contracts speak of them).</summary>
        private static readonly string[] Collections =
        {
            "System.Collections.Generic.List<T>", "System.Collections.Generic.Dictionary<TKey, TValue>",
            "System.Collections.Generic.HashSet<T>", "System.Collections.Generic.Stack<T>", "System.Collections.Generic.Queue<T>",
        };

        /// <summary>The collection's kind: List, Dictionary, HashSet, Stack, Queue (null: not one).</summary>
        public static string CollectionKind(ITypeSymbol t) =>
            t is INamedTypeSymbol n && n.IsGenericType && Collections.Contains(n.OriginalDefinition.ToDisplayString()) ? n.Name :
            // (a builder, its length its model; a writer, of no model: their members' stubs as a list's are)
            t is INamedTypeSymbol { IsGenericType: false } b && b.ToDisplayString() is "System.Text.StringBuilder" or "System.IO.TextWriter" ? b.Name : null;

        /// <summary>
        /// A collection of the subset's values: an object, its contents its models. The keys of a dictionary and the
        /// members of a set are compared as the verifier compares them: as values, by reference, strings by content.
        /// </summary>
        public static bool IsCollection(ITypeSymbol t) =>
            CollectionKind(t) is string kind && ((INamedTypeSymbol)t).TypeArguments.Select((a, i) => FuncValue(a) ||
                // (a dictionary's values may be data, which it never compares)
                kind == "Dictionary" && i == 1 && IsData(a)).All(x => x);

        /// <summary>A collection's key (a dictionary's key, a set's member) as its models index it: a string marked as a key ($keyed), so that two of one content are one.</summary>
        public static KExpr Keyed(KExpr k, ITypeSymbol t) => IsString(t) ? new KOp("$keyed", k) : k;

        public static bool IsList(ITypeSymbol t) => CollectionKind(t) == "List" && IsCollection(t);

        /// <summary>A dictionary's pair (a foreach's): a value whose Key and Value are functions of it.</summary>
        public static bool IsPair(ITypeSymbol t) =>
            t is INamedTypeSymbol { Arity: 2 } n && n.OriginalDefinition.ToDisplayString() == "System.Collections.Generic.KeyValuePair<TKey, TValue>" &&
            n.TypeArguments.All(FuncValue);

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
                "StringBuilder" => new[] { "Size" },
                "TextWriter" => new string[0],
                _ => new[] { "Size", "Version", "Items" },
            }).Select(x => ModelOf(x, collection));

        /// <summary>An interface of the program's, not generic, of abstract members only (their contracts from a contract class).</summary>
        public static bool IsInterface(ITypeSymbol t) =>
            t is INamedTypeSymbol n && n.TypeKind == TypeKind.Interface && n.Arity == 0 && n.DeclaringSyntaxReferences.Length > 0 &&
            n.ContainingNamespace?.ToDisplayString() != SpecSymbols.Namespace &&
            // (its implementations may run concurrently: [RunsConcurrently], as a class may be)
            !n.GetAttributes().Any(a => a.AttributeClass?.ContainingNamespace?.ToDisplayString() == SpecSymbols.Namespace && a.AttributeClass.Name != "RunsConcurrentlyAttribute") &&
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
            t is INamedTypeSymbol n && n.TypeKind == TypeKind.Class && !n.IsStatic && !n.IsRecord && GenericClassArguments(n) &&
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
            s != null && FieldEffects.IsHeapField(s) && InSubset(FieldType(s)) && !IsLockObject(s) && !IsGivenTask(FieldType(s)) && !IsLibraryObject(FieldType(s)) && // (a lock's object: no state of the kernel's)
           
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

        public static KExpr Default(ITypeSymbol t) => IsGhost(t) ? Default(GhostOf(t)) : IsObjSet(t) ? new KLit("(lambda r$: Ref :: false)") : IsFloating(t) ? FloatLiteral(0.0, t) : new KLit(IsNullable(t) ? "null" : t.SpecialType == SpecialType.System_Boolean ? "false" : "0");

        /// <summary>A non-nullable reference type, in an enabled nullable context (an oblivious one promises nothing).</summary>
        /// (Not a type parameter's: where T : class may be instantiated with K?, as CsVerify's engine has it.)
        public static bool NotNullable(ITypeSymbol t) => t.IsReferenceType && t.NullableAnnotation == NullableAnnotation.NotAnnotated && !(t is ITypeParameterSymbol);

        public static string TypeOf(ITypeSymbol t) =>
            IsGhost(t) ? TypeOf(GhostOf(t)) : IsTypeParameter(t) ? "Box" : IsObjSet(t) ? "[Ref]bool" : IsMemValue(t) ? "Ref" : IsFloating(t) ? FloatType(t) : IsLinqGroup(t) ? "int" :
            IsSeqValue(t) ? "[int]" + (((INamedTypeSymbol)t).TypeArguments[0].SpecialType == SpecialType.System_Boolean ? "bool" : "int") :
            IsRef(t) || IsView(t) || IsShare(t) || IsString(t) || IsException(t) || IsDelegate(t) || IsPair(t) || IsData(t) || IsToken(t) || IsGivenTask(t) || IsTuple(t) || IsNullableValue(t) ? "Ref" : t.SpecialType == SpecialType.System_Boolean ? "bool" : "int";

        public static string ElementMap(SpecialType t) => "$E." + t.ToString().Substring("System_".Length);

        /// <summary>The map of an array type's elements.</summary>
        public static string Elements(ITypeSymbol array) => ElementMap(IsRefArray(array) ? SpecialType.System_Object : ((IArrayTypeSymbol)array).ElementType.SpecialType);

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
