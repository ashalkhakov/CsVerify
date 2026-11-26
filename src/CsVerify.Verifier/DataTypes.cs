using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Positional records as algebraic data types. A data record is a record class whose whole state is
    /// its positional properties (and, of an abstract base, the properties its constructor stores its parameters in):
    /// a value is its constructor applied to its arguments. A hierarchy is closed (its cases are
    /// known) when the abstract root cannot be derived from outside this compilation: every constructor is private,
    /// or the type is not visible outside the assembly. Each case gets a tag, so type tests and <c>switch</c> are
    /// case analysis. A generic record is one data type for all its instantiations: tags, constructors and fields
    /// are those of its definition (<c>List&lt;T&gt;.Cons</c>), so a <c>List&lt;int&gt;</c> built by a caller and the
    /// <c>List&lt;T&gt;</c> a generic function takes apart are the same values. Every method here takes either form.
    /// </summary>
    internal sealed class DataTypes
    {
        private readonly Dictionary<INamedTypeSymbol, int> _tags = new Dictionary<INamedTypeSymbol, int>(SymbolEqualityComparer.Default);

        private readonly HashSet<ITypeSymbol> _stringInterfaces = new HashSet<ITypeSymbol>(SymbolEqualityComparer.Default);

        public DataTypes(Compilation compilation, IEnumerable<SyntaxTree> userTrees)
        {
            foreach (var i in compilation.GetSpecialType(SpecialType.System_String).AllInterfaces)
            {
                _stringInterfaces.Add(i.OriginalDefinition);
            }
            var candidates = new List<INamedTypeSymbol>();
            foreach (var tree in userTrees)
            {
                var model = compilation.ModelOf(tree);
                foreach (var decl in tree.GetRoot().DescendantNodes().OfType<RecordDeclarationSyntax>())
                {
                    if (model.GetDeclaredSymbol(decl) is INamedTypeSymbol t && (t.TypeKind == TypeKind.Class || SpecSymbols.IsLinearPackage(t)))
                    {
                        candidates.Add(t);
                    }
                }
            }
            // a record is data if its own state is positional and its base (if any) is data too
            bool changed = true;
            var data = new HashSet<INamedTypeSymbol>(SymbolEqualityComparer.Default);
            while (changed)
            {
                changed = false;
                foreach (var t in candidates)
                {
                    if (!data.Contains(t) && HasDataShape(t) && (t.BaseType?.SpecialType == SpecialType.System_Object ||
                        t.BaseType?.SpecialType == SpecialType.System_ValueType || data.Contains(Def(t.BaseType))))
                    {
                        changed = data.Add(t) || changed;
                    }
                }
            }
            int tag = 1;
            foreach (var t in candidates.Where(data.Contains))
            {
                _tags[t] = tag++;
            }
        }

        private static bool HasDataShape(INamedTypeSymbol t)
        {
            if (!(t.IsSealed || t.IsAbstract))
            {
                return false;
            }
            foreach (var m in t.GetMembers())
            {
                if (m.IsStatic || m.IsImplicitlyDeclared && !(m is IFieldSymbol))
                {
                    continue;
                }
                switch (m)
                {
                    // every field is the backing field of a positional property, of a case's init property, or of a
                    // property an abstract base's constructor stores a parameter in
                    case IFieldSymbol fd when !(fd.AssociatedSymbol is IPropertySymbol p && (IsPositional(p) || t.IsSealed && IsInitField(p) || IsStored(p))): return false;
                    // an explicit constructor may only be an abstract record's: an empty, parameterless one, or one that
                    // only stores its parameters
                    case IMethodSymbol c when c.MethodKind == MethodKind.Constructor && !IsPrimary(c):
                        if (Stored(t) != null)
                        {
                            break;
                        }
                        if (!t.IsAbstract || c.Parameters.Length > 0 ||
                            c.DeclaringSyntaxReferences.Any(r => r.GetSyntax() is ConstructorDeclarationSyntax cd &&
                                ((cd.Body?.Statements.Count ?? 0) > 0 || cd.ExpressionBody != null || cd.Initializer != null)))
                        {
                            return false;
                        }
                        break;
                }
            }
            return true;
        }

        public static bool IsPositional(IPropertySymbol p) =>
            p.DeclaringSyntaxReferences.Length > 0 && p.DeclaringSyntaxReferences.All(r => r.GetSyntax() is ParameterSyntax);

        /// <summary>
        /// A case's init property besides its positional ones (public IReadOnlyList&lt;T&gt; Undone { get; init; } = ...):
        /// a field of its value, its initializer's unless an object initializer or a with expression sets it.
        /// </summary>
        public static bool IsInitField(IPropertySymbol p) =>
            !p.IsStatic && !IsPositional(p) && p.GetMethod != null && p.SetMethod is { IsInitOnly: true } && p.DeclaringSyntaxReferences.Length > 0 &&
            p.DeclaringSyntaxReferences.All(r => r.GetSyntax() is PropertyDeclarationSyntax { AccessorList: { } al } && al.Accessors.All(a => a.Body == null && a.ExpressionBody == null));

        /// <summary>A data value's field: a positional property, a case's init property, or one an abstract base's constructor stores a parameter in.</summary>
        public static bool IsDataField(IPropertySymbol p) => IsPositional(p) || IsInitField(p) && p.ContainingType.IsSealed || IsStored(p);

        private static readonly System.Runtime.CompilerServices.ConditionalWeakTable<INamedTypeSymbol, StoredOf> _stored =
            new System.Runtime.CompilerServices.ConditionalWeakTable<INamedTypeSymbol, StoredOf>();

        private sealed class StoredOf
        {
            public Dictionary<IPropertySymbol, IParameterSymbol> Parameters;
        }

        /// <summary>
        /// An abstract record's constructor that only stores its parameters, each in a get-only property
        /// (private protected Command(DateTime now) => Now = now;): the parameter each property holds, as a primary
        /// constructor's positional properties hold theirs; null where the record has no such constructor.
        /// </summary>
        public static IReadOnlyDictionary<IPropertySymbol, IParameterSymbol> Stored(INamedTypeSymbol t) =>
            Def(t) is INamedTypeSymbol d ? _stored.GetValue(d, x => new StoredOf { Parameters = SpecSymbols.StoredParameters(x) }).Parameters : null;

        /// <summary>A property an abstract record's constructor stores a parameter in (Stored).</summary>
        public static bool IsStored(IPropertySymbol p) => Stored(p.ContainingType)?.ContainsKey(p.OriginalDefinition) == true;

        /// <summary>
        /// The constructor a record's values are built by: its primary one (the implicit parameterless one, of a record
        /// without a parameter list), or the one that stores its parameters.
        /// </summary>
        public static IMethodSymbol Constructor(INamedTypeSymbol t) =>
            Stored(t) != null ? Def(t).InstanceConstructors.First(c => !c.IsImplicitlyDeclared) : PrimaryConstructor(t);

        /// <summary>
        /// The parameter of the record's constructor that a field holds as it is given: its own positional or stored
        /// property's, or a base's field's where the record's header hands the base that parameter and nothing more;
        /// null where the field's value is computed.
        /// </summary>
        public static IParameterSymbol Held(INamedTypeSymbol c, IPropertySymbol field)
        {
            c = Def(c);
            field = field.OriginalDefinition;
            if (!(Constructor(c) is IMethodSymbol ctor))
            {
                return null;
            }
            if (SymbolEqualityComparer.Default.Equals(field.ContainingType, c))
            {
                return Stored(c) is { } stored && stored.TryGetValue(field, out var from) ? from
                    : IsPositional(field) ? ctor.Parameters.FirstOrDefault(p => p.Name == field.Name) : null;
            }
            return Def(c.BaseType) is INamedTypeSymbol b && Held(b, field) is IParameterSymbol handed && BaseArgument(c, handed) is IdentifierNameSyntax id
                ? ctor.Parameters.FirstOrDefault(p => p.Name == id.Identifier.ValueText)
                : null;
        }

        /// <summary>The argument a record's header gives a parameter of its base's constructor (Ind(Fact Prev) : Fact(Prev.N + 1)); null if none.</summary>
        public static ExpressionSyntax BaseArgument(INamedTypeSymbol c, IParameterSymbol parameter)
        {
            var call = Def(c).DeclaringSyntaxReferences.Select(r => r.GetSyntax()).OfType<RecordDeclarationSyntax>()
                .Select(d => d.BaseList?.Types.OfType<PrimaryConstructorBaseTypeSyntax>().FirstOrDefault()).FirstOrDefault(x => x != null);
            if (call == null)
            {
                return null;
            }
            var args = call.ArgumentList.Arguments;
            if (args.FirstOrDefault(a => a.NameColon?.Name.Identifier.ValueText == parameter.Name) is ArgumentSyntax named)
            {
                return named.Expression;
            }
            return parameter.Ordinal < args.Count && args[parameter.Ordinal].NameColon == null ? args[parameter.Ordinal].Expression : null;
        }

        /// <summary>
        /// The property a constructor's parameter is read back from: the one of its name where that holds it (Held), else
        /// any field that holds it; null where the parameter is kept nowhere as it is given (D(int N) : A(N + 1)).
        /// </summary>
        public IPropertySymbol Holder(INamedTypeSymbol c, IParameterSymbol parameter)
        {
            if (PositionalProperty(c, parameter.Ordinal) is IPropertySymbol named && SymbolEqualityComparer.Default.Equals(Held(c, named), parameter))
            {
                return named;
            }
            return Fields(c).FirstOrDefault(f => !IsInitField(f) && SymbolEqualityComparer.Default.Equals(Held(c, f), parameter));
        }

        /// <summary>A case's init properties, as declared.</summary>
        public static IEnumerable<IPropertySymbol> InitFields(INamedTypeSymbol t) =>
            Def(t).GetMembers().OfType<IPropertySymbol>().Where(IsInitField).OrderBy(p => p.DeclaringSyntaxReferences[0].Span.Start);

        /// <summary>An init property's initializer, if it has one.</summary>
        public static ExpressionSyntax InitializerOf(IPropertySymbol p) =>
            p.DeclaringSyntaxReferences.Select(r => r.GetSyntax()).OfType<PropertyDeclarationSyntax>().FirstOrDefault()?.Initializer?.Value;

        private static bool IsPrimary(IMethodSymbol ctor) =>
            ctor.DeclaringSyntaxReferences.Any(r => r.GetSyntax() is RecordDeclarationSyntax);

        /// <summary>The generic definition of a (possibly constructed, possibly nested in a constructed) type.</summary>
        public static INamedTypeSymbol Def(ITypeSymbol t) => (t as INamedTypeSymbol)?.OriginalDefinition;

        public bool IsData(ITypeSymbol t) => Def(t) is INamedTypeSymbol n && _tags.ContainsKey(n);

        public int TagOf(INamedTypeSymbol t) => _tags[Def(t)];

        /// <summary>Could a value of this static type be a data value (so its reference identity is not modeled)?</summary>
        /// <summary>
        /// Could a value of this static type be a data value (so its reference identity is not modeled)? Strings are
        /// values too, so an interface a string implements (IComparable, IEnumerable&lt;char&gt;) may hold one.
        /// </summary>
        public bool MayHoldData(ITypeSymbol t) =>
            t != null && (IsData(t) || t.SpecialType == SpecialType.System_Object || t.TypeKind == TypeKind.TypeParameter ||
                          t.TypeKind == TypeKind.Interface && (_tags.Keys.Any(r => r.AllInterfaces.Contains(t, SymbolEqualityComparer.Default)) ||
                                                               _stringInterfaces.Contains(t.OriginalDefinition)));

        /// <summary>
        /// The primary constructor of the definition (its parameters are what the record header's base arguments refer to); for a
        /// record without a parameter list (<c>sealed record Started : Event;</c>), its implicit parameterless one.
        /// </summary>
        public static IMethodSymbol PrimaryConstructor(INamedTypeSymbol t) =>
            Def(t).InstanceConstructors.FirstOrDefault(IsPrimary) ??
            Def(t).InstanceConstructors.FirstOrDefault(c => c.IsImplicitlyDeclared && c.Parameters.Length == 0);

        /// <summary>
        /// A value's fields: the positional properties (of the definition) and those a base's constructor stores, its
        /// bases' first, then a case's init properties.
        /// </summary>
        public IReadOnlyList<IPropertySymbol> Fields(INamedTypeSymbol t)
        {
            t = Def(t);
            var result = IsData(t.BaseType) ? Fields(Def(t.BaseType)).ToList() : new List<IPropertySymbol>();
            result.AddRange(t.GetMembers().OfType<IPropertySymbol>().Where(p => !p.IsStatic && (IsPositional(p) || IsStored(p))));
            if (t.IsSealed)
            {
                result.AddRange(InitFields(t));
            }
            return result;
        }

        /// <summary>The property a primary-constructor parameter initializes (its own, or a base's of the same name).</summary>
        public static IPropertySymbol PositionalProperty(INamedTypeSymbol t, int ordinal)
        {
            t = Def(t);
            // (a record with no primary constructor has no positional property)
            if (!(PrimaryConstructor(t) is { } primary) || ordinal >= primary.Parameters.Length)
            {
                return null;
            }
            var name = primary.Parameters[ordinal].Name;
            for (var s = t; s != null; s = Def(s.BaseType))
            {
                if (s.GetMembers(name).OfType<IPropertySymbol>().FirstOrDefault() is IPropertySymbol p)
                {
                    return p.OriginalDefinition;
                }
            }
            return null;
        }

        /// <summary>A closed type's cases: the non-abstract data records derived from it (itself, if not abstract).</summary>
        public IReadOnlyList<INamedTypeSymbol> Cases(INamedTypeSymbol t)
        {
            if (!IsData(t))
            {
                return null;
            }
            t = Def(t);
            if (!t.IsAbstract)
            {
                return new[] { t };
            }
            if (!IsClosed(t))
            {
                return null;
            }
            return _tags.Keys.Where(c => !c.IsAbstract && Derives(c, t)).ToList();
        }

        /// <summary>A type's cases as far as the program has them: a closed type's all, an open one's (an abstract root others may derive from) those here.</summary>
        public IReadOnlyList<INamedTypeSymbol> KnownCases(INamedTypeSymbol t) =>
            Cases(t) ?? (IsData(t) ? _tags.Keys.Where(c => !c.IsAbstract && Derives(c, Def(t))).ToList() : null);

        /// <summary>An abstract data root that isn't closed: its values may be of cases the program doesn't have.</summary>
        public bool IsOpen(INamedTypeSymbol t) => IsData(t) && Cases(t) == null;

        private bool IsClosed(INamedTypeSymbol t)
        {
            // (the record's synthesized copy constructor is protected; deriving through it from another assembly is
            // not considered)
            if (t.InstanceConstructors.All(c => c.DeclaredAccessibility == Accessibility.Private ||
                                               c.IsImplicitlyDeclared && c.Parameters.Length == 1 && SymbolEqualityComparer.Default.Equals(c.Parameters[0].Type, t)))
            {
                return true;
            }
            for (ISymbol s = t; s is INamedTypeSymbol n; s = s.ContainingType)
            {
                if (n.DeclaredAccessibility == Accessibility.Private || n.DeclaredAccessibility == Accessibility.Internal ||
                    n.DeclaredAccessibility == Accessibility.ProtectedAndInternal)
                {
                    return true;
                }
            }
            return false;
        }

        /// <summary>Is <paramref name="t"/> <paramref name="from"/> or derived from it (generic definitions compared)?</summary>
        public static bool Derives(ITypeSymbol t, ITypeSymbol from)
        {
            for (var s = t; s != null; s = s.BaseType)
            {
                if (SymbolEqualityComparer.Default.Equals(s, from) || from is INamedTypeSymbol && SymbolEqualityComparer.Default.Equals(Def(s), Def(from)))
                {
                    return true;
                }
            }
            return false;
        }

        /// <summary>The [Invariant] methods holding for every object of the type: its own and its bases'.</summary>
        public static IEnumerable<IMethodSymbol> Invariants(ITypeSymbol t)
        {
            for (var s = t as INamedTypeSymbol; s != null; s = s.BaseType)
            {
                foreach (var m in s.GetMembers().OfType<IMethodSymbol>())
                {
                    if (SpecSymbols.IsInvariant(m) && !m.IsStatic && m.Parameters.Length == 0 &&
                        m.ReturnType.SpecialType == SpecialType.System_Boolean && SpecSymbols.IsPure(m))
                    {
                        yield return m;
                    }
                }
            }
        }

        /// <summary>
        /// Record equality is equality of values (the synthesized <c>==</c> compares the runtime type and each
        /// field) when every field compares the way the verifier models it: integers, booleans, arrays (by
        /// reference, as EqualityComparer does) and data records of the same kind. A field of a type parameter
        /// compares as the type argument does: <c>List&lt;int&gt;</c> has value equality, <c>List&lt;string&gt;</c> not.
        /// </summary>
        public bool HasValueEquality(INamedTypeSymbol t, HashSet<string> seen = null)
        {
            seen ??= new HashSet<string>();
            if (!seen.Add(t.ToDisplayString()))
            {
                return true;
            }
            var cases = Cases(t);
            if (cases == null)
            {
                return false;
            }
            var rootArgs = Arguments(t);
            foreach (var c in cases)
            {
                var subst = CaseArguments(c, Def(t), rootArgs);
                foreach (var p in Fields(c))
                {
                    if (!(Substitute(p.Type, subst) is ITypeSymbol ft) || !ComparesAsModeled(ft, seen))
                    {
                        return false;
                    }
                }
            }
            return true;
        }

        private bool ComparesAsModeled(ITypeSymbol ft, HashSet<string> seen) =>
            ft.SpecialType == SpecialType.System_Boolean || ft.TypeKind == TypeKind.Enum || ft is IArrayTypeSymbol ||
            ft.SpecialType >= SpecialType.System_Char && ft.SpecialType <= SpecialType.System_UInt64 ||
            // (a DateTime's or a TimeSpan's ticks, a Guid: the int the kernel keeps for each is what its Equals compares)
            Boogie.KernelTypes.IsOpaqueTicks(ft) || Boogie.KernelTypes.IsOpaqueId(ft) ||
            ft is INamedTypeSymbol n && IsData(n) && HasValueEquality(n, seen);

        /// <summary>Type parameter to type argument, for a type and the generic types it is nested in.</summary>
        private static Dictionary<ITypeParameterSymbol, ITypeSymbol> Arguments(INamedTypeSymbol t)
        {
            var map = new Dictionary<ITypeParameterSymbol, ITypeSymbol>(SymbolEqualityComparer.Default);
            for (var s = t; s != null; s = s.ContainingType)
            {
                for (int i = 0; i < s.TypeArguments.Length; i++)
                {
                    map[s.OriginalDefinition.TypeParameters[i]] = s.TypeArguments[i];
                }
            }
            return map;
        }

        /// <summary>
        /// A case's own type parameters in terms of the root's arguments: <c>Some&lt;U&gt; : Option&lt;U&gt;</c> at
        /// <c>Option&lt;int&gt;</c> has U = int. (A case nested in the root uses the root's parameters directly.)
        /// </summary>
        private static Dictionary<ITypeParameterSymbol, ITypeSymbol> CaseArguments(INamedTypeSymbol c, INamedTypeSymbol root,
            Dictionary<ITypeParameterSymbol, ITypeSymbol> rootArgs)
        {
            var map = new Dictionary<ITypeParameterSymbol, ITypeSymbol>(rootArgs, SymbolEqualityComparer.Default);
            for (var s = c; s != null && !SymbolEqualityComparer.Default.Equals(Def(s), root); s = s.BaseType)
            {
                if (s.BaseType is INamedTypeSymbol b && SymbolEqualityComparer.Default.Equals(Def(b), root))
                {
                    for (int i = 0; i < b.TypeArguments.Length; i++)
                    {
                        if (b.TypeArguments[i] is ITypeParameterSymbol own && rootArgs.TryGetValue(root.TypeParameters[i], out var arg))
                        {
                            map[own] = arg;
                        }
                    }
                }
            }
            return map;
        }

        /// <summary>The type with its type parameters replaced; null if that cannot be built.</summary>
        private static ITypeSymbol Substitute(ITypeSymbol t, Dictionary<ITypeParameterSymbol, ITypeSymbol> map)
        {
            switch (t)
            {
                case ITypeParameterSymbol tp: return map.TryGetValue(tp, out var a) ? a : null;
                case INamedTypeSymbol n when n.TypeArguments.Length > 0 && n.ContainingType?.IsGenericType != true:
                {
                    var args = n.TypeArguments.Select(x => Substitute(x, map)).ToArray();
                    return args.Any(x => x == null) ? null : n.OriginalDefinition.Construct(args);
                }
                case INamedTypeSymbol n when n.ContainingType?.IsGenericType == true:
                {
                    // a type nested in a generic one (List<T>.Cons): rebuild the container, then find the member
                    if (!(Substitute(n.ContainingType, map) is INamedTypeSymbol outer) || n.TypeArguments.Length > 0)
                    {
                        return null;
                    }
                    return outer.GetTypeMembers(n.Name).FirstOrDefault();
                }
                default: return t;
            }
        }
    }
}
