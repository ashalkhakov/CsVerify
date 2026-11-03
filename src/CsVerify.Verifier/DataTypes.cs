using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Positional records as algebraic data types. A data record is a non-generic record class whose whole state is
    /// its positional properties: a value is its constructor applied to them. A hierarchy is closed (its cases are
    /// known) when the abstract root cannot be derived from outside this compilation: every constructor is private,
    /// or the type is not visible outside the assembly. Each case gets a tag, so type tests and <c>switch</c> are
    /// case analysis.
    /// </summary>
    internal sealed class DataTypes
    {
        private readonly Dictionary<INamedTypeSymbol, int> _tags = new Dictionary<INamedTypeSymbol, int>(SymbolEqualityComparer.Default);

        public DataTypes(Compilation compilation, IEnumerable<SyntaxTree> userTrees)
        {
            var candidates = new List<INamedTypeSymbol>();
            foreach (var tree in userTrees)
            {
                var model = compilation.GetSemanticModel(tree);
                foreach (var decl in tree.GetRoot().DescendantNodes().OfType<RecordDeclarationSyntax>())
                    if (model.GetDeclaredSymbol(decl) is INamedTypeSymbol t && t.TypeKind == TypeKind.Class) candidates.Add(t);
            }
            // a record is data if its own state is positional and its base (if any) is data too
            bool changed = true;
            var data = new HashSet<INamedTypeSymbol>(SymbolEqualityComparer.Default);
            while (changed)
            {
                changed = false;
                foreach (var t in candidates)
                    if (!data.Contains(t) && HasDataShape(t) && (t.BaseType?.SpecialType == SpecialType.System_Object || data.Contains(t.BaseType)))
                        changed = data.Add(t) || changed;
            }
            int tag = 1;
            foreach (var t in candidates.Where(data.Contains)) _tags[t] = tag++;
        }

        private static bool HasDataShape(INamedTypeSymbol t)
        {
            if (t.IsGenericType || !(t.IsSealed || t.IsAbstract)) return false;
            foreach (var m in t.GetMembers())
            {
                if (m.IsStatic || m.IsImplicitlyDeclared && !(m is IFieldSymbol)) continue;
                switch (m)
                {
                    // every field is the backing field of a positional property
                    case IFieldSymbol fd when !(fd.AssociatedSymbol is IPropertySymbol p && IsPositional(p)): return false;
                    // an explicit constructor may only be an abstract root's empty, parameterless one
                    case IMethodSymbol c when c.MethodKind == MethodKind.Constructor && !IsPrimary(c):
                        if (!t.IsAbstract || c.Parameters.Length > 0 ||
                            c.DeclaringSyntaxReferences.Any(r => r.GetSyntax() is ConstructorDeclarationSyntax cd &&
                                ((cd.Body?.Statements.Count ?? 0) > 0 || cd.ExpressionBody != null || cd.Initializer != null)))
                            return false;
                        break;
                }
            }
            return true;
        }

        public static bool IsPositional(IPropertySymbol p) =>
            p.DeclaringSyntaxReferences.Length > 0 && p.DeclaringSyntaxReferences.All(r => r.GetSyntax() is ParameterSyntax);

        private static bool IsPrimary(IMethodSymbol ctor) =>
            ctor.DeclaringSyntaxReferences.Any(r => r.GetSyntax() is RecordDeclarationSyntax);

        public bool IsData(ITypeSymbol t) => t is INamedTypeSymbol n && _tags.ContainsKey(n);

        public int TagOf(INamedTypeSymbol t) => _tags[t];

        /// <summary>Could a value of this static type be a data value (so its reference identity is not modeled)?</summary>
        public bool MayHoldData(ITypeSymbol t) =>
            t != null && (IsData(t) || t.SpecialType == SpecialType.System_Object || t.TypeKind == TypeKind.TypeParameter ||
                          t.TypeKind == TypeKind.Interface && _tags.Keys.Any(r => r.AllInterfaces.Contains(t, SymbolEqualityComparer.Default)));

        public static IMethodSymbol PrimaryConstructor(INamedTypeSymbol t) => t.InstanceConstructors.FirstOrDefault(IsPrimary);

        /// <summary>The positional properties of a record, its bases' first: the arguments of its value constructor.</summary>
        public IReadOnlyList<IPropertySymbol> Fields(INamedTypeSymbol t)
        {
            var result = IsData(t.BaseType) ? Fields(t.BaseType).ToList() : new List<IPropertySymbol>();
            result.AddRange(t.GetMembers().OfType<IPropertySymbol>().Where(p => !p.IsStatic && IsPositional(p)));
            return result;
        }

        /// <summary>The property a primary-constructor parameter initializes (its own, or a base's of the same name).</summary>
        public static IPropertySymbol PositionalProperty(INamedTypeSymbol t, int ordinal)
        {
            var name = PrimaryConstructor(t)?.Parameters[ordinal].Name;
            for (var s = t; s != null; s = s.BaseType)
                if (s.GetMembers(name).OfType<IPropertySymbol>().FirstOrDefault() is IPropertySymbol p) return p;
            return null;
        }

        /// <summary>A closed type's cases: the non-abstract data records derived from it (itself, if not abstract).</summary>
        public IReadOnlyList<INamedTypeSymbol> Cases(INamedTypeSymbol t)
        {
            if (!IsData(t)) return null;
            if (!t.IsAbstract) return new[] { t };
            if (!IsClosed(t)) return null;
            return _tags.Keys.Where(c => !c.IsAbstract && Derives(c, t)).ToList();
        }

        private bool IsClosed(INamedTypeSymbol t)
        {
            // (the record's synthesized copy constructor is protected; deriving through it from another assembly is
            // not considered)
            if (t.InstanceConstructors.All(c => c.DeclaredAccessibility == Accessibility.Private ||
                                               c.IsImplicitlyDeclared && c.Parameters.Length == 1 && SymbolEqualityComparer.Default.Equals(c.Parameters[0].Type, t))) return true;
            for (ISymbol s = t; s is INamedTypeSymbol n; s = s.ContainingType)
                if (n.DeclaredAccessibility == Accessibility.Private || n.DeclaredAccessibility == Accessibility.Internal ||
                    n.DeclaredAccessibility == Accessibility.ProtectedAndInternal)
                    return true;
            return false;
        }

        public static bool Derives(ITypeSymbol t, ITypeSymbol from)
        {
            for (var s = t; s != null; s = s.BaseType)
                if (SymbolEqualityComparer.Default.Equals(s, from)) return true;
            return false;
        }

        /// <summary>The [Invariant] methods holding for every object of the type: its own and its bases'.</summary>
        public static IEnumerable<IMethodSymbol> Invariants(ITypeSymbol t)
        {
            for (var s = t as INamedTypeSymbol; s != null; s = s.BaseType)
                foreach (var m in s.GetMembers().OfType<IMethodSymbol>())
                    if (SpecSymbols.IsInvariant(m) && !m.IsStatic && m.Parameters.Length == 0 &&
                        m.ReturnType.SpecialType == SpecialType.System_Boolean && SpecSymbols.IsPure(m))
                        yield return m;
        }

        /// <summary>
        /// Record equality is equality of values (the synthesized <c>==</c> compares the runtime type and each
        /// field) when every field compares the way the verifier models it: integers, booleans, arrays (by
        /// reference, as EqualityComparer does) and data records of the same kind.
        /// </summary>
        public bool HasValueEquality(INamedTypeSymbol t, HashSet<INamedTypeSymbol> seen = null)
        {
            seen ??= new HashSet<INamedTypeSymbol>(SymbolEqualityComparer.Default);
            if (!seen.Add(t)) return true;
            var cases = Cases(t);
            if (cases == null) return false;
            foreach (var c in cases)
                foreach (var p in Fields(c))
                {
                    var ft = p.Type;
                    bool ok = ft.SpecialType == SpecialType.System_Boolean || ft.TypeKind == TypeKind.Enum || ft is IArrayTypeSymbol ||
                              ft.SpecialType >= SpecialType.System_Char && ft.SpecialType <= SpecialType.System_UInt64 ||
                              ft is INamedTypeSymbol n && IsData(n) && HasValueEquality(n, seen);
                    if (!ok) return false;
                }
            return true;
        }
    }
}
