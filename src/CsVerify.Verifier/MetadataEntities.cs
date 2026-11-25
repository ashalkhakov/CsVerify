using System.Collections.Generic;
using System.Linq;
using System.Reflection.Metadata;
using Microsoft.CodeAnalysis;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Entity classes from referenced assemblies (a domain project's), and the library bases of the program's (Identity's
    /// IdentityUser&lt;TKey&gt;), as EF reads them: their auto-properties, which the compiler gives a backing field
    /// (&lt;P&gt;k__BackingField) beside them, are heap fields, as a source class's are; those with a setter (of any
    /// accessibility) are columns. A property with code of its own is neither.
    /// </summary>
    internal sealed class MetadataEntities
    {
        /// <summary>The program's, for the run this thread is in.</summary>
        [System.ThreadStatic] public static MetadataEntities Current;

        public readonly HashSet<ISymbol> Fields = new HashSet<ISymbol>(SymbolEqualityComparer.Default);
        public readonly HashSet<ISymbol> Columns = new HashSet<ISymbol>(SymbolEqualityComparer.Default);
        public readonly HashSet<ITypeSymbol> Types = new HashSet<ITypeSymbol>(SymbolEqualityComparer.Default);

        /// <summary>
        /// A generic library base's instantiation the program's entities derive from (IdentityUser&lt;long&gt; of
        /// IdentityUser&lt;TKey&gt;), where they derive from one only: its fields are that one's, of its types.
        /// </summary>
        public readonly Dictionary<ITypeSymbol, INamedTypeSymbol> Instantiations = new Dictionary<ITypeSymbol, INamedTypeSymbol>(SymbolEqualityComparer.Default);

        /// <summary>A class of a referenced assembly that could be an entity: not the framework's, nor a library's of Microsoft or System.</summary>
        public static bool IsUserClass(ITypeSymbol t) =>
            t is INamedTypeSymbol { TypeKind: TypeKind.Class, SpecialType: SpecialType.None } n && !n.Locations.Any(l => l.IsInSource) &&
            !(n.ContainingNamespace?.ToDisplayString() is string ns && (ns == "System" || ns.StartsWith("System.") || ns == "Microsoft" || ns.StartsWith("Microsoft.")));

        public static bool IsEntity(ITypeSymbol t) => Current != null && t != null && Current.Types.Contains(t.OriginalDefinition);

        public static MetadataEntities For(Compilation compilation, IEnumerable<INamedTypeSymbol> entities)
        {
            var m = new MetadataEntities();
            foreach (var e in entities)
            {
                // (a referenced assembly's entity, and its bases there; a library base, of an entity of the program's; a
                // library's own entity, which EF's model has: Identity's IdentityUser<long> as it is, and its bases)
                bool library = !e.Locations.Any(l => l.IsInSource) && !IsUserClass(e);
                var first = library || IsUserClass(e) ? e.OriginalDefinition : LibraryBase(e);
                if (first != null && first != e.OriginalDefinition)
                {
                    m.Instantiate(e);
                }
                if (library)
                {
                    m.Instantiate(e, itself: true);
                }
                for (var b = first; b != null && (IsUserClass(b) || (library || first != e.OriginalDefinition) && b.SpecialType == SpecialType.None); b = b.BaseType?.OriginalDefinition)
                {
                    if (m.Types.Add(b))
                    {
                        m.Read(compilation, b);
                    }
                }
            }
            return m;
        }

        private readonly HashSet<ITypeSymbol> _ambiguous = new HashSet<ITypeSymbol>(SymbolEqualityComparer.Default);

        private void Instantiate(INamedTypeSymbol e, bool itself = false)
        {
            for (var b = itself ? e : e.BaseType; b != null && b.SpecialType != SpecialType.System_Object; b = b.BaseType)
            {
                if (!b.IsGenericType || b.Locations.Any(l => l.IsInSource) || _ambiguous.Contains(b.OriginalDefinition))
                {
                    continue;
                }
                if (Instantiations.TryGetValue(b.OriginalDefinition, out var had) && !SymbolEqualityComparer.Default.Equals(had, b))
                {
                    Instantiations.Remove(b.OriginalDefinition);
                    _ambiguous.Add(b.OriginalDefinition);
                    continue;
                }
                Instantiations[b.OriginalDefinition] = b;
            }
        }

        /// <summary>A member of a generic library base as its instantiation's (IdentityUser&lt;long&gt;.Id, of type long), where there is one.</summary>
        public static ISymbol Instantiated(ISymbol s) =>
            Current != null && s?.ContainingType is INamedTypeSymbol { IsGenericType: true } t && Current.Instantiations.TryGetValue(t.OriginalDefinition, out var c)
                ? c.GetMembers(s.Name).FirstOrDefault(m => m.Kind == s.Kind) ?? s : s;

        /// <summary>The first base of an entity of the program's that is a library's (Identity's IdentityUser&lt;TKey&gt;), or null.</summary>
        private static INamedTypeSymbol LibraryBase(INamedTypeSymbol e)
        {
            var b = e.BaseType;
            while (b != null && b.Locations.Any(l => l.IsInSource))
            {
                b = b.BaseType;
            }
            return b == null || b.SpecialType == SpecialType.System_Object ? null : b.OriginalDefinition;
        }

        private void Read(Compilation compilation, INamedTypeSymbol t)
        {
            if (!(compilation.GetMetadataReference(t.ContainingAssembly) is PortableExecutableReference pe) || !(pe.GetMetadata() is AssemblyMetadata am))
            {
                return;
            }
            var name = MetadataName(t);
            foreach (var module in am.GetModules())
            {
                var r = module.GetMetadataReader();
                foreach (var h in r.TypeDefinitions)
                {
                    var td = r.GetTypeDefinition(h);
                    if (FullName(r, td) != name)
                    {
                        continue;
                    }
                    var fields = new HashSet<string>(td.GetFields().Select(f => r.GetString(r.GetFieldDefinition(f).Name)));
                    bool reference = t.ContainingAssembly.GetAttributes().Any(a => a.AttributeClass?.ToDisplayString() == "System.Runtime.CompilerServices.ReferenceAssemblyAttribute");
                    foreach (var ph in td.GetProperties())
                    {
                        var pd = r.GetPropertyDefinition(ph);
                        var pn = r.GetString(pd.Name);
                        // (an auto-property: its backing field beside it, or, in a reference assembly (a targeting pack's) that has
                        // no private fields, its accessors the compiler's, #129)
                        if (!(t.GetMembers(pn).OfType<IPropertySymbol>().FirstOrDefault(p => !p.IsStatic && !p.IsIndexer) is IPropertySymbol p) ||
                            !(fields.Contains("<" + pn + ">k__BackingField") || reference && CompilerGenerated(p.GetMethod) && (p.SetMethod == null || CompilerGenerated(p.SetMethod))))
                        {
                            continue;
                        }
                        Fields.Add(p);
                        if (!pd.GetAccessors().Setter.IsNil)
                        {
                            Columns.Add(p);
                        }
                    }
                }
            }
        }

        private static bool CompilerGenerated(IMethodSymbol m) =>
            m != null && m.GetAttributes().Any(a => a.AttributeClass?.ToDisplayString() == "System.Runtime.CompilerServices.CompilerGeneratedAttribute");

        private static string MetadataName(INamedTypeSymbol t) =>
            t.ContainingType != null ? MetadataName(t.ContainingType) + "+" + t.MetadataName
            : t.ContainingNamespace == null || t.ContainingNamespace.IsGlobalNamespace ? t.MetadataName : t.ContainingNamespace.ToDisplayString() + "." + t.MetadataName;

        private static string FullName(MetadataReader r, TypeDefinition td)
        {
            var n = r.GetString(td.Name);
            if (!td.GetDeclaringType().IsNil)
            {
                return FullName(r, r.GetTypeDefinition(td.GetDeclaringType())) + "+" + n;
            }
            var ns = r.GetString(td.Namespace);
            return ns.Length == 0 ? n : ns + "." + n;
        }
    }
}
