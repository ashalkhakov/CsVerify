using System.Collections.Generic;
using System.Linq;
using System.Reflection.Metadata;
using Microsoft.CodeAnalysis;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Entity classes from referenced assemblies (a domain project's), as EF reads them: their auto-properties, which
    /// the compiler gives a backing field (&lt;P&gt;k__BackingField) beside them, are heap fields, as a source class's
    /// are; those with a setter (of any accessibility) are columns. A property with code of its own is neither.
    /// </summary>
    internal sealed class MetadataEntities
    {
        /// <summary>The program's, for the run this thread is in.</summary>
        [System.ThreadStatic] public static MetadataEntities Current;

        public readonly HashSet<ISymbol> Fields = new HashSet<ISymbol>(SymbolEqualityComparer.Default);
        public readonly HashSet<ISymbol> Columns = new HashSet<ISymbol>(SymbolEqualityComparer.Default);
        public readonly HashSet<ITypeSymbol> Types = new HashSet<ITypeSymbol>(SymbolEqualityComparer.Default);

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
                for (var b = e.OriginalDefinition; b != null && IsUserClass(b); b = b.BaseType?.OriginalDefinition)
                {
                    if (m.Types.Add(b))
                    {
                        m.Read(compilation, b);
                    }
                }
            }
            return m;
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
                    foreach (var ph in td.GetProperties())
                    {
                        var pd = r.GetPropertyDefinition(ph);
                        var pn = r.GetString(pd.Name);
                        if (!fields.Contains("<" + pn + ">k__BackingField") || !(t.GetMembers(pn).OfType<IPropertySymbol>().FirstOrDefault(p => !p.IsStatic && !p.IsIndexer) is IPropertySymbol p))
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
