using System;
using System.Collections.Generic;
using System.Linq;
using System.Text.RegularExpressions;
using Microsoft.CodeAnalysis;

namespace CsVerify.Verifier
{
    /// <summary>
    /// The model as EF itself builds it (EfRuntimeModel), in place of what was read from the configuration's source: of
    /// each entity EF's model has, its keys, unique indexes, columns, tokens and relationships are EF's. Query filters'
    /// bodies stay the source's (they are lambdas the verifier lowers).
    /// </summary>
    internal sealed partial class EfModel
    {
        /// <summary>Why EF's own model of a context wasn't read (the configuration's source was, instead).</summary>
        public readonly List<(string context, string why)> RuntimeFailures = new List<(string, string)>();

        /// <summary>Was EF's own model read, of every context?</summary>
        public bool FromRuntime { get; private set; }

        internal static string MetadataName(INamedTypeSymbol t) =>
            t.ContainingType != null ? MetadataName(t.ContainingType) + "+" + t.MetadataName
            : t.ContainingNamespace is { IsGlobalNamespace: false } ns ? ns.ToDisplayString() + "." + t.MetadataName : t.MetadataName;

        private void ApplyRuntime(Compilation compilation, EfRuntimeModel runtime)
        {
            RuntimeFailures.AddRange(runtime.Failures);
            if (runtime.Contexts.Count == 0)
            {
                return;
            }
            var read = new Dictionary<Entity, EfRuntimeModel.Entity>();
            foreach (var r in runtime.Entities.Values)
            {
                if (compilation.GetTypeByMetadataName(r.Type) is not INamedTypeSymbol type || type.IsGenericType)
                {
                    continue;
                }
                Add(type);
                if (EntityOf(type) is Entity e)
                {
                    read[e] = r;
                }
            }
            foreach (var (e, r) in read)
            {
                var props = PropertiesOf(e.Type).GroupBy(p => p.Name).ToDictionary(g => g.Key, g => g.First());
                List<IPropertySymbol> Mapped(List<string> names) =>
                    names != null && names.Count > 0 && names.All(props.ContainsKey) ? names.Select(n => props[n]).ToList() : null;
                e.Unread = false;
                e.Key = Mapped(r.Key) ?? new List<IPropertySymbol>();
                e.Unique.Clear();
                e.Alternate.Clear();
                e.UniqueWhereFiltered.Clear();
                e.Tokens.Clear();
                e.RowVersions.Clear();
                e.Converted.Clear();
                e.Shadow.Clear();
                e.Required.Clear();
                e.ModelNullable.Clear();
                e.ForeignKeys.Clear();
                e.CollectionKeys.Clear();
                foreach (var k in r.AlternateKeys)
                {
                    if (Mapped(k) is List<IPropertySymbol> alt)
                    {
                        e.AddUnique(alt);
                        e.Alternate.Add(alt);
                    }
                }
                foreach (var ix in r.UniqueIndexes)
                {
                    if (Mapped(ix.Properties) is List<IPropertySymbol> index)
                    {
                        switch (FilterKind(ix, r))
                        {
                            case IndexFilter.None: e.AddUnique(index); break;
                            case IndexFilter.QueryFilter: e.UniqueWhereFiltered.Add(index); break;
                        }
                    }
                }
                foreach (var p in r.Properties)
                {
                    if (p.Shadow || !props.TryGetValue(p.Name, out var symbol))
                    {
                        if (p.Shadow && TypeOf(compilation, p.ClrType) is ITypeSymbol shadow)
                        {
                            e.Shadow[p.Name] = shadow;
                        }
                        continue;
                    }
                    var def = symbol.OriginalDefinition;
                    e.Configured.Add(def);
                    e.ModelNullable[def] = p.Nullable;
                    if (p.Converted)
                    {
                        e.Converted.Add(def);
                    }
                    if (p.Token)
                    {
                        e.AddToken(symbol);
                    }
                    if (p.RowVersion)
                    {
                        e.AddRowVersion(symbol);
                    }
                }
                foreach (var nav in e.References.Concat(e.Collections))
                {
                    _inverses.Remove(nav.OriginalDefinition);
                    _oneToOne.Remove(nav.OriginalDefinition);
                    _unreadNavigations.Remove(nav);
                }
                _unreadEntities.Remove(e.Type.OriginalDefinition);
            }
            foreach (var fk in runtime.ForeignKeys)
            {
                if (fk.Dependent == null || fk.Principal == null || compilation.GetTypeByMetadataName(fk.Dependent) is not INamedTypeSymbol dt || EntityOf(dt) is not Entity d ||
                    compilation.GetTypeByMetadataName(fk.Principal) is not INamedTypeSymbol pt || EntityOf(pt) is not Entity p || !read.ContainsKey(d) || !read.ContainsKey(p))
                {
                    continue;
                }
                var toPrincipal = fk.ToPrincipal == null ? null : PropertiesOf(d.Type).FirstOrDefault(x => x.Name == fk.ToPrincipal);
                var toDependent = fk.ToDependent == null ? null : PropertiesOf(p.Type).FirstOrDefault(x => x.Name == fk.ToDependent);
                Pair(toPrincipal, toDependent);
                if (fk.Unique)
                {
                    // (its unique index: of all rows, or of those the dependent's query filter keeps)
                    var index = read[d].UniqueIndexes.FirstOrDefault(ix => ix.Properties.SequenceEqual(fk.Properties));
                    var kind = index == null ? IndexFilter.None : FilterKind(index, read[d]);
                    foreach (var end in new[] { toPrincipal, toDependent }.Where(x => x != null))
                    {
                        if (kind == IndexFilter.None)
                        {
                            _oneToOne.Add(end.OriginalDefinition);
                        }
                        else if (kind == IndexFilter.QueryFilter)
                        {
                            _oneToOneWhereFiltered.Add(end.OriginalDefinition);
                        }
                    }
                }
                // (a foreign key of one property of the class, to the principal's key)
                if (fk.Properties.Count == 1 && p.Key.Count == 1 && fk.PrincipalKey.Count == 1 && fk.PrincipalKey[0] == p.Key[0].Name &&
                    PropertiesOf(d.Type).FirstOrDefault(x => x.Name == fk.Properties[0]) is IPropertySymbol column)
                {
                    if (toPrincipal != null)
                    {
                        d.ForeignKeys[toPrincipal] = column;
                    }
                    if (toDependent != null && NavigationTarget(toDependent.Type, out bool many) != null && many)
                    {
                        p.CollectionKeys[toDependent] = column;
                    }
                }
            }
            FromRuntime = runtime.Failures.Count == 0;
            if (FromRuntime)
            {
                Unread.Clear();
            }
        }

        private enum IndexFilter { None, QueryFilter, Other }

        /// <summary>
        /// What a unique index's filter leaves of its uniqueness. Each conjunct that a column of the index IS NOT NULL
        /// leaves it whole (a row a value not null fixes meets it). Each that a bool column is false, where the entity's
        /// query filter says so of every row, leaves it among the rows the query filter keeps. Any other: nothing.
        /// </summary>
        private static IndexFilter FilterKind(EfRuntimeModel.Index ix, EfRuntimeModel.Entity e)
        {
            if (string.IsNullOrWhiteSpace(ix.Filter))
            {
                return IndexFilter.None;
            }
            var kind = IndexFilter.None;
            foreach (var conjunct in Regex.Split(ix.Filter, @"\s+AND\s+", RegexOptions.IgnoreCase))
            {
                var c = conjunct.Trim().Trim('(', ')').Trim();
                if (Regex.Match(c, @"^[\[""`]?(\w+)[\]""`]?\s+IS\s+NOT\s+NULL$", RegexOptions.IgnoreCase) is { Success: true } notNull &&
                    e.Properties.Any(p => p.Column == notNull.Groups[1].Value && ix.Properties.Contains(p.Name)))
                {
                    continue;
                }
                if ((Regex.Match(c, @"^[\[""`]?(\w+)[\]""`]?\s*=\s*(?:0|FALSE|CAST\(0 AS bit\))$", RegexOptions.IgnoreCase) is { Success: true } isFalse ||
                     (isFalse = Regex.Match(c, @"^NOT\s+[\[""`]?(\w+)[\]""`]?$", RegexOptions.IgnoreCase)).Success) &&
                    e.Properties.FirstOrDefault(p => p.Column == isFalse.Groups[1].Value) is { ClrType: "System.Boolean" } flag && e.FilteredFalse.Contains(flag.Name))
                {
                    kind = IndexFilter.QueryFilter;
                    continue;
                }
                return IndexFilter.Other;
            }
            return kind;
        }

        /// <summary>A CLR type by its reflection name: a type of the compilation, or Nullable of one.</summary>
        private static ITypeSymbol TypeOf(Compilation compilation, string name)
        {
            if (name == null)
            {
                return null;
            }
            var nullable = Regex.Match(name, @"^System\.Nullable`1\[\[([^,\]]+)");
            if (nullable.Success)
            {
                return compilation.GetTypeByMetadataName(nullable.Groups[1].Value) is INamedTypeSymbol inner
                    ? compilation.GetSpecialType(SpecialType.System_Nullable_T).Construct(inner) : null;
            }
            return name.Contains('[') ? null : compilation.GetTypeByMetadataName(name);
        }
    }
}
