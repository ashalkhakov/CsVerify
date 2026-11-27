using System;
using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// The Entity Framework Core model of the program, as its sources declare it: the entity types (a context's
    /// DbSet properties, and what their navigations lead to), each one's key, unique indexes, concurrency tokens, query
    /// filter and navigations. Read from EF's attributes ([Key], [Index], [ConcurrencyCheck], [Timestamp]), its
    /// conventions (Id or TypeId is the key), and the fluent configuration in OnModelCreating and
    /// IEntityTypeConfiguration&lt;T&gt;.Configure, in the forms EF's documentation writes it.
    /// </summary>
    internal sealed partial class EfModel
    {
        internal sealed class Entity
        {
            public INamedTypeSymbol Type;
            /// <summary>The primary key's properties (none if the type has no key the model says or the conventions find).</summary>
            public List<IPropertySymbol> Key = new List<IPropertySymbol>();
            /// <summary>Other sets of properties no two rows share: unique indexes and alternate keys.</summary>
            public List<List<IPropertySymbol>> Unique = new List<List<IPropertySymbol>>();
            /// <summary>The alternate keys (HasAlternateKey), among Unique: like the key, EF never lets a tracked entity's change.</summary>
            public List<List<IPropertySymbol>> Alternate = new List<List<IPropertySymbol>>();
            /// <summary>Concurrency tokens: [ConcurrencyCheck] or IsConcurrencyToken, and row versions ([Timestamp], IsRowVersion).</summary>
            public List<IPropertySymbol> Tokens = new List<IPropertySymbol>();
            public HashSet<IPropertySymbol> RowVersions = new HashSet<IPropertySymbol>(SymbolEqualityComparer.Default);
            /// <summary>The properties the configuration names (Property, HasKey, HasAlternateKey): columns, a get-only one too.</summary>
            public HashSet<IPropertySymbol> Configured = new HashSet<IPropertySymbol>(SymbolEqualityComparer.Default);
            /// <summary>The columns configured required (IsRequired(), [Required]): NOT NULL, whatever their nullable annotation.</summary>
            public HashSet<IPropertySymbol> Required = new HashSet<IPropertySymbol>(SymbolEqualityComparer.Default);
            /// <summary>The columns stored by a value converter (HasConversion): compared by their stored values, as scalars are.</summary>
            public HashSet<IPropertySymbol> Converted = new HashSet<IPropertySymbol>(SymbolEqualityComparer.Default);
            /// <summary>Shadow columns (Property&lt;T&gt;("Name") of no property of the class): their names and types.</summary>
            public Dictionary<string, ITypeSymbol> Shadow = new Dictionary<string, ITypeSymbol>();
            /// <summary>
            /// The keys by their columns' names, shadow columns too, as EF's own model has them (null where it wasn't read):
            /// the key, alternate keys and unique indexes, each with whether it is one only among the rows the entity's
            /// query filter keeps.
            /// </summary>
            public List<(List<string> columns, bool whereFiltered)> KeyColumns;
            /// <summary>The shadow columns that are NOT NULL, as EF's model has them.</summary>
            public HashSet<string> ShadowNotNull = new HashSet<string>();
            /// <summary>A reference navigation's foreign key, its columns' names (shadow ones too), as EF's model has it.</summary>
            public Dictionary<IPropertySymbol, List<string>> ReferenceColumns = new Dictionary<IPropertySymbol, List<string>>(SymbolEqualityComparer.Default);
            /// <summary>Whether each column is nullable, as EF's own model has it (EfRuntimeModel), where that was read.</summary>
            public Dictionary<IPropertySymbol, bool> ModelNullable = new Dictionary<IPropertySymbol, bool>(SymbolEqualityComparer.Default);
            /// <summary>
            /// Sets of properties no two rows the entity's query filter keeps share: a unique index filtered by what the
            /// query filter says of every row (a soft delete's). Not of a query that ignores the filters.
            /// </summary>
            public List<List<IPropertySymbol>> UniqueWhereFiltered = new List<List<IPropertySymbol>>();
            /// <summary>Is the column NOT NULL: as EF's model says; else of a value type not Nullable, annotated not null, or configured required.</summary>
            public bool NotNullColumn(IPropertySymbol p) =>
                ModelNullable.TryGetValue(p.OriginalDefinition, out bool nullable) ? !nullable :
                p.Type.IsValueType ? p.Type is not INamedTypeSymbol { OriginalDefinition.SpecialType: SpecialType.System_Nullable_T }
                : p.NullableAnnotation == NullableAnnotation.NotAnnotated || Required.Contains(p.OriginalDefinition) ||
                  p.GetAttributes().Any(a => a.AttributeClass?.ToDisplayString() == "System.ComponentModel.DataAnnotations.RequiredAttribute");
            /// <summary>
            /// Configured by a library context's OnModelCreating that no model of the Spec library's describes: its key,
            /// tokens and row versions there aren't known, so none is taken by convention, and what depends on its tokens
            /// (Attach, Update, a write of a column of its library base) isn't translated.
            /// </summary>
            public bool Unread;
            /// <summary>The query filters (HasQueryFilter), each a lambda over the entity.</summary>
            public List<IAnonymousFunctionOperation> Filters = new List<IAnonymousFunctionOperation>();
            /// <summary>Navigations to one entity.</summary>
            public List<IPropertySymbol> References = new List<IPropertySymbol>();
            /// <summary>Navigations to many (a collection of entities).</summary>
            public List<IPropertySymbol> Collections = new List<IPropertySymbol>();
            /// <summary>A reference navigation's foreign key, a property of this entity (where the model says which).</summary>
            public Dictionary<IPropertySymbol, IPropertySymbol> ForeignKeys = new Dictionary<IPropertySymbol, IPropertySymbol>(SymbolEqualityComparer.Default);
            /// <summary>A collection navigation's foreign key, a property of the entity it holds (where the model says which).</summary>
            public Dictionary<IPropertySymbol, IPropertySymbol> CollectionKeys = new Dictionary<IPropertySymbol, IPropertySymbol>(SymbolEqualityComparer.Default);

            public void AddFilter(IAnonymousFunctionOperation filter) => Filters.Add(filter);

            public void AddKey(IEnumerable<IPropertySymbol> collection) => Key.AddRange(collection);

            public bool AddRowVersion(IPropertySymbol rowVersion) => RowVersions.Add(rowVersion);

            public void AddToken(IPropertySymbol token) => Tokens.Add(token);

            public void AddUnique(List<IPropertySymbol> unique) => Unique.Add(unique);

            /// <summary>A property of the key or of an alternate key: a tracked entity's is its row's (EF throws where one changes).</summary>
            public bool IsKeyProperty(IPropertySymbol p) =>
                Key.Concat(Alternate.SelectMany(k => k)).Any(k => SymbolEqualityComparer.Default.Equals(k.OriginalDefinition, p.OriginalDefinition));

            /// <summary>Every set of properties that identifies a row: the key, then the unique ones.</summary>
            public IEnumerable<List<IPropertySymbol>> Identifying => (Key.Count > 0 ? new[] { Key } : Array.Empty<List<IPropertySymbol>>()).Concat(Unique);
        }

        private readonly Dictionary<ITypeSymbol, Entity> _entities = new Dictionary<ITypeSymbol, Entity>(SymbolEqualityComparer.Default);

        /// <summary>The program's DbContext classes.</summary>
        public readonly List<INamedTypeSymbol> Contexts = new List<INamedTypeSymbol>();

        /// <summary>Model configuration this reading does not understand, where it could change what is proved.</summary>
        public readonly List<(Location at, string what)> Unread = new List<(Location, string)>();

        public INamedTypeSymbol DbContextType { get; }

        /// <summary>
        /// Does the program turn on SQL's null semantics (UseRelationalNulls) for some context? Then for every one: which
        /// context a provider's options are for isn't followed.
        /// </summary>
        public bool RelationalNulls { get; private set; }

        /// <summary>
        /// Does the database compare strings as .NET's == does? When the only providers the program names are SQLite
        /// (whose default collation, BINARY, compares them exactly) and the in-memory one, and nothing sets a collation
        /// (UseCollation, a column type with COLLATE, EF.Functions.Collate). Then also for a database not made from this
        /// model: the model can't tell.
        /// </summary>
        public bool ExactStrings => _providers.Count > 0 && _providers.All(p => p == "UseSqlite" || p == "UseInMemoryDatabase") && !_collation;

        /// <summary>The providers the sources name, and whether they set a collation (ExactStrings).</summary>
        private readonly HashSet<string> _providers = new HashSet<string>();
        private bool _collation;

        private static readonly string[] Providers =
        {
            "UseSqlServer", "UseAzureSql", "UseAzureSynapse", "UseSqlite", "UseNpgsql", "UseMySql", "UseMySQL", "UseOracle",
            "UseInMemoryDatabase", "UseCosmos", "UseFirebird", "UseJet", "UseDb2", "UseSpanner",
        };

        /// <summary>
        /// A library's own classes that are entities of this run's model, as EF's own model has them (Identity's
        /// IdentityUser&lt;TKey&gt; used as it is): their properties are read as an entity's of the program's are.
        /// </summary>
        [System.ThreadStatic] internal static HashSet<ITypeSymbol> LibraryEntities;

        /// <summary>The model, or null for a program that does not reference EF Core.</summary>
        public static EfModel For(Compilation compilation, IReadOnlyList<SyntaxTree> userTrees, IReadOnlyList<INamedTypeSymbol> sourceTypes, bool runtime = true,
            IReadOnlyList<string> nativeLibraries = null)
        {
            LibraryEntities = new HashSet<ITypeSymbol>(SymbolEqualityComparer.Default);
            var dbContext = compilation.GetTypeByMetadataName("Microsoft.EntityFrameworkCore.DbContext");
            if (dbContext == null)
            {
                return null;
            }
            var model = new EfModel(compilation, userTrees, sourceTypes, dbContext);
            if (runtime)
            {
                model.ApplyRuntime(compilation, EfRuntimeModel.Read(compilation, model.Contexts.Where(c => !c.IsAbstract && !c.IsGenericType), model._providers, nativeLibraries ?? new List<string>()));
            }
            return model;
        }

        private EfModel(Compilation compilation, IReadOnlyList<SyntaxTree> userTrees, IReadOnlyList<INamedTypeSymbol> sourceTypes, INamedTypeSymbol dbContext)
        {
            DbContextType = dbContext;
            ReadOwned(compilation, userTrees);
            var called = userTrees.SelectMany(t => t.GetRoot().DescendantNodes().OfType<InvocationExpressionSyntax>())
                .Select(i => i.Expression is MemberAccessExpressionSyntax ma ? ma.Name.Identifier.Text : (i.Expression as IdentifierNameSyntax)?.Identifier.Text)
                .Where(n => n != null).ToList();
            _providers.UnionWith(called.Where(n => Providers.Contains(n)));
            _collation = called.Any(n => n == "UseCollation" || n == "Collate") ||
                userTrees.Any(t => t.GetRoot().DescendantNodes().OfType<LiteralExpressionSyntax>()
                    .Any(l => l.Token.ValueText.IndexOf("COLLATE", StringComparison.OrdinalIgnoreCase) >= 0 || l.Token.ValueText.Contains("Relational:Collation")));
            RelationalNulls = userTrees.Any(t => t.GetRoot().DescendantNodes().OfType<InvocationExpressionSyntax>().Any(i =>
                i.Expression is MemberAccessExpressionSyntax { Name.Identifier.Text: "UseRelationalNulls" } &&
                !(i.ArgumentList.Arguments.FirstOrDefault()?.Expression is LiteralExpressionSyntax l && l.IsKind(SyntaxKind.FalseLiteralExpression))));
            foreach (var t in sourceTypes.Where(t => IsContextType(t)))
            {
                Contexts.Add(t);
                foreach (var p in AllMembers(t).OfType<IPropertySymbol>())
                {
                    if (p.Type is INamedTypeSymbol set && set.Name == "DbSet" && set.TypeArguments.Length == 1 && set.TypeArguments[0] is INamedTypeSymbol e)
                    {
                        Add(e);
                    }
                }
                // (a library base's, of the program's classes: IdentityDbContext's Users)
                foreach (var b in LibraryContexts(t))
                {
                    foreach (var e in DbSetsOf(b).Where(e => IsSourceClass(e, sourceTypes)))
                    {
                        Add(e);
                    }
                }
            }
            // configured types are entity types too: modelBuilder.Entity<T>(), and what is called on its builder; and a
            // library context's, as the Spec library's model of it has it
            var configuration = Configuration(compilation, userTrees).Select(c => (c.tree, c.inv, c.builder, configuration: (INamedTypeSymbol)null))
                .Concat(GenericConfiguration(compilation, sourceTypes)).Concat(LibraryModels(compilation, sourceTypes)).ToList();
            foreach (var (tree, inv, builder, _) in configuration)
            {
                if (builder.TypeArguments[0] is INamedTypeSymbol e)
                {
                    Add(e);
                }
            }
            foreach (var tree in userTrees)
            {
                var model = compilation.ModelOf(tree);
                foreach (var inv in tree.GetRoot().DescendantNodes().OfType<InvocationExpressionSyntax>())
                {
                    if (inv.Expression is MemberAccessExpressionSyntax { Name: GenericNameSyntax { Identifier.Text: "Entity" } } &&
                        model.GetSymbolInfo(inv).Symbol is IMethodSymbol { ContainingType.Name: "ModelBuilder", TypeArguments.Length: 1 } entity &&
                        entity.TypeArguments[0] is INamedTypeSymbol configured && IsSourceClass(configured, sourceTypes))
                    {
                        Add(configured);
                    }
                }
            }
            // and what navigations reach
            for (bool grew = true; grew;)
            {
                grew = false;
                foreach (var e in _entities.Values.ToList())
                {
                    foreach (var p in PropertiesOf(e.Type))
                    {
                        if (NavigationTarget(p.Type, out _) is INamedTypeSymbol target && IsSourceClass(target, sourceTypes) && !_entities.ContainsKey(target) && !IsOwned(target))
                        {
                            Add(target);
                            grew = true;
                        }
                    }
                }
            }
            foreach (var e in _entities.Values)
            {
                ReadAttributes(e);
            }
            MarkUnread(compilation);
            foreach (var (tree, inv, builder, of) in configuration)
            {
                ReadFluent(compilation, tree, inv, builder, of);
            }
            foreach (var e in _entities.Values)
            {
                if (e.Key.Count == 0 && !e.Unread)
                {
                    e.AddKey(ConventionKey(e.Type));
                }
                foreach (var p in PropertiesOf(e.Type))
                {
                    if (NavigationTarget(p.Type, out bool many) is INamedTypeSymbol target && _entities.ContainsKey(target))
                    {
                        (many ? e.Collections : e.References).Add(p);
                    }
                }
            }
            Inherit();
            ReadRelationships();
        }

        // ------------------------------------------------------------------ relationships

        /// <summary>Navigations the fluent configuration names in a way this reading doesn't follow: no foreign key for them.</summary>
        private readonly HashSet<IPropertySymbol> _unreadNavigations = new HashSet<IPropertySymbol>(SymbolEqualityComparer.Default);

        /// <summary>Entities with a relationship configured by name (HasOne("Customer")): no foreign key for any of their navigations.</summary>
        private readonly HashSet<ITypeSymbol> _unreadEntities = new HashSet<ITypeSymbol>(SymbolEqualityComparer.Default);

        /// <summary>From the fluent configuration: a reference navigation's foreign key, and a collection's inverse reference.</summary>
        private readonly Dictionary<IPropertySymbol, IPropertySymbol> _fluentKeys = new Dictionary<IPropertySymbol, IPropertySymbol>(SymbolEqualityComparer.Default);
        private readonly Dictionary<IPropertySymbol, IPropertySymbol> _fluentInverse = new Dictionary<IPropertySymbol, IPropertySymbol>(SymbolEqualityComparer.Default);

        /// <summary>Each navigation's inverse, where the model says: the one paired with it, or null where it has none (WithMany(), WithOne()).</summary>
        private readonly Dictionary<IPropertySymbol, IPropertySymbol> _inverses = new Dictionary<IPropertySymbol, IPropertySymbol>(SymbolEqualityComparer.Default);

        private readonly HashSet<IPropertySymbol> _oneToOne = new HashSet<IPropertySymbol>(SymbolEqualityComparer.Default);

        /// <summary>One-to-one ends whose unique index is filtered by what the dependent's query filter says of every row.</summary>
        private readonly HashSet<IPropertySymbol> _oneToOneWhereFiltered = new HashSet<IPropertySymbol>(SymbolEqualityComparer.Default);

        /// <summary>Is the navigation an end of a one-to-one: among all rows, or (filtered) among those the query filters keep?</summary>
        public bool OneToOne(IPropertySymbol nav, bool filtered = false) =>
            _oneToOne.Contains(nav.OriginalDefinition) || filtered && _oneToOneWhereFiltered.Contains(nav.OriginalDefinition);

        /// <summary>Does the model say what a navigation's inverse is (null: it has none)?</summary>
        public bool KnownInverse(IPropertySymbol nav, out IPropertySymbol inverse) => _inverses.TryGetValue(nav.OriginalDefinition, out inverse);

        private void Pair(IPropertySymbol a, IPropertySymbol b)
        {
            if (a != null)
            {
                _inverses.TryAdd(a.OriginalDefinition, b?.OriginalDefinition);
            }
            if (b != null)
            {
                _inverses.TryAdd(b.OriginalDefinition, a?.OriginalDefinition);
            }
        }

        /// <summary>
        /// The foreign keys of navigations, as EF finds them: the fluent HasOne/HasMany ... HasForeignKey, [ForeignKey] on
        /// the navigation or on the key, or EF's convention (the navigation's name, or the principal's, then the key's
        /// name or Id), for a dependent with one navigation to the principal. A collection's is its inverse
        /// reference's: the one the configuration pairs it with, or the dependent's only navigation to the principal.
        /// Only to a principal of one key property, and only where nothing else (a principal key, [InverseProperty])
        /// could make it another.
        /// </summary>
        private void ReadRelationships()
        {
            // (EF's convention: two entities each with one reference navigation to the other, configured no other way,
            // are the ends of a one-to-one)
            foreach (var a in _entities.Values.Where(x => !_unreadEntities.Contains(x.Type)))
            {
                foreach (var nav in a.References)
                {
                    var b = EntityOf(nav.Type);
                    var back = b?.References.Where(r => ReferenceEquals(EntityOf(r.Type), a)).ToList();
                    if (b == null || ReferenceEquals(a, b) || back.Count != 1 || a.References.Count(r => ReferenceEquals(EntityOf(r.Type), b)) != 1 ||
                        b.Collections.Any(c => ReferenceEquals(EntityOf(NavigationTarget(c.Type, out _)), a)) || a.Collections.Any(c => ReferenceEquals(EntityOf(NavigationTarget(c.Type, out _)), b)) ||
                        new[] { nav, back[0] }.Any(x => _inverses.ContainsKey(x.OriginalDefinition) || _unreadNavigations.Contains(x) || Has(x, "InversePropertyAttribute")))
                    {
                        continue;
                    }
                    _oneToOne.Add(nav.OriginalDefinition);
                    _oneToOne.Add(back[0].OriginalDefinition);
                }
            }
            foreach (var d in _entities.Values.Where(x => !_unreadEntities.Contains(x.Type)))
            {
                foreach (var nav in d.References)
                {
                    if (_unreadNavigations.Contains(nav) || Has(nav, "InversePropertyAttribute") || _unreadEntities.Contains(nav.Type.OriginalDefinition))
                    {
                        continue;
                    }
                    var p = EntityOf(nav.Type);
                    if (p == null || p.Key.Count != 1)
                    {
                        continue;
                    }
                    var key = p.Key[0];
                    var props = PropertiesOf(d.Type).ToList();
                    IPropertySymbol fk = _fluentKeys.TryGetValue(nav, out var fluent) ? fluent : null;
                    if (fk == null && Attribute(nav, "ForeignKeyAttribute") is string named)
                    {
                        // (a composite key, "A,B", isn't followed)
                        fk = props.FirstOrDefault(x => x.Name == named);
                        if (fk == null)
                        {
                            continue;
                        }
                    }
                    fk ??= props.FirstOrDefault(x => Attribute(x, "ForeignKeyAttribute") == nav.Name);
                    if (fk == null && d.References.Count(r => ReferenceEquals(EntityOf(r.Type), p)) == 1)
                    {
                        foreach (var name in new[] { nav.Name + key.Name, nav.Name + "Id", p.Type.Name + key.Name, p.Type.Name + "Id" })
                        {
                            if ((fk = props.FirstOrDefault(x => string.Equals(x.Name, name, StringComparison.OrdinalIgnoreCase))) != null)
                            {
                                break;
                            }
                        }
                    }
                    if (fk == null)
                    {
                        continue;
                    }
                    var t = fk.Type is INamedTypeSymbol { OriginalDefinition.SpecialType: SpecialType.System_Nullable_T } n ? n.TypeArguments[0] : fk.Type;
                    if (SymbolEqualityComparer.Default.Equals(t, key.Type))
                    {
                        d.ForeignKeys[nav] = fk;
                    }
                }
            }
            foreach (var p in _entities.Values.Where(x => !_unreadEntities.Contains(x.Type)))
            {
                foreach (var nav in p.Collections)
                {
                    if (_unreadNavigations.Contains(nav) || Has(nav, "InversePropertyAttribute"))
                    {
                        continue;
                    }
                    var d = EntityOf(NavigationTarget(nav.Type, out _));
                    if (d == null)
                    {
                        continue;
                    }
                    var inverse = _fluentInverse.TryGetValue(nav, out var paired) ? paired : null;
                    if (inverse == null)
                    {
                        var back = d.References.Where(r => ReferenceEquals(EntityOf(r.Type), p)).ToList();
                        int many = p.Collections.Count(c => ReferenceEquals(EntityOf(NavigationTarget(c.Type, out _)), d));
                        if (back.Count == 1 && many == 1 && !_fluentInverse.Values.Contains(back[0], SymbolEqualityComparer.Default))
                        {
                            inverse = back[0];
                        }
                    }
                    if (inverse != null)
                    {
                        Pair(nav, inverse);
                    }
                    if (inverse != null && d.ForeignKeys.TryGetValue(inverse, out var fk))
                    {
                        p.CollectionKeys[nav] = fk;
                    }
                    else if (inverse == null && p.Key.Count == 1 && !d.References.Any(r => ReferenceEquals(EntityOf(r.Type), p)) &&
                             p.Collections.Count(c => ReferenceEquals(EntityOf(NavigationTarget(c.Type, out _)), d)) == 1 &&
                             !_fluentInverse.ContainsKey(nav) && !_fluentKeys.Keys.Any(k => ReferenceEquals(EntityOf(k.ContainingType), d)))
                    {
                        // (no navigation back: EF's convention, the principal's name and its key's, or Id)
                        var key = p.Key[0];
                        var props = PropertiesOf(d.Type).ToList();
                        var named = new[] { p.Type.Name + key.Name, p.Type.Name + "Id" }
                            .Select(n => props.FirstOrDefault(x => string.Equals(x.Name, n, StringComparison.OrdinalIgnoreCase))).FirstOrDefault(x => x != null);
                        var t = named?.Type is INamedTypeSymbol { OriginalDefinition.SpecialType: SpecialType.System_Nullable_T } nt ? nt.TypeArguments[0] : named?.Type;
                        if (named != null && SymbolEqualityComparer.Default.Equals(t, key.Type))
                        {
                            p.CollectionKeys[nav] = named;
                        }
                    }
                }
            }
        }

        /// <summary>The string an attribute of this name is given ([ForeignKey("CustomerId")]), if any.</summary>
        private static string Attribute(ISymbol s, string name) =>
            s.GetAttributes().FirstOrDefault(a => a.AttributeClass?.Name == name)?.ConstructorArguments.FirstOrDefault().Value as string;

        /// <summary>
        /// HasOne(x => x.Nav) or HasMany(x => x.Navs), then WithMany/WithOne, HasForeignKey: which navigations pair, and
        /// the foreign key. Anything else on the chain (a principal key, a key by name, a one-to-one's key) leaves both
        /// navigations without one.
        /// </summary>
        private void ReadRelationship(SemanticModel model, Entity e, string name, ExpressionSyntax arg, List<(string name, InvocationExpressionSyntax call)> next)
        {
            if (arg != null && !(arg is LambdaExpressionSyntax))
            {
                // (by name, or by type: HasOne("Customer"), HasMany(typeof(Order)): any of the entity's navigations)
                _unreadEntities.Add(e.Type.OriginalDefinition);
                return;
            }
            var first = Nav(arg, model);
            var with = next.FirstOrDefault(x => x.name == "WithMany" || x.name == "WithOne");
            var second = with.call == null ? null : Nav(with.call.ArgumentList.Arguments.FirstOrDefault()?.Expression, model);
            var reference = name == "HasOne" ? first : second;
            var collection = name == "HasMany" ? first : with.name == "WithMany" ? second : null;
            // (the two ends, each the other's inverse; WithMany() and WithOne() say the first has none)
            if (with.call != null && first != null)
            {
                Pair(first, second);
            }
            // (a one-to-one's ends: a row of either has one row of the other at most, by its unique foreign key, #130)
            if (name == "HasOne" && with.name == "WithOne")
            {
                foreach (var end in new[] { first, second }.Where(x => x != null))
                {
                    _oneToOne.Add(end.OriginalDefinition);
                }
            }
            var key = next.FirstOrDefault(x => x.name == "HasForeignKey").call;
            bool unread = first == null && arg != null || next.Any(x => x.name == "HasPrincipalKey") || name == "HasOne" && with.name == "WithOne" ||
                          name == "HasMany" && with.name == "WithMany";
            IPropertySymbol fk = null;
            if (key != null)
            {
                var k = key.ArgumentList.Arguments.FirstOrDefault()?.Expression;
                fk = (key.Expression as MemberAccessExpressionSyntax)?.Name is GenericNameSyntax || key.ArgumentList.Arguments.Count != 1 ? null : Nav(k, model);
                if (fk == null)
                {
                    unread = true;
                }
            }
            if (unread)
            {
                foreach (var nav in new[] { first, second })
                {
                    if (nav != null)
                    {
                        _unreadNavigations.Add(nav);
                    }
                }
                return;
            }
            if (reference != null && fk != null)
            {
                _fluentKeys[reference] = fk;
            }
            if (reference != null && collection != null)
            {
                _fluentInverse[collection] = reference;
            }
        }

        private IPropertySymbol Nav(ExpressionSyntax x, SemanticModel model) =>
            x is SimpleLambdaExpressionSyntax { Body: MemberAccessExpressionSyntax m } ? model.GetSymbolInfo(m).Symbol as IPropertySymbol : null;

        /// <summary>
        /// Owned types and complex types: their properties are columns of their owner, which EF always loads with it. They
        /// are neither entities nor navigations here: nothing is said of them.
        /// </summary>
        private readonly HashSet<ITypeSymbol> _owned = new HashSet<ITypeSymbol>(SymbolEqualityComparer.Default);

        public bool IsOwned(ITypeSymbol t) => t != null && _owned.Contains(t.OriginalDefinition);

        private static readonly HashSet<string> OwningCalls = new HashSet<string>
        { "OwnsOne", "OwnsMany", "Owned", "ComplexProperty", "ComplexCollection", "ComplexProperties" };

        /// <summary>[Owned], [ComplexType], and OwnsOne/OwnsMany/ComplexProperty (of a navigation, or a type) or Owned&lt;T&gt;() anywhere.</summary>
        private void ReadOwned(Compilation compilation, IReadOnlyList<SyntaxTree> trees)
        {
            foreach (var tree in trees)
            {
                var model = compilation.ModelOf(tree);
                foreach (var decl in tree.GetRoot().DescendantNodes().OfType<TypeDeclarationSyntax>())
                {
                    if (model.GetDeclaredSymbol(decl) is INamedTypeSymbol t && (Has(t, "OwnedAttribute") || Has(t, "ComplexTypeAttribute")))
                    {
                        _owned.Add(t.OriginalDefinition);
                    }
                }
                foreach (var inv in tree.GetRoot().DescendantNodes().OfType<InvocationExpressionSyntax>())
                {
                    var name = inv.Expression is MemberAccessExpressionSyntax ma ? ma.Name : inv.Expression as SimpleNameSyntax;
                    if (name == null || !OwningCalls.Contains(name.Identifier.Text))
                    {
                        continue;
                    }
                    if (name is GenericNameSyntax g)
                    {
                        foreach (var a in g.TypeArgumentList.Arguments)
                        {
                            if (model.GetTypeInfo(a).Type is ITypeSymbol owned)
                            {
                                _owned.Add(owned.OriginalDefinition);
                            }
                        }
                    }
                    if (inv.ArgumentList.Arguments.FirstOrDefault()?.Expression is SimpleLambdaExpressionSyntax { Body: MemberAccessExpressionSyntax m } &&
                        model.GetSymbolInfo(m).Symbol is IPropertySymbol p)
                    {
                        _owned.Add((NavigationTarget(p.Type, out _) ?? p.Type).OriginalDefinition);
                    }
                }
            }
        }

        /// <summary>
        /// A type's instance properties, its source base classes' too (an entity's columns and navigations, declared
        /// where it inherits them), each once.
        /// </summary>
        internal static IEnumerable<IPropertySymbol> PropertiesOf(INamedTypeSymbol t)
        {
            var seen = new HashSet<string>();
            // (and a library base's, as EF maps them: Identity's IdentityUser<TKey>)
            bool entity = t.Locations.Any(l => l.IsInSource) || MetadataEntities.IsUserClass(t) || LibraryEntities?.Contains(t.OriginalDefinition) == true;
            for (var b = t; b != null && b.SpecialType != SpecialType.System_Object && entity; b = b.BaseType)
            {
                foreach (var p in b.GetMembers().OfType<IPropertySymbol>().Where(p => !p.IsStatic))
                {
                    if (seen.Add(p.Name))
                    {
                        yield return p;
                    }
                }
            }
        }

        /// <summary>
        /// What a type inherits of its base entity's (EF reads them from the root of the hierarchy): its key, query
        /// filters, unique indexes and concurrency tokens, the base's first so that a chain inherits from its root.
        /// </summary>
        private void Inherit()
        {
            foreach (var e in _entities.Values.OrderBy(x => Depth(x.Type)))
            {
                Entity b = null;
                for (var up = e.Type.BaseType; up != null && b == null; up = up.BaseType)
                {
                    b = EntityOf(up);
                }
                if (b == null)
                {
                    continue;
                }
                if (b.Key.Count > 0)
                {
                    e.Key = new List<IPropertySymbol>(b.Key);
                }
                foreach (var filter in b.Filters)
                {
                    if (!e.Filters.Contains(filter))
                    {
                        e.AddFilter(filter);
                    }
                }
                foreach (var u in b.Unique)
                {
                    e.AddUnique(u);
                }
                e.Alternate.AddRange(b.Alternate);
                foreach (var token in b.Tokens)
                {
                    if (!e.Tokens.Contains(token))
                    {
                        e.AddToken(token);
                    }
                }
                foreach (var v in b.RowVersions)
                {
                    e.AddRowVersion(v);
                }
            }
        }

        private int Depth(ITypeSymbol x)
        {
            int d = 0;
            for (var b = x.BaseType; b != null; b = b.BaseType)
            {
                d++;
            }
            return d;
        }

        public bool IsContextType(ITypeSymbol t)
        {
            for (var b = t as INamedTypeSymbol; b != null; b = b.BaseType)
            {
                if (SymbolEqualityComparer.Default.Equals(b.OriginalDefinition, DbContextType))
                {
                    return true;
                }
            }
            return false;
        }

        /// <summary>The entity type of the model, or null.</summary>
        public Entity EntityOf(ITypeSymbol t) => t != null && _entities.TryGetValue(t.OriginalDefinition, out var e) ? e : null;

        public IEnumerable<Entity> Entities => _entities.Values;

        private void Add(INamedTypeSymbol t)
        {
            if (!_owned.Contains(t.OriginalDefinition) && !_entities.ContainsKey(t.OriginalDefinition))
            {
                _entities[t.OriginalDefinition] = new Entity { Type = t };
            }
        }

        /// <summary>A context's library bases but DbContext (IdentityDbContext&lt;AppUser, ...&gt;), as the context instantiates them.</summary>
        private IEnumerable<INamedTypeSymbol> LibraryContexts(INamedTypeSymbol t)
        {
            for (var b = t.BaseType; b != null && !SymbolEqualityComparer.Default.Equals(b.OriginalDefinition, DbContextType); b = b.BaseType)
            {
                if (!b.Locations.Any(l => l.IsInSource))
                {
                    yield return b;
                }
            }
        }

        /// <summary>The entity types a class's own DbSet&lt;T&gt; properties name.</summary>
        private static IEnumerable<INamedTypeSymbol> DbSetsOf(INamedTypeSymbol t) =>
            t.GetMembers().OfType<IPropertySymbol>().Select(p => p.Type).OfType<INamedTypeSymbol>()
                .Where(set => set.Name == "DbSet" && set.TypeArguments.Length == 1).Select(set => set.TypeArguments[0]).OfType<INamedTypeSymbol>();

        /// <summary>Does the library context configure a model of its own (declare OnModelCreating)?</summary>
        private static bool ConfiguresModel(INamedTypeSymbol b) => b.GetMembers("OnModelCreating").OfType<IMethodSymbol>().Any(m => !m.IsAbstract);

        /// <summary>The Spec library's model of a library context (a [ModelOf] class), or null.</summary>
        private static INamedTypeSymbol ModelOf(Compilation compilation, INamedTypeSymbol context)
        {
            var attribute = compilation.GetTypeByMetadataName("CsVerify.Ef.ModelOfAttribute");
            if (attribute == null)
            {
                return null;
            }
            return Types(attribute.ContainingAssembly.GlobalNamespace).FirstOrDefault(m => m.Arity == context.Arity && m.GetAttributes().Any(a =>
                SymbolEqualityComparer.Default.Equals(a.AttributeClass, attribute) && a.ConstructorArguments.FirstOrDefault().Value is INamedTypeSymbol of &&
                SymbolEqualityComparer.Default.Equals(of.OriginalDefinition, context.OriginalDefinition)));
        }

        private static IEnumerable<INamedTypeSymbol> Types(INamespaceSymbol ns) =>
            ns.GetTypeMembers().Concat(ns.GetNamespaceMembers().SelectMany(Types));

        /// <summary>
        /// The calls on an entity's builder in the Spec library's models of the contexts' library bases, each builder as
        /// the context instantiates the base (EntityTypeBuilder&lt;TUser&gt; as EntityTypeBuilder&lt;AppUser&gt;).
        /// </summary>
        private IEnumerable<(SyntaxTree tree, InvocationExpressionSyntax inv, INamedTypeSymbol builder, INamedTypeSymbol configuration)> LibraryModels(
            Compilation compilation, IReadOnlyList<INamedTypeSymbol> sourceTypes)
        {
            foreach (var b in sourceTypes.Where(t => IsContextType(t)).SelectMany(LibraryContexts).Where(ConfiguresModel).Distinct<INamedTypeSymbol>(SymbolEqualityComparer.Default))
            {
                if (!(ModelOf(compilation, b) is INamedTypeSymbol m) ||
                    !(m.GetMembers("OnModelCreating").OfType<IMethodSymbol>().FirstOrDefault()?.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() is MethodDeclarationSyntax decl))
                {
                    continue;
                }
                _modeled.Add(b);
                var model = compilation.ModelOf(decl.SyntaxTree);
                foreach (var inv in decl.DescendantNodes().OfType<InvocationExpressionSyntax>())
                {
                    if (inv.Expression is MemberAccessExpressionSyntax ma && model.GetTypeInfo(ma.Expression).Type is INamedTypeSymbol { Name: "EntityTypeBuilder", TypeArguments.Length: 1 } builder &&
                        builder.TypeArguments[0] is ITypeParameterSymbol tp && tp.Ordinal < b.TypeArguments.Length && b.TypeArguments[tp.Ordinal] is INamedTypeSymbol entity &&
                        IsSourceClass(entity, sourceTypes))
                    {
                        Add(entity);
                        _stubbed.Add(entity);
                        yield return (decl.SyntaxTree, inv, builder.OriginalDefinition.Construct(entity), null);
                    }
                }
            }
        }

        /// <summary>The library contexts the Spec library has a model of, and the entities those models configure.</summary>
        private readonly HashSet<INamedTypeSymbol> _modeled = new HashSet<INamedTypeSymbol>(SymbolEqualityComparer.Default);
        private readonly HashSet<INamedTypeSymbol> _stubbed = new HashSet<INamedTypeSymbol>(SymbolEqualityComparer.Default);

        /// <summary>
        /// The entities a library context's OnModelCreating may configure that no model describes: its type arguments and
        /// its own DbSets' (where it declares OnModelCreating), but those a model of the Spec library's configures.
        /// </summary>
        private void MarkUnread(Compilation compilation)
        {
            foreach (var b in Contexts.SelectMany(LibraryContexts).Where(ConfiguresModel))
            {
                foreach (var t in b.TypeArguments.OfType<INamedTypeSymbol>().Concat(DbSetsOf(b)))
                {
                    if (EntityOf(t) is Entity e && !(_modeled.Contains(b) && _stubbed.Contains(e.Type)))
                    {
                        e.Unread = true;
                    }
                }
            }
        }

        private static IEnumerable<ISymbol> AllMembers(INamedTypeSymbol t)
        {
            for (var b = t; b != null && b.Locations.Any(l => l.IsInSource); b = b.BaseType)
            {
                foreach (var m in b.GetMembers())
                {
                    yield return m;
                }
            }
        }

        /// <summary>A class of the program's, or of a referenced assembly of its own (a domain project's), that may be an entity.</summary>
        private static bool IsSourceClass(INamedTypeSymbol t, IReadOnlyList<INamedTypeSymbol> sourceTypes) =>
            t.TypeKind == TypeKind.Class && (sourceTypes.Contains(t.OriginalDefinition, SymbolEqualityComparer.Default) || MetadataEntities.IsUserClass(t));

        /// <summary>The entity a navigation of this type leads to: the type itself, or the element of a collection of it.</summary>
        internal static INamedTypeSymbol NavigationTarget(ITypeSymbol t, out bool many)
        {
            many = false;
            if (t is INamedTypeSymbol n && n.IsGenericType && n.TypeArguments.Length == 1 &&
                (n.Name == "ICollection" || n.Name == "IList" || n.Name == "List" || n.Name == "HashSet" || n.Name == "IEnumerable" || n.Name == "ISet" || n.Name == "IReadOnlyCollection" || n.Name == "IReadOnlyList") &&
                n.ContainingNamespace?.ToDisplayString().StartsWith("System.Collections") == true)
            {
                many = true;
                return n.TypeArguments[0] as INamedTypeSymbol;
            }
            return t?.TypeKind == TypeKind.Class && t.SpecialType == SpecialType.None && t.ContainingNamespace?.ToDisplayString().StartsWith("System") != true
                ? t as INamedTypeSymbol : null;
        }

        private static readonly HashSet<string> KeyTypes = new HashSet<string> { "Int32", "Int64", "Int16", "Guid", "String", "Byte" };

        /// <summary>EF's convention: a property named Id, or the type's name and Id.</summary>
        private static IEnumerable<IPropertySymbol> ConventionKey(INamedTypeSymbol t)
        {
            var props = PropertiesOf(t).Where(p => KeyTypes.Contains(p.Type.Name)).ToList();
            var key = props.FirstOrDefault(p => string.Equals(p.Name, "Id", StringComparison.OrdinalIgnoreCase))
                   ?? props.FirstOrDefault(p => string.Equals(p.Name, t.Name + "Id", StringComparison.OrdinalIgnoreCase));
            return key == null ? Array.Empty<IPropertySymbol>() : new[] { key };
        }

        private static bool Has(ISymbol s, string name) => s.GetAttributes().Any(a => a.AttributeClass?.Name == name);

        private void ReadAttributes(Entity e)
        {
            var props = PropertiesOf(e.Type).ToList();
            var keys = props.Where(p => Has(p, "KeyAttribute")).ToList();
            if (keys.Count > 0)
            {
                e.Key = keys;
            }
            foreach (var p in props)
            {
                if (Has(p, "ConcurrencyCheckAttribute"))
                {
                    e.AddToken(p);
                }
                if (Has(p, "TimestampAttribute"))
                {
                    e.AddToken(p);
                    e.AddRowVersion(p);
                }
            }
            // [Index(nameof(A), nameof(B), IsUnique = true)] on the class
            foreach (var a in e.Type.GetAttributes().Where(a => a.AttributeClass?.Name == "IndexAttribute"))
            {
                bool unique = a.NamedArguments.Any(n => n.Key == "IsUnique" && n.Value.Value is true);
                if (!unique)
                {
                    continue;
                }
                var names = a.ConstructorArguments.SelectMany(c => c.Kind == TypedConstantKind.Array ? (IEnumerable<TypedConstant>)c.Values : new[] { c }).Select(c => c.Value as string).ToList();
                var set = names.Select(n => props.FirstOrDefault(p => p.Name == n)).ToList();
                if (set.Count > 0 && set.All(p => p != null))
                {
                    e.AddUnique(set);
                }
            }
        }

        /// <summary>
        /// The calls on an entity type's builder (EntityTypeBuilder&lt;T&gt;) in the model's configuration: OnModelCreating
        /// of the contexts, and the Configure methods of IEntityTypeConfiguration&lt;T&gt;.
        /// </summary>
        private IEnumerable<(SyntaxTree tree, InvocationExpressionSyntax inv, INamedTypeSymbol builder)> Configuration(Compilation compilation, IReadOnlyList<SyntaxTree> trees)
        {
            foreach (var tree in trees)
            {
                var model = compilation.ModelOf(tree);
                foreach (var method in tree.GetRoot().DescendantNodes().OfType<MethodDeclarationSyntax>())
                {
                    if (!(method.Identifier.Text == "OnModelCreating" || method.Identifier.Text == "Configure"))
                    {
                        continue;
                    }
                    foreach (var inv in method.DescendantNodes().OfType<InvocationExpressionSyntax>())
                    {
                        if (!(inv.Expression is MemberAccessExpressionSyntax ma))
                        {
                            continue;
                        }
                        if (model.GetTypeInfo(ma.Expression).Type is INamedTypeSymbol builder && builder.Name == "EntityTypeBuilder" && builder.TypeArguments.Length == 1)
                        {
                            yield return (tree, inv, builder);
                        }
                    }
                }
            }
        }

        /// <summary>
        /// The Configure of an IEntityTypeConfiguration&lt;E&gt; that a class of the program's inherits from a generic base
        /// (KeyedConfiguration&lt;T&gt;): the calls on its builder, as on E's, with the members the class overrides.
        /// </summary>
        private IEnumerable<(SyntaxTree tree, InvocationExpressionSyntax inv, INamedTypeSymbol builder, INamedTypeSymbol configuration)> GenericConfiguration(
            Compilation compilation, IReadOnlyList<INamedTypeSymbol> sourceTypes)
        {
            foreach (var c in sourceTypes.Where(t => t.TypeKind == TypeKind.Class && !t.IsAbstract))
            {
                foreach (var i in c.AllInterfaces.Where(i => i.Name == "IEntityTypeConfiguration" && i.TypeArguments.Length == 1 && i.TypeArguments[0] is INamedTypeSymbol))
                {
                    if (!(i.GetMembers("Configure").OfType<IMethodSymbol>().FirstOrDefault() is IMethodSymbol configure) ||
                        !(c.FindImplementationForInterfaceMember(configure) is IMethodSymbol impl) || !impl.ContainingType.IsGenericType ||
                        !(impl.OriginalDefinition.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() is MethodDeclarationSyntax decl) ||
                        !(impl.Parameters.FirstOrDefault()?.Type is INamedTypeSymbol { Name: "EntityTypeBuilder" } builder))
                    {
                        continue;
                    }
                    var model = compilation.ModelOf(decl.SyntaxTree);
                    foreach (var inv in decl.DescendantNodes().OfType<InvocationExpressionSyntax>())
                    {
                        if (inv.Expression is MemberAccessExpressionSyntax ma && model.GetTypeInfo(ma.Expression).Type is INamedTypeSymbol { Name: "EntityTypeBuilder", TypeArguments.Length: 1 })
                        {
                            yield return (decl.SyntaxTree, inv, builder, c);
                        }
                    }
                }
            }
        }

        /// <summary>
        /// What an argument stands for: itself, or, a member a configuration class overrides (a generic base's abstract
        /// Key), the lambda its override's expression body is, with that body's model.
        /// </summary>
        private static (SemanticModel model, ExpressionSyntax arg) Resolve(Compilation compilation, SemanticModel model, ExpressionSyntax arg, INamedTypeSymbol configuration)
        {
            if (configuration == null || arg == null || arg is LambdaExpressionSyntax || !(model.GetSymbolInfo(arg).Symbol is IPropertySymbol member) || !(member.IsAbstract || member.IsVirtual))
            {
                return (model, arg);
            }
            for (var k = configuration; k != null; k = k.BaseType)
            {
                foreach (var p in k.GetMembers(member.Name).OfType<IPropertySymbol>().Where(p => p.IsOverride))
                {
                    for (var o = p.OverriddenProperty; o != null; o = o.OverriddenProperty)
                    {
                        if (SymbolEqualityComparer.Default.Equals(o.OriginalDefinition, member.OriginalDefinition) &&
                            p.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() is PropertyDeclarationSyntax { ExpressionBody.Expression: LambdaExpressionSyntax lambda })
                        {
                            return (compilation.ModelOf(lambda.SyntaxTree), lambda);
                        }
                    }
                }
            }
            return (model, arg);
        }

        /// <summary>
        /// The properties HasKey names by string: a constant (nameof(T.P), "P"), or the name of the member a key lambda
        /// selects (((MemberExpression)Key.Body).Member.Name).
        /// </summary>
        private static List<IPropertySymbol> Named(Compilation compilation, SemanticModel model, InvocationExpressionSyntax inv, Entity e, INamedTypeSymbol configuration)
        {
            var props = PropertiesOf(e.Type).ToList();
            var named = new List<IPropertySymbol>();
            foreach (var a in inv.ArgumentList.Arguments.Select(x => x.Expression))
            {
                IPropertySymbol p = null;
                if (model.GetConstantValue(a) is { HasValue: true, Value: string name })
                {
                    p = props.FirstOrDefault(x => x.Name == name);
                }
                else if (a is MemberAccessExpressionSyntax { Name.Identifier.Text: "Name", Expression: MemberAccessExpressionSyntax { Name.Identifier.Text: "Member" } member } &&
                         Unparenthesized(member.Expression) is CastExpressionSyntax cast && Unparenthesized(cast.Expression) is MemberAccessExpressionSyntax { Name.Identifier.Text: "Body" } body)
                {
                    var (km, key) = Resolve(compilation, model, body.Expression, configuration);
                    p = Properties(km, key, e) is List<IPropertySymbol> { Count: 1 } one ? one[0] : null;
                }
                if (p == null)
                {
                    return null;
                }
                named.Add(p);
            }
            return named.Count > 0 ? named : null;
        }

        private static ExpressionSyntax Unparenthesized(ExpressionSyntax x)
        {
            while (x is ParenthesizedExpressionSyntax p)
            {
                x = p.Expression;
            }
            return x;
        }

        /// <summary>One call on an entity type's builder, and what is called on its result.</summary>
        private void ReadFluent(Compilation compilation, SyntaxTree tree, InvocationExpressionSyntax inv, INamedTypeSymbol builder, INamedTypeSymbol configuration = null)
        {
            var model = compilation.ModelOf(tree);
            var e = EntityOf(builder.TypeArguments[0]);
            if (e == null)
            {
                return;
            }
            var name = ((MemberAccessExpressionSyntax)inv.Expression).Name.Identifier.Text;
            var (argModel, arg) = Resolve(compilation, model, inv.ArgumentList.Arguments.FirstOrDefault()?.Expression, configuration);
            // what is called on the result: .IsUnique(), .IsConcurrencyToken(), .IsRowVersion()
            var next = new List<(string name, InvocationExpressionSyntax call)>();
            for (SyntaxNode n = inv; n.Parent is MemberAccessExpressionSyntax up && up.Parent is InvocationExpressionSyntax call; n = call)
            {
                next.Add((up.Name.Identifier.Text, call));
            }
            switch (name)
            {
                case "HasKey":
                    if ((Properties(argModel, arg, e) ?? Named(compilation, model, inv, e, configuration)) is List<IPropertySymbol> key)
                    {
                        e.Key = key;
                        e.Configured.UnionWith(key.Select(x => x.OriginalDefinition));
                    }
                    else
                    {
                        Unread.Add((inv.GetLocation(), "a key the verifier can't read"));
                    }
                    break;
                case "HasAlternateKey":
                    // (by the properties, or their names: HasAlternateKey("ExternalId"), #129)
                    if ((Properties(argModel, arg, e) ?? Named(compilation, model, inv, e, configuration)) is List<IPropertySymbol> alt)
                    {
                        e.AddUnique(alt);
                        e.Alternate.Add(alt);
                        e.Configured.UnionWith(alt.Select(x => x.OriginalDefinition));
                    }
                    break;
                case "HasIndex":
                    // (a filtered one, unique among the rows the filter keeps: only a column's IS NOT NULL, which a row a
                    // value not null fixes meets, #130)
                    if (Called("IsUnique", out var isUnique, next) && !(isUnique.ArgumentList.Arguments.FirstOrDefault()?.Expression is LiteralExpressionSyntax l && l.IsKind(SyntaxKind.FalseLiteralExpression))
                        && (Properties(argModel, arg, e) ?? Named(compilation, model, inv, e, configuration)) is List<IPropertySymbol> index &&
                        (!Called("HasFilter", out var indexFilter, next) || NotNullFilter(indexFilter, index)))
                    {
                        e.AddUnique(index);
                    }
                    break;
                case "Property":
                    // (a shadow column: Property<T>("Name") of a name the class has no property of)
                    if (arg is LiteralExpressionSyntax { Token.Value: string shadow } && PropertiesOf(e.Type).All(x => x.Name != shadow) &&
                        model.GetSymbolInfo(inv).Symbol is IMethodSymbol { TypeArguments: [var shadowType] })
                    {
                        e.Shadow[shadow] = shadowType;
                        break;
                    }
                    if ((Properties(argModel, arg, e) ?? Named(compilation, model, inv, e, configuration)) is List<IPropertySymbol> p && p.Count == 1)
                    {
                        e.Configured.Add(p[0].OriginalDefinition);
                        if (Called("HasConversion", out _, next))
                        {
                            e.Converted.Add(p[0].OriginalDefinition);
                        }
                        if (Called("IsRequired", out var required, next) &&
                            !(required.ArgumentList.Arguments.FirstOrDefault()?.Expression is LiteralExpressionSyntax r && r.IsKind(SyntaxKind.FalseLiteralExpression)))
                        {
                            e.Required.Add(p[0].OriginalDefinition);
                        }
                        if (Called("IsRowVersion", out _, next))
                        {
                            if (!e.Tokens.Contains(p[0]))
                            {
                                e.AddToken(p[0]);
                            }
                            e.AddRowVersion(p[0]);
                        }
                        else if (Called("IsConcurrencyToken", out var token, next) &&
                                 !(token.ArgumentList.Arguments.FirstOrDefault()?.Expression is LiteralExpressionSyntax f && f.IsKind(SyntaxKind.FalseLiteralExpression)) &&
                                 !e.Tokens.Contains(p[0]))
                        {
                            e.AddToken(p[0]);
                        }
                    }
                    break;
                case "HasOne":
                case "HasMany":
                    ReadRelationship(model, e, name, arg, next);
                    break;
                case "OwnsOne":
                case "OwnsMany":
                    if (arg is SimpleLambdaExpressionSyntax { Body: MemberAccessExpressionSyntax owned } && model.GetSymbolInfo(owned).Symbol is IPropertySymbol ownedNav)
                    {
                        _unreadNavigations.Add(ownedNav);
                    }
                    break;
                case "HasQueryFilter":
                    if (arg is LambdaExpressionSyntax lambda && model.GetOperation(lambda) is IAnonymousFunctionOperation filter)
                    {
                        e.AddFilter(filter);
                    }
                    // (a filter that isn't a lambda only removes rows: it says nothing, which is what is assumed)
                    break;
            }
        }

        /// <summary>HasFilter("[C] IS NOT NULL") of one of the index's columns (bracketed, quoted or bare).</summary>
        private static bool NotNullFilter(InvocationExpressionSyntax filter, List<IPropertySymbol> index) =>
            filter.ArgumentList.Arguments.Count == 1 && filter.ArgumentList.Arguments[0].Expression is LiteralExpressionSyntax { Token.Value: string sql } &&
            System.Text.RegularExpressions.Regex.Match(sql, @"^\s*[\[""`]?(\w+)[\]""`]?\s+IS\s+NOT\s+NULL\s*$", System.Text.RegularExpressions.RegexOptions.IgnoreCase) is { Success: true } m &&
            index.Any(c => c.Name == m.Groups[1].Value);

        private bool Called(string m, out InvocationExpressionSyntax call, List<(string name, InvocationExpressionSyntax call)> next)
        {
            call = next.FirstOrDefault(x => x.name == m).call;
            return call != null;
        }

        /// <summary>The properties a lambda names: x => x.P, or x => new { x.A, x.B }.</summary>
        private static List<IPropertySymbol> Properties(SemanticModel model, ExpressionSyntax arg, Entity e)
        {
            if (!(arg is SimpleLambdaExpressionSyntax lambda))
            {
                return null;
            }
            switch (lambda.Body)
            {
                case MemberAccessExpressionSyntax m:
                    return Of(e, One(m, lambda, model)) is IPropertySymbol p ? new List<IPropertySymbol> { p } : null;
                case AnonymousObjectCreationExpressionSyntax a:
                    var ps = a.Initializers.Select(i => Of(e, One(i.Expression, lambda, model))).ToList();
                    return ps.All(p => p != null) && ps.Count > 0 ? ps : null;
                default:
                    return null;
            }
        }

        /// <summary>
        /// The entity's property a lambda names: an interface's (a generic configuration's, over T : IHasId) is its
        /// implementation; a base class's of another instantiation (a library model's, over TUser : IdentityUser&lt;TKey&gt;)
        /// is the entity's own of the same definition.
        /// </summary>
        private static IPropertySymbol Of(Entity e, IPropertySymbol p)
        {
            if (p?.ContainingType?.TypeKind == TypeKind.Interface && e?.Type != null)
            {
                return e.Type.FindImplementationForInterfaceMember(p) as IPropertySymbol;
            }
            if (p != null && e?.Type != null && p.ContainingType?.IsGenericType == true)
            {
                return PropertiesOf(e.Type).FirstOrDefault(x => SymbolEqualityComparer.Default.Equals(x.OriginalDefinition, p.OriginalDefinition)) ?? p;
            }
            return p;
        }

        private static IPropertySymbol One(ExpressionSyntax x, SimpleLambdaExpressionSyntax lambda, SemanticModel model) =>
            x is MemberAccessExpressionSyntax m && m.Expression is IdentifierNameSyntax id && id.Identifier.Text == lambda.Parameter.Identifier.Text
                ? model.GetSymbolInfo(m).Symbol as IPropertySymbol : null;
    }
}
