using System;
using System.Collections.Generic;
using System.Linq;
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
    internal sealed class EfModel
    {
        internal sealed class Entity
        {
            public INamedTypeSymbol Type;
            /// <summary>The primary key's properties (none if the type has no key the model says or the conventions find).</summary>
            public List<IPropertySymbol> Key = new List<IPropertySymbol>();
            /// <summary>Other sets of properties no two rows share: unique indexes and alternate keys.</summary>
            public List<List<IPropertySymbol>> Unique = new List<List<IPropertySymbol>>();
            /// <summary>Concurrency tokens: [ConcurrencyCheck] or IsConcurrencyToken, and row versions ([Timestamp], IsRowVersion).</summary>
            public List<IPropertySymbol> Tokens = new List<IPropertySymbol>();
            public HashSet<IPropertySymbol> RowVersions = new HashSet<IPropertySymbol>(SymbolEqualityComparer.Default);
            /// <summary>The query filters (HasQueryFilter), each a lambda over the entity.</summary>
            public List<IAnonymousFunctionOperation> Filters = new List<IAnonymousFunctionOperation>();
            /// <summary>Navigations to one entity.</summary>
            public List<IPropertySymbol> References = new List<IPropertySymbol>();
            /// <summary>Navigations to many (a collection of entities).</summary>
            public List<IPropertySymbol> Collections = new List<IPropertySymbol>();

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
        public readonly bool RelationalNulls;

        /// <summary>The model, or null for a program that does not reference EF Core.</summary>
        public static EfModel For(Compilation compilation, IReadOnlyList<SyntaxTree> userTrees, IReadOnlyList<INamedTypeSymbol> sourceTypes)
        {
            var dbContext = compilation.GetTypeByMetadataName("Microsoft.EntityFrameworkCore.DbContext");
            return dbContext == null ? null : new EfModel(compilation, userTrees, sourceTypes, dbContext);
        }

        private EfModel(Compilation compilation, IReadOnlyList<SyntaxTree> userTrees, IReadOnlyList<INamedTypeSymbol> sourceTypes, INamedTypeSymbol dbContext)
        {
            DbContextType = dbContext;
            RelationalNulls = userTrees.Any(t => t.GetRoot().DescendantNodes().OfType<InvocationExpressionSyntax>().Any(i =>
                i.Expression is MemberAccessExpressionSyntax { Name.Identifier.Text: "UseRelationalNulls" } &&
                !(i.ArgumentList.Arguments.FirstOrDefault()?.Expression is LiteralExpressionSyntax l && l.IsKind(SyntaxKind.FalseLiteralExpression))));
            foreach (var t in sourceTypes.Where(t => IsContextType(t)))
            {
                Contexts.Add(t);
                foreach (var p in AllMembers(t).OfType<IPropertySymbol>())
                    if (p.Type is INamedTypeSymbol set && set.Name == "DbSet" && set.TypeArguments.Length == 1 && set.TypeArguments[0] is INamedTypeSymbol e)
                        Add(e);
            }
            // configured types are entity types too
            foreach (var (tree, inv, builder) in Configuration(compilation, userTrees))
                if (builder.TypeArguments[0] is INamedTypeSymbol e) Add(e);
            // and what navigations reach
            for (bool grew = true; grew;)
            {
                grew = false;
                foreach (var e in _entities.Values.ToList())
                    foreach (var p in e.Type.GetMembers().OfType<IPropertySymbol>().Where(p => !p.IsStatic))
                        if (NavigationTarget(p.Type, out _) is INamedTypeSymbol target && IsSourceClass(target, sourceTypes) && !_entities.ContainsKey(target))
                        { Add(target); grew = true; }
            }
            foreach (var e in _entities.Values) ReadAttributes(e);
            foreach (var (tree, inv, builder) in Configuration(compilation, userTrees)) ReadFluent(compilation, tree, inv, builder);
            foreach (var e in _entities.Values)
            {
                if (e.Key.Count == 0) e.Key.AddRange(ConventionKey(e.Type));
                foreach (var p in e.Type.GetMembers().OfType<IPropertySymbol>().Where(p => !p.IsStatic))
                    if (NavigationTarget(p.Type, out bool many) is INamedTypeSymbol target && _entities.ContainsKey(target))
                        (many ? e.Collections : e.References).Add(p);
            }
        }

        public bool IsContextType(ITypeSymbol t)
        {
            for (var b = t as INamedTypeSymbol; b != null; b = b.BaseType)
                if (SymbolEqualityComparer.Default.Equals(b.OriginalDefinition, DbContextType)) return true;
            return false;
        }

        /// <summary>The entity type of the model, or null.</summary>
        public Entity EntityOf(ITypeSymbol t) => t != null && _entities.TryGetValue(t.OriginalDefinition, out var e) ? e : null;

        public IEnumerable<Entity> Entities => _entities.Values;

        private void Add(INamedTypeSymbol t)
        {
            if (!_entities.ContainsKey(t.OriginalDefinition)) _entities[t.OriginalDefinition] = new Entity { Type = t };
        }

        private static IEnumerable<ISymbol> AllMembers(INamedTypeSymbol t)
        {
            for (var b = t; b != null && b.Locations.Any(l => l.IsInSource); b = b.BaseType)
                foreach (var m in b.GetMembers()) yield return m;
        }

        private static bool IsSourceClass(INamedTypeSymbol t, IReadOnlyList<INamedTypeSymbol> sourceTypes) =>
            t.TypeKind == TypeKind.Class && sourceTypes.Contains(t.OriginalDefinition, SymbolEqualityComparer.Default);

        /// <summary>The entity a navigation of this type leads to: the type itself, or the element of a collection of it.</summary>
        private static INamedTypeSymbol NavigationTarget(ITypeSymbol t, out bool many)
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
            var props = t.GetMembers().OfType<IPropertySymbol>().Where(p => !p.IsStatic && KeyTypes.Contains(p.Type.Name)).ToList();
            var key = props.FirstOrDefault(p => string.Equals(p.Name, "Id", StringComparison.OrdinalIgnoreCase))
                   ?? props.FirstOrDefault(p => string.Equals(p.Name, t.Name + "Id", StringComparison.OrdinalIgnoreCase));
            return key == null ? Array.Empty<IPropertySymbol>() : new[] { key };
        }

        private static bool Has(ISymbol s, string name) => s.GetAttributes().Any(a => a.AttributeClass?.Name == name);

        private void ReadAttributes(Entity e)
        {
            var props = e.Type.GetMembers().OfType<IPropertySymbol>().Where(p => !p.IsStatic).ToList();
            var keys = props.Where(p => Has(p, "KeyAttribute")).ToList();
            if (keys.Count > 0) e.Key = keys;
            foreach (var p in props)
            {
                if (Has(p, "ConcurrencyCheckAttribute")) e.Tokens.Add(p);
                if (Has(p, "TimestampAttribute")) { e.Tokens.Add(p); e.RowVersions.Add(p); }
            }
            // [Index(nameof(A), nameof(B), IsUnique = true)] on the class
            foreach (var a in e.Type.GetAttributes().Where(a => a.AttributeClass?.Name == "IndexAttribute"))
            {
                bool unique = a.NamedArguments.Any(n => n.Key == "IsUnique" && n.Value.Value is true);
                if (!unique) continue;
                var names = a.ConstructorArguments.SelectMany(c => c.Kind == TypedConstantKind.Array ? (IEnumerable<TypedConstant>)c.Values : new[] { c }).Select(c => c.Value as string).ToList();
                var set = names.Select(n => props.FirstOrDefault(p => p.Name == n)).ToList();
                if (set.Count > 0 && set.All(p => p != null)) e.Unique.Add(set);
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
                var model = compilation.GetSemanticModel(tree);
                foreach (var method in tree.GetRoot().DescendantNodes().OfType<MethodDeclarationSyntax>())
                {
                    if (!(method.Identifier.Text == "OnModelCreating" || method.Identifier.Text == "Configure")) continue;
                    foreach (var inv in method.DescendantNodes().OfType<InvocationExpressionSyntax>())
                    {
                        if (!(inv.Expression is MemberAccessExpressionSyntax ma)) continue;
                        if (model.GetTypeInfo(ma.Expression).Type is INamedTypeSymbol builder && builder.Name == "EntityTypeBuilder" && builder.TypeArguments.Length == 1)
                            yield return (tree, inv, builder);
                    }
                }
            }
        }

        /// <summary>One call on an entity type's builder, and what is called on its result.</summary>
        private void ReadFluent(Compilation compilation, SyntaxTree tree, InvocationExpressionSyntax inv, INamedTypeSymbol builder)
        {
            var model = compilation.GetSemanticModel(tree);
            var e = EntityOf(builder.TypeArguments[0]);
            if (e == null) return;
            var name = ((MemberAccessExpressionSyntax)inv.Expression).Name.Identifier.Text;
            var arg = inv.ArgumentList.Arguments.FirstOrDefault()?.Expression;
            // what is called on the result: .IsUnique(), .IsConcurrencyToken(), .IsRowVersion()
            var next = new List<(string name, InvocationExpressionSyntax call)>();
            for (SyntaxNode n = inv; n.Parent is MemberAccessExpressionSyntax up && up.Parent is InvocationExpressionSyntax call; n = call)
                next.Add((up.Name.Identifier.Text, call));
            bool Called(string m, out InvocationExpressionSyntax call)
            {
                call = next.FirstOrDefault(x => x.name == m).call;
                return call != null;
            }
            switch (name)
            {
                case "HasKey":
                    if (Properties(model, arg, e) is List<IPropertySymbol> key) e.Key = key;
                    else Unread.Add((inv.GetLocation(), "a key the verifier can't read"));
                    break;
                case "HasAlternateKey":
                    if (Properties(model, arg, e) is List<IPropertySymbol> alt) e.Unique.Add(alt);
                    break;
                case "HasIndex":
                    if (Called("IsUnique", out var isUnique) && !(isUnique.ArgumentList.Arguments.FirstOrDefault()?.Expression is LiteralExpressionSyntax l && l.IsKind(SyntaxKind.FalseLiteralExpression))
                        && Properties(model, arg, e) is List<IPropertySymbol> index)
                        e.Unique.Add(index);
                    break;
                case "Property":
                    if (Properties(model, arg, e) is List<IPropertySymbol> p && p.Count == 1)
                    {
                        if (Called("IsRowVersion", out _)) { if (!e.Tokens.Contains(p[0])) e.Tokens.Add(p[0]); e.RowVersions.Add(p[0]); }
                        else if (Called("IsConcurrencyToken", out var token) &&
                                 !(token.ArgumentList.Arguments.FirstOrDefault()?.Expression is LiteralExpressionSyntax f && f.IsKind(SyntaxKind.FalseLiteralExpression)) &&
                                 !e.Tokens.Contains(p[0]))
                            e.Tokens.Add(p[0]);
                    }
                    break;
                case "HasQueryFilter":
                    if (arg is LambdaExpressionSyntax lambda && model.GetOperation(lambda) is IAnonymousFunctionOperation filter)
                        e.Filters.Add(filter);
                    // (a filter that isn't a lambda only removes rows: it says nothing, which is what is assumed)
                    break;
            }
        }

        /// <summary>The properties a lambda names: x => x.P, or x => new { x.A, x.B }.</summary>
        private static List<IPropertySymbol> Properties(SemanticModel model, ExpressionSyntax arg, Entity e)
        {
            if (!(arg is SimpleLambdaExpressionSyntax lambda)) return null;
            IPropertySymbol One(ExpressionSyntax x) =>
                x is MemberAccessExpressionSyntax m && m.Expression is IdentifierNameSyntax id && id.Identifier.Text == lambda.Parameter.Identifier.Text
                    ? model.GetSymbolInfo(m).Symbol as IPropertySymbol : null;
            switch (lambda.Body)
            {
                case MemberAccessExpressionSyntax m:
                    return One(m) is IPropertySymbol p ? new List<IPropertySymbol> { p } : null;
                case AnonymousObjectCreationExpressionSyntax a:
                    var ps = a.Initializers.Select(i => One(i.Expression)).ToList();
                    return ps.All(p => p != null) && ps.Count > 0 ? ps : null;
                default:
                    return null;
            }
        }
    }
}
