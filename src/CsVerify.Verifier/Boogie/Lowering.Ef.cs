using System.Collections.Generic;
using System.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.FlowAnalysis;
using Microsoft.CodeAnalysis.Operations;
using static CsVerify.Verifier.Boogie.KernelTypes;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>
    /// Entity Framework Core's queries, as CsVerify's engine reads them (MethodVerifier.EntityFramework, its model
    /// EfModel): a query on a context's DbSet is LINQ over the table as it is when the query runs, a sequence in no order
    /// the database promises, whose rows are not null, have distinct keys (and distinct values of each unique index),
    /// and pass the entity's query filters unless the query ignores them. Queryable's operators and EF's ...Async forms
    /// (awaited where they're called) are LINQ to Objects' (Lowering.Linq), over that sequence.
    /// </summary>
    internal sealed partial class Lowering
    {
        /// <summary>A table as a query reads it: its context, its entity, and how (EF's calls on it).</summary>
        private sealed class DbTable
        {
            public KExpr Context;
            public EfModel.Entity Entity;
            public bool NoTracking, IdentityResolution, IgnoreFilters, UnknownInclude;
            public SyntaxNode At;
            /// <summary>What Include and ThenInclude load: each path's navigations, in order; the first ones, Include's.</summary>
            public List<List<IPropertySymbol>> IncludePaths = new List<List<IPropertySymbol>>();
            public HashSet<IPropertySymbol> Includes = new HashSet<IPropertySymbol>(SymbolEqualityComparer.Default);
            /// <summary>The types on the last path, to find one that comes back to a type on it (CSV1032 without tracking).</summary>
            public List<ITypeSymbol> IncludePath = new List<ITypeSymbol>();
            public SyntaxNode Cycle;
            public string Key => $"{(Context as KVar)?.Name}/{Entity.Type.ToDisplayString()}/{NoTracking}/{IdentityResolution}/{IgnoreFilters}/{UnknownInclude}/" +
                                 string.Join(";", IncludePaths.Select(p => string.Join(".", p.Select(n => n.Name))));
        }

        private static bool IsEfMethod(IMethodSymbol m) =>
            m?.ContainingNamespace?.ToDisplayString() is string ns && (ns == "Microsoft.EntityFrameworkCore" || ns.StartsWith("Microsoft.EntityFrameworkCore."));

        private static bool IsQueryableMethod(IMethodSymbol m) => m?.ContainingType?.ToDisplayString() == "System.Linq.Queryable";

        /// <summary>An EF ...Async query operator (ToListAsync, FirstOrDefaultAsync, CountAsync...): the LINQ operator's name it is.</summary>
        private static string EfAsyncTwin(IMethodSymbol m) =>
            m != null && IsEfMethod(m) && m.Name.EndsWith("Async") && (m.ReducedFrom ?? m).ContainingType?.Name == "EntityFrameworkQueryableExtensions"
                ? m.Name.Substring(0, m.Name.Length - "Async".Length) : null;

        /// <summary>DbSet&lt;T&gt; of an entity type: its entity.</summary>
        private static EfModel.Entity DbSetEntity(ITypeSymbol t) =>
            KernelTypes.Ef != null && t is INamedTypeSymbol n && n.Name == "DbSet" && n.TypeArguments.Length == 1 &&
            n.ContainingNamespace?.ToDisplayString() == "Microsoft.EntityFrameworkCore" ? KernelTypes.Ef.EntityOf(n.TypeArguments[0]) : null;

        /// <summary>
        /// The table a query's source is, as it reads it: a context's DbSet property, ctx.Set&lt;T&gt;(), and EF's calls that
        /// don't change which rows it gives (AsNoTracking, IgnoreQueryFilters, Include...). Null for anything else.
        /// </summary>
        private DbTable TableOf(IOperation op)
        {
            if (KernelTypes.Ef == null || op == null) return null;
            op = Unconverted(op);
            while (op is IFlowCaptureReferenceOperation r && _captured.TryGetValue(r.Id, out var v)) op = Unconverted(v);
            switch (op)
            {
                case IPropertyReferenceOperation pr when pr.Instance != null && DbSetEntity(pr.Type) is EfModel.Entity e && KernelTypes.Ef.IsContextType(pr.Instance.Type):
                    return new DbTable { Context = ContextValue(pr.Instance), Entity = e, At = pr.Syntax };
                case IInvocationOperation set when set.TargetMethod.Name == "Set" && set.Arguments.Length == 0 && set.Instance != null &&
                                                   KernelTypes.Ef.IsContextType(set.Instance.Type) && DbSetEntity(set.Type) is EfModel.Entity se:
                    return new DbTable { Context = ContextValue(set.Instance), Entity = se, At = set.Syntax };
                case IInvocationOperation ef when IsEfMethod(ef.TargetMethod) && ef.Arguments.Length >= 1:
                {
                    var src = TableOf(ef.Arguments.OrderBy(a => a.Parameter.Ordinal).First().Value);
                    if (src == null) return null;
                    switch (ef.TargetMethod.Name)
                    {
                        case "AsNoTracking": src.NoTracking = true; return src;
                        case "AsNoTrackingWithIdentityResolution": src.NoTracking = true; src.IdentityResolution = true; return src;
                        case "AsTracking" when ef.Arguments.Length == 1: src.NoTracking = false; return src;
                        case "IgnoreQueryFilters": src.IgnoreFilters = true; return src;
                        case "AsSplitQuery": case "AsSingleQuery": case "TagWith": case "TagWithCallSite": return src;
                        case "Include": case "ThenInclude":
                        {
                            // (a navigation of the lambda's parameter; by name, or another lambda: what it loads isn't known)
                            var lambda = ef.Arguments.FirstOrDefault(a => a.Parameter.Ordinal == 1)?.Value;
                            var nav = lambda != null && PureLambda(lambda) is var (body, p1, _) && Unconverted(body) is IPropertyReferenceOperation { Instance: IParameterReferenceOperation pr } np &&
                                      SymbolEqualityComparer.Default.Equals(pr.Parameter, p1) ? (IPropertySymbol)np.Property.OriginalDefinition : null;
                            if (nav == null) { src.UnknownInclude = true; return src; }
                            if (ef.TargetMethod.Name == "Include") { src.IncludePaths.Add(new List<IPropertySymbol> { nav }); src.Includes.Add(nav); src.IncludePath = new List<ITypeSymbol> { src.Entity.Type.OriginalDefinition }; }
                            else if (src.IncludePaths.Count > 0) src.IncludePaths[src.IncludePaths.Count - 1].Add(nav);
                            else { src.UnknownInclude = true; return src; }
                            var to = EfModel.NavigationTarget(nav.Type, out _)?.OriginalDefinition;
                            if (to == null) { src.IncludePath.Clear(); return src; }
                            if (src.IncludePath.Count > 0 && src.IncludePath.Contains(to, SymbolEqualityComparer.Default)) src.Cycle ??= ef.Syntax;
                            src.IncludePath.Add(to);
                            return src;
                        }
                        default: return null;
                    }
                }
                default: return null;
            }
        }

        /// <summary>A context a query reads through: its value, not null (CSV1013).</summary>
        private KExpr ContextValue(IOperation instance)
        {
            var c = Spec(Unconverted(instance), null);
            return c;
        }

        /// <summary>The tables read in the query being lowered: one reading of each per run, as a definition may read its source twice.</summary>
        private Dictionary<string, LSeq> _tableReads;

        /// <summary>
        /// The table as the query sees it: n rows, a map of them, each not null, a different object at each index, no
        /// two with the same key or the same value of a unique index, each passing the query filters unless ignored.
        /// </summary>
        private LSeq ReadTable(DbTable t)
        {
            _tableReads ??= new Dictionary<string, LSeq>();
            if (_tableReads.TryGetValue(t.Key, out var known)) return known;
            var e = t.Entity;
            var at = t.At;
            // (a path that comes back to a type on it: a query without tracking refuses it, CSV1032)
            if (t.Cycle != null && t.NoTracking && !t.IdentityResolution)
                Emit(new KCheck { Cond = new KLit("false"), Id = "CSV1032", At = t.Cycle, NotAssumedAfter = true,
                                  Message = $"'{t.Cycle}' makes an Include path that comes back to a type on it, which a query without tracking refuses " +
                                            "(EF throws when it runs): track the query, or use AsNoTrackingWithIdentityResolution" });
            var rows = new KVar(LinqMap("[int]Ref"));
            var n = Declare("t$" + _temps++, _model.Compilation.GetSpecialType(SpecialType.System_Int32));
            Emit(new KHavoc { Var = n });
            var len = new KVar(n);
            KExpr Row(KExpr i) => new KOp("sel", rows, i);
            LinqFact(new KOp("<=", new KLit("0"), len), at);
            LinqFact(Over(new KLit("0"), len, i => new KOp("!=", Row(i), new KLit("null"))), at);
            // (a different object at each index)
            LinqFact(Over(new KLit("0"), len, i => Over(new KLit("0"), len, j => new KOp("||", new KOp("==", i, j), new KOp("!=", Row(i), Row(j))))), at);
            // no two rows share a key, or a unique index's value
            foreach (var key in e.Identifying.Where(k => k.All(IsField)))
            {
                foreach (var p in key) _p.Fields.Add(p.OriginalDefinition);
                LinqFact(Over(new KLit("0"), len, i => Over(new KLit("0"), len, j => new KOp("||", new KOp("==", i, j),
                    new KOp("!", key.Select(p => SameColumn(p, Column(p, Row(i)), Column(p, Row(j)))).Aggregate((a, b) => new KOp("&&", a, b)))))), at);
            }
            // each passes the entity's query filters, unless the query ignores them
            if (!t.IgnoreFilters)
                foreach (var filter in e.Filters)
                    if (filter.Body.Operations.Length == 1 && filter.Body.Operations[0] is IReturnOperation { ReturnedValue: { } body })
                        LinqFact(Over(new KLit("0"), len, i => Apply((body, filter.Symbol.Parameters[0], null), Row(i))), at);
            // (each an entity of the type; which row an object is, the inverse of Row)
            LinqFact(Over(new KLit("0"), len, i => Isa(Row(i), e)), at);
            var index = new KVar(LinqMap("[Ref]int"));
            LinqFact(Over(new KLit("0"), len, i => new KOp("==", new KOp("sel", index, Row(i)), i)), at);
            var y = new KVar("y$");
            var isRow = new KOp("&&", Between(new KLit("0"), new KOp("sel", index, y), len), new KOp("==", Row(new KOp("sel", index, y)), y));
            if (t.NoTracking)
            {
                Materialized(t, rows, len, at, index);
                ReadRows(t.Context, e, isRow);
            }
            // (with tracking: what is known of the rows past their reading, only where the context tracked none of the type
            // before; and tracked from here on)
            else
            {
                var k = "ef$known" + _temps++;
                _p.Locals.Add(new KLocal { Name = k, Raw = "bool" });
                Emit(new KHavoc { Var = k });
                var o = new KVar("o$");
                var none = new KQuant { Forall = true, Var = "o$", Type = "Ref", Body = new KOp("==>", new KOp("!=", State(t.Context, o), I(EfDetached)), new KOp("!", Isa(o, e))) };
                var outer = _known;
                _known = null;
                LinqFact(new KOp("==", new KVar(k), none), at);
                TrackedIncludes(t, rows, len, at, new KVar(k));
                _known = outer == null ? new KVar(k) : (KExpr)new KOp("&&", outer, new KVar(k));
                TrackedRows(t.Context, isRow);
            }
            var seq = new LSeq { Length = len, Elem = Row, Type = e.Type };
            _tableReads[t.Key] = seq;
            return seq;
        }

        /// <summary>
        /// Objects a read without tracking made, of one level: every one (All of a body), some one (Any), their entity.
        /// The rows; what a path's navigation loads of each object of the level above.
        /// </summary>
        private sealed class Made
        {
            public System.Func<System.Func<KExpr, KExpr>, KExpr> All, Any;
            public EfModel.Entity Entity;
        }

        /// <summary>
        /// Rows read without tracking, as CsVerify's engine has them (MethodVerifier.EntityFramework's Navigations): new
        /// objects, each a different one; a reference navigation not included null, a collection one as its initializer
        /// made it (a new empty List, or null), but where a path loads its type (EF may fix it up then); an included
        /// reference the row its foreign key names, an included List the rows whose foreign key is this row's key, each
        /// through its type's filters, and so on down each path (Loaded). With identity resolution, or an Include not read
        /// here, EF fixes up navigations from the other rows it loads: nothing is known of them.
        /// </summary>
        private void Materialized(DbTable t, KVar rows, KVar len, SyntaxNode at, KVar index)
        {
            var e = t.Entity;
            KExpr Row(KExpr i) => new KOp("sel", rows, i);
            KExpr Alloc(KExpr r) => new KOp("sel", new KVar("$Alloc"), r);
            KExpr Zero = new KLit("0");
            KExpr Null = new KLit("null");
            LinqFact(Over(Zero, len, i => new KOp("!", Alloc(Row(i)))), at);
            var top = new Made { Entity = e, All = body => Over(Zero, len, i => body(Row(i))), Any = body => Over(Zero, len, i => body(Row(i)), forall: false) };
            var made = new List<Made> { top };
            var loadedTypes = new HashSet<ITypeSymbol>(t.IncludePaths.SelectMany(x => x).Select(nav => EfModel.NavigationTarget(nav.Type, out _)?.OriginalDefinition)
                .Where(x => x != null), SymbolEqualityComparer.Default);
            if (!t.IdentityResolution && !t.UnknownInclude)
            {
                foreach (var nav in e.References.Where(IsField))
                {
                    _p.Fields.Add(nav.OriginalDefinition);
                    if (t.Includes.Contains(nav.OriginalDefinition) || loadedTypes.Contains(nav.Type.OriginalDefinition)) continue;
                    LinqFact(top.All(x => new KOp("==", Column(nav, x), Null)), at);
                }
                foreach (var nav in e.Collections.Where(IsField))
                {
                    _p.Fields.Add(nav.OriginalDefinition);
                    if (t.Includes.Contains(nav.OriginalDefinition) || loadedTypes.Contains(EfModel.NavigationTarget(nav.Type, out _)?.OriginalDefinition)) continue;
                    switch (EmptyListInitializer(nav))
                    {
                        case false:
                            LinqFact(top.All(x => new KOp("==", Column(nav, x), Null)), at);
                            break;
                        case true when MadeAsList(nav) is INamedTypeSymbol list:
                        {
                            foreach (var m in ModelsOf(list)) _p.Models[m.Name] = m;
                            // a new list at each row, empty
                            LinqFact(top.All(x => ListMade(Column(nav, x))), at);
                            LinqFact(top.All(x => new KOp("==", new KOp("sel", new KVar(SizeMap), Column(nav, x)), Zero)), at);
                            made.Add(new Made { All = body => top.All(x => body(Column(nav, x))), Any = body => top.Any(x => body(Column(nav, x))) });
                            break;
                        }
                        case true:
                            throw new NotTranslated($"what a row's {nav.Name} is, read without tracking");
                        default:
                            // (an initializer not read here: nothing is known of it)
                            break;
                    }
                }
                Loaded(t, top, t.IncludePaths, made, at);
            }
            // each made object a different one: of every two, at different places or levels
            for (int k = 0; k < made.Count; k++)
                for (int l = k; l < made.Count; l++)
                {
                    var (mk, ml) = (made[k], made[l]);
                    if (k == 0 && l == 0) continue; // (the rows: a fact of every reading)
                    // (two places of one level may hold one object only where it's the same place: said of different levels alone)
                    if (k != l) LinqFact(mk.All(x => ml.All(y => new KOp("!=", x, y))), at);
                }
            // (allocated now: the rows, and what was made for them; no other object)
            var before = Allocate(made, null, at);
            KExpr IsNew(KExpr x) => new KOp("&&", new KOp("sel", new KVar("$Alloc"), x), new KOp("!", new KOp("sel", new KVar(before), x)));
            // (no other code reaches them, if the method lets none out: an await leaves their columns as they were)
            if (_unshared != null)
            {
                Emit(new KAssign { Var = _unshared, Value = new KOp("lambda", new KLit("r$: Ref"), new KOp("||", new KOp("sel", new KVar(_unshared), new KVar("r$")), IsNew(new KVar("r$")))) });
                foreach (var p in KernelTypes.Ef.Entities.SelectMany(x => EfModel.PropertiesOf(x.Type)).Where(IsField)) _p.Fields.Add(p.OriginalDefinition);
            }
        }

        /// <summary>
        /// What a tracked query's Include loads, as CsVerify's engine has it: where the context tracked no entity of the
        /// rows' type before (<paramref name="known"/>), an included reference is null or the row its foreign key names;
        /// where it tracked none of the types the paths load either, what they load is the database's, as without
        /// tracking (Loaded), and tracked from here on, unchanged (of an entity of those types the context didn't track,
        /// whether it does now isn't known, so that a later query doesn't take it for untracked).
        /// </summary>
        private void TrackedIncludes(DbTable t, KVar rows, KVar len, SyntaxNode at, KExpr known)
        {
            if (t.UnknownInclude || t.IncludePaths.Count == 0) return;
            var e = t.Entity;
            KExpr Row(KExpr i) => new KOp("sel", rows, i);
            KExpr Null = new KLit("null");
            var top = new Made { Entity = e, All = body => Over(new KLit("0"), len, i => body(Row(i))), Any = body => Over(new KLit("0"), len, i => body(Row(i)), forall: false) };
            _known = known;
            foreach (var nav in e.References.Where(r => t.Includes.Contains(r.OriginalDefinition) && IsField(r)))
                if (e.ForeignKeys.TryGetValue(nav, out var fk) && KernelTypes.Ef.EntityOf(nav.Type) is EfModel.Entity p && p.Key.Count == 1 && IsField(fk) && IsField(p.Key[0]) &&
                    !IsNullableValue(fk.Type) && SymbolEqualityComparer.Default.Equals(fk.Type, p.Key[0].Type))
                {
                    _p.Fields.Add(nav.OriginalDefinition); _p.Fields.Add(fk.OriginalDefinition); _p.Fields.Add(p.Key[0].OriginalDefinition);
                    LinqFact(top.All(x => new KOp("||", new KOp("==", Column(nav, x), Null), new KOp("&&", Isa(Column(nav, x), p), new KOp("==", Column(fk, x), Column(p.Key[0], Column(nav, x)))))), at);
                }
                else throw new NotTranslated("EF's Include of " + nav.Name + ", tracked");
            // (none of the types the paths load tracked before either)
            var types = t.IncludePaths.SelectMany(x => x).Select(nav => KernelTypes.Ef.EntityOf(EfModel.NavigationTarget(nav.Type, out _))).Where(x => x != null).Distinct().ToList();
            var all = "ef$known" + _temps++;
            _p.Locals.Add(new KLocal { Name = all, Raw = "bool" });
            Emit(new KHavoc { Var = all });
            var o = new KVar("o$");
            KExpr none = known;
            foreach (var d in types)
                none = new KOp("&&", none, new KQuant { Forall = true, Var = "o$", Type = "Ref", Body = new KOp("==>", new KOp("!=", State(t.Context, o), I(EfDetached)), new KOp("!", Isa(o, d))) });
            _known = null;
            LinqFact(new KOp("==", new KVar(all), none), at);
            var made = new List<Made> { top };
            _known = new KVar(all);
            Loaded(t, top, t.IncludePaths, made, at);
            Allocate(made.Skip(1).ToList(), new KVar(all), at);
            _known = null;
            // (tracked now: of those types, maybe)
            var maybe = new KVar(LinqMap("[Ref]bool"));
            var y = new KVar("y$");
            KExpr ofTypes = types.Select(d => Isa(y, d)).DefaultIfEmpty(new KLit("false")).Aggregate((a, b) => new KOp("||", a, b));
            SetStates(t.Context, new KOp("lambda", new KLit("y$: Ref"), new KOp("ite", new KOp("&&", new KOp("==", State(t.Context, y), I(EfDetached)), ofTypes),
                new KOp("ite", new KOp("sel", maybe, y), I(Unchanged), I(EfDetached)), State(t.Context, y))));
        }

        /// <summary>
        /// What a query made below its rows allocated (where <paramref name="guard"/>): no other object; their references
        /// to allocated objects, as every object's are. The allocation before, for what's new.
        /// </summary>
        private string Allocate(List<Made> made, KExpr guard, SyntaxNode at)
        {
            KExpr Alloc(KExpr r) => new KOp("sel", new KVar("$Alloc"), r);
            KExpr Null = new KLit("null");
            _p.Modifies.Add("$Alloc");
            _p.AnyWrites.Add("$Alloc");
            var before = "ef$alloc" + _temps++;
            _p.Locals.Add(new KLocal { Name = before, Raw = "[Ref]bool" });
            Emit(new KAssign { Var = before, Value = new KVar("$Alloc") });
            if (made.Count == 0) return before;
            var known = _known;
            _known = null;
            var after = new KVar(LinqMap("[Ref]bool"));
            var r = new KVar("r$");
            KExpr isMade = made.Select(m => m.Any(x => new KOp("==", x, r))).Aggregate((x, y) => new KOp("||", x, y));
            if (guard != null) isMade = new KOp("&&", guard, isMade);
            LinqFact(new KQuant { Forall = true, Var = "r$", Type = "Ref", Body = new KOp("==", new KOp("sel", after, r), new KOp("||", Alloc(r), new KOp("&&", new KOp("!=", r, Null), isMade))) }, at);
            Emit(new KRow { Map = "$Alloc", Ref = null, Value = after });
            _known = guard;
            foreach (var m in made.Where(m => m.Entity != null))
                foreach (var p in EfModel.PropertiesOf(m.Entity.Type).Where(p => IsField(p) && IsRef(p.Type)))
                {
                    _p.Fields.Add(p.OriginalDefinition);
                    LinqFact(m.All(x => new KOp("||", new KOp("==", Column(p, x), Null), Alloc(Column(p, x)))), at);
                }
            _known = known;
            return before;
        }

        /// <summary>A new List, not yet allocated.</summary>
        private static KExpr ListMade(KExpr l) =>
            new KOp("&&", new KOp("&&", new KOp("!=", l, new KLit("null")), new KOp("!", new KOp("sel", new KVar("$Alloc"), l))), new KOp("&&", new KOp("$coll", l), new KOp("!", new KOp("$arr", l))));

        private static List<List<IPropertySymbol>> PathsAfter(List<List<IPropertySymbol>> paths, IPropertySymbol nav) =>
            paths.Where(p => p.Count > 1 && SymbolEqualityComparer.Default.Equals(p[0], nav)).Select(p => p.Skip(1).ToList()).ToList();

        /// <summary>
        /// What the paths load of each object of a level (CsVerify's engine's Loaded): an included reference is the row its
        /// foreign key names (not null where the key can't be), an included List holds only rows with this object's key,
        /// each through its type's filters; new objects, each; and so on down each path.
        /// </summary>
        private void Loaded(DbTable t, Made level, List<List<IPropertySymbol>> paths, List<Made> made, SyntaxNode at)
        {
            var e = level.Entity;
            KExpr Null = new KLit("null");
            foreach (var nav in paths.Select(p => p[0]).Distinct<IPropertySymbol>(SymbolEqualityComparer.Default))
            {
                if (!IsField(nav)) throw new NotTranslated("EF's Include of " + nav.Name);
                _p.Fields.Add(nav.OriginalDefinition);
                var after = PathsAfter(paths, nav);
                Made child;
                if (e.References.Contains(nav) && e.ForeignKeys.TryGetValue(nav, out var fk) && KernelTypes.Ef.EntityOf(nav.Type) is EfModel.Entity p && p.Key.Count == 1 &&
                    IsField(fk) && IsField(p.Key[0]) && !IsNullableValue(fk.Type) && SymbolEqualityComparer.Default.Equals(fk.Type, p.Key[0].Type))
                {
                    _p.Fields.Add(fk.OriginalDefinition); _p.Fields.Add(p.Key[0].OriginalDefinition);
                    // (a key that can't be null: there is one)
                    LinqFact(level.All(x => new KOp("&&", new KOp("&&", new KOp("!=", Column(nav, x), Null), new KOp("!", new KOp("sel", new KVar("$Alloc"), Column(nav, x)))),
                        new KOp("&&", new KOp("&&", Isa(Column(nav, x), p), new KOp("==", Column(fk, x), Column(p.Key[0], Column(nav, x)))), Filtered(t, p, Column(nav, x))))), at);
                    child = new Made { Entity = p, All = body => level.All(x => body(Column(nav, x))), Any = body => level.Any(x => body(Column(nav, x))) };
                    made.Add(child);
                }
                else if (e.Collections.Contains(nav) && MadeAsList(nav) is INamedTypeSymbol list && e.CollectionKeys.TryGetValue(nav, out var cfk) && e.Key.Count == 1 &&
                         KernelTypes.Ef.EntityOf(EfModel.NavigationTarget(nav.Type, out _)) is EfModel.Entity d && IsField(cfk) && IsField(e.Key[0]) && !IsNullableValue(cfk.Type) &&
                         SymbolEqualityComparer.Default.Equals(cfk.Type, e.Key[0].Type))
                {
                    _p.Fields.Add(cfk.OriginalDefinition); _p.Fields.Add(e.Key[0].OriginalDefinition);
                    foreach (var m in ModelsOf(list)) _p.Models[m.Name] = m;
                    var items = ModelOf("Items", list).Name;
                    KExpr L(KExpr x) => Column(nav, x);
                    KExpr Size(KExpr x) => new KOp("sel", new KVar(SizeMap), L(x));
                    KExpr El(KExpr x, KExpr j) => new KOp("sel", new KVar(items), L(x), j);
                    LinqFact(level.All(x => ListMade(L(x))), at);
                    LinqFact(level.All(x => Over(new KLit("0"), Size(x), j => new KOp("&&", new KOp("&&", new KOp("!=", El(x, j), Null), new KOp("!", new KOp("sel", new KVar("$Alloc"), El(x, j)))),
                        new KOp("&&", new KOp("&&", Isa(El(x, j), d), new KOp("==", Column(cfk, El(x, j)), Column(e.Key[0], x))), Filtered(t, d, El(x, j)))))), at);
                    // (each element a different object: at different places of a list, and of two lists)
                    LinqFact(level.All(x => Over(new KLit("0"), Size(x), j => Over(new KLit("0"), Size(x), k => new KOp("||", new KOp("==", j, k), new KOp("!=", El(x, j), El(x, k)))))), at);
                    made.Add(new Made { All = body => level.All(x => body(L(x))), Any = body => level.Any(x => body(L(x))) });
                    child = new Made { Entity = d, All = body => level.All(x => Over(new KLit("0"), Size(x), j => body(El(x, j)))),
                                       Any = body => level.Any(x => Over(new KLit("0"), Size(x), j => body(El(x, j)), forall: false)) };
                    made.Add(child);
                }
                else throw new NotTranslated("EF's Include of " + nav.Name);
                if (after.Count > 0) Loaded(t, child, after, made, at);
            }
        }

        /// <summary>The entity passes its type's query filters (true where the query ignores them), as the database evaluates them.</summary>
        private KExpr Filtered(DbTable t, EfModel.Entity of, KExpr o)
        {
            if (t.IgnoreFilters) return new KLit("true");
            KExpr all = new KLit("true");
            _inDatabase++;
            try
            {
                foreach (var filter in of.Filters)
                    if (filter.Body.Operations.Length == 1 && filter.Body.Operations[0] is IReturnOperation { ReturnedValue: { } body })
                        all = new KOp("&&", all, Apply((body, filter.Symbol.Parameters[0], null), o));
            }
            finally { _inDatabase--; }
            return all;
        }

        /// <summary>
        /// Before an await: the entities' columns (and lists' models), to keep at the objects no other code reaches. After
        /// it, each as it was there (CsVerify's engine's KeepUnshared).
        /// </summary>
        private List<(string map, string snapshot, bool whole)> UnsharedBefore()
        {
            if (KernelTypes.Ef == null) return null;
            var kept = new List<(string, string, bool)>();
            void Keep(string map, string type, bool whole)
            {
                var snap = "ef$kept" + _temps++;
                _p.Locals.Add(new KLocal { Name = snap, Raw = type });
                Emit(new KAssign { Var = snap, Value = new KVar(map) });
                kept.Add((map, snap, whole));
            }
            // (the tracker's state, whole: a context is this code's alone while it runs, CSV1036)
            if (_failed != null)
                foreach (var m in new[] { StateMap, UnsavedMap, InTxMap }) Keep(m, _p.Models[m].Type, true);
            if (_unshared == null) return kept;
            var columns = KernelTypes.Ef.Entities.SelectMany(x => EfModel.PropertiesOf(x.Type)).Where(IsField).Select(p => p.OriginalDefinition)
                .Distinct<IPropertySymbol>(SymbolEqualityComparer.Default).ToList();
            foreach (var p in columns) _p.Fields.Add(p);
            var maps = columns.Select(p => (FieldMap(p), "[Ref]" + TypeOf(FieldType(p)))).ToList();
            var lists = _p.Models.Values.Where(m => m.Type.StartsWith("[Ref]") && !m.Name.StartsWith("$F.$ef.")).ToList();
            foreach (var m in lists) maps.Add((m.Name, m.Type));
            if (lists.Count > 0) maps.Add((SizeMap, "[Ref]int"));
            foreach (var (map, type) in maps.Distinct()) Keep(map, type, false);
            return kept;
        }

        private void UnsharedAfter(List<(string map, string snapshot, bool whole)> kept)
        {
            if (kept == null) return;
            foreach (var (map, snap, whole) in kept)
                if (whole) Emit(new KAssume { Cond = new KOp("==", new KVar(map), new KVar(snap)) });
                else
                    LinqFact(new KQuant { Forall = true, Var = "r$", Type = "Ref",
                                          Body = new KOp("==>", new KOp("sel", new KVar(_unshared), new KVar("r$")),
                                                         new KOp("==", new KOp("sel", new KVar(map), new KVar("r$")), new KOp("sel", new KVar(snap), new KVar("r$")))) }, _decl);
        }

        private bool? _entitiesStayHere;

        /// <summary>
        /// Does the method keep the entities it has to itself (as CsVerify's engine reads it)? None is passed to the
        /// program's code, to a library call on something not local, or to a constructor, stored anywhere but in a local,
        /// captured by a lambda that isn't a query's, or yielded. (EF's calls and LINQ's take them without letting other
        /// code reach them.)
        /// </summary>
        private bool EntitiesStayHere()
        {
            if (_entitiesStayHere is bool known) return known;
            bool stay = true;
            bool IsEntity(ITypeSymbol t) => t != null && KernelTypes.Ef.Entities.Any(e => Mentions(t, e.Type));
            bool Harmless(IMethodSymbol m) => IsEfMethod(m) || KernelTypes.Ef.IsContextType(m.ContainingType) || m.ContainingNamespace?.ToDisplayString() == "System.Linq";
            // (a member of .NET's own, as CsVerify's engine's IsLibrary has it)
            bool Library(IMethodSymbol m)
            {
                var type = m.ContainingType;
                if (type == null || type.DeclaringSyntaxReferences.Length > 0) return false;
                var ns = type.ContainingNamespace?.ToDisplayString() ?? "";
                return (ns == "System" || ns.StartsWith("System.")) && !ns.StartsWith("System.Threading") && !ns.StartsWith("System.Runtime") && !ns.StartsWith("System.Reflection");
            }
            bool LocalReceiver(Microsoft.CodeAnalysis.CSharp.Syntax.ExpressionSyntax e) => e is Microsoft.CodeAnalysis.CSharp.Syntax.IdentifierNameSyntax id && _model.GetSymbolInfo(id).Symbol is ILocalSymbol;
            foreach (var n in _decl.DescendantNodes())
            {
                switch (n)
                {
                    case Microsoft.CodeAnalysis.CSharp.Syntax.InvocationExpressionSyntax call when _model.GetSymbolInfo(call).Symbol is IMethodSymbol m && !Harmless(m):
                    {
                        var receiver = call.Expression is Microsoft.CodeAnalysis.CSharp.Syntax.MemberAccessExpressionSyntax ma ? ma.Expression : null;
                        bool argOut = call.ArgumentList.Arguments.Any(a => IsEntity(_model.GetTypeInfo(a.Expression).Type));
                        bool thisOut = receiver != null && !m.IsStatic && IsEntity(_model.GetTypeInfo(receiver).Type) && !Library(m);
                        if (thisOut || argOut && (!Library(m) || m.IsStatic || receiver == null || !LocalReceiver(receiver))) stay = false;
                        break;
                    }
                    case Microsoft.CodeAnalysis.CSharp.Syntax.BaseObjectCreationExpressionSyntax made when made.ArgumentList != null &&
                            made.ArgumentList.Arguments.Any(a => IsEntity(_model.GetTypeInfo(a.Expression).Type)):
                        stay = false; break;
                    case Microsoft.CodeAnalysis.CSharp.Syntax.AssignmentExpressionSyntax assign when IsEntity(_model.GetTypeInfo(assign.Right).Type) &&
                            !(_model.GetSymbolInfo(assign.Left).Symbol is ILocalSymbol):
                        stay = false; break;
                    case Microsoft.CodeAnalysis.CSharp.Syntax.YieldStatementSyntax y when y.Expression != null && IsEntity(_model.GetTypeInfo(y.Expression).Type):
                        stay = false; break;
                    case Microsoft.CodeAnalysis.CSharp.Syntax.AnonymousFunctionExpressionSyntax lambda when !(lambda.Parent is Microsoft.CodeAnalysis.CSharp.Syntax.ArgumentSyntax arg &&
                            arg.Parent?.Parent is Microsoft.CodeAnalysis.CSharp.Syntax.InvocationExpressionSyntax q && _model.GetSymbolInfo(q).Symbol is IMethodSymbol qm && Harmless(qm)):
                        foreach (var id in lambda.Body.DescendantNodesAndSelf().OfType<Microsoft.CodeAnalysis.CSharp.Syntax.IdentifierNameSyntax>())
                            if (_model.GetSymbolInfo(id).Symbol is ISymbol s && (s is ILocalSymbol || s is IParameterSymbol) &&
                                IsEntity(s is ILocalSymbol l ? l.Type : ((IParameterSymbol)s).Type) && !s.DeclaringSyntaxReferences.Any(r => lambda.Span.Contains(r.Span)))
                                stay = false;
                        break;
                }
                if (!stay) break;
            }
            _entitiesStayHere = stay;
            return stay;
        }

        /// <summary>Lowering a database query: its lambdas are the database's to evaluate (strings compared by its collation).</summary>
        private int _inDatabase;

        /// <summary>
        /// While a database query read with tracking is lowered (from its table's reading to its last operator): that the
        /// context tracked no entity of the table's type before, which what LINQ says of its rows assumes.
        /// </summary>
        private KExpr _known;

        private KExpr StringEqual(KExpr l, KExpr r) =>
            _inDatabase > 0 && KernelTypes.Ef != null && !KernelTypes.Ef.ExactStrings ? new KOp("$collate", l, r) : new KOp("streq", l, r);

        /// <summary>A collection navigation EF makes a List of: of List&lt;T&gt;, or an interface its initializer makes a List for. That List type.</summary>
        private INamedTypeSymbol MadeAsList(IPropertySymbol nav)
        {
            if (IsList(nav.Type)) return (INamedTypeSymbol)nav.Type;
            if (!(nav.Type is INamedTypeSymbol { TypeKind: TypeKind.Interface, TypeArguments.Length: 1 } n)) return null;
            var decl = nav.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() as Microsoft.CodeAnalysis.CSharp.Syntax.PropertyDeclarationSyntax;
            if (decl?.Initializer?.Value is not Microsoft.CodeAnalysis.CSharp.Syntax.ExpressionSyntax init) return null;
            var made = _model.Compilation.GetSemanticModel(init.SyntaxTree).GetTypeInfo(init).Type;
            return made != null && IsList(made) ? (INamedTypeSymbol)made : null;
        }

        /// <summary>A navigation's initializer: true for an empty new collection, false for none (or null), null for anything else (or a constructor of the type's own).</summary>
        private static bool? EmptyListInitializer(IPropertySymbol nav)
        {
            if (nav.ContainingType.InstanceConstructors.Any(c => !c.IsImplicitlyDeclared)) return null;
            if (!(nav.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() is Microsoft.CodeAnalysis.CSharp.Syntax.PropertyDeclarationSyntax decl)) return null;
            var init = decl.Initializer?.Value;
            while (init is Microsoft.CodeAnalysis.CSharp.Syntax.PostfixUnaryExpressionSyntax bang && bang.IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.SuppressNullableWarningExpression)) init = bang.Operand;
            switch (init)
            {
                case null: return false;
                case Microsoft.CodeAnalysis.CSharp.Syntax.LiteralExpressionSyntax l when l.IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.NullLiteralExpression) || l.IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.DefaultLiteralExpression): return false;
                case Microsoft.CodeAnalysis.CSharp.Syntax.ImplicitObjectCreationExpressionSyntax io when io.ArgumentList.Arguments.Count == 0 && io.Initializer == null: return true;
                case Microsoft.CodeAnalysis.CSharp.Syntax.ObjectCreationExpressionSyntax oc when (oc.ArgumentList?.Arguments.Count ?? 0) == 0 && oc.Initializer == null: return true;
                case Microsoft.CodeAnalysis.CSharp.Syntax.CollectionExpressionSyntax ce when ce.Elements.Count == 0: return true;
                default: return null;
            }
        }

        /// <summary>
        /// What of EF CsVerify's engine checks that isn't translated yet: its change tracker (Add, Attach, Update, Remove,
        /// Entry, SaveChanges, Find, transactions, ExecuteUpdate: CSV1033 to CSV1035), a write of a row version (CSV1034),
        /// an operation not awaited where it starts, and a context used in a lambda (CSV1036). A method with any is
        /// verified by CsVerify's engine.
        /// </summary>
        /// <summary>
        /// The objects read without tracking that no other code reaches (a [Ref]bool local), where the method lets none of
        /// them out (<see cref="EntitiesStayHere"/>) and awaits; null otherwise.
        /// </summary>
        private string _unshared;

        private void EfNotYet()
        {
            if (KernelTypes.Ef == null || _model.GetOperation(_decl) is not IOperation root) return;
            TrackerModels();
            if (root.DescendantsAndSelf().OfType<IAwaitOperation>().Any() && EntitiesStayHere())
            {
                _unshared = "ef$unshared";
                _p.Locals.Add(new KLocal { Name = _unshared, Raw = "[Ref]bool" });
            }
            foreach (var op in root.DescendantsAndSelf())
                switch (op)
                {
                    case IInvocationOperation inv when EfTrackerOp(inv) is string why:
                        throw new NotTranslated(why);
                    case IInvocationOperation q when EfQueryNotYet(q) is string whyQ:
                        throw new NotTranslated(whyQ);
                    case IPropertyReferenceOperation pr when pr.Instance != null && (pr.Property.GetMethod ?? pr.Property.SetMethod) is IMethodSymbol acc && IsEfMethod(acc) && TrackerReceiver(pr.Instance.Type) && !TrackerProperty(pr):
                        throw new NotTranslated($"EF's {pr.Property.Name}");
                    case IPropertyReferenceOperation rv when rv.Parent is IAssignmentOperation a && a.Target == rv && KernelTypes.Ef.EntityOf(rv.Property.ContainingType) is EfModel.Entity e && e.RowVersions.Contains(rv.Property.OriginalDefinition):
                        throw new NotTranslated($"a write of {rv.Property.Name}, a row version");
                    case IAnonymousFunctionOperation lambda when ContextFromOutside(lambda):
                        throw new NotTranslated("a context used in a lambda");
                }
        }

        private static readonly HashSet<string> RowLimits = new HashSet<string>
        { "First", "FirstOrDefault", "Last", "LastOrDefault", "ElementAt", "ElementAtOrDefault", "Take", "Skip", "TakeLast", "SkipLast" };

        private static readonly HashSet<string> EqualityOperators = new HashSet<string>
        {
            "Distinct", "DistinctBy", "GroupBy", "GroupJoin", "Join", "LeftJoin", "RightJoin", "Union", "UnionBy", "Intersect", "IntersectBy", "Except", "ExceptBy",
            "Contains", "SequenceEqual", "CountBy", "AggregateBy", "IndexOf",
        };

        /// <summary>
        /// Why an operator of a query the database runs isn't translated yet, or null. Not yet: keeping rows by their place
        /// (First, Take, Single...: CSV1031's order check, and what one row matching proves), lambdas EF can't translate
        /// (CSV1032), strings the database compares by its collation, SQL's nulls (UseRelationalNulls), equality of keys
        /// the database and .NET don't compare alike, the rows of an entity with navigations (what a read loads of them),
        /// and rows read without tracking in a method that awaits (kept across it where no other code reaches them).
        /// </summary>
        private string EfQueryNotYet(IInvocationOperation inv)
        {
            var m = inv.TargetMethod;
            bool query = IsQueryableMethod(m) || IsEfMethod(m) && (m.ReducedFrom ?? m).IsExtensionMethod;
            if (!query && !IsEnumerableCall(m)) return null;
            if (DatabaseRoot(inv, out bool noTracking) is not EfModel.Entity root) return null;
            var name = m.Name.EndsWith("Async") ? m.Name.Substring(0, m.Name.Length - "Async".Length) : m.Name;
            if (query)
            {
                // (First and Last: CSV1031's check where the order isn't by a key, DatabaseOrder; of a tracked query, only
                // where the context tracked no rows of the type before, CsVerify's engine's Known)
                if (RowLimits.Contains(name) && !(name is "First" or "FirstOrDefault" or "Last" or "LastOrDefault" or "Single" or "SingleOrDefault" or "Take" or "Skip"))
                    return $"EF's {m.Name} on a database query";
                // (a join on keys the database and .NET compare alike: LINQ's, in no order)
                if (EqualityOperators.Contains(name) && !(name == "Join" && inv.Arguments.FirstOrDefault(a => a.Parameter.Ordinal == 2)?.Value is IOperation key &&
                                                          PureLambda(key) is var (kb, _, _) && ComparedAlike(Unconverted(kb).Type ?? kb.Type) && ComparedAlike(kb.Type)))
                    return $"EF's {m.Name} on a database query";
                foreach (var a in inv.Arguments)
                    if (Unconverted(a.Value) is IAnonymousFunctionOperation fn && DatabaseLambdaNotYet(fn, name is "Select" or "SelectMany") is string why) return why;
                foreach (var filter in root.Filters)
                    if (DatabaseLambdaNotYet(filter, false) is string why) return "a query filter's " + why;
            }
            // (what the query gives, at its last operator: rows of an entity, of which more is known than their columns)
            IOperation up = inv.Parent;
            while (up is IConversionOperation or IArgumentOperation) up = up.Parent;
            if (up is IInvocationOperation outer && DatabaseRoot(outer, out _) != null) return null;
            var result = inv.Type is INamedTypeSymbol { Name: "Task" or "ValueTask", Arity: 1 } task ? task.TypeArguments[0] : inv.Type;
            foreach (var e in KernelTypes.Ef.Entities.Where(e => Mentions(result, e.Type)))
            {
            }
            return null;
        }

        private readonly HashSet<SyntaxNode> _translationChecked = new HashSet<SyntaxNode>();

        /// <summary>
        /// The lambdas of a Queryable or EF operator the database runs (CSV1032), as CsVerify's engine checks them: what
        /// depends on their parameters may only read mapped properties and navigations, and call what EF translates.
        /// Code of the program, or a property computed in C#, can't be sent to the database: EF throws when the query
        /// runs. A projection runs on the client when it is the query's last, so anything may be called there: Select's
        /// and SelectMany's are left out, and Include's.
        /// </summary>
        private void TranslationChecks(IInvocationOperation inv)
        {
            var m = inv.TargetMethod;
            if (!(IsQueryableMethod(m) || IsEfMethod(m)) || m.Name is "Select" or "SelectMany" || m.Name.StartsWith("Include") || m.Name.StartsWith("ThenInclude")) return;
            if (!_translationChecked.Add(inv.Syntax)) return;
            foreach (var a in inv.Arguments)
                if (a.Parameter.Type is INamedTypeSymbol { Name: "Expression" } &&
                    (Unconverted(a.Value) is IAnonymousFunctionOperation f ? f : Unconverted(a.Value) is IFlowAnonymousFunctionOperation fq ? LambdaBySymbol(fq) : null) is IAnonymousFunctionOperation fn)
                {
                    var parameters = new HashSet<IParameterSymbol>(SymbolEqualityComparer.Default);
                    foreach (var l in fn.DescendantsAndSelf().OfType<IAnonymousFunctionOperation>()) parameters.UnionWith(l.Symbol.Parameters);
                    bool Depends(IOperation op) => op.DescendantsAndSelf().OfType<IParameterReferenceOperation>().Any(p => parameters.Contains(p.Parameter));
                    foreach (var op in fn.Body.Descendants())
                    {
                        string why = null;
                        switch (op)
                        {
                            case IInvocationOperation call when Depends(call) && !Translates(call.TargetMethod):
                                why = $"'{call.TargetMethod.ToDisplayString()}' has no translation to SQL";
                                break;
                            case IPropertyReferenceOperation pr when pr.Instance != null && Depends(pr.Instance) && KernelTypes.Ef.EntityOf(pr.Property.ContainingType) is EfModel.Entity e && !Mapped(pr.Property, e):
                                why = $"'{pr.Property.Name}' isn't a column of {e.Type.Name} (it is computed in C#, or [NotMapped])";
                                break;
                        }
                        if (why != null)
                            Emit(new KCheck { Cond = new KLit("false"), Id = "CSV1032", At = op.Syntax, NotAssumedAfter = true,
                                              Message = $"'{op.Syntax}' can't be translated to SQL: {why}; EF throws when the query runs. Compute it before the query, or after it (AsEnumerable)" });
                    }
                }
        }

        /// <summary>A column or a navigation: an auto-property with a setter, not [NotMapped].</summary>
        private static bool Mapped(IPropertySymbol p, EfModel.Entity e) =>
            e.References.Contains(p) || e.Collections.Contains(p) ||
            IsField(p) && p.SetMethod != null && !p.GetAttributes().Any(a => a.AttributeClass?.Name == "NotMappedAttribute");

        private static readonly HashSet<string> TranslatedTypes = new HashSet<string>
        {
            "System.Math", "System.MathF", "System.String", "System.DateTime", "System.DateTimeOffset", "System.DateOnly", "System.TimeOnly",
            "System.TimeSpan", "System.Guid", "System.Convert", "System.Linq.Enumerable", "System.Linq.Queryable",
            "Microsoft.EntityFrameworkCore.EF", "Microsoft.EntityFrameworkCore.DbFunctionsExtensions",
            "Microsoft.EntityFrameworkCore.SqlServerDbFunctionsExtensions", "Microsoft.EntityFrameworkCore.RelationalDbFunctionsExtensions",
        };

        /// <summary>Does EF translate a call of this member (whose arguments depend on the row)?</summary>
        private static bool Translates(IMethodSymbol m)
        {
            var type = (m.ReducedFrom ?? m).ContainingType;
            if (type == null) return false;
            var name = type.OriginalDefinition.ContainingNamespace?.ToDisplayString() + "." + type.OriginalDefinition.MetadataName;
            if (type.SpecialType != SpecialType.None && (m.Name == "Equals" || m.Name == "CompareTo" || m.Name == "ToString")) return true;
            if (type.OriginalDefinition.SpecialType == SpecialType.System_Nullable_T) return true;
            if (m.Name == "Equals" && m.IsStatic && type.SpecialType == SpecialType.System_Object) return true;
            if (m.Name == "Contains" && type.ContainingNamespace?.ToDisplayString() == "System.Collections.Generic") return true; // (a list passed in: IN)
            return TranslatedTypes.Contains(name);
        }

        /// <summary>
        /// First or Last of a database query (CSV1031): the database gives its rows in no order but the one the query
        /// sorts them by, so unless that is by a key (or a unique index), at most one row may match.
        /// </summary>
        private void DatabaseOrder(IInvocationOperation call, IOperation source, KExpr count)
        {
            if (KernelTypes.Ef == null || DatabaseRoot(call, out _) == null || OrderedByKey(source)) return;
            Emit(new KCheck { Cond = _known == null ? new KOp("<=", count, new KLit("1")) : new KOp("==>", _known, new KOp("<=", count, new KLit("1"))), Id = "CSV1031", At = call.Syntax, NotAssumedAfter = true,
                              Message = $"'{call.Syntax}' keeps rows by their place in an order the database doesn't fix: order the query by a key " +
                                        "(OrderBy, or ThenBy, ending in the key or a unique index), or show that at most one row matches" });
        }

        /// <summary>Is the query (as written here) sorted by a set of columns that identifies a row?</summary>
        private bool OrderedByKey(IOperation op)
        {
            var keys = new HashSet<IPropertySymbol>(SymbolEqualityComparer.Default);
            EfModel.Entity entity = null;
            for (op = Unconverted(op); op is IInvocationOperation c; op = Unconverted(c.Arguments.OrderBy(a => a.Parameter.Ordinal).FirstOrDefault()?.Value ?? c.Instance))
            {
                var name = c.TargetMethod.Name;
                if (name is "OrderBy" or "OrderByDescending" or "ThenBy" or "ThenByDescending")
                {
                    var key = c.Arguments.FirstOrDefault(a => a.Parameter.Ordinal == 1)?.Value;
                    if (key != null && PureLambda(key) is var (body, p1, _) && Unconverted(body) is IPropertyReferenceOperation { Instance: IParameterReferenceOperation pr } prop &&
                        SymbolEqualityComparer.Default.Equals(pr.Parameter, p1))
                    { keys.Add(prop.Property.OriginalDefinition); entity ??= KernelTypes.Ef.EntityOf(prop.Property.ContainingType); }
                    if (name.StartsWith("OrderBy")) break;
                    continue;
                }
                if (name is "Select" or "SelectMany" or "GroupBy" || name.StartsWith("Join")) return false;
            }
            return entity != null && entity.Identifying.Any(set => set.All(p => keys.Contains(p.OriginalDefinition)));
        }

        /// <summary>
        /// Keys the database and .NET compare alike (as CsVerify's engine's ComparedAlike, but not nullable ones yet, nor
        /// tuples): integers, bool, enums, Guid; strings where it compares them exactly.
        /// </summary>
        private static bool ComparedAlike(ITypeSymbol t) =>
            t != null && (t.SpecialType == SpecialType.System_String ? KernelTypes.Ef.ExactStrings :
            t.TypeKind == TypeKind.Enum ||
            t.SpecialType is SpecialType.System_Boolean or SpecialType.System_SByte or SpecialType.System_Byte or SpecialType.System_Int16 or
                SpecialType.System_UInt16 or SpecialType.System_Int32 or SpecialType.System_UInt32 or SpecialType.System_Int64 or SpecialType.System_UInt64 ||
            t.ToDisplayString() == "System.Guid");

        private static bool Mentions(ITypeSymbol t, ITypeSymbol entity) =>
            t != null && (SymbolEqualityComparer.Default.Equals(t.OriginalDefinition, entity.OriginalDefinition) ||
                          t is INamedTypeSymbol n && n.TypeArguments.Any(a => Mentions(a, entity)) || t is IArrayTypeSymbol a && Mentions(a.ElementType, entity));

        /// <summary>The entity of the table a query reads (through its first sources), or null; whether it's read without tracking.</summary>
        private EfModel.Entity DatabaseRoot(IOperation op, out bool noTracking)
        {
            noTracking = false;
            for (int depth = 0; depth < 64 && op != null; depth++)
            {
                op = Unconverted(op);
                switch (op)
                {
                    case IPropertyReferenceOperation pr when DbSetEntity(pr.Type) is EfModel.Entity e:
                        return e;
                    case IInvocationOperation set when set.TargetMethod.Name == "Set" && DbSetEntity(set.Type) is EfModel.Entity se:
                        return se;
                    case IInvocationOperation c:
                        if (c.TargetMethod.Name is "AsNoTracking" or "AsNoTrackingWithIdentityResolution") noTracking = true;
                        op = c.Instance ?? c.Arguments.OrderBy(a => a.Parameter.Ordinal).FirstOrDefault()?.Value;
                        continue;
                    default:
                        return null;
                }
            }
            return null;
        }

        /// <summary>Why a lambda the database runs isn't translated yet: CSV1032's check, strings, SQL's nulls.</summary>
        private string DatabaseLambdaNotYet(IAnonymousFunctionOperation fn, bool projection)
        {
            var parameters = new HashSet<IParameterSymbol>(SymbolEqualityComparer.Default);
            foreach (var l in fn.DescendantsAndSelf().OfType<IAnonymousFunctionOperation>()) parameters.UnionWith(l.Symbol.Parameters);
            bool Depends(IOperation op) => op.DescendantsAndSelf().OfType<IParameterReferenceOperation>().Any(p => parameters.Contains(p.Parameter));
            foreach (var op in fn.Body.DescendantsAndSelf())
                switch (op)
                {
                    // (a call EF translates, the database's: not yet; one it doesn't is CSV1032's, TranslationChecks)
                    case IInvocationOperation call when !projection && Depends(call) && Translates(call.TargetMethod):
                        return "a call in a database query's lambda";
                    case IBinaryOperation b when !projection && KernelTypes.Ef.RelationalNulls && b.OperatorKind is BinaryOperatorKind.Equals or BinaryOperatorKind.NotEquals &&
                                                 (IsNullableValue(Unconverted(b.LeftOperand).Type) || IsNullableValue(Unconverted(b.RightOperand).Type) ||
                                                  Unconverted(b.LeftOperand).Type?.IsReferenceType == true || Unconverted(b.RightOperand).Type?.IsReferenceType == true):
                        return "SQL's nulls (UseRelationalNulls)";
                }
            return null;
        }

        /// <summary>The properties Lowering.EfTracker reads: Database and ChangeTracker where their calls are its, CurrentTransaction, an entry's State.</summary>
        private bool TrackerProperty(IPropertyReferenceOperation pr)
        {
            switch (pr.Property.Name)
            {
                case "Database" or "ChangeTracker" when KernelTypes.Ef.IsContextType(pr.Instance.Type):
                    return pr.Parent is IInvocationOperation inv && inv.Instance == pr && EfTrackerOp(inv) == null ||
                           pr.Parent is IPropertyReferenceOperation { Property.Name: "CurrentTransaction" };
                case "CurrentTransaction":
                    return Unconverted(pr.Instance) is IPropertyReferenceOperation { Property.Name: "Database", Instance: { } db } && KernelTypes.Ef.IsContextType(db.Type);
                case "State":
                    return Unconverted(pr.Instance) is IInvocationOperation { TargetMethod.Name: "Entry" } entry && EfTrackerOp(entry) == null;
                // (a local view, read by LINQ or for its Count)
                case "Local" when DbSetEntity(pr.Instance.Type) != null:
                {
                    IOperation up = pr.Parent;
                    while (up is IConversionOperation) up = up.Parent;
                    return up is IPropertyReferenceOperation { Property.Name: "Count" } || up is IArgumentOperation { Parent: IInvocationOperation q } && IsEnumerableCall(q.TargetMethod);
                }
                case "Count" when IsLocalView(pr.Instance):
                    return true;
                default:
                    return false;
            }
        }

        /// <summary>A context, or what EF's tracker hangs on one: a DbSet, its Database, ChangeTracker, an entry, a transaction, a factory.</summary>
        private static bool TrackerReceiver(ITypeSymbol t) =>
            t != null && (KernelTypes.Ef.IsContextType(t) || t is INamedTypeSymbol { Name: "DbSet" or "DatabaseFacade" or "ChangeTracker" or "EntityEntry" or "PropertyEntry" or "IDbContextTransaction" or "IDbContextFactory" } ||
                          t.AllInterfaces.Any(i => i.Name is "IDbContextTransaction" or "IDbContextFactory"));

        /// <summary>Why an EF call isn't translated yet, or null: a query's (Lowering.Linq), ctx.Set&lt;T&gt;(), a context's disposal, the model's configuration.</summary>
        private string EfTrackerOp(IInvocationOperation inv)
        {
            var m = inv.TargetMethod;
            var name = m.Name.EndsWith("Async") ? m.Name.Substring(0, m.Name.Length - "Async".Length) : m.Name;
            var receiverOp = inv.Instance ?? (m.IsExtensionMethod || m.ReducedFrom != null ? inv.Arguments.OrderBy(a => a.Parameter.Ordinal).FirstOrDefault()?.Value : null);
            var receiver = receiverOp == null ? null : Unconverted(receiverOp).Type;
            int given = inv.Arguments.Count(a => !IsToken(a.Parameter.Type) && a.ArgumentKind == ArgumentKind.Explicit);
            // (an operation that isn't awaited where it starts: CSV1036)
            if (m.Name.EndsWith("Async") && m.Name != "CreateDbContextAsync" && (IsEfMethod(m) || KernelTypes.Ef.IsContextType(m.ContainingType) || IsTransactionType(m.ContainingType)) && !AwaitedAtOnce(inv))
                return $"EF's {m.Name} not awaited where it starts";
            // (the tracker's, Lowering.EfTracker)
            if (name is "ExecuteUpdate" or "ExecuteDelete" && IsEfMethod(m)) return RootTable(receiverOp) != null ? null : "EF's " + m.Name;
            if (EfAsyncTwin(m) != null) return null;
            if (!TrackerReceiver(receiver) || !(IsEfMethod(m) || KernelTypes.Ef.IsContextType(m.ContainingType) || IsTransactionType(m.ContainingType))) return null;
            if (m.Name == "Set" && inv.Arguments.Length == 0 && KernelTypes.Ef.IsContextType(receiver)) return null;
            if (m.Name is "Dispose" or "DisposeAsync" && KernelTypes.Ef.IsContextType(receiver)) return null;
            // (a query's operators on a DbSet: AsNoTracking, Include, Where... are the query's)
            if (receiver is INamedTypeSymbol { Name: "DbSet" } && (m.ReducedFrom ?? m).IsExtensionMethod &&
                (IsQueryHandle(inv.Type) || inv.Type.AllInterfaces.Any(i => i.Name == "IQueryable" && i.ContainingNamespace?.ToDisplayString() == "System.Linq"))) return null;
            var r = Unconverted(receiverOp);
            bool onContext = KernelTypes.Ef.IsContextType(receiver) ||
                             receiver is INamedTypeSymbol { Name: "DbSet" } && TableOf(r) is DbTable t && !t.NoTracking && !t.IgnoreFilters && (r is IPropertyReferenceOperation || r is IInvocationOperation { TargetMethod.Name: "Set" });
            switch (name)
            {
                case "Add" or "Attach" or "Update" or "Remove" when onContext && given == 1 && Discarded(inv):
                case "SaveChanges" when onContext && (given == 0 || given == 1 && m.Parameters[0].Type.SpecialType == SpecialType.System_Boolean):
                case "Find" when onContext && receiver is INamedTypeSymbol { Name: "DbSet" } && !m.Name.EndsWith("Async"):
                    return null;
                case "Entry" when KernelTypes.Ef.IsContextType(receiver) && given == 1 &&
                                  (inv.Parent is IPropertyReferenceOperation { Property.Name: "State" } ||
                                   inv.Parent is IInvocationOperation { TargetMethod.Name: "Reload" or "ReloadAsync" } rl && rl.Instance == inv && Discarded(rl)):
                case "Reload" when r is IInvocationOperation { TargetMethod.Name: "Entry" } && Discarded(inv):
                    return null;
                case "BeginTransaction" when r is IPropertyReferenceOperation { Property.Name: "Database", Instance: { } db } && KernelTypes.Ef.IsContextType(db.Type) && given == 0:
                case "Clear" when r is IPropertyReferenceOperation { Property.Name: "ChangeTracker", Instance: { } db2 } && KernelTypes.Ef.IsContextType(db2.Type) && given == 0:
                    return null;
                case "Commit" or "Rollback" or "Dispose" when r is ILocalReferenceOperation txl && IsTransactionType(txl.Type) && given == 0 && TransactionContext(txl.Local) != null:
                    return null;
            }
            return "EF's " + m.Name;
        }

        /// <summary>A call whose value isn't used (awaited or not).</summary>
        private static bool Discarded(IOperation op)
        {
            var p = op.Parent;
            while (p is IConversionOperation || p is IAwaitOperation || p is IInvocationOperation { TargetMethod.Name: "ConfigureAwait" }) p = p.Parent;
            return p is IExpressionStatementOperation;
        }

        private static bool AwaitedAtOnce(IOperation op)
        {
            for (var p = op.Parent; p != null; op = p, p = p.Parent)
            {
                if (p is IAwaitOperation) return true;
                if (p is IConversionOperation) continue;
                if (p is IInvocationOperation ca && ca.TargetMethod.Name == "ConfigureAwait" && ca.Instance == op) continue;
                if (p is IReturnOperation && p.SemanticModel?.GetEnclosingSymbol(p.Syntax.SpanStart) is IMethodSymbol { IsAsync: false }) return true;
                return false;
            }
            return false;
        }

        /// <summary>A lambda that uses a context it didn't make: a field, or a local or parameter from outside it.</summary>
        private static bool ContextFromOutside(IAnonymousFunctionOperation lambda) =>
            lambda.Body.DescendantsAndSelf().Any(o =>
                o is IFieldReferenceOperation f && KernelTypes.Ef.IsContextType(f.Type) ||
                o is IPropertyReferenceOperation p && p.Instance is IInstanceReferenceOperation && KernelTypes.Ef.IsContextType(p.Type) ||
                o is ILocalReferenceOperation l && KernelTypes.Ef.IsContextType(l.Type) && !l.Local.DeclaringSyntaxReferences.Any(r => lambda.Syntax.Span.Contains(r.Span)) ||
                o is IParameterReferenceOperation pa && KernelTypes.Ef.IsContextType(pa.Type) && !SymbolEqualityComparer.Default.Equals(pa.Parameter.ContainingSymbol, lambda.Symbol));

        /// <summary>Two rows' values of a column the same, as the database compares them (strings by its collation).</summary>
        private KExpr SameColumn(IPropertySymbol p, KExpr a, KExpr b)
        {
            if (!IsString(p.Type)) return new KOp("==", a, b);
            _inDatabase++;
            try { return StringEqual(a, b); }
            finally { _inDatabase--; }
        }

        /// <summary>A column of a row: the entity's property, as a field.</summary>
        private KExpr Column(IPropertySymbol p, KExpr row) =>
            new KField { Field = p.OriginalDefinition, Instance = row, OnThis = false, At = _decl, InstanceAt = _decl };
    }
}
