using System.Collections.Generic;
using System.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.FlowAnalysis;
using Microsoft.CodeAnalysis.Operations;
using static CsVerify.Verifier.Boogie.KernelTypes;
using static CsVerify.Verifier.Boogie.KOp;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>
    /// Entity Framework Core's queries (StaticChecks.EntityFramework, its model
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
            if (KernelTypes.Ef == null || op == null)
            {
                return null;
            }
            op = Unconverted(op);
            while (op is IFlowCaptureReferenceOperation r && _captured.TryGetValue(r.Id, out var v))
            {
                op = Unconverted(v);
            }
            switch (op)
            {
                case IPropertyReferenceOperation pr when pr.Instance != null && DbSetEntity(pr.Type) is EfModel.Entity e && KernelTypes.Ef.IsContextType(pr.Instance.Type):
                    return new DbTable
                    {
                        Context = ContextValue(pr.Instance),
                        Entity = e,
                        At = pr.Syntax,
                    };
                case IInvocationOperation set when set.TargetMethod.Name == "Set" && set.Arguments.Length == 0 && set.Instance != null &&
                                                   KernelTypes.Ef.IsContextType(set.Instance.Type) && DbSetEntity(set.Type) is EfModel.Entity se:
                    return new DbTable
                    {
                        Context = ContextValue(set.Instance),
                        Entity = se,
                        At = set.Syntax,
                    };
                case IInvocationOperation ef when IsEfMethod(ef.TargetMethod) && ef.Arguments.Length >= 1:
                {
                    var src = TableOf(ef.Arguments.OrderBy(a => a.Parameter.Ordinal).First().Value);
                    if (src == null)
                    {
                        return null;
                    }
                    switch (ef.TargetMethod.Name)
                    {
                        case "AsNoTracking":
                            src.NoTracking = true;
                            return src;
                        case "AsNoTrackingWithIdentityResolution":
                            src.NoTracking = true;
                            src.IdentityResolution = true;
                            return src;
                        case "AsTracking" when ef.Arguments.Length == 1:
                            src.NoTracking = false;
                            return src;
                        case "IgnoreQueryFilters":
                            src.IgnoreFilters = true;
                            return src;
                        case "AsSplitQuery": case "AsSingleQuery": case "TagWith": case "TagWithCallSite": return src;
                        case "Include": case "ThenInclude":
                        {
                            // (a navigation of the lambda's parameter; by name, or another lambda: what it loads isn't known)
                            var lambda = ef.Arguments.FirstOrDefault(a => a.Parameter.Ordinal == 1)?.Value;
                            var nav = lambda != null && PureLambda(lambda) is var (body, p1, _) && Unconverted(body) is IPropertyReferenceOperation { Instance: IParameterReferenceOperation pr } np &&
                                      SymbolEqualityComparer.Default.Equals(pr.Parameter, p1) ? (IPropertySymbol)np.Property.OriginalDefinition : null;
                            if (nav == null)
                            {
                                src.UnknownInclude = true;
                                return src;
                            }
                            if (ef.TargetMethod.Name == "Include")
                            {
                                src.IncludePaths.Add(new List<IPropertySymbol> { nav });
                                src.Includes.Add(nav);
                                src.IncludePath = new List<ITypeSymbol> { src.Entity.Type.OriginalDefinition };
                            }
                            else if (src.IncludePaths.Count > 0)
                            {
                                src.IncludePaths[src.IncludePaths.Count - 1].Add(nav);
                            }
                            else
                            {
                                src.UnknownInclude = true;
                                return src;
                            }
                            var to = EfModel.NavigationTarget(nav.Type, out _)?.OriginalDefinition;
                            if (to == null)
                            {
                                src.IncludePath.Clear();
                                return src;
                            }
                            if (src.IncludePath.Count > 0 && src.IncludePath.Contains(to, SymbolEqualityComparer.Default))
                            {
                                src.Cycle ??= ef.Syntax;
                            }
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
            if (_tableReads.TryGetValue(t.Key, out var known))
            {
                return known;
            }
            var e = t.Entity;
            var at = t.At;
            // (a path that comes back to a type on it: a query without tracking refuses it, CSV1032)
            if (t.Cycle != null && t.NoTracking && !t.IdentityResolution)
            {
                Emit(KCheck.Of(
                    KLit.False,
                    "CSV1032",
                    t.Cycle,
                    notAssumedAfter: true,
                    message: $"'{t.Cycle}' makes an Include path that comes back to a type on it, which a query without tracking refuses " +
                                           "(EF throws when it runs): track the query, or use AsNoTrackingWithIdentityResolution"));
            }
            var rows = new KVar(LinqMap("[int]Ref"));
            var n = Declare("t$" + _temps++, _model.Compilation.GetSpecialType(SpecialType.System_Int32));
            Emit(KHavoc.Of(n));
            var len = new KVar(n);
            KExpr Row(KExpr i) => Sel(rows, i);
            LinqFact(Le(KLit.Zero, len), at);
            LinqFact(Over(KLit.Zero, len, i => NotNull(Row(i))), at);
            // (a different object at each index)
            LinqFact(Over(KLit.Zero, len, i => Over(KLit.Zero, len, j => OrElse(Eq(i, j), Ne(Row(i), Row(j))))), at);
            // no two rows share a key, or a unique index's value
            foreach (var key in e.Identifying.Where(k => k.All(IsField)))
            {
                foreach (var p in key)
                {
                    _p.Fields.Add(p.OriginalDefinition);
                }
                LinqFact(Over(KLit.Zero, len, i => Over(KLit.Zero, len, j => OrElse(Eq(i, j),
                    Not(AndAll(key.Select(p => SameColumn(p, Column(p, Row(i)), Column(p, Row(j))))))))), at);
            }
            // each passes the entity's query filters, unless the query ignores them
            if (!t.IgnoreFilters)
            {
                foreach (var filter in e.Filters)
                {
                    if (filter.Body.Operations.Length == 1 && filter.Body.Operations[0] is IReturnOperation { ReturnedValue: { } body })
                    {
                        LinqFact(Over(KLit.Zero, len, i => Apply((body, filter.Symbol.Parameters[0], null), Row(i))), at);
                    }
                }
            }
            // (each an entity of the type; which row an object is, the inverse of Row)
            LinqFact(Over(KLit.Zero, len, i => Isa(Row(i), e)), at);
            var index = new KVar(LinqMap("[Ref]int"));
            LinqFact(Over(KLit.Zero, len, i => Eq(Sel(index, Row(i)), i)), at);
            var y = new KVar("y$");
            var isRow = AndAlso(Between(KLit.Zero, Sel(index, y), len), Eq(Row(Sel(index, y)), y));
            // (a query that gives no entity of the type, Count, Any, a projection of columns: the database's values, no objects)
            if (_dbResult != null && !Mentions(_dbResult, e.Type)) { }
            else if (t.NoTracking)
            {
                Materialized(t, rows, len, at, index);
                ReadRows(t.Context, e, isRow);
            }
            // (with tracking: what is known of the rows past their reading, only where the context tracked none of the type
            // before; and tracked from here on)
            else
            {
                var k = "ef$known" + _temps++;
                _p.Locals.Add(KLocal.Of(k, "bool"));
                Emit(KHavoc.Of(k));
                var o = new KVar("o$");
                var none = KQuant.ForAll("o$", "Ref", Implies(Ne(State(t.Context, o), I(EfDetached)), Not(Isa(o, e))));
                var outer = _known;
                _known = null;
                LinqFact(Eq(new KVar(k), none), at);
                TrackedIncludes(t, rows, len, index, at, new KVar(k));
                _known = outer == null ? new KVar(k) : (KExpr)AndAlso(outer, new KVar(k));
                TrackedRows(t.Context, isRow);
            }
            var seq = new LSeq
            {
                Length = len,
                Elem = Row,
                Type = e.Type,
            };
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
            /// <summary>An object is one of them: quantifier-free, by inverse maps (which row, which of its list).</summary>
            public System.Func<KExpr, KExpr> Has;
            public EfModel.Entity Entity;
        }

        /// <summary>What one navigation of each object of a level holds (where not null): a level of its own, each with its parent known.</summary>
        private Made ChildOf(Made parent, System.Func<KExpr, KExpr> of, bool maybeNull, EfModel.Entity entity, SyntaxNode at)
        {
            var parentOf = new KVar(LinqMap("[Ref]Ref"));
            KExpr Null = KLit.Null;
            LinqFact(parent.All(x => maybeNull ? Implies(Ne(of(x), Null), Eq(Sel(parentOf, of(x)), x))
                                               : Eq(Sel(parentOf, of(x)), x)), at);
            return new Made
            {
                Entity = entity,
                All = maybeNull ? body => parent.All(x => Implies(Ne(of(x), Null), body(of(x)))) : body => parent.All(x => body(of(x))),
                Any = maybeNull ? body => parent.Any(x => AndAlso(Ne(of(x), Null), body(of(x)))) : body => parent.Any(x => body(of(x))),
                Has = r => AndAlso(AndAlso(Ne(r, Null), parent.Has(Sel(parentOf, r))), Eq(of(Sel(parentOf, r)), r)),
            };
        }

        /// <summary>The elements of a list each object of a level holds: a level, each with its list's object and its index known.</summary>
        private Made ElementsOf(Made parent, System.Func<KExpr, KExpr> size, System.Func<KExpr, KExpr, KExpr> el, EfModel.Entity entity, SyntaxNode at)
        {
            var parentOf = new KVar(LinqMap("[Ref]Ref"));
            var indexOf = new KVar(LinqMap("[Ref]int"));
            LinqFact(parent.All(x => Over(KLit.Zero, size(x), j => AndAlso(Eq(Sel(parentOf, el(x, j)), x), Eq(Sel(indexOf, el(x, j)), j)))), at);
            KExpr P(KExpr r) => Sel(parentOf, r);
            KExpr J(KExpr r) => Sel(indexOf, r);
            return new Made
            {
                Entity = entity,
                All = body => parent.All(x => Over(KLit.Zero, size(x), j => body(el(x, j)))),
                Any = body => parent.Any(x => Over(KLit.Zero, size(x), j => body(el(x, j)), forall: false)),
                Has = r => AndAlso(AndAlso(parent.Has(P(r)), Between(KLit.Zero, J(r), size(P(r)))), Eq(el(P(r), J(r)), r)),
            };
        }

        /// <summary>The members of a set each object of a level holds: a level, each with its set's object known.</summary>
        private Made MembersOf(Made parent, System.Func<KExpr, KExpr, KExpr> member, EfModel.Entity entity, SyntaxNode at)
        {
            var parentOf = new KVar(LinqMap("[Ref]Ref"));
            KExpr P(KExpr r) => Sel(parentOf, r);
            LinqFact(parent.All(x => KQuant.ForAll("z$", "Ref", Implies(member(x, new KVar("z$")), Eq(P(new KVar("z$")), x)))), at);
            return new Made
            {
                Entity = entity,
                All = body => parent.All(x => KQuant.ForAll("z$", "Ref", Implies(member(x, new KVar("z$")), body(new KVar("z$"))))),
                Any = body => parent.Any(x => KQuant.Exists("z$", "Ref", AndAlso(member(x, new KVar("z$")), body(new KVar("z$"))))),
                Has = r => AndAlso(parent.Has(P(r)), member(P(r), r)),
            };
        }

        /// <summary>
        /// Rows read without tracking (StaticChecks.EntityFramework's Navigations): new
        /// objects, each a different one; a reference navigation not included null, a collection one as its initializer
        /// made it (a new empty List, or null), but where a path loads its type (EF may fix it up then); an included
        /// reference the row its foreign key names, an included List the rows whose foreign key is this row's key, each
        /// through its type's filters, and so on down each path (Loaded). With identity resolution, or an Include not read
        /// here, EF fixes up navigations from the other rows it loads: nothing is known of them.
        /// </summary>
        private void Materialized(DbTable t, KVar rows, KVar len, SyntaxNode at, KVar index)
        {
            var e = t.Entity;
            KExpr Row(KExpr i) => Sel(rows, i);
            KExpr Alloc(KExpr r) => Sel("$Alloc", r);
            KExpr Zero = KLit.Zero;
            KExpr Null = KLit.Null;
            LinqFact(Over(Zero, len, i => Not(Alloc(Row(i)))), at);
            var top = new Made
            {
                Entity = e,
                All = body => Over(Zero, len, i => body(Row(i))),
                Any = body => Over(Zero, len, i => body(Row(i)), forall: false),
                Has = r => AndAlso(Between(Zero, Sel(index, r), len), Eq(Row(Sel(index, r)), r)),
            };
            var made = new List<Made> { top };
            var loadedTypes = new HashSet<ITypeSymbol>(t.IncludePaths.SelectMany(x => x).Select(nav => EfModel.NavigationTarget(nav.Type, out _)?.OriginalDefinition)
                .Where(x => x != null), SymbolEqualityComparer.Default);
            if (!t.IdentityResolution && !t.UnknownInclude)
            {
                foreach (var nav in e.References.Where(IsField))
                {
                    _p.Fields.Add(nav.OriginalDefinition);
                    if (t.Includes.Contains(nav.OriginalDefinition) || loadedTypes.Contains(nav.Type.OriginalDefinition))
                    {
                        continue;
                    }
                    LinqFact(top.All(x => Eq(Column(nav, x), Null)), at);
                }
                foreach (var nav in e.Collections.Where(IsField))
                {
                    _p.Fields.Add(nav.OriginalDefinition);
                    if (t.Includes.Contains(nav.OriginalDefinition) || loadedTypes.Contains(EfModel.NavigationTarget(nav.Type, out _)?.OriginalDefinition))
                    {
                        continue;
                    }
                    switch (EmptyListInitializer(nav))
                    {
                        case false:
                            LinqFact(top.All(x => Eq(Column(nav, x), Null)), at);
                            break;
                        case true when MadeAsList(nav) is INamedTypeSymbol list:
                        {
                            foreach (var m in ModelsOf(list))
                            {
                                _p.Models[m.Name] = m;
                            }
                            // a new list at each row, empty
                            LinqFact(top.All(x => ListMade(Column(nav, x))), at);
                            LinqFact(top.All(x => Eq(Sel(SizeMap, Column(nav, x)), Zero)), at);
                            made.Add(ChildOf(top, x => Column(nav, x), false, null, at));
                            break;
                        }
                        case true when MadeAsSet(nav) is INamedTypeSymbol set:
                        {
                            // a new set at each row, empty
                            foreach (var m in ModelsOf(set))
                            {
                                _p.Models[m.Name] = m;
                            }
                            var members = ModelOf("Members", set).Name;
                            LinqFact(top.All(x => ListMade(Column(nav, x))), at);
                            LinqFact(top.All(x => Eq(Sel(SizeMap, Column(nav, x)), Zero)), at);
                            LinqFact(top.All(x => KQuant.ForAll(
                                "z$",
                                "Ref",
                                Not(Sel(members, Column(nav, x), new KVar("z$"))))), at);
                            made.Add(ChildOf(top, x => Column(nav, x), false, null, at));
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
            // (allocated now: the rows, and what was made for them; no other object)
            var before = Allocate(made, null, at);
            KExpr IsNew(KExpr x) => AndAlso(Sel("$Alloc", x), Not(Sel(before, x)));
            // (no other code reaches them, if the method lets none out: an await leaves their columns as they were)
            if (_unshared != null)
            {
                Emit(KAssign.Of(_unshared, MapLambda("r$: Ref", OrElse(Sel(_unshared, new KVar("r$")), IsNew(new KVar("r$"))))));
                foreach (var p in KernelTypes.Ef.Entities.SelectMany(x => EfModel.PropertiesOf(x.Type)).Where(IsField))
                {
                    _p.Fields.Add(p.OriginalDefinition);
                }
            }
        }

        /// <summary>
        /// What a tracked query's Include loads: where the context tracked no entity of the
        /// rows' type before (<paramref name="known"/>), an included reference is null or the row its foreign key names;
        /// where it tracked none of the types the paths load either, what they load is the database's, as without
        /// tracking (Loaded), and tracked from here on, unchanged (of an entity of those types the context didn't track,
        /// whether it does now isn't known, so that a later query doesn't take it for untracked).
        /// </summary>
        private void TrackedIncludes(DbTable t, KVar rows, KVar len, KVar index, SyntaxNode at, KExpr known)
        {
            if (t.UnknownInclude || t.IncludePaths.Count == 0)
            {
                return;
            }
            var e = t.Entity;
            KExpr Row(KExpr i) => Sel(rows, i);
            KExpr Null = KLit.Null;
            var top = new Made
            {
                Entity = e,
                All = body => Over(KLit.Zero, len, i => body(Row(i))),
                Any = body => Over(KLit.Zero, len, i => body(Row(i)), forall: false),
                Has = r => AndAlso(Between(KLit.Zero, Sel(index, r), len), Eq(Row(Sel(index, r)), r)),
            };
            _known = known;
            foreach (var nav in e.References.Where(r => t.Includes.Contains(r.OriginalDefinition) && IsField(r)))
            {
                if (e.ForeignKeys.TryGetValue(nav, out var fk) && KernelTypes.Ef.EntityOf(nav.Type) is EfModel.Entity p && p.Key.Count == 1 && KeyMatches(fk, p.Key[0]))
                {
                    _p.Fields.Add(nav.OriginalDefinition);
                    LinqFact(top.All(x => OrElse(Eq(Column(nav, x), Null), AndAlso(Isa(Column(nav, x), p), ForeignKey(fk, x, p.Key[0], Column(nav, x))))), at);
                }
                else
                {
                    throw new NotTranslated("EF's Include of " + nav.Name + ", tracked");
                }
            }
            // (none of the types the paths load tracked before either)
            var types = t.IncludePaths.SelectMany(x => x).Select(nav => KernelTypes.Ef.EntityOf(EfModel.NavigationTarget(nav.Type, out _))).Where(x => x != null).Distinct().ToList();
            var all = "ef$known" + _temps++;
            _p.Locals.Add(KLocal.Of(all, "bool"));
            Emit(KHavoc.Of(all));
            var o = new KVar("o$");
            KExpr none = known;
            foreach (var d in types)
            {
                none = AndAlso(none, KQuant.ForAll(
                    "o$",
                    "Ref",
                    Implies(Ne(State(t.Context, o), I(EfDetached)), Not(Isa(o, d)))));
            }
            _known = null;
            LinqFact(Eq(new KVar(all), none), at);
            var made = new List<Made> { top };
            _known = new KVar(all);
            Loaded(t, top, t.IncludePaths, made, at);
            Allocate(made.Skip(1).ToList(), new KVar(all), at);
            _known = null;
            // (tracked now: of those types, maybe)
            var maybe = new KVar(LinqMap("[Ref]bool"));
            var y = new KVar("y$");
            KExpr ofTypes = OrAny(types.Select(d => Isa(y, d)));
            SetStates(t.Context, MapLambda("y$: Ref", Ite(AndAlso(Eq(State(t.Context, y), I(EfDetached)), ofTypes),
                Ite(Sel(maybe, y), I(Unchanged), I(EfDetached)), State(t.Context, y))));
        }

        /// <summary>
        /// What a query made below its rows allocated (where <paramref name="guard"/>): no other object; their references
        /// to allocated objects, as every object's are. The allocation before, for what's new.
        /// </summary>
        private string Allocate(List<Made> made, KExpr guard, SyntaxNode at)
        {
            KExpr Alloc(KExpr r) => Sel("$Alloc", r);
            KExpr Null = KLit.Null;
            _p.Modifies.Add("$Alloc");
            _p.AnyWrites.Add("$Alloc");
            var before = "ef$alloc" + _temps++;
            _p.Locals.Add(KLocal.Of(before, "[Ref]bool"));
            Emit(KAssign.Of(before, new KVar("$Alloc")));
            if (made.Count == 0)
            {
                return before;
            }
            var known = _known;
            _known = null;
            var after = new KVar(LinqMap("[Ref]bool"));
            var r = new KVar("r$");
            // (what's made: by the inverse maps, no quantifier in it, so the solver finds no more objects than these)
            KExpr isMade = OrAny(made.Select(m => m.Has(r)));
            if (guard != null)
            {
                isMade = AndAlso(guard, isMade);
            }
            LinqFact(KQuant.ForAll(
                "r$",
                "Ref",
                Eq(Sel(after, r), OrElse(Alloc(r), AndAlso(Ne(r, Null), isMade)))), at);
            Emit(KRow.Of("$Alloc", null, after));
            _known = guard;
            foreach (var m in made.Where(m => m.Entity != null))
            {
                foreach (var p in EfModel.PropertiesOf(m.Entity.Type).Where(p => IsField(p) && IsRef(p.Type)))
                {
                    _p.Fields.Add(p.OriginalDefinition);
                    LinqFact(m.All(x => OrElse(Eq(Column(p, x), Null), Alloc(Column(p, x)))), at);
                }
            }
            _known = known;
            return before;
        }

        /// <summary>A foreign key the kernel compares with its principal's key: of its type, or of its type made nullable.</summary>
        private bool KeyMatches(IPropertySymbol fk, IPropertySymbol key)
        {
            if (!IsField(fk) || !IsField(key))
            {
                return false;
            }
            var t = IsNullableValue(fk.Type) ? Underlying(fk.Type) : fk.Type;
            if (!SymbolEqualityComparer.Default.Equals(t, key.Type) || !(IsIntegral(t) || t.SpecialType == SpecialType.System_Boolean))
            {
                return false;
            }
            _p.Fields.Add(fk.OriginalDefinition); _p.Fields.Add(key.OriginalDefinition);
            return true;
        }

        /// <summary>The dependent's foreign key is the principal's key (a nullable one: has a value, and it's that).</summary>
        private KExpr ForeignKey(IPropertySymbol fk, KExpr dependent, IPropertySymbol key, KExpr principal) =>
            IsNullableValue(fk.Type)
                ? AndAlso(NotNull(Column(fk, dependent)), Eq(NullableValue(Column(fk, dependent), fk.Type), Column(key, principal)))
                : Eq(Column(fk, dependent), Column(key, principal));

        /// <summary>A new List, not yet allocated.</summary>
        private static KExpr ListMade(KExpr l) =>
            AndAlso(AndAlso(NotNull(l), Not(Sel("$Alloc", l))), AndAlso(new KOp("$coll", l), Not(new KOp("$arr", l))));

        private static List<List<IPropertySymbol>> PathsAfter(List<List<IPropertySymbol>> paths, IPropertySymbol nav) =>
            paths.Where(p => p.Count > 1 && SymbolEqualityComparer.Default.Equals(p[0], nav)).Select(p => p.Skip(1).ToList()).ToList();

        /// <summary>
        /// What the paths load of each object of a level: an included reference is the row its
        /// foreign key names (not null where the key can't be), an included List holds only rows with this object's key,
        /// each through its type's filters; new objects, each; and so on down each path.
        /// </summary>
        private void Loaded(DbTable t, Made level, List<List<IPropertySymbol>> paths, List<Made> made, SyntaxNode at)
        {
            var e = level.Entity;
            KExpr Null = KLit.Null;
            foreach (var nav in paths.Select(p => p[0]).Distinct<IPropertySymbol>(SymbolEqualityComparer.Default))
            {
                if (!IsField(nav))
                {
                    throw new NotTranslated("EF's Include of " + nav.Name);
                }
                _p.Fields.Add(nav.OriginalDefinition);
                var after = PathsAfter(paths, nav);
                Made child;
                if (e.References.Contains(nav) && e.ForeignKeys.TryGetValue(nav, out var fk) && KernelTypes.Ef.EntityOf(nav.Type) is EfModel.Entity p && p.Key.Count == 1 &&
                    KeyMatches(fk, p.Key[0]))
                {
                    // (a key that can't be null: there is one; one that can: there is one, or it's null)
                    KExpr Ok(KExpr x) => AndAlso(AndAlso(Ne(Column(nav, x), Null), Not(Sel("$Alloc", Column(nav, x)))),
                        AndAlso(AndAlso(Isa(Column(nav, x), p), ForeignKey(fk, x, p.Key[0], Column(nav, x))), Filtered(t, p, Column(nav, x))));
                    LinqFact(level.All(x => IsNullableValue(fk.Type) ? OrElse(Eq(Column(nav, x), Null), Ok(x)) : Ok(x)), at);
                    child = ChildOf(level, x => Column(nav, x), IsNullableValue(fk.Type), p, at);
                    made.Add(child);
                }
                // (a reference whose foreign key is EF's own, a shadow property: a row of its type, through its filters, a
                // new object; or null, where nothing says there is one)
                else if (e.References.Contains(nav) && !e.ForeignKeys.ContainsKey(nav) && KernelTypes.Ef.EntityOf(nav.Type) is EfModel.Entity sp)
                {
                    KExpr Ok(KExpr x) => AndAlso(AndAlso(Ne(Column(nav, x), Null), Not(Sel("$Alloc", Column(nav, x)))),
                        AndAlso(Isa(Column(nav, x), sp), Filtered(t, sp, Column(nav, x))));
                    LinqFact(level.All(x => OrElse(Eq(Column(nav, x), Null), Ok(x))), at);
                    child = ChildOf(level, x => Column(nav, x), true, sp, at);
                    made.Add(child);
                }
                else if (e.Collections.Contains(nav) && MadeAsList(nav) is INamedTypeSymbol list && e.CollectionKeys.TryGetValue(nav, out var cfk) && e.Key.Count == 1 &&
                         KernelTypes.Ef.EntityOf(EfModel.NavigationTarget(nav.Type, out _)) is EfModel.Entity d && KeyMatches(cfk, e.Key[0]))
                {
                    foreach (var m in ModelsOf(list))
                    {
                        _p.Models[m.Name] = m;
                    }
                    var items = ModelOf("Items", list).Name;
                    KExpr L(KExpr x) => Column(nav, x);
                    KExpr Size(KExpr x) => Sel(SizeMap, L(x));
                    KExpr El(KExpr x, KExpr j) => Sel(items, L(x), j);
                    LinqFact(level.All(x => ListMade(L(x))), at);
                    LinqFact(level.All(x => Over(KLit.Zero, Size(x), j => AndAlso(AndAlso(Ne(El(x, j), Null), Not(Sel("$Alloc", El(x, j)))),
                        AndAlso(AndAlso(Isa(El(x, j), d), ForeignKey(cfk, El(x, j), e.Key[0], x)), Filtered(t, d, El(x, j)))))), at);
                    var lists = ChildOf(level, L, false, null, at);
                    made.Add(lists);
                    child = ElementsOf(lists, l => Sel(SizeMap, l), (l, j) => Sel(items, l, j), d, at);
                    made.Add(child);
                }
                else if (e.Collections.Contains(nav) && MadeAsSet(nav) is INamedTypeSymbol set && e.CollectionKeys.TryGetValue(nav, out var sfk) && e.Key.Count == 1 &&
                         KernelTypes.Ef.EntityOf(EfModel.NavigationTarget(nav.Type, out _)) is EfModel.Entity sd && KeyMatches(sfk, e.Key[0]))
                {
                    // (a new set, of rows of this key, each through its type's filters, new objects)
                    foreach (var m in ModelsOf(set))
                    {
                        _p.Models[m.Name] = m;
                    }
                    var members = ModelOf("Members", set).Name;
                    KExpr S(KExpr x) => Column(nav, x);
                    KExpr In(KExpr x, KExpr z) => Sel(members, S(x), z);
                    LinqFact(level.All(x => ListMade(S(x))), at);
                    LinqFact(level.All(x => KQuant.ForAll(
                        "z$",
                        "Ref",
                        Implies(In(x, new KVar("z$")),
                        AndAlso(AndAlso(Ne(new KVar("z$"), Null), Not(Sel("$Alloc", new KVar("z$")))),
                            AndAlso(AndAlso(Isa(new KVar("z$"), sd), ForeignKey(sfk, new KVar("z$"), e.Key[0], x)), Filtered(t, sd, new KVar("z$"))))))), at);
                    var sets = ChildOf(level, S, false, null, at);
                    made.Add(sets);
                    child = MembersOf(sets, (set, z) => Sel(members, set, z), sd, at);
                    made.Add(child);
                }
                else
                {
                    throw new NotTranslated("EF's Include of " + nav.Name);
                }
                if (after.Count > 0)
                {
                    Loaded(t, child, after, made, at);
                }
            }
        }

        /// <summary>The entity passes its type's query filters (true where the query ignores them), as the database evaluates them.</summary>
        private KExpr Filtered(DbTable t, EfModel.Entity of, KExpr o)
        {
            if (t.IgnoreFilters)
            {
                return KLit.True;
            }
            KExpr all = KLit.True;
            _inDatabase++;
            try
            {
                foreach (var filter in of.Filters)
                {
                    if (filter.Body.Operations.Length == 1 && filter.Body.Operations[0] is IReturnOperation { ReturnedValue: { } body })
                    {
                        all = AndAlso(all, Apply((body, filter.Symbol.Parameters[0], null), o));
                    }
                }
            }
            finally
            {
                _inDatabase--;
            }
            return all;
        }

        /// <summary>
        /// Before an await: the entities' columns (and lists' models), to keep at the objects no other code reaches. After
        /// it, each as it was there.
        /// </summary>
        private List<(string map, string snapshot, bool whole)> UnsharedBefore()
        {
            if (KernelTypes.Ef == null)
            {
                return null;
            }
            var kept = new List<(string, string, bool)>();
            void Keep(string map, string type, bool whole)
            {
                var snap = "ef$kept" + _temps++;
                _p.Locals.Add(KLocal.Of(snap, type));
                Emit(KAssign.Of(snap, new KVar(map)));
                kept.Add((map, snap, whole));
            }
            // (the tracker's state, whole: a context is this code's alone while it runs, CSV1036)
            if (_failed != null)
            {
                foreach (var m in new[] { StateMap, UnsavedMap, InTxMap })
                {
                    Keep(m, _p.Models[m].Type, true);
                }
            }
            if (_unshared == null)
            {
                return kept;
            }
            var columns = KernelTypes.Ef.Entities.SelectMany(x => EfModel.PropertiesOf(x.Type)).Where(IsField).Select(p => p.OriginalDefinition)
                .Distinct<IPropertySymbol>(SymbolEqualityComparer.Default).ToList();
            foreach (var p in columns)
            {
                _p.Fields.Add(p);
            }
            var maps = columns.Select(p => (FieldMap(p), "[Ref]" + TypeOf(FieldType(p)))).ToList();
            var lists = _p.Models.Values.Where(m => m.Type.StartsWith("[Ref]") && !m.Name.StartsWith("$F.$ef.")).ToList();
            foreach (var m in lists)
            {
                maps.Add((m.Name, m.Type));
            }
            if (lists.Count > 0)
            {
                maps.Add((SizeMap, "[Ref]int"));
            }
            foreach (var (map, type) in maps.Distinct())
            {
                Keep(map, type, false);
            }
            return kept;
        }

        private void UnsharedAfter(List<(string map, string snapshot, bool whole)> kept)
        {
            if (kept == null)
            {
                return;
            }
            foreach (var (map, snap, whole) in kept)
            {
                if (whole)
                {
                    Emit(KAssume.Of(Eq(new KVar(map), new KVar(snap))));
                }
                else
                {
                    LinqFact(KQuant.ForAll(
                        "r$",
                        "Ref",
                        Implies(Sel(_unshared, new KVar("r$")),
                                                         Eq(Sel(map, new KVar("r$")), Sel(snap, new KVar("r$"))))), _decl);
                }
            }
        }

        private bool? _entitiesStayHere;

        /// <summary>
        /// Does the method keep the entities it has to itself? None is passed to the
        /// program's code, to a library call on something not local, or to a constructor, stored anywhere but in a local,
        /// captured by a lambda that isn't a query's, or yielded. (EF's calls and LINQ's take them without letting other
        /// code reach them.)
        /// </summary>
        private bool EntitiesStayHere() => _entitiesStayHere ??= !_decl.DescendantNodes().Any(LetsAnEntityOut);

        /// <summary>
        /// Does this node of the method hand an entity to code that could keep it: a call (but EF's and LINQ's), a
        /// constructor, a store anywhere but in a local, a yield, a lambda that isn't a query's?
        /// </summary>
        private bool LetsAnEntityOut(SyntaxNode n)
        {
            switch (n)
            {
                case Microsoft.CodeAnalysis.CSharp.Syntax.InvocationExpressionSyntax call when _model.GetSymbolInfo(call).Symbol is IMethodSymbol m && !EntitySafe(m):
                    return CallLetsAnEntityOut(call, m);
                case Microsoft.CodeAnalysis.CSharp.Syntax.BaseObjectCreationExpressionSyntax made when made.ArgumentList != null &&
                        made.ArgumentList.Arguments.Any(a => IsEntityType(_model.GetTypeInfo(a.Expression).Type)):
                    return true;
                case Microsoft.CodeAnalysis.CSharp.Syntax.AssignmentExpressionSyntax assign when IsEntityType(_model.GetTypeInfo(assign.Right).Type) &&
                        !(_model.GetSymbolInfo(assign.Left).Symbol is ILocalSymbol):
                    return true;
                case Microsoft.CodeAnalysis.CSharp.Syntax.YieldStatementSyntax y when y.Expression != null && IsEntityType(_model.GetTypeInfo(y.Expression).Type):
                    return true;
                case Microsoft.CodeAnalysis.CSharp.Syntax.AnonymousFunctionExpressionSyntax lambda when !(lambda.Parent is Microsoft.CodeAnalysis.CSharp.Syntax.ArgumentSyntax arg &&
                        arg.Parent?.Parent is Microsoft.CodeAnalysis.CSharp.Syntax.InvocationExpressionSyntax q && _model.GetSymbolInfo(q).Symbol is IMethodSymbol qm && EntitySafe(qm)):
                    return CapturesAnEntity(lambda);
                default: return false;
            }
        }

        /// <summary>A call, not EF's or LINQ's, handed an entity: as its receiver (but .NET's), or an argument (but to .NET's instance method of a local).</summary>
        private bool CallLetsAnEntityOut(Microsoft.CodeAnalysis.CSharp.Syntax.InvocationExpressionSyntax call, IMethodSymbol m)
        {
            var receiver = call.Expression is Microsoft.CodeAnalysis.CSharp.Syntax.MemberAccessExpressionSyntax ma ? ma.Expression : null;
            bool argOut = call.ArgumentList.Arguments.Any(a => IsEntityType(_model.GetTypeInfo(a.Expression).Type));
            bool thisOut = receiver != null && !m.IsStatic && IsEntityType(_model.GetTypeInfo(receiver).Type) && !DotNets(m);
            return thisOut || argOut && (!DotNets(m) || m.IsStatic || receiver == null || !(receiver is Microsoft.CodeAnalysis.CSharp.Syntax.IdentifierNameSyntax id && _model.GetSymbolInfo(id).Symbol is ILocalSymbol));
        }

        /// <summary>A lambda that reads an entity of a local or parameter declared outside it.</summary>
        private bool CapturesAnEntity(Microsoft.CodeAnalysis.CSharp.Syntax.AnonymousFunctionExpressionSyntax lambda) =>
            lambda.Body.DescendantNodesAndSelf().OfType<Microsoft.CodeAnalysis.CSharp.Syntax.IdentifierNameSyntax>().Any(id =>
                _model.GetSymbolInfo(id).Symbol is ISymbol s && (s is ILocalSymbol || s is IParameterSymbol) &&
                IsEntityType(s is ILocalSymbol l ? l.Type : ((IParameterSymbol)s).Type) && !s.DeclaringSyntaxReferences.Any(r => lambda.Span.Contains(r.Span)));

        /// <summary>A type that is, or holds, one of the model's entities.</summary>
        private bool IsEntityType(ITypeSymbol t) => t != null && KernelTypes.Ef.Entities.Any(e => Mentions(t, e.Type));

        /// <summary>A member that takes entities without letting other code reach them: EF's, a context's, LINQ's.</summary>
        private static bool EntitySafe(IMethodSymbol m) => IsEfMethod(m) || KernelTypes.Ef.IsContextType(m.ContainingType) || m.ContainingNamespace?.ToDisplayString() == "System.Linq";

        /// <summary>A member of .NET's own (System's, but threading's, the runtime's, reflection's).</summary>
        private static bool DotNets(IMethodSymbol m)
        {
            var type = m.ContainingType;
            if (type == null || type.DeclaringSyntaxReferences.Length > 0)
            {
                return false;
            }
            var ns = type.ContainingNamespace?.ToDisplayString() ?? "";
            return (ns == "System" || ns.StartsWith("System.")) && !ns.StartsWith("System.Threading") && !ns.StartsWith("System.Runtime") && !ns.StartsWith("System.Reflection");
        }

        /// <summary>Lowering a database query: its lambdas are the database's to evaluate (strings compared by its collation).</summary>
        private int _inDatabase;

        /// <summary>
        /// While a database query read with tracking is lowered (from its table's reading to its last operator): that the
        /// context tracked no entity of the table's type before, which what LINQ says of its rows assumes.
        /// </summary>
        private KExpr _known;

        /// <summary>What the database query being lowered gives (its last operator's type, or its task's T), for whether it gives entities.</summary>
        private ITypeSymbol _dbResult;

        /// <summary>
        /// == or != of strings in a database query's lambda, with SQL's nulls (UseRelationalNulls): where an operand that may
        /// be null (declared so, and not the literal null) is, unknown, for each comparison; else as it is.
        /// </summary>
        private KExpr RelationalStrings(IBinaryOperation b, KExpr value, KExpr l, KExpr r)
        {
            if (_inDatabase == 0 || KernelTypes.Ef?.RelationalNulls != true || !(b.OperatorKind is BinaryOperatorKind.Equals or BinaryOperatorKind.NotEquals))
            {
                return value;
            }
            bool MayBeNull(IOperation op) => !(Unconverted(op).ConstantValue is { HasValue: true, Value: null }) && Unconverted(op).Type?.NullableAnnotation != NullableAnnotation.NotAnnotated;
            if (Unconverted(b.LeftOperand).ConstantValue is { HasValue: true, Value: null } || Unconverted(b.RightOperand).ConstantValue is { HasValue: true, Value: null })
            {
                return value;
            }
            KExpr isNull = KLit.False;
            if (MayBeNull(b.LeftOperand))
            {
                isNull = OrElse(isNull, IsNull(l));
            }
            if (MayBeNull(b.RightOperand))
            {
                isNull = OrElse(isNull, IsNull(r));
            }
            if (isNull is KLit)
            {
                return value;
            }
            var unknown = new KVar(LinqMap("[Ref][Ref]bool"));
            var eq = b.OperatorKind == BinaryOperatorKind.Equals ? value : Not(value);
            var result = Ite(isNull, Sel(unknown, l, r), eq);
            return b.OperatorKind == BinaryOperatorKind.Equals ? result : Not(result);
        }

        private KExpr StringEqual(KExpr l, KExpr r) =>
            _inDatabase > 0 && KernelTypes.Ef != null && !KernelTypes.Ef.ExactStrings ? new KOp("$collate", l, r) : new KOp("streq", l, r);

        /// <summary>A HashSet navigation (as declared), of objects: that type, for its models.</summary>
        private static INamedTypeSymbol MadeAsSet(IPropertySymbol nav) =>
            nav.Type is INamedTypeSymbol { Name: "HashSet", Arity: 1 } h && h.ContainingNamespace?.ToDisplayString() == "System.Collections.Generic" && IsCollection(h) &&
            h.TypeArguments[0].IsReferenceType ? h : null;

        /// <summary>A collection navigation EF makes a List of: of List&lt;T&gt;, or an interface its initializer makes a List for. That List type.</summary>
        private INamedTypeSymbol MadeAsList(IPropertySymbol nav)
        {
            if (IsList(nav.Type))
            {
                return (INamedTypeSymbol)nav.Type;
            }
            if (!(nav.Type is INamedTypeSymbol { TypeKind: TypeKind.Interface, TypeArguments.Length: 1 } n))
            {
                return null;
            }
            var decl = nav.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() as Microsoft.CodeAnalysis.CSharp.Syntax.PropertyDeclarationSyntax;
            var init = decl?.Initializer?.Value;
            while (init is Microsoft.CodeAnalysis.CSharp.Syntax.PostfixUnaryExpressionSyntax bang && bang.IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.SuppressNullableWarningExpression))
            {
                init = bang.Operand;
            }
            // (none, or null: an IList EF makes a List of)
            if (init == null || init is Microsoft.CodeAnalysis.CSharp.Syntax.LiteralExpressionSyntax l && (l.IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.NullLiteralExpression) || l.IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.DefaultLiteralExpression)))
            {
                return n.OriginalDefinition.ToDisplayString() == "System.Collections.Generic.IList<T>"
                    ? KernelTypes.Compilation.GetTypeByMetadataName("System.Collections.Generic.List`1").Construct(n.TypeArguments[0]) : null;
            }
            if (nav.ContainingType.InstanceConstructors.Any(c => !c.IsImplicitlyDeclared))
            {
                return null;
            }
            var made = _model.Compilation.GetSemanticModel(init.SyntaxTree).GetTypeInfo(init).Type;
            return made != null && IsList(made) ? (INamedTypeSymbol)made : null;
        }

        /// <summary>A navigation's initializer: true for an empty new collection, false for none (or null), null for anything else (or a constructor of the type's own).</summary>
        private static bool? EmptyListInitializer(IPropertySymbol nav)
        {
            if (nav.ContainingType.InstanceConstructors.Any(c => !c.IsImplicitlyDeclared))
            {
                return null;
            }
            if (!(nav.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() is Microsoft.CodeAnalysis.CSharp.Syntax.PropertyDeclarationSyntax decl))
            {
                return null;
            }
            var init = decl.Initializer?.Value;
            while (init is Microsoft.CodeAnalysis.CSharp.Syntax.PostfixUnaryExpressionSyntax bang && bang.IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.SuppressNullableWarningExpression))
            {
                init = bang.Operand;
            }
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
        /// The objects read without tracking that no other code reaches (a [Ref]bool local), where the method lets none of
        /// them out (<see cref="EntitiesStayHere"/>) and awaits; null otherwise.
        /// </summary>
        private string _unshared;

        private void EfNotYet()
        {
            if (KernelTypes.Ef == null || _model.GetOperation(_decl) is not IOperation root)
            {
                return;
            }
            TrackerModels();
            if (root.DescendantsAndSelf().OfType<IAwaitOperation>().Any() && EntitiesStayHere())
            {
                _unshared = "ef$unshared";
                _p.Locals.Add(KLocal.Of(_unshared, "[Ref]bool"));
            }
            foreach (var op in root.DescendantsAndSelf())
            {
                switch (op)
                {
                    case IInvocationOperation inv when EfTrackerOp(inv) is string why:
                        throw new NotTranslated(why);
                    case IInvocationOperation q when EfQueryNotYet(q) is string whyQ:
                        throw new NotTranslated(whyQ);
                    case IPropertyReferenceOperation pr when pr.Instance != null && (pr.Property.GetMethod ?? pr.Property.SetMethod) is IMethodSymbol acc && IsEfMethod(acc) && TrackerReceiver(pr.Instance.Type) && !TrackerProperty(pr):
                        throw new NotTranslated($"EF's {pr.Property.Name}");
                }
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
            if (!query && !IsEnumerableCall(m))
            {
                return null;
            }
            if (DatabaseRoot(inv, out bool noTracking) is not EfModel.Entity root)
            {
                return null;
            }
            var name = m.Name.EndsWith("Async") ? m.Name.Substring(0, m.Name.Length - "Async".Length) : m.Name;
            var receiver = (inv.Instance ?? inv.Arguments.OrderBy(a => a.Parameter.Ordinal).FirstOrDefault()?.Value) is IOperation r0 ? Unconverted(r0).Type : null;
            int given = inv.Arguments.Count(a => !IsToken(a.Parameter.Type) && a.ArgumentKind == ArgumentKind.Explicit);
            if (query)
            {
                // (First and Last: CSV1031's check where the order isn't by a key, DatabaseOrder; of a tracked query, only
                // where the context tracked no rows of the type before)
                if (RowLimits.Contains(name) && !(name is "First" or "FirstOrDefault" or "Last" or "LastOrDefault" or "Single" or "SingleOrDefault" or "Take" or "Skip"))
                {
                    return $"EF's {m.Name} on a database query";
                }
                // (a join on keys the database and .NET compare alike: LINQ's, in no order)
                // (a join on keys the database and .NET compare alike: LINQ's, in no order; Distinct and Contains of values
                // compared alike: LINQ's, Distinct's in no order)
                bool alike = name is "Join" or "LeftJoin" or "GroupJoin" && inv.Arguments.FirstOrDefault(a => a.Parameter.Ordinal == 2)?.Value is IOperation key &&
                             PureLambda(key) is var (kb, _, _) && ComparedAlike(Unconverted(kb).Type ?? kb.Type) && ComparedAlike(kb.Type) ||
                             name == "GroupBy" && given == 2 && inv.Arguments.FirstOrDefault(a => a.Parameter.Ordinal == 1)?.Value is IOperation gkey &&
                             PureLambda(gkey) is var (gkb, _, _) && ComparedAlike(gkb.Type) ||
                             name is "Distinct" or "Contains" or "Union" && given <= (name == "Distinct" ? 1 : 2) && ElementOf(receiver) is ITypeSymbol el && ComparedAlike(el);
                // (one that compares what the database and .NET don't compare alike, and RightJoin: a library call that says
                // nothing of what it gives: Lowering.Linq's DatabaseUnknown)
                if (EqualityOperators.Contains(name) && !alike && !DatabaseUnknown(inv))
                {
                    return $"EF's {m.Name} on a database query";
                }
                foreach (var a in inv.Arguments)
                {
                    if (Unconverted(a.Value) is IAnonymousFunctionOperation fn && DatabaseLambdaNotYet(fn, name is "Select" or "SelectMany") is string why)
                    {
                        return why;
                    }
                }
                foreach (var filter in root.Filters)
                {
                    if (DatabaseLambdaNotYet(filter, false) is string why)
                    {
                        return "a query filter's " + why;
                    }
                }
            }
            // (what the query gives, at its last operator: rows of an entity, of which more is known than their columns)
            IOperation up = inv.Parent;
            while (up is IConversionOperation or IArgumentOperation)
            {
                up = up.Parent;
            }
            if (up is IInvocationOperation outer && DatabaseRoot(outer, out _) != null)
            {
                return null;
            }
            var result = inv.Type is INamedTypeSymbol { Name: "Task" or "ValueTask", Arity: 1 } task ? task.TypeArguments[0] : inv.Type;
            foreach (var e in KernelTypes.Ef.Entities.Where(e => Mentions(result, e.Type)))
            {
            }
            return null;
        }

        private readonly HashSet<SyntaxNode> _translationChecked = new HashSet<SyntaxNode>();

        /// <summary>
        /// The lambdas of a Queryable or EF operator the database runs (CSV1032): what
        /// depends on their parameters may only read mapped properties and navigations, and call what EF translates.
        /// Code of the program, or a property computed in C#, can't be sent to the database: EF throws when the query
        /// runs. A projection runs on the client when it is the query's last, so anything may be called there: Select's
        /// and SelectMany's are left out, and Include's.
        /// </summary>
        private bool TranslationChecks(IInvocationOperation inv)
        {
            var m = inv.TargetMethod;
            if (!(IsQueryableMethod(m) || IsEfMethod(m)) || m.Name is "Select" or "SelectMany" || m.Name.StartsWith("Include") || m.Name.StartsWith("ThenInclude"))
            {
                return false;
            }
            if (!_translationChecked.Add(inv.Syntax))
            {
                return _untranslatable.Contains(inv.Syntax);
            }
            foreach (var a in inv.Arguments)
            {
                if (a.Parameter.Type is INamedTypeSymbol { Name: "Expression" } &&
                    (Unconverted(a.Value) is IAnonymousFunctionOperation f ? f : Unconverted(a.Value) is IFlowAnonymousFunctionOperation fq ? LambdaBySymbol(fq) : null) is IAnonymousFunctionOperation fn)
                {
                    var parameters = new HashSet<IParameterSymbol>(SymbolEqualityComparer.Default);
                    foreach (var l in fn.DescendantsAndSelf().OfType<IAnonymousFunctionOperation>())
                    {
                        parameters.UnionWith(l.Symbol.Parameters);
                    }
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
                        {
                            Emit(KCheck.Of(
                                KLit.False,
                                "CSV1032",
                                op.Syntax,
                                notAssumedAfter: true,
                                message: $"'{op.Syntax}' can't be translated to SQL: {why}; EF throws when the query runs. Compute it before the query, or after it (AsEnumerable)"));
                            _untranslatable.Add(inv.Syntax);
                        }
                    }
                }
            }
            return _untranslatable.Contains(inv.Syntax);
        }

        /// <summary>The database queries' operators with a lambda EF can't translate (CSV1032): what they give isn't known.</summary>
        private readonly HashSet<SyntaxNode> _untranslatable = new HashSet<SyntaxNode>();

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
        /// <summary>
        /// In a database query's lambda: a library member EF translates that the kernel has no function of (a string's
        /// ToUpper, Math's Round), of the subset's values. The database's function of its arguments.
        /// </summary>
        private bool DatabaseFunction(IInvocationOperation inv)
        {
            var m = inv.TargetMethod;
            return _inDatabase > 0 && KernelTypes.Ef != null && m.DeclaringSyntaxReferences.Length == 0 && Translates(m) && !m.ReturnsVoid && InSubset(m.ReturnType) &&
                   !m.IsGenericMethod && !LoweredOtherwise(inv) &&
                   (inv.Instance == null || InSubset(inv.Instance.Type)) && inv.Arguments.All(a => a.Parameter.RefKind == RefKind.None && InSubset(a.Value.Type) && !IsDelegate(a.Value.Type));
        }

        /// <summary>A call the kernel lowers another way, in a query too: a stub's function, a string's equality, LINQ's, Math's.</summary>
        private bool LoweredOtherwise(IInvocationOperation inv) =>
            IsStub(inv.TargetMethod.OriginalDefinition) || StringEquals(inv) != null || IsEnumerableCall(inv.TargetMethod) || IsQueryableMethod(inv.TargetMethod) ||
            inv.TargetMethod.ContainingType?.ToDisplayString() == "System.Math";

        private static bool Translates(IMethodSymbol m)
        {
            var type = (m.ReducedFrom ?? m).ContainingType;
            if (type == null)
            {
                return false;
            }
            var name = type.OriginalDefinition.ContainingNamespace?.ToDisplayString() + "." + type.OriginalDefinition.MetadataName;
            if (type.SpecialType != SpecialType.None && (m.Name == "Equals" || m.Name == "CompareTo" || m.Name == "ToString"))
            {
                return true;
            }
            if (type.OriginalDefinition.SpecialType == SpecialType.System_Nullable_T)
            {
                return true;
            }
            if (m.Name == "Equals" && m.IsStatic && type.SpecialType == SpecialType.System_Object)
            {
                return true;
            }
            if (m.Name == "Contains" && type.ContainingNamespace?.ToDisplayString() == "System.Collections.Generic")
            {
                return true; // (a list passed in: IN)
            } // (a list passed in: IN)
            return TranslatedTypes.Contains(name);
        }

        /// <summary>
        /// First or Last of a database query (CSV1031): the database gives its rows in no order but the one the query
        /// sorts them by, so unless that is by a key (or a unique index), at most one row may match.
        /// </summary>
        private void DatabaseOrder(IInvocationOperation call, IOperation source, KExpr count)
        {
            if (KernelTypes.Ef == null || DatabaseRoot(call, out _) == null || OrderedByKey(source))
            {
                return;
            }
            Emit(KCheck.Of(
                _known == null ? Le(count, KLit.One) : Implies(_known, Le(count, KLit.One)),
                "CSV1031",
                call.Syntax,
                notAssumedAfter: true,
                message: $"'{call.Syntax}' keeps rows by their place in an order the database doesn't fix: order the query by a key " +
                                       "(OrderBy, or ThenBy, ending in the key or a unique index), or show that at most one row matches"));
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
                    {
                        keys.Add(prop.Property.OriginalDefinition);
                        entity ??= KernelTypes.Ef.EntityOf(prop.Property.ContainingType);
                    }
                    if (name.StartsWith("OrderBy"))
                    {
                        break;
                    }
                    continue;
                }
                if (name is "Select" or "SelectMany" or "GroupBy" || name.StartsWith("Join"))
                {
                    return false;
                }
            }
            return entity != null && entity.Identifying.Any(set => set.All(p => keys.Contains(p.OriginalDefinition)));
        }

        /// <summary>
        /// A database query's operator that compares values for equality as the database does (strings by its collation,
        /// rows by every column), not as LINQ's definition says, or RightJoin (EF Core applies the left side's filters after
        /// the join): read as a library call, which says nothing of what it gives.
        /// </summary>
        private bool DatabaseUnknown(IInvocationOperation inv)
        {
            var m = inv.TargetMethod;
            if (!IsQueryableMethod(m) || DatabaseRoot(inv, out _) == null || !IsQueryHandle(inv.Type) && !inv.Type.AllInterfaces.Any(i => i.Name == "IQueryable"))
            {
                return false;
            }
            if (m.Name == "RightJoin")
            {
                return true;
            }
            ITypeSymbol compared = m.Name switch
            {
                "Join" or "LeftJoin" or "GroupJoin" or "GroupBy" => inv.Arguments.FirstOrDefault(a => a.Parameter.Ordinal == 2 || m.Name == "GroupBy" && a.Parameter.Ordinal == 1)?.Value is IOperation key &&
                                                                   PureLambda(key) is var (kb, _, _) ? kb.Type : null,
                "Distinct" or "Union" or "Intersect" or "Except" => ElementOf(inv.Type),
                _ => null,
            };
            return compared != null && !ComparedAlike(compared);
        }

        /// <summary>
        /// Keys the database and .NET compare alike (not nullable ones yet, nor tuples): integers, bool, enums, Guid; strings where it compares them exactly.
        /// </summary>
        private static bool ComparedAlike(ITypeSymbol t) =>
            t != null && (t is INamedTypeSymbol { OriginalDefinition.SpecialType: SpecialType.System_Nullable_T } n ? ComparedAlike(n.TypeArguments[0]) :
            t.SpecialType == SpecialType.System_String ? KernelTypes.Ef.ExactStrings :
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
                        if (c.TargetMethod.Name is "AsNoTracking" or "AsNoTrackingWithIdentityResolution")
                        {
                            noTracking = true;
                        }
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
                    while (up is IConversionOperation)
                    {
                        up = up.Parent;
                    }
                    return up is IPropertyReferenceOperation { Property.Name: "Count" } || up is IArgumentOperation { Parent: IInvocationOperation q } && IsEnumerableCall(q.TargetMethod);
                }
                case "Count" when IsLocalView(pr.Instance):
                    return true;
                default:
                    return false;
            }
        }

        /// <summary>The parameters of a compiled query's lambda being read at its call: locals q$name, its arguments.</summary>
        private readonly HashSet<IParameterSymbol> _compiledParams = new HashSet<IParameterSymbol>(SymbolEqualityComparer.Default);

        /// <summary>
        /// A compiled query (a static readonly field made by EF.CompileQuery, in this file) that gives a value (First,
        /// Single, Count, Any...) called: the query its lambda writes, on the arguments, read at the call.
        /// Null for any other call.
        /// </summary>
        private KExpr CompiledQueryCall(IInvocationOperation call)
        {
            if (KernelTypes.Ef == null || call.TargetMethod.MethodKind != MethodKind.DelegateInvoke || !(Unconverted(call.Instance) is IFieldReferenceOperation fr) ||
                !fr.Field.IsStatic || !fr.Field.IsReadOnly)
            {
                return null;
            }
            var declarator = fr.Field.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() as Microsoft.CodeAnalysis.CSharp.Syntax.VariableDeclaratorSyntax;
            if (declarator?.Initializer?.Value is not Microsoft.CodeAnalysis.CSharp.Syntax.ExpressionSyntax init || init.SyntaxTree != _decl.SyntaxTree)
            {
                return null;
            }
            if (!(_model.GetOperation(init) is IInvocationOperation compile) || compile.TargetMethod.Name != "CompileQuery" || compile.TargetMethod.ContainingType?.Name != "EF" ||
                !IsEfMethod(compile.TargetMethod) || compile.Arguments.Length != 1)
            {
                return null;
            }
            var lambda = Unconverted(compile.Arguments[0].Value) is IDelegateCreationOperation dc ? dc.Target as IAnonymousFunctionOperation : Unconverted(compile.Arguments[0].Value) as IAnonymousFunctionOperation;
            if (lambda == null || lambda.Body.Operations.Length != 1 || !(lambda.Body.Operations[0] is IReturnOperation { ReturnedValue: { } body }) ||
                !(Unconverted(body) is IInvocationOperation query) || IsQueryHandle(query.Type) || query.Type.AllInterfaces.Any(i => i.Name == "IEnumerable"))
            {
                return null;
            }
            // (what isn't translated yet, in it)
            foreach (var op in lambda.Body.DescendantsAndSelf())
            {
                if (op is IInvocationOperation inv && (EfTrackerOp(inv) ?? EfQueryNotYet(inv)) is string why)
                {
                    throw new NotTranslated(why + ", in a compiled query");
                }
            }
            var args = call.Arguments.OrderBy(a => a.Parameter.Ordinal).ToList();
            if (args.Count != lambda.Symbol.Parameters.Length)
            {
                return null;
            }
            for (int k = 0; k < args.Count; k++)
            {
                var p = lambda.Symbol.Parameters[k];
                var local = Declare("q$" + p.Name, p.Type);
                Emit(KAssign.Of(local, Expr(args[k].Value)));
                _compiledParams.Add(p);
            }
            try
            {
                return Linq(query);
            }
            finally
            {
                foreach (var p in lambda.Symbol.Parameters)
                {
                    _compiledParams.Remove(p);
                }
            }
        }

        /// <summary>
        /// A compiled query of a sequence (EF.CompileQuery's lambda giving IEnumerable or IQueryable), called: a library
        /// call, which says nothing of the rows it gives. Its arguments read; null for any other source.
        /// </summary>
        private LSeq CompiledSequence(IOperation src)
        {
            if (KernelTypes.Ef == null || !(Unconverted(src) is IInvocationOperation call) || call.TargetMethod.MethodKind != MethodKind.DelegateInvoke ||
                !(Unconverted(call.Instance) is IFieldReferenceOperation fr) || !fr.Field.IsStatic || !fr.Field.IsReadOnly)
            {
                return null;
            }
            var declarator = fr.Field.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() as Microsoft.CodeAnalysis.CSharp.Syntax.VariableDeclaratorSyntax;
            if (declarator?.Initializer?.Value is not Microsoft.CodeAnalysis.CSharp.Syntax.ExpressionSyntax init ||
                !(_model.Compilation.GetSemanticModel(init.SyntaxTree).GetOperation(init) is IInvocationOperation compile) ||
                compile.TargetMethod.Name != "CompileQuery" || compile.TargetMethod.ContainingType?.Name != "EF" || !IsEfMethod(compile.TargetMethod))
            {
                return null;
            }
            var elem = ElementOf(call.Type);
            if (elem == null || !InSubset(elem))
            {
                return null;
            }
            foreach (var a in call.Arguments.OrderBy(a => a.Parameter.Ordinal))
            {
                var v = Expr(a.Value);
                if (KernelTypes.Ef.IsContextType(a.Value.Type))
                {
                    Emit(KCheck.Of(NotNull(v), "CSV1013", a.Value.Syntax, $"'{a.Value.Syntax}' might be null in '{call.Syntax}'"));
                }
            }
            var items = new KVar(LinqMap("[int]" + TypeOf(elem)));
            var n = Declare("t$" + _temps++, KernelTypes.Compilation.GetSpecialType(SpecialType.System_Int32));
            Emit(KHavoc.Of(n));
            ShapeFact(Le(KLit.Zero, new KVar(n)), call.Syntax);
            return new LSeq
            {
                Length = new KVar(n),
                Elem = i => Sel(items, i),
                Type = elem,
            };
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
            // (the tracker's, Lowering.EfTracker)
            if (name is "ExecuteUpdate" or "ExecuteDelete" && IsEfMethod(m))
            {
                return RootTable(receiverOp) != null ? null : "EF's " + m.Name;
            }
            if (EfAsyncTwin(m) != null)
            {
                return null;
            }
            if (!TrackerReceiver(receiver) || !(IsEfMethod(m) || KernelTypes.Ef.IsContextType(m.ContainingType) || IsTransactionType(m.ContainingType)))
            {
                return null;
            }
            if (m.Name == "Set" && inv.Arguments.Length == 0 && KernelTypes.Ef.IsContextType(receiver))
            {
                return null;
            }
            if (m.Name is "Dispose" or "DisposeAsync" && KernelTypes.Ef.IsContextType(receiver))
            {
                return null;
            }
            // (a context's constructor calling DbContext's)
            if (m.MethodKind == MethodKind.Constructor && inv.Instance is IInstanceReferenceOperation && m.ContainingType?.ToDisplayString() == "Microsoft.EntityFrameworkCore.DbContext")
            {
                return null;
            }
            // (a query's operators on a DbSet: AsNoTracking, Include, Where... are the query's)
            if (receiver is INamedTypeSymbol { Name: "DbSet" } && (m.ReducedFrom ?? m).IsExtensionMethod &&
                (IsQueryHandle(inv.Type) || inv.Type.AllInterfaces.Any(i => i.Name == "IQueryable" && i.ContainingNamespace?.ToDisplayString() == "System.Linq")))
            {
                return null;
            }
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
                case "CreateDbContext" when IsEfFactory(receiver) && given == 0:
                    return null;
            }
            return "EF's " + m.Name;
        }

        /// <summary>A call whose value isn't used (awaited or not).</summary>
        private static bool Discarded(IOperation op)
        {
            var p = op.Parent;
            while (p is IConversionOperation || p is IAwaitOperation || p is IInvocationOperation { TargetMethod.Name: "ConfigureAwait" })
            {
                p = p.Parent;
            }
            return p is IExpressionStatementOperation;
        }


        /// <summary>Two rows' values of a column the same, as the database compares them (strings by its collation).</summary>
        private KExpr SameColumn(IPropertySymbol p, KExpr a, KExpr b)
        {
            if (!IsString(p.Type))
            {
                return Eq(a, b);
            }
            _inDatabase++;
            try
            {
                return StringEqual(a, b);
            }
            finally
            {
                _inDatabase--;
            }
        }

        /// <summary>A column of a row: the entity's property, as a field.</summary>
        private KExpr Column(IPropertySymbol p, KExpr row) =>
            new KField
            {
                Field = p.OriginalDefinition,
                Instance = row,
                OnThis = false,
                At = _decl,
                InstanceAt = _decl,
            };
    }
}
