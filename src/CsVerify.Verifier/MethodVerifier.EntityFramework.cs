using System.Collections.Generic;
using System.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.FlowAnalysis;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Entity Framework Core (EfModel has the model). A query on a context's DbSet is LINQ over the table as it is when
    /// the query runs: a sequence in no order the database promises, whose rows have distinct keys (and distinct values
    /// of each unique index) and pass the entity's query filters. Queryable's operators and EF's ...Async forms are read
    /// from LINQ to Objects' definitions over it.
    /// </summary>
    internal partial class MethodVerifier
    {
        /// <summary>A table of a context, as a query's source, and how the query reads it.</summary>
        private sealed class DbTable
        {
            public Term Context;
            public EfModel.Entity Entity;
            public bool NoTracking;
            /// <summary>AsNoTrackingWithIdentityResolution: one object for each row, whose navigations EF fixes up from the others.</summary>
            public bool IdentityResolution;
            public bool IgnoreFilters;
            /// <summary>The navigations Include loads (at the first level).</summary>
            public HashSet<IPropertySymbol> Includes = new HashSet<IPropertySymbol>(SymbolEqualityComparer.Default);
            /// <summary>The entity types of the Include path being written (Include, then each ThenInclude).</summary>
            public List<ITypeSymbol> IncludePath = new List<ITypeSymbol>();
            /// <summary>An Include path that comes back to a type on it, which a query without tracking refuses.</summary>
            public SyntaxNode Cycle;
            /// <summary>An Include this doesn't read (by name, or filtered): what it loads isn't known.</summary>
            public bool UnknownInclude;
            /// <summary>Each Include path: its Include's navigation, then each ThenInclude's.</summary>
            public List<List<IPropertySymbol>> IncludePaths = new List<List<IPropertySymbol>>();

            public DbTable With(System.Action<DbTable> change)
            {
                var t = new DbTable { Context = Context, Entity = Entity, NoTracking = NoTracking, IdentityResolution = IdentityResolution,
                                      IgnoreFilters = IgnoreFilters, Includes = new HashSet<IPropertySymbol>(Includes, SymbolEqualityComparer.Default),
                                      IncludePath = new List<ITypeSymbol>(IncludePath), Cycle = Cycle, UnknownInclude = UnknownInclude,
                                      IncludePaths = IncludePaths.Select(p => new List<IPropertySymbol>(p)).ToList() };
                change(t);
                return t;
            }
        }

        private readonly Dictionary<string, DbTable> _tables = new Dictionary<string, DbTable>();

        private EfModel Ef => _engine.Ef;

        /// <summary>DbSet&lt;T&gt; of an entity type: its entity.</summary>
        private EfModel.Entity DbSetEntity(ITypeSymbol t) =>
            Ef != null && t is INamedTypeSymbol n && n.Name == "DbSet" && n.TypeArguments.Length == 1 &&
            n.ContainingNamespace?.ToDisplayString() == "Microsoft.EntityFrameworkCore" ? Ef.EntityOf(n.TypeArguments[0]) : null;

        private Term NewTable(Term context, EfModel.Entity entity)
        {
            var t = _z3.Fresh("table", Sort.Int);
            _z3.Assume(NotNull(t));
            _tables[t.S] = new DbTable { Context = T.Coerce(context, Sort.Int), Entity = entity };
            return t;
        }

        /// <summary>DbSet.Local: the context and entity of each local view.</summary>
        private readonly Dictionary<string, (Term context, EfModel.Entity entity)> _localViews = new Dictionary<string, (Term, EfModel.Entity)>();
        private readonly Dictionary<string, Sequence> _localReadings = new Dictionary<string, Sequence>();

        /// <summary>
        /// A local view as it is now: each entity of its type the context tracks and doesn't delete (Unchanged,
        /// Modified or Added) once, in some order, and every one.
        /// </summary>
        private Sequence LocalSequence(Term c, EfModel.Entity e, Frame f)
        {
            var states = Named(ModelRow("State", c, f), "states");
            var cacheKey = c.S + "|" + states.S + "|" + e.Type.ToDisplayString();
            if (_localReadings.TryGetValue(cacheKey, out var known)) return known;
            int id = _materialized++;
            var n = _z3.Fresh("local", Sort.Int);
            AssumeSide(T.Le(T.Int(0), n));
            Term El(Term i) => _z3.Apply("local#" + id, Sort.Int, new[] { i });
            Term Idx(Term y) => _z3.Apply("local.index#" + id, Sort.Int, new[] { y });
            Term Live(Term y)
            {
                var st = T.Coerce(T.Select(states, y, Sort.Int), Sort.Int);
                return T.And(T.Not(T.Eq(st, T.Int(EfDetached))), T.Not(T.Eq(st, T.Int(Deleted))));
            }
            Term Each(Term i) => T.And(T.Eq(Idx(El(i)), i), NotNull(El(i)), IsEntity(El(i), e), Live(El(i)));
            AssumeSide(OverIndices("forall", T.Int(0), n, Each, El));
            AssumeSide(T.Implies(T.Lt(T.Int(0), n), Each(T.Int(0)))); // (the first, if any: an empty view is shown so)
            var yn = _z3.FreshName("y");
            var y = new Term(yn, Sort.Int);
            var every = T.Implies(T.And(IsEntity(y, e), Live(y)), T.And(T.Le(T.Int(0), Idx(y)), T.Lt(Idx(y), n), T.Eq(El(Idx(y)), y)));
            AssumeSide(new Term($"(forall (({yn} Int)) (! {every.S} :pattern ((select {states.S} {yn}))))", Sort.Bool));
            return _localReadings[cacheKey] = new Sequence { Length = n, Element = El, ElementType = e.Type };
        }

        /// <summary>A context's DbSet property (ctx.Orders): its table. Its Local, and the local view's Count.</summary>
        private Term DbSetProperty(IPropertyReferenceOperation pr, Frame f, SpecEnv spec)
        {
            if (pr.Instance != null && pr.Property.Name == "Local" && DbSetEntity(pr.Instance.Type) is EfModel.Entity local &&
                T.Coerce(Eval(pr.Instance, f, spec), Sort.Int) is Term set && _tables.TryGetValue(set.S, out var table))
            {
                var view = _z3.Fresh("local", Sort.Int);
                _z3.Assume(NotNull(view));
                _localViews[view.S] = (table.Context, local);
                return view;
            }
            if (pr.Instance != null && pr.Property.Name == "Count" && pr.Instance.Type?.Name == "LocalView" &&
                T.Coerce(Eval(pr.Instance, f, spec), Sort.Int) is Term lv && _localViews.TryGetValue(lv.S, out var of))
                return LocalSequence(of.context, of.entity, f).Length;
            if (pr.Instance == null || DbSetEntity(pr.Type) is not EfModel.Entity e || !Ef.IsContextType(pr.Instance.Type)) return null;
            var context = Eval(pr.Instance, f, spec);
            Deref(pr.Instance, context, pr.Syntax);
            return NewTable(context, e);
        }

        private static bool IsEfMethod(IMethodSymbol m) =>
            m.ContainingNamespace?.ToDisplayString() is string ns && (ns == "Microsoft.EntityFrameworkCore" || ns.StartsWith("Microsoft.EntityFrameworkCore."));

        private static bool IsQueryable(IMethodSymbol m) => m.ContainingType?.ToDisplayString() == "System.Linq.Queryable";

        /// <summary>
        /// EF calls on queries that don't change which rows they give: ctx.Set&lt;T&gt;(), and AsNoTracking, AsTracking,
        /// IgnoreQueryFilters, Include, AsSplitQuery and the like, each a table read differently.
        /// </summary>
        private Term DbQueryCall(IInvocationOperation inv, Frame f, SpecEnv spec)
        {
            if (Ef == null) return null;
            var m = inv.TargetMethod;
            if (m.Name == "Set" && m.TypeArguments.Length == 1 && inv.Instance != null && Ef.IsContextType(inv.Instance.Type) && Ef.EntityOf(m.TypeArguments[0]) is EfModel.Entity entity)
            {
                var context = Eval(inv.Instance, f, spec);
                Deref(inv.Instance, context, inv.Syntax);
                return NewTable(context, entity);
            }
            if (!IsEfMethod(m) || !m.IsExtensionMethod && m.ReducedFrom == null) return null;
            var source = inv.Arguments.FirstOrDefault(a => a.Parameter.Ordinal == 0)?.Value ?? inv.Instance;
            if (source == null) return null;
            switch (m.Name)
            {
                case "AsNoTracking": case "AsNoTrackingWithIdentityResolution": case "AsTracking": case "IgnoreQueryFilters":
                case "Include": case "ThenInclude": case "AsSplitQuery": case "AsSingleQuery": case "TagWith": case "TagWithCallSite":
                    break;
                default:
                    return null;
            }
            var s = T.Coerce(Eval(source, f, spec), Sort.Int);
            if (!_tables.TryGetValue(s.S, out var table))
                return m.Name == "Include" || m.Name == "ThenInclude" || m.Name.StartsWith("Tag") || m.Name.StartsWith("As") ? s : null;
            var read = table.With(t =>
            {
                switch (m.Name)
                {
                    case "AsNoTracking": t.NoTracking = true; t.IdentityResolution = false; break;
                    case "AsNoTrackingWithIdentityResolution": t.NoTracking = true; t.IdentityResolution = true; break;
                    case "AsTracking": t.NoTracking = false; t.IdentityResolution = false; break;
                    case "IgnoreQueryFilters": t.IgnoreFilters = true; break;
                    case "Include":
                    case "ThenInclude":
                    {
                        var nav = inv.Arguments.FirstOrDefault(a => a.Parameter.Ordinal == 1)?.Value is IOperation lambda ? Navigation(lambda) : null;
                        if (nav == null) t.UnknownInclude = true;
                        else if (m.Name == "Include") t.IncludePaths.Add(new List<IPropertySymbol> { nav });
                        else if (t.IncludePaths.Count > 0) t.IncludePaths[t.IncludePaths.Count - 1].Add(nav);
                        else t.UnknownInclude = true;
                        if (m.Name == "Include")
                        {
                            if (nav != null) t.Includes.Add(nav);
                            t.IncludePath = new List<ITypeSymbol> { t.Entity.Type.OriginalDefinition };
                        }
                        var to = nav == null ? null : EfModel.NavigationTarget(nav.Type, out _)?.OriginalDefinition;
                        if (to == null) { t.IncludePath.Clear(); break; }
                        if (t.IncludePath.Count > 0 && t.IncludePath.Contains(to, SymbolEqualityComparer.Default)) t.Cycle ??= inv.Syntax;
                        t.IncludePath.Add(to);
                        break;
                    }
                }
            });
            if (read.Cycle != null && read.NoTracking && !read.IdentityResolution && _codeMode && _queryContexts.Count == 0 && _cyclesReported.Add(read.Cycle))
                Report(TranslateId, read.Cycle, $"'{read.Cycle}' makes an Include path that comes back to a type on it, which a query without tracking refuses " +
                       "(EF throws when it runs): track the query, or use AsNoTrackingWithIdentityResolution", isError: true);
            var r = _z3.Fresh("table", Sort.Int);
            _z3.Assume(NotNull(r));
            _tables[r.S] = read;
            return r;
        }

        private readonly HashSet<SyntaxNode> _cyclesReported = new HashSet<SyntaxNode>();

        /// <summary>
        /// A compiled query (a static readonly field made by EF.CompileQuery, in this file) that gives a value (First,
        /// Single, Count, Any...) called: the query its lambda writes, on the arguments, read at the call. One that
        /// gives a sequence (read when it is enumerated, after the call), EF.CompileAsyncQuery's, and one declared in
        /// another file are library calls.
        /// </summary>
        private Term CompiledQueryCall(IInvocationOperation inv, Frame f, SpecEnv spec)
        {
            if (Ef == null || inv.TargetMethod.MethodKind != MethodKind.DelegateInvoke || !(Unwrapped(inv.Instance) is IFieldReferenceOperation fr) ||
                !fr.Field.IsStatic || !fr.Field.IsReadOnly) return null;
            if (!(fr.Field.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() is Microsoft.CodeAnalysis.CSharp.Syntax.VariableDeclaratorSyntax decl) ||
                decl.SyntaxTree != _model.SyntaxTree || !(decl.Initializer?.Value is Microsoft.CodeAnalysis.CSharp.Syntax.InvocationExpressionSyntax made)) return null;
            if (!(_model.GetOperation(made) is IInvocationOperation compile) || compile.TargetMethod.Name != "CompileQuery" ||
                compile.TargetMethod.ContainingType?.ToDisplayString() != "Microsoft.EntityFrameworkCore.EF") return null;
            var lambda = compile.Arguments.Length == 1 ? QuotedLambda(compile.Arguments[0].Value) : null;
            if (lambda == null || lambda.Body.Operations.Length != 1 || !(lambda.Body.Operations[0] is IReturnOperation ret) || ret.ReturnedValue == null) return null;
            var ps = lambda.Symbol.Parameters;
            if (ps.Length != inv.Arguments.Length || IsSequenceType(inv.Type)) return null;
            // (the lambda's parameters, bound in this frame while its body runs: they are no other variable)
            var args = Enumerable.Range(0, ps.Length).Select(k => Eval(inv.Arguments.First(a => a.Parameter.Ordinal == k).Value, f, spec)).ToList();
            for (int k = 0; k < ps.Length; k++) f.Vars[ps[k]] = args[k];
            try { return Eval(ret.ReturnedValue, f, spec); }
            finally { foreach (var p in ps) f.Vars.Remove(p); }
        }

        /// <summary>The navigation an Include lambda names (x => x.Customer).</summary>
        private IPropertySymbol Navigation(IOperation lambda) =>
            QuotedLambda(lambda) is IAnonymousFunctionOperation fn && fn.Body.Operations.Length == 1 && fn.Body.Operations[0] is IReturnOperation ret &&
            Unwrapped(ret.ReturnedValue) is IPropertyReferenceOperation pr && pr.Instance is IParameterReferenceOperation ? pr.Property : null;

        private static IOperation Unwrapped(IOperation op)
        {
            while (op is IConversionOperation c && c.IsImplicit) op = c.Operand;
            return op;
        }

        /// <summary>
        /// A lambda as an argument: made into a delegate, or quoted as an expression tree (in a flow graph's
        /// operations, the lambda's own operation, from the semantic model).
        /// </summary>
        private IAnonymousFunctionOperation QuotedLambda(IOperation arg)
        {
            switch (arg)
            {
                case IDelegateCreationOperation d: return QuotedLambda(d.Target);
                case IConversionOperation c: return QuotedLambda(c.Operand);
                case IAnonymousFunctionOperation a: return a;
                case IFlowAnonymousFunctionOperation fa when fa.Syntax.SyntaxTree == _model.SyntaxTree: return _model.GetOperation(fa.Syntax) as IAnonymousFunctionOperation;
                default: return null;
            }
        }

        private readonly Dictionary<IMethodSymbol, IMethodSymbol> _dbDefinitions = new Dictionary<IMethodSymbol, IMethodSymbol>(SymbolEqualityComparer.Default);

        /// <summary>
        /// The LINQ to Objects member a Queryable operator, or an EF ...Async one, is read as: the same name (less Async),
        /// with IQueryable for IEnumerable, Expression&lt;F&gt; for F, and EF's trailing CancellationToken left out.
        /// </summary>
        private IMethodSymbol EnumerableTwin(IMethodSymbol m)
        {
            if (Ef == null || m == null) return null;
            m = (m.ReducedFrom ?? m).OriginalDefinition;
            if (_dbDefinitions.TryGetValue(m, out var known)) return known;
            IMethodSymbol twin = null;
            bool async = IsEfMethod(m) && m.Name.EndsWith("Async") && m.ContainingType?.Name == "EntityFrameworkQueryableExtensions";
            if (IsQueryable(m) || async)
            {
                var name = async ? m.Name.Substring(0, m.Name.Length - "Async".Length) : m.Name;
                var ps = m.Parameters.Where(p => !(async && p.Type.Name == "CancellationToken")).ToList();
                var enumerable = _model.Compilation.GetTypeByMetadataName("System.Linq.Enumerable");
                twin = enumerable?.GetMembers(name).OfType<IMethodSymbol>().FirstOrDefault(e =>
                    e.Parameters.Length == ps.Count && e.TypeParameters.Length == m.TypeParameters.Length &&
                    e.Parameters.Zip(ps, (a, b) => SameShape(a.Type, b.Type, e, m)).All(x => x));
            }
            _dbDefinitions[m] = twin;
            return twin;
        }

        /// <summary>Does a parameter of the Enumerable member correspond to the Queryable one's?</summary>
        private static bool SameShape(ITypeSymbol e, ITypeSymbol q, IMethodSymbol em, IMethodSymbol qm)
        {
            if (e is ITypeParameterSymbol ep && q is ITypeParameterSymbol qp) return ep.Ordinal == qp.Ordinal;
            if (q is INamedTypeSymbol qn && qn.Name == "Expression" && qn.TypeArguments.Length == 1) return SameShape(e, qn.TypeArguments[0], em, qm);
            if (!(e is INamedTypeSymbol en) || !(q is INamedTypeSymbol qt)) return SymbolEqualityComparer.Default.Equals(e, q);
            string Name(INamedTypeSymbol t) => t.Name == "IQueryable" ? "IEnumerable" : t.Name == "IOrderedQueryable" ? "IOrderedEnumerable" : t.Name;
            return Name(en) == Name(qt) && en.TypeArguments.Length == qt.TypeArguments.Length &&
                   en.TypeArguments.Zip(qt.TypeArguments, (a, b) => SameShape(a, b, em, qm)).All(x => x);
        }

        /// <summary>An EF ...Async query operator (ToListAsync, FirstOrDefaultAsync, CountAsync...)?</summary>
        private bool IsEfAsyncQuery(IMethodSymbol m) =>
            m != null && IsEfMethod(m) && m.Name.EndsWith("Async") && (m.ReducedFrom ?? m).ContainingType?.Name == "EntityFrameworkQueryableExtensions";

        /// <summary>
        /// The table as a query running now sees it: n rows, each an entity of the table's type, a different object at
        /// each index, no two with the same key or the same value of a unique index, each passing the query filters.
        /// Run without tracking, they are new objects whose navigations are null (or empty) unless included; run with
        /// tracking, they are what the context tracks for their keys, and they are tracked from here on.
        /// </summary>
        /// <summary>Which run of a query is being read: one reading of each table per run (a definition may read its source twice).</summary>
        private int _queryRun;
        private readonly Dictionary<(DbTable, int, bool), Sequence> _readings = new Dictionary<(DbTable, int, bool), Sequence>();

        private Sequence TableSequence(DbTable t, Frame f)
        {
            bool entitiesOut = _queryResult != null && Mentions(_queryResult, t.Entity.Type);
            var key = (t, _queryRun, entitiesOut);
            if (_readings.TryGetValue(key, out var read)) return read;
            return _readings[key] = ReadTable(t, f);
        }

        private Sequence ReadTable(DbTable t, Frame f)
        {
            int id = _materialized++;
            var e = t.Entity;
            var n = _z3.Fresh("rows", Sort.Int);
            AssumeSide(T.Le(T.Int(0), n));
            Term Row(Term i) => _z3.Apply("row#" + id, Sort.Int, new[] { i });
            Term Index(Term y) => _z3.Apply("row.index#" + id, Sort.Int, new[] { y });
            // (a row is Row(i) for some i: Index is its inverse at every i, so that needs no bounds, which the solver
            // would have to find; Row(i) past the rows stands for no object, and is counted made, so nothing new is it)
            Term IsRow(Term y) => T.Eq(Row(Index(y)), y);
            var iname = _z3.FreshName("i");
            var iv = new Term(iname, Sort.Int);
            AssumeSide(new Term($"(forall (({iname} Int)) (! {T.And(T.Eq(Index(Row(iv)), iv), NotNull(Row(iv)), f.Alloc != null && t.NoTracking ? T.Not(InSet(f.Alloc, Row(iv))) : T.True).S} :pattern ({Row(iv).S})))", Sort.Bool));
            AssumeSide(OverIndices("forall", T.Int(0), n, i => IsEntity(Row(i), e), Row));
            // no two rows share a key, or a unique index's value
            foreach (var key in e.Identifying)
                AssumeSide(TwoRows(n, Row, (a, b) => T.Not(T.And(key.Select(p => SameColumn(p, a, b, f)).ToArray()))));
            if (!t.IgnoreFilters)
                foreach (var filter in e.Filters)
                {
                    var body = (filter.Body.Operations.Length == 1 && filter.Body.Operations[0] is IReturnOperation r) ? r.ReturnedValue : null;
                    if (body != null)
                        AssumeSide(OverIndices("forall", T.Int(0), n, i => T.Coerce(InDatabase(() => ApplyValue(body, filter.Symbol.Parameters[0], Row(i), f), Row(i)), Sort.Bool), Row));
                }
            Term known = T.True;
            // (Count, Any, a projection of columns: the database's values, nothing tracked)
            bool entitiesOut = _queryResult != null && Mentions(_queryResult, e.Type);
            if (!entitiesOut)
            {
            }
            else if (t.NoTracking)
            {
                // new objects
                if (f.Alloc != null)
                    f.Alloc = Pointwise("materialized", Sort.Row, $"(ite {IsRow(new Term("y", Sort.Int)).S} 1 (select {f.Alloc.S} y))");
                // (with identity resolution, EF fixes up navigations from the other rows it loads: nothing is known of them)
                if (!t.IdentityResolution && !t.UnknownInclude) Navigations(t, n, Row, IsRow, f);
                // no other code reaches them, if the method lets none out
                if (TrackerModel("Unshared") is IMethodSymbol unshared && EntitiesStayHere())
                {
                    var was = FieldMap(f, unshared);
                    f.Link = null;
                    f.Fields[FieldEffects.Key(unshared)] = Pointwise("unshared", Sort.Row, $"(ite {IsRow(new Term("y", Sort.Int)).S} 1 (select {was.S} y))");
                }
                // what the context read of them: their concurrency tokens, each at its key (TokenKey)
                var heapTokens = e.Tokens.Where(FieldEffects.IsHeapField).ToList();
                if (TrackerModel("Read") != null && heapTokens.Count > 0)
                {
                    var y = new Term("y", Sort.Int);
                    var read = ModelRow("Read", t.Context, f);
                    var tokens = ModelRow("TokenRead", t.Context, f);
                    SetModelRow("Read", t.Context, Pointwise("read", Sort.Row, $"(ite {IsRow(y).S} 1 (select {read.S} y))"), f);
                    var of = _z3.Apply("token.of", Sort.Int, new[] { y });
                    var no = _z3.Apply("token.no", Sort.Int, new[] { y });
                    TokenKey(T.Int(0), 0); // (its axiom)
                    var isKey = T.And(T.Eq(_z3.Apply("token.key", Sort.Int, new[] { of, no }), y), IsRow(of), T.Le(T.Int(0), no), T.Lt(no, T.Int(heapTokens.Count)));
                    Term value = T.Int(0);
                    for (int j = heapTokens.Count - 1; j >= 0; j--)
                        value = T.Ite(T.Eq(no, T.Int(j)), TokenValue(heapTokens[j], of, f), value);
                    SetModelRow("TokenRead", t.Context, Pointwise("tokenRead", Sort.Row, $"(ite {isKey.S} {value.S} (select {tokens.S} y))"), f);
                }
            }
            else if (TrackerModel("State") is IMethodSymbol state)
            {
                // what it tracked before: if it tracked no entity of this type, the rows are new and the database's
                var states = FieldMap(f, state);
                var tracked = Named(T.Select(states, t.Context, Sort.Row), "tracked");
                var on = _z3.FreshName("o");
                var o = new Term(on, Sort.Int);
                known = new Term($"(forall (({on} Int)) (! (=> (distinct (select {tracked.S} {on}) 0) (not {IsEntity(o, e).S})) :pattern ((select {tracked.S} {on}))))", Sort.Bool);
                // identity: a row whose key the context tracks is that instance
                if (e.Key.Count > 0)
                    AssumeSide(OverIndices("forall", T.Int(0), n, i =>
                    {
                        var yn = _z3.FreshName("y");
                        var y = new Term(yn, Sort.Int);
                        var same = T.And(T.Not(T.Eq(T.Select(tracked, y, Sort.Int), T.Int(0))), IsEntity(y, e), SameKey(e, y, Row(i), f));
                        return new Term($"(forall (({yn} Int)) (! (=> {same.S} (= {Row(i).S} {yn})) :pattern ((select {tracked.S} {yn}))))", Sort.Bool);
                    }, Row));
                // an included reference is the row its foreign key names, when the context tracked none of these rows
                // before (so their keys are the database's): EF sets it to the instance it tracks for that key
                if (!t.UnknownInclude)
                    foreach (var nav in e.References.Where(r => t.Includes.Contains(r) && FieldEffects.IsHeapField(r)))
                        if (e.ForeignKeys.TryGetValue(nav, out var fk) && Ef.EntityOf(nav.Type) is EfModel.Entity p && p.Key.Count == 1)
                        {
                            var guard = known;
                            AssumeSide(T.Implies(guard, OverIndices("forall", T.Int(0), n, i =>
                            {
                                var v = T.Coerce(T.Select(FieldMap(f, nav), Row(i), Sort.Int), Sort.Int);
                                return T.Or(T.Not(NotNull(v)), T.And(IsEntity(v, p), ForeignKeyMatches(fk, Row(i), p.Key[0], v, f) ?? T.True));
                            }, Row)));
                        }
                // every level the Include paths load, as without tracking, when the context tracked none of their types
                // before either: then all of it is the database's, and what EF fixes up from is only what this loads
                if (t.IncludePaths.Count > 0 && !t.UnknownInclude)
                {
                    var types = t.IncludePaths.SelectMany(p => p).Select(nav => Ef.EntityOf(EfModel.NavigationTarget(nav.Type, out _)))
                        .Where(x => x != null).Distinct().ToList();
                    Term NoneTracked(EfModel.Entity of)
                    {
                        var vn = _z3.FreshName("o");
                        var v = new Term(vn, Sort.Int);
                        return new Term($"(forall (({vn} Int)) (! (=> (distinct (select {tracked.S} {vn}) 0) (not {IsEntity(v, of).S})) :pattern ((select {tracked.S} {vn}))))", Sort.Bool);
                    }
                    var all = T.And(new[] { known }.Concat(types.Select(NoneTracked)).ToArray());
                    var name = "rows.loaded#" + _materialized++;
                    System.Func<Term, Term> isRow = y => _z3.Apply(name, Sort.Bool, new[] { T.Coerce(y, Sort.Int) });
                    AssumeSide(OverIndices("forall", T.Int(0), n, i => isRow(Row(i)), Row));
                    _madeBelow = new List<(System.Func<Term, Term>, System.Func<Term, Term>)>();
                    try { Loaded(t, e, isRow, t.IncludePaths, f, all); }
                    finally { MarkMade(f, all); }
                    // and what they load is tracked from here on, unchanged: of an entity of those types the context
                    // didn't track, whether it does now isn't known (so a later query doesn't take it for untracked)
                    var maybe = _z3.Fresh("loadedState", Sort.Row);
                    var yv = new Term("y", Sort.Int);
                    var ofTypes = T.Or(types.Select(x => IsEntity(yv, x)).ToArray());
                    var now = Pointwise("tracked", Sort.Row, $"(ite (and (= (select {tracked.S} y) 0) {ofTypes.S}) (ite (= (select {maybe.S} y) 1) {Unchanged} 0) (select {tracked.S} y))");
                    f.Link = null;
                    f.Fields[FieldEffects.Key(state)] = T.Store(states, t.Context, now);
                    states = FieldMap(f, state);
                    tracked = Named(T.Select(states, t.Context, Sort.Row), "tracked");
                }
                // tracked from here on
                f.Link = null;
                var after = Pointwise("tracked", Sort.Row, $"(ite (and {IsRow(new Term("y", Sort.Int)).S} (= (select {tracked.S} y) 0)) 1 (select {tracked.S} y))");
                f.Fields[FieldEffects.Key(state)] = T.Store(states, t.Context, after);
            }
            return new Sequence { Length = n, Element = Row, ElementType = e.Type, Known = known };
        }

        /// <summary>
        /// The navigations of rows read without tracking: one not included is null, or a collection with an empty
        /// list for initializer is that, empty; an included reference is the row its foreign key names (not null, for a
        /// key that can't be null), and an included List holds only rows whose foreign key is this row's key; each
        /// passing its type's query filters, unless the query ignores them.
        /// </summary>
        /// <summary>The entity passes its type's query filters (true where the query ignores them).</summary>
        private Term Filtered(DbTable t, EfModel.Entity of, Term o, Frame f)
        {
            if (t.IgnoreFilters) return T.True;
            var all = new List<Term>();
            foreach (var filter in of.Filters)
                if (filter.Body.Operations.Length == 1 && filter.Body.Operations[0] is IReturnOperation r)
                    all.Add(T.Coerce(InDatabase(() => ApplyValue(r.ReturnedValue, filter.Symbol.Parameters[0], o, f), o), Sort.Bool));
            return T.And(all.ToArray());
        }

        /// <summary>The dependent's foreign key is the principal's key (null where a column isn't followed).</summary>
        private Term ForeignKeyMatches(IPropertySymbol fk, Term dependent, IPropertySymbol key, Term principal, Frame f)
        {
            var fkv = KeyColumn(fk, dependent, f);
            var kv = KeyColumn(key, principal, f);
            if (fkv == null || kv == null) return null;
            return IsNullableValue(fk.Type) ? T.And(HasValue(fkv), T.Eq(T.Coerce(ValueOf(fkv, fk.Type), kv.Sort), kv)) : T.Eq(T.Coerce(fkv, kv.Sort), kv);
        }

        /// <summary>
        /// For every object y the predicate holds of, body(y) (triggered by the predicate); the side facts reading the
        /// body gives are quantified the same way, not left naming y outside its quantifier (as OverIndices does).
        /// </summary>
        private Term ForEachObject(System.Func<Term, Term> holds, System.Func<Term, Term> body)
        {
            var name = _z3.FreshName("y");
            var y = new Term(name, Sort.Int);
            _quantDepth++;
            int factLevels = _quantFacts.Count;
            _quantFacts.Push(new List<Term>());
            bool wasCode = _codeMode;
            _codeMode = false;
            _foreignSpec++;
            try
            {
                var b = AsBool(body(y));
                var collected = _quantFacts.Pop();
                foreach (var plain in collected.Where(x => !x.S.Contains(name))) AssumeSide(plain);
                var facts = T.And(collected.Where(x => x.S.Contains(name)).ToArray());
                var guard = holds(y);
                if (facts != T.True) AssumeSide(new Term($"(forall (({name} Int)) (! {T.Implies(guard, facts).S} :pattern ({guard.S})))", Sort.Bool));
                return new Term($"(forall (({name} Int)) (! {T.Implies(guard, b).S} :pattern ({guard.S})))", Sort.Bool);
            }
            finally
            {
                while (_quantFacts.Count > factLevels) _quantFacts.Pop();
                _foreignSpec--;
                _codeMode = wasCode;
                _quantDepth--;
            }
        }

        /// <summary>The Include paths that go on from this navigation, without it.</summary>
        private static List<List<IPropertySymbol>> PathsAfter(List<List<IPropertySymbol>> paths, IPropertySymbol nav) =>
            paths.Where(p => p.Count > 1 && SymbolEqualityComparer.Default.Equals(p[0], nav)).Select(p => p.Skip(1).ToList()).ToList();

        /// <summary>
        /// The objects an Include path loads below the rows (the predicate <paramref name="loaded"/> holds of them),
        /// as the rows' own: an included reference is the row its foreign key names, an included List holds only rows
        /// with this key, each through its type's filters; and so on down each path.
        /// </summary>
        /// <summary>
        /// What EF made below the rows, as (which objects, what of each): new objects, marked allocated so that what is
        /// made after the query is none of them (MarkMade).
        /// </summary>
        private List<(System.Func<Term, Term> holds, System.Func<Term, Term> obj)> _madeBelow;

        /// <summary>
        /// The objects EF made below the rows are allocated (and, where <paramref name="guard"/> holds, weren't
        /// before): M(z) holds of each, and allocation is M or what it was.
        /// </summary>
        private void MarkMade(Frame f, Term guard)
        {
            var made = _madeBelow;
            _madeBelow = null;
            if (made == null || made.Count == 0 || f.Alloc == null) return;
            var name = "made.below#" + _materialized++;
            Term M(Term z) => _z3.Apply(name, Sort.Bool, new[] { T.Coerce(z, Sort.Int) });
            var before = f.Alloc;
            foreach (var (holds, obj) in made)
                AssumeSide(ForEachObject(holds, y => T.Implies(NotNull(obj(y)),
                    T.And(M(obj(y)), guard == null ? T.Not(InSet(before, obj(y))) : T.Implies(guard, T.Not(InSet(before, obj(y))))))));
            f.Alloc = Pointwise("madeBelow", Sort.Row, $"(ite {M(new Term("y", Sort.Int)).S} 1 (select {before.S} y))");
        }

        private void Loaded(DbTable t, EfModel.Entity e, System.Func<Term, Term> loaded, List<List<IPropertySymbol>> paths, Frame f, Term guard = null)
        {
            foreach (var nav in paths.Select(p => p[0]).Distinct<IPropertySymbol>(SymbolEqualityComparer.Default).Where(FieldEffects.IsHeapField))
            {
                var after = PathsAfter(paths, nav);
                System.Func<Term, Term> next = null;
                if (after.Count > 0)
                {
                    var name = "loaded#" + _materialized++;
                    next = y => _z3.Apply(name, Sort.Bool, new[] { T.Coerce(y, Sort.Int) });
                }
                EfModel.Entity child = null;
                System.Func<Term, Term> fact = null;
                if (e.References.Contains(nav) && e.ForeignKeys.TryGetValue(nav, out var fk) && Ef.EntityOf(nav.Type) is EfModel.Entity p && p.Key.Count == 1)
                {
                    child = p;
                    bool required = fk.Type.IsValueType && !IsNullableValue(fk.Type);
                    fact = y =>
                    {
                        var v = T.Coerce(T.Select(FieldMap(f, nav), y, Sort.Int), Sort.Int);
                        var ok = T.And(NotNull(v), IsEntity(v, p), ForeignKeyMatches(fk, y, p.Key[0], v, f) ?? T.True, Filtered(t, p, v, f), next != null ? next(v) : T.True);
                        return required ? ok : T.Or(T.Not(NotNull(v)), ok);
                    };
                }
                else if (e.Collections.Contains(nav) && MadeAsList(nav) && ListModels && e.CollectionKeys.TryGetValue(nav, out var cfk) && e.Key.Count == 1 &&
                         Ef.EntityOf(EfModel.NavigationTarget(nav.Type, out _)) is EfModel.Entity d)
                {
                    child = d;
                    fact = y =>
                    {
                        var l = T.Coerce(T.Select(FieldMap(f, nav), y, Sort.Int), Sort.Int);
                        var size = T.Coerce(ModelAt(ListModel("Size"), new[] { l }, f), Sort.Int);
                        Term Element(Term j) => T.Coerce(T.Select(T.Select(FieldMap(f, ListModel("Items")), l, Sort.Row), j, Sort.Int), Sort.Int);
                        return T.And(NotNull(l), AsList(l), OverIndices("forall", T.Int(0), size, j =>
                        {
                            var el = Element(j);
                            return T.And(NotNull(el), IsEntity(el, d), ForeignKeyMatches(cfk, el, e.Key[0], y, f) ?? T.True, Filtered(t, d, el, f), next != null ? next(el) : T.True);
                        }, pattern: j => T.Select(T.Select(FieldMap(f, ListModel("Items")), l, Sort.Row), j, Sort.Int)));
                    };
                }
                else if (e.Collections.Contains(nav) && MadeAsSet(nav) && e.CollectionKeys.TryGetValue(nav, out var sfk) && e.Key.Count == 1 &&
                         Ef.EntityOf(EfModel.NavigationTarget(nav.Type, out _)) is EfModel.Entity sd)
                {
                    child = sd;
                    fact = y => SetHolds(t, T.Coerce(T.Select(FieldMap(f, nav), y, Sort.Int), Sort.Int), sd, sfk, e.Key[0], y, next, f);
                }
                if (fact == null) continue;
                _madeBelow?.Add((loaded, y => T.Coerce(T.Select(FieldMap(f, nav), y, Sort.Int), Sort.Int)));
                var each = ForEachObject(loaded, fact);
                AssumeSide(guard == null ? each : T.Implies(guard, each));
                if (next != null) Loaded(t, child, next, after, f, guard);
            }
        }

        private void Navigations(DbTable t, Term n, System.Func<Term, Term> Row, System.Func<Term, Term> IsRow, Frame f)
        {
            _madeBelow = new List<(System.Func<Term, Term>, System.Func<Term, Term>)>();
            try { RowNavigations(t, n, Row, IsRow, f); }
            finally { MarkMade(f, null); }
        }

        private void RowNavigations(DbTable t, Term n, System.Func<Term, Term> Row, System.Func<Term, Term> IsRow, Frame f)
        {
            var e = t.Entity;
            Term Filtered(EfModel.Entity of, Term o) => this.Filtered(t, of, o, f);
            Term Matches(IPropertySymbol fk, Term dependent, IPropertySymbol key, Term principal) => ForeignKeyMatches(fk, dependent, key, principal, f);
            // what the Include paths load, at any level (EF may fix up a row's navigation to one of them)
            var loadedTypes = new HashSet<ITypeSymbol>(t.IncludePaths.SelectMany(p => p).Select(nav => EfModel.NavigationTarget(nav.Type, out _)?.OriginalDefinition)
                .Where(x => x != null), SymbolEqualityComparer.Default);
            // the objects the paths load below the first level: marked by a predicate of each first navigation's
            System.Func<Term, Term> Next(IPropertySymbol nav)
            {
                var after = PathsAfter(t.IncludePaths, nav);
                if (after.Count == 0 || !(Ef.EntityOf(EfModel.NavigationTarget(nav.Type, out _)) is EfModel.Entity child)) return null;
                var name = "loaded#" + _materialized++;
                System.Func<Term, Term> next = y => _z3.Apply(name, Sort.Bool, new[] { T.Coerce(y, Sort.Int) });
                Loaded(t, child, next, after, f);
                return next;
            }
            foreach (var nav in e.References.Where(FieldEffects.IsHeapField))
            {
                if (!t.Includes.Contains(nav))
                {
                    if (loadedTypes.Contains(nav.Type.OriginalDefinition)) continue;
                    // (written into its map, so any read of it at a row sees it)
                    var before = FieldMap(f, nav);
                    f.Link = null;
                    f.Fields[FieldEffects.Key(nav)] = Pointwise("materialized", MapSort(nav), $"(ite {IsRow(new Term("y", Sort.Int)).S} 0 (select {before.S} y))");
                    continue;
                }
                if (!e.ForeignKeys.TryGetValue(nav, out var fk) || !(Ef.EntityOf(nav.Type) is EfModel.Entity p) || p.Key.Count != 1) continue;
                bool required = fk.Type.IsValueType && !IsNullableValue(fk.Type);
                var deeper = Next(nav);
                AssumeSide(OverIndices("forall", T.Int(0), n, i =>
                {
                    var o = Row(i);
                    var v = T.Coerce(T.Select(FieldMap(f, nav), o, Sort.Int), Sort.Int);
                    var match = Matches(fk, o, p.Key[0], v) ?? T.True;
                    var loaded = T.And(NotNull(v), IsEntity(v, p), match, Filtered(p, v), deeper != null ? deeper(v) : T.True);
                    return required ? loaded : T.Or(T.Not(NotNull(v)), loaded);
                }, Row));
            }
            // what EF made for these rows, a list or a row it loaded with them: new objects (where not null: a list is
            // never, a reference where it was loaded), one for each row, which no other code reaches if the method lets
            // none out. Made(y) is exactly these: y is the one made for the row its inverse names.
            var newObjects = new List<System.Func<Term, Term>>();
            void Unshared(System.Func<Term, Term> made) => newObjects.Add(made);
            void Allocated()
            {
                if (newObjects.Count == 0) return;
                var made = new List<Term>();
                var yv = new Term("y", Sort.Int);
                var before = f.Alloc;
                foreach (var m in newObjects)
                {
                    var name = "made.row#" + _materialized++;
                    Term Inverse(Term y) => _z3.Apply(name, Sort.Int, new[] { y });
                    AssumeSide(OverIndices("forall", T.Int(0), n, i => T.Implies(NotNull(m(Row(i))),
                        T.And(T.Eq(Inverse(m(Row(i))), i), before != null ? T.Not(InSet(before, m(Row(i)))) : T.True)), Row));
                    var at = Inverse(yv);
                    made.Add(T.And(NotNull(yv), T.Le(T.Int(0), at), T.Lt(at, n), T.Eq(m(Row(at)), yv)));
                }
                var isMade = T.Or(made.ToArray());
                if (before != null) f.Alloc = Pointwise("made", Sort.Row, $"(ite {isMade.S} 1 (select {before.S} y))");
                if (TrackerModel("Unshared") is IMethodSymbol unshared && EntitiesStayHere())
                {
                    var was = FieldMap(f, unshared);
                    f.Link = null;
                    f.Fields[FieldEffects.Key(unshared)] = Pointwise("unshared", Sort.Row, $"(ite {isMade.S} 1 (select {was.S} y))");
                }
            }
            foreach (var nav in e.References.Where(r => t.Includes.Contains(r) && FieldEffects.IsHeapField(r) && e.ForeignKeys.ContainsKey(r)))
                Unshared(o => T.Coerce(T.Select(FieldMap(f, nav), o, Sort.Int), Sort.Int));
            if (!ListModels) { Allocated(); return; }
            foreach (var nav in e.Collections.Where(c => FieldEffects.IsHeapField(c) && MadeAsSet(c) &&
                (t.Includes.Contains(c) || EmptyListInitializer(c) == true && !loadedTypes.Contains(EfModel.NavigationTarget(c.Type, out _)?.OriginalDefinition))))
                Unshared(o => T.Coerce(T.Select(FieldMap(f, nav), o, Sort.Int), Sort.Int));
            foreach (var nav in e.Collections.Where(c => FieldEffects.IsHeapField(c) && MadeAsSet(c)))
            {
                var d = Ef.EntityOf(EfModel.NavigationTarget(nav.Type, out _));
                if (d == null) continue;
                if (!t.Includes.Contains(nav))
                {
                    if (!loadedTypes.Contains(d.Type.OriginalDefinition) && EmptyListInitializer(nav) is bool empty)
                        AssumeSide(OverIndices("forall", T.Int(0), n, i =>
                        {
                            var l = T.Coerce(T.Select(FieldMap(f, nav), Row(i), Sort.Int), Sort.Int);
                            return empty ? SetEmpty(l, f) : T.Not(NotNull(l));
                        }, Row));
                    continue;
                }
                if (!e.CollectionKeys.TryGetValue(nav, out var fk) || e.Key.Count != 1) continue;
                var deeper = Next(nav);
                AssumeSide(OverIndices("forall", T.Int(0), n, i =>
                    SetHolds(t, T.Coerce(T.Select(FieldMap(f, nav), Row(i), Sort.Int), Sort.Int), d, fk, e.Key[0], Row(i), deeper, f), Row));
            }
            foreach (var nav in e.Collections.Where(c => FieldEffects.IsHeapField(c) && MadeAsList(c) &&
                (t.Includes.Contains(c) || EmptyListInitializer(c) == true && !loadedTypes.Contains(EfModel.NavigationTarget(c.Type, out _)?.OriginalDefinition))))
                Unshared(o => T.Coerce(T.Select(FieldMap(f, nav), o, Sort.Int), Sort.Int));
            Allocated();
            foreach (var nav in e.Collections.Where(c => FieldEffects.IsHeapField(c) && MadeAsList(c)))
            {
                var d = Ef.EntityOf(EfModel.NavigationTarget(nav.Type, out _));
                if (d == null) continue;
                if (!t.Includes.Contains(nav))
                {
                    if (!loadedTypes.Contains(d.Type.OriginalDefinition) && EmptyListInitializer(nav) is bool empty)
                        AssumeSide(OverIndices("forall", T.Int(0), n, i =>
                        {
                            var l = T.Coerce(T.Select(FieldMap(f, nav), Row(i), Sort.Int), Sort.Int);
                            return empty ? T.And(NotNull(l), AsList(l), T.Eq(T.Coerce(ModelAt(ListModel("Size"), new[] { l }, f), Sort.Int), T.Int(0))) : T.Not(NotNull(l));
                        }, Row));
                    continue;
                }
                if (!e.CollectionKeys.TryGetValue(nav, out var fk) || e.Key.Count != 1) continue;
                var deeper = Next(nav);
                AssumeSide(OverIndices("forall", T.Int(0), n, i =>
                {
                    var o = Row(i);
                    var l = T.Coerce(T.Select(FieldMap(f, nav), o, Sort.Int), Sort.Int);
                    var size = T.Coerce(ModelAt(ListModel("Size"), new[] { l }, f), Sort.Int);
                    var each = OverIndices("forall", T.Int(0), size, j =>
                    {
                        var el = T.Coerce(T.Select(T.Select(FieldMap(f, ListModel("Items")), l, Sort.Row), j, Sort.Int), Sort.Int);
                        return T.And(NotNull(el), IsEntity(el, d), Matches(fk, el, e.Key[0], o) ?? T.True, Filtered(d, el), deeper != null ? deeper(el) : T.True);
                    });
                    return T.And(NotNull(l), AsList(l), each);
                }, Row));
            }
        }

        /// <summary>An initializer that leaves the property null (null, null!, default): as if there were none.</summary>
        private static bool NullInitializer(Microsoft.CodeAnalysis.CSharp.Syntax.ExpressionSyntax init)
        {
            while (init is Microsoft.CodeAnalysis.CSharp.Syntax.PostfixUnaryExpressionSyntax bang && bang.IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.SuppressNullableWarningExpression)) init = bang.Operand;
            return init is Microsoft.CodeAnalysis.CSharp.Syntax.LiteralExpressionSyntax l && (l.IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.NullLiteralExpression) || l.IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.DefaultLiteralExpression));
        }

        /// <summary>A HashSet navigation (as declared): its members are what EF loads, or what its initializer made.</summary>
        private bool MadeAsSet(IPropertySymbol nav) => IsSetType(nav.Type) && SetModel("Members") != null && SetModel("Size") != null;

        /// <summary>
        /// The set l holds only rows of d whose foreign key is the principal's key, each through d's filters (and
        /// <paramref name="next"/> of each, for what a path loads below it).
        /// </summary>
        private Term SetHolds(DbTable t, Term l, EfModel.Entity d, IPropertySymbol fk, IPropertySymbol key, Term principal, System.Func<Term, Term> next, Frame f)
        {
            var members = T.Select(FieldMap(f, SetModel("Members")), l, Sort.Row);
            var zn = _z3.FreshName("z");
            var z = new Term(zn, Sort.Int);
            var member = SetMember(members, z, d.Type);
            var each = T.And(NotNull(z), IsEntity(z, d), ForeignKeyMatches(fk, z, key, principal, f) ?? T.True, Filtered(t, d, z, f), next != null ? next(z) : T.True);
            return T.And(NotNull(l), new Term($"(forall (({zn} Int)) (! (=> {member.S} {each.S}) :pattern ({T.Select(members, z, Sort.Int).S})))", Sort.Bool));
        }

        /// <summary>A set made empty: no members, size 0.</summary>
        private Term SetEmpty(Term l, Frame f) =>
            T.And(NotNull(l), T.Eq(T.Coerce(ModelAt(SetModel("Size"), new[] { l }, f), Sort.Int), T.Int(0)),
                  T.Eq(T.Select(FieldMap(f, SetModel("Members")), l, Sort.Row), T.ConstRow(T.Int(0))));

        /// <summary>A List, not an array: what reading it through IList or ICollection goes by.</summary>
        private Term AsList(Term l) => T.And(IsListObject(l), T.Not(IsArrayObject(l)));

        /// <summary>
        /// Is a collection navigation a List&lt;T&gt; when EF makes or loads it? Of that type, or IList&lt;T&gt; (EF makes
        /// a List), or another collection interface whose initializer makes a List.
        /// </summary>
        private bool MadeAsList(IPropertySymbol nav)
        {
            if (IsListType(nav.Type)) return true;
            if (!(nav.Type is INamedTypeSymbol n) || n.TypeKind != TypeKind.Interface || n.TypeArguments.Length != 1) return false;
            var decl = nav.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() as Microsoft.CodeAnalysis.CSharp.Syntax.PropertyDeclarationSyntax;
            var init = NullInitializer(decl?.Initializer?.Value) ? null : decl?.Initializer?.Value;
            if (init == null) return n.OriginalDefinition.ToDisplayString() == "System.Collections.Generic.IList<T>";
            if (nav.ContainingType.InstanceConstructors.Any(c => !c.IsImplicitlyDeclared)) return false;
            var made = _model.Compilation.GetSemanticModel(init.SyntaxTree).GetTypeInfo(init).Type;
            if (init is Microsoft.CodeAnalysis.CSharp.Syntax.CollectionExpressionSyntax)
                return n.OriginalDefinition.ToDisplayString() is "System.Collections.Generic.IList<T>" or "System.Collections.Generic.ICollection<T>";
            return made != null && IsListType(made);
        }

        /// <summary>
        /// What a collection navigation is when EF doesn't load it, made by its type's constructor: true for an empty
        /// list (an initializer new(), new List&lt;T&gt;() or []), false for null (no initializer), null if unknown
        /// (a constructor of the type's own, or another initializer).
        /// </summary>
        private static bool? EmptyListInitializer(IPropertySymbol nav)
        {
            if (nav.ContainingType.InstanceConstructors.Any(c => !c.IsImplicitlyDeclared)) return null;
            if (!(nav.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() is Microsoft.CodeAnalysis.CSharp.Syntax.PropertyDeclarationSyntax decl)) return null;
            switch (NullInitializer(decl.Initializer?.Value) ? null : decl.Initializer?.Value)
            {
                case null: return false;
                case Microsoft.CodeAnalysis.CSharp.Syntax.ImplicitObjectCreationExpressionSyntax io when io.ArgumentList.Arguments.Count == 0 && io.Initializer == null: return true;
                case Microsoft.CodeAnalysis.CSharp.Syntax.ObjectCreationExpressionSyntax oc when (oc.ArgumentList?.Arguments.Count ?? 0) == 0 && oc.Initializer == null: return true;
                case Microsoft.CodeAnalysis.CSharp.Syntax.CollectionExpressionSyntax ce when ce.Elements.Count == 0: return true;
                default: return null;
            }
        }

        /// <summary>Where TokenRead keeps an entity's j-th concurrency token: a key of its own for each (entity, j).</summary>
        private Term TokenKey(Term o, int j)
        {
            {
                // (assumed where it is used: a scope it was assumed in may have been left)
                var ov = new Term("o", Sort.Int);
                var jv = new Term("j", Sort.Int);
                var key = _z3.Apply("token.key", Sort.Int, new[] { ov, jv });
                var inverse = T.And(T.Eq(_z3.Apply("token.of", Sort.Int, new[] { key }), ov), T.Eq(_z3.Apply("token.no", Sort.Int, new[] { key }), jv));
                _z3.Assume(new Term($"(forall ((o Int) (j Int)) (! {inverse.S} :pattern ({key.S})))", Sort.Bool));
            }
            return _z3.Apply("token.key", Sort.Int, new[] { T.Coerce(o, Sort.Int), T.Int(j) });
        }

        /// <summary>A concurrency token's value at an object, as TokenRead keeps it.</summary>
        private Term TokenValue(IPropertySymbol token, Term o, Frame f) =>
            T.Coerce(T.Select(FieldMap(f, token), T.Coerce(o, Sort.Int), ValueSort(token) == Sort.Row ? Sort.Row : Sort.Int), Sort.Int);

        /// <summary>Every concurrency token of o is the value the context read (where it read o).</summary>
        private void TokensAsRead(Term c, Term o, EfModel.Entity e, Frame f, SyntaxNode at, string then)
        {
            var tokens = e.Tokens.Where(FieldEffects.IsHeapField).ToList();
            for (int j = 0; j < tokens.Count; j++)
                ProveEf(T.Implies(AsBool(Model("Read", c, f, o)), T.Eq(TokenValue(tokens[j], o, f), T.Coerce(Model("TokenRead", c, f, TokenKey(o, j)), Sort.Int))), TokenId, at,
                    $"'{at}' takes {tokens[j].Name}, a concurrency token, as the value the row had when read, but it was changed since: " +
                    $"EF would check the row against the new value. {then}");
        }

        /// <summary>The type of the query call being read (its result, or its task's), for <see cref="TableSequence"/>.</summary>
        private ITypeSymbol _queryResult;

        private static bool Mentions(ITypeSymbol t, ITypeSymbol entity) =>
            SymbolEqualityComparer.Default.Equals(t.OriginalDefinition, entity.OriginalDefinition) ||
            t is INamedTypeSymbol n && n.TypeArguments.Any(a => Mentions(a, entity)) || t is IArrayTypeSymbol a && Mentions(a.ElementType, entity);

        /// <summary>An object of the entity's type (without the facts ClassTest assumes, so of a bound variable too).</summary>
        private Term IsEntity(Term o, EfModel.Entity e)
        {
            if (ModeledType(e.Type) is not INamedTypeSymbol d) return T.True;
            InPlay(d);
            return Isa(o, d);
        }

        /// <summary>A condition on every two rows at different indices.</summary>
        private Term TwoRows(Term n, System.Func<Term, Term> row, System.Func<Term, Term, Term> body)
        {
            var an = _z3.FreshName("i"); var bn = _z3.FreshName("j");
            var a = new Term(an, Sort.Int); var b = new Term(bn, Sort.Int);
            var guard = T.And(T.Le(T.Int(0), a), T.Lt(a, n), T.Le(T.Int(0), b), T.Lt(b, n), T.Not(T.Eq(a, b)));
            return new Term($"(forall (({an} Int) ({bn} Int)) (! {T.Implies(guard, body(row(a), row(b))).S} :pattern ({row(a).S} {row(b).S})))", Sort.Bool);
        }

        /// <summary>Two rows' values of a column are the same, as the database compares them (strings by its collation).</summary>
        private Term SameColumn(IPropertySymbol p, Term a, Term b, Frame f)
        {
            if (!FieldEffects.IsHeapField(p)) return _z3.Fresh("same", Sort.Bool);
            var map = FieldMap(f, p);
            var sort = SortOf(p.Type);
            var x = T.Select(map, a, sort == Sort.Row ? Sort.Row : Sort.Int);
            var y = T.Select(map, b, sort == Sort.Row ? Sort.Row : Sort.Int);
            return p.Type.SpecialType == SpecialType.System_String ? CollationEqual(x, y) : T.Eq(x, y);
        }

        private int _inDatabase;

        /// <summary>The lazy queries on a database's tables (a table, or such a query, among their sources).</summary>
        private readonly HashSet<string> _databaseQueries = new HashSet<string>();

        private bool IsDatabaseQuery(Term t) => _tables.ContainsKey(T.Coerce(t, Sort.Int).S) || _databaseQueries.Contains(T.Coerce(t, Sort.Int).S);

        /// <summary>The rows a lambda the database evaluates is applied to, innermost last.</summary>
        private readonly Stack<Term[]> _databaseRows = new Stack<Term[]>();

        /// <summary>A query's lambda as the database evaluates it, on these rows: strings compared by its collation.</summary>
        private Term InDatabase(System.Func<Term> body, params Term[] rows)
        {
            _inDatabase++;
            _databaseRows.Push(rows.Where(r => r != null).ToArray());
            try { return body(); }
            finally { _inDatabase--; _databaseRows.Pop(); }
        }

        /// <summary>
        /// Spec.Equal in a lambda the database evaluates (Contains, a join's keys, a group's): strings by its collation, a
        /// value with a string in it (a tuple, an anonymous type) by what isn't known, and with SQL's null semantics,
        /// unknown where either side is null. Null for what compares as in .NET.
        /// </summary>
        private Term DatabaseEqual(ITypeSymbol t, Term a, Term b)
        {
            if (t == null) return null;
            bool HasString(ITypeSymbol x) =>
                x.SpecialType == SpecialType.System_String ||
                x is INamedTypeSymbol { IsTupleType: true } tuple && tuple.TupleElements.Any(e => HasString(e.Type)) ||
                x.IsAnonymousType && ((INamedTypeSymbol)x).GetMembers().OfType<IPropertySymbol>().Any(p => HasString(p.Type)) ||
                IsNullableValue(x) && HasString(Underlying(x));
            Term exact = null;
            if (t.SpecialType == SpecialType.System_String) exact = CollationEqual(a, b);
            else if (HasString(t) && !(Ef != null && Ef.ExactStrings))
                exact = _z3.Apply("database.equal:" + t.ToDisplayString(), Sort.Bool, new[] { T.Coerce(a, Sort.Int), T.Coerce(b, Sort.Int) });
            if (Ef != null && Ef.RelationalNulls && (IsNullableValue(t) || t.IsReferenceType))
            {
                Term IsNull(Term v) => IsNullableValue(t) ? T.Not(HasValue(v)) : T.Not(NotNull(T.Coerce(v, Sort.Int)));
                var rows = _databaseRows.Count > 0 ? _databaseRows.Peek() : System.Array.Empty<Term>();
                var unknown = _z3.Apply("relational.null.equal", Sort.Bool, rows.Select(r => T.Coerce(r, Sort.Int)).Concat(new[] { T.Coerce(a, Sort.Int), T.Coerce(b, Sort.Int) }).ToArray());
                if (exact == null)
                {
                    _inDatabase--;
                    try
                    {
                        exact = KnownEquality(t) ? T.Eq(a, b)
                            : IsNullableValue(t) && KnownEquality(Underlying(t)) ? T.And(T.Eq(HasValue(a), HasValue(b)), T.Implies(HasValue(a), T.Eq(ValueOf(a, t), ValueOf(b, t))))
                            : null;
                    }
                    finally { _inDatabase++; }
                    if (exact == null) return null;
                }
                return T.Ite(T.Or(IsNull(a), IsNull(b)), unknown, exact);
            }
            return exact;
        }

        private int _relationalNullsOff;

        /// <summary>
        /// With SQL's null semantics (UseRelationalNulls), == and != of two operands either of which may be null: as in
        /// C# where neither is, and where one is, unknown (SQL's unknown, which EF passes through a NOT, so a row is kept
        /// or not by what else the query says). Unknown for each row and comparison: nothing is known of such rows.
        /// </summary>
        private Term RelationalNullEquality(IBinaryOperation b, Frame f, SpecEnv spec)
        {
            if (_inDatabase == 0 || _relationalNullsOff > 0 || Ef == null || !Ef.RelationalNulls) return null;
            if (!(b.OperatorKind == BinaryOperatorKind.Equals || b.OperatorKind == BinaryOperatorKind.NotEquals)) return null;
            if (IsNullConstant(Unconverted(b.LeftOperand)) || IsNullConstant(Unconverted(b.RightOperand))) return null;
            Term MayBeNull(IOperation op)
            {
                var t = Unconverted(op).Type;
                if (IsNullableValue(t)) return T.Not(HasValue(Eval(Unconverted(op), f, spec)));
                if (t != null && t.IsReferenceType && Unconverted(op).Type.NullableAnnotation != NullableAnnotation.NotAnnotated)
                    return T.Not(NotNull(T.Coerce(Eval(Unconverted(op), f, spec), Sort.Int)));
                return null;
            }
            var nl = MayBeNull(b.LeftOperand);
            var nr = MayBeNull(b.RightOperand);
            if (nl == null && nr == null) return null;
            Term inCSharp;
            _relationalNullsOff++;
            try { inCSharp = AsBool(Eval(b, f, spec)); }
            finally { _relationalNullsOff--; }
            var rows = _databaseRows.Count > 0 ? _databaseRows.Peek() : System.Array.Empty<Term>();
            var unknown = _z3.Apply("relational.null#" + b.Syntax.SpanStart, Sort.Bool, rows.Select(r => T.Coerce(r, Sort.Int)).Append(T.Int(0)).ToArray());
            return T.Ite(T.Or(nl ?? T.False, nr ?? T.False), unknown, inCSharp);
        }

        /// <summary>
        /// Two strings equal as the database compares them (cv_collate, <see cref="CollationTheory"/>): an equivalence
        /// that equal strings satisfy, and nothing else is known of (SQL Server's default collation ignores case, and
        /// its = ignores trailing spaces).
        /// </summary>
        private Term CollationEqual(Term a, Term b) =>
            Ef != null && Ef.ExactStrings ? T.Eq(a, b) : new Term($"(cv_collate {T.Coerce(a, Sort.Int).S} {T.Coerce(b, Sort.Int).S})", Sort.Bool);

        internal const string CollationTheory =
            "(declare-fun cv_collate (Int Int) Bool)\n" +
            "(assert (forall ((x Int)) (! (cv_collate x x) :pattern ((cv_collate x x)))))\n" +
            "(assert (forall ((x Int) (y Int)) (! (=> (cv_collate x y) (cv_collate y x)) :pattern ((cv_collate x y)))))\n" +
            "(assert (forall ((x Int) (y Int) (z Int)) (! (=> (and (cv_collate x y) (cv_collate y z)) (cv_collate x z)) :pattern ((cv_collate x y) (cv_collate y z)))))";

        /// <summary>
        /// await of an EF ...Async query: other code runs while it does, then the query runs on the table as it is then
        /// (so what it gives is known past the await), and it may throw.
        /// </summary>
        private Term EfAwait(IInvocationOperation call, IAwaitOperation aw, Frame f, SpecEnv spec)
        {
            if (Ef == null) return null;
            if (!IsEfAsyncQuery(call.TargetMethod) || call.TargetMethod.Name.StartsWith("Execute"))
            {
                // SaveChangesAsync, FindAsync, AddAsync, BeginTransactionAsync, CommitAsync, ExecuteUpdateAsync...
                if (!(IsEfMethod(call.TargetMethod) || IsTransactionType(call.TargetMethod.ContainingType)) || !call.TargetMethod.Name.EndsWith("Async")) return null;
                Interleave(f);
                _efAwaited = true;
                var value = EfTrackerCall(call, f, spec);
                if (value == null) return null;
                return aw.Type == null || aw.Type.SpecialType == SpecialType.System_Void ? T.True : value;
            }
            Interleave(f);
            var result = LinqCall(call, f, spec);
            foreach (var a in call.Arguments.Where(a => a.Parameter.Type.Name == "CancellationToken")) Eval(a.Value, f, spec);
            if (result == null)
            {
                Eval(call, f, spec);
                result = aw.Type == null || aw.Type.SpecialType == SpecialType.System_Void ? T.True : Unknown(aw.Type, "awaited");
            }
            MayRaise(T.True, f, null);
            return result;
        }

        internal const string OrderId = "CSV1031", TranslateId = "CSV1032";

        private static readonly HashSet<string> EqualityOperators = new HashSet<string>
        {
            "Distinct", "DistinctBy", "GroupBy", "GroupJoin", "Join", "LeftJoin", "RightJoin", "Union", "UnionBy", "Intersect", "IntersectBy", "Except", "ExceptBy",
            "Contains", "SequenceEqual", "ToDictionary", "ToLookup", "ToHashSet", "CountBy", "AggregateBy", "IndexOf",
        };

        /// <summary>
        /// Does the operator compare values for equality as the database does? It compares strings by its collation and
        /// rows by every column, not as LINQ to Objects' definition says: such a query is a library call, which says
        /// nothing of what it gives. A join on a key that both compare alike (<see cref="ComparedAlike"/>) is read from
        /// its definition.
        /// </summary>
        private bool ComparesByEquality(IMethodSymbol definition, IMethodSymbol called)
        {
            if (!EqualityOperators.Contains(definition.Name)) return false;
            // (made in memory from the rows the database gave: compared as .NET does)
            if (definition.Name is "ToDictionary" or "ToLookup" or "ToHashSet") return false;
            // what is compared: a join's or a group's key, or the elements
            string compared = definition.Name switch
            {
                "Join" or "LeftJoin" or "GroupJoin" or "GroupBy" => "K",
                "Distinct" or "Union" or "Intersect" or "Except" or "Contains" => "T",
                // (not RightJoin: EF Core applies the left side's query filters after the join, which drops right
                // rows; not the By forms, nor SequenceEqual, IndexOf, CountBy, AggregateBy, which EF doesn't translate)
                _ => null,
            };
            var p = compared == null ? null : definition.TypeParameters.FirstOrDefault(t => t.Name == compared);
            return p == null || !DefinitionInstantiation(definition, called).TryGetValue(p, out var k) || !ComparedAlike(k);
        }

        private static readonly HashSet<string> SourceCombinations = new HashSet<string>
        { "Join", "LeftJoin", "RightJoin", "GroupJoin", "SelectMany", "Concat", "GroupBy", "Distinct", "Union", "Intersect", "Except" };

        /// <summary>
        /// Does the operator combine rows of two sources (a join, SelectMany, Concat), or rows that compare equal (a
        /// group, Distinct, a set operator)? The database gives the result in no order of theirs (SQL Server's hash
        /// join doesn't keep an outer row's matches together, nor GROUP BY the order keys first appear in): it is read
        /// in any.
        /// </summary>
        private static bool CombinesSources(IMethodSymbol definition) => SourceCombinations.Contains(definition.Name);

        /// <summary>
        /// Keys the database and .NET compare alike: integers, bool, enums and Guid, and those nullable (in a join, null
        /// matches nothing in either); strings where it compares them exactly (<see cref="EfModel.ExactStrings"/>). Not
        /// floating point and dates (by the column's precision).
        /// </summary>
        private bool ComparedAlike(ITypeSymbol t) =>
            t is INamedTypeSymbol { OriginalDefinition.SpecialType: SpecialType.System_Nullable_T } n ? ComparedAlike(n.TypeArguments[0]) :
            // (several columns: each compared alike)
            t is INamedTypeSymbol { IsTupleType: true } tuple ? tuple.TupleElements.All(e => ComparedAlike(e.Type)) :
            t.IsAnonymousType ? ((INamedTypeSymbol)t).GetMembers().OfType<IPropertySymbol>().All(p => ComparedAlike(p.Type)) :
            t.SpecialType == SpecialType.System_String ? Ef.ExactStrings :
            t.TypeKind == TypeKind.Enum ||
            t.SpecialType is SpecialType.System_Boolean or SpecialType.System_SByte or SpecialType.System_Byte or SpecialType.System_Int16 or
                SpecialType.System_UInt16 or SpecialType.System_Int32 or SpecialType.System_UInt32 or SpecialType.System_Int64 or SpecialType.System_UInt64 ||
            t.ToDisplayString() == "System.Guid";

        private static readonly HashSet<string> RowLimits = new HashSet<string>
        { "First", "FirstOrDefault", "Last", "LastOrDefault", "ElementAt", "ElementAtOrDefault", "Take", "Skip", "TakeLast", "SkipLast" };

        /// <summary>
        /// What a query the database runs must be: its lambdas ones EF translates to SQL (CSV1032), and where it keeps
        /// some rows by their place (First, Take, Skip...), an order that fixes it: by a key, or at most one row (CSV1031).
        /// </summary>
        private void DatabaseQueryChecks(IInvocationOperation inv, IInvocationOperation syntaxCall, IMethodSymbol definition,
                                         List<(IParameterSymbol, object)> args, Dictionary<int, Lambda> lambdas, Frame f)
        {
            if (!RowLimits.Contains(definition.Name)) return;
            var sourceOp = syntaxCall.Arguments.FirstOrDefault(a => a.Parameter.Ordinal == 0)?.Value ?? syntaxCall.Instance;
            if (sourceOp == null || OrderedByKey(sourceOp)) return;
            // at most one row: of a reading of the source (any reading: nothing is known of which this one is)
            var src = args[0].Item2 as Term;
            var outer = _queryResult;
            _queryResult = null;
            Sequence seq;
            try { seq = SequenceOfTerm(src, Unconverted(sourceOp).Type, f); }
            finally { _queryResult = outer; }
            var message = $"'{inv.Syntax}' keeps rows by their place in an order the database doesn't fix: order the query by a key " +
                          "(OrderBy, or ThenBy, ending in the key or a unique index), or show that at most one row matches";
            if (seq == null) { Report(OrderId, inv.Syntax, message, isError: true); return; }
            var count = seq.Length;
            var given = lambdas.Where(l => l.Key > 0).Select(l => l.Value).FirstOrDefault();
            var predicate = given == null ? null : new Lambda { Body = given.Body, P1 = given.P1, P2 = given.P2, Frame = f, Database = true };
            if (predicate != null && definition.Parameters.Length == 2 && definition.Parameters[1].Type.TypeKind == TypeKind.Delegate)
                count = Filter(seq, j => T.Coerce(ApplyLambda(predicate, seq.Element(j)), Sort.Bool), seq.ElementType, out _).Length;
            Prove(T.Implies(T.And(_guards.Append(seq.Known).ToArray()), T.Le(count, T.Int(1))), OrderId, inv.Syntax, message, assume: false);
        }

        private readonly HashSet<SyntaxNode> _translationChecked = new HashSet<SyntaxNode>();

        /// <summary>
        /// The lambdas of a Queryable operator or an EF one, which the database runs (CSV1032): checked once each, whether
        /// or not the verifier reads the query. A projection runs on the client when it is the query's last, so anything
        /// may be called there: Select's and SelectMany's are left out.
        /// </summary>
        private void TranslationChecks(IInvocationOperation inv)
        {
            if (Ef == null || !_codeMode) return;
            var m = inv.TargetMethod;
            if (!(IsQueryable(m) || IsEfMethod(m)) || m.Name == "Select" || m.Name == "SelectMany" || m.Name.StartsWith("Include") || m.Name.StartsWith("ThenInclude")) return;
            if (!_translationChecked.Add(inv.Syntax)) return;
            foreach (var a in inv.Arguments)
                if (a.Parameter.Type is INamedTypeSymbol p && p.Name == "Expression" && QuotedLambda(a.Value) is IAnonymousFunctionOperation fn) Translatable(fn);
        }

        /// <summary>Is the query (as written here) sorted by a set of columns that identifies a row?</summary>
        private bool OrderedByKey(IOperation op)
        {
            var keys = new HashSet<IPropertySymbol>(SymbolEqualityComparer.Default);
            EfModel.Entity entity = null;
            for (op = Unconverted(op); op is IInvocationOperation c; op = Unconverted(c.Arguments.FirstOrDefault(a => a.Parameter.Ordinal == 0)?.Value ?? c.Instance))
            {
                var name = c.TargetMethod.Name;
                if (name == "OrderBy" || name == "OrderByDescending" || name == "ThenBy" || name == "ThenByDescending")
                {
                    var key = c.Arguments.FirstOrDefault(a => a.Parameter.Ordinal == 1)?.Value;
                    if (key != null && Navigation(key) is IPropertySymbol p) { keys.Add(p); entity ??= Ef.EntityOf(p.ContainingType); }
                    if (name.StartsWith("OrderBy")) break;
                    continue;
                }
                if (name == "Select" || name == "SelectMany" || name == "GroupBy" || name.StartsWith("Join")) return false;
            }
            return entity != null && entity.Identifying.Any(set => set.All(keys.Contains));
        }

        /// <summary>
        /// A lambda of a query the database runs must be translatable: what depends on its parameters may only read
        /// mapped properties and navigations, and call what EF translates (operators, string and Math members, dates,
        /// LINQ over navigations and over lists the program passes in). Code of the program, or a property computed in
        /// C#, can't be sent to the database: EF throws when the query runs. What doesn't depend on the parameters is
        /// evaluated on the client first, so it may call anything.
        /// </summary>
        private void Translatable(IAnonymousFunctionOperation fn)
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
                    case IPropertyReferenceOperation pr when pr.Instance != null && Depends(pr.Instance) && Ef.EntityOf(pr.Property.ContainingType) is EfModel.Entity e && !Mapped(pr.Property, e):
                        why = $"'{pr.Property.Name}' isn't a column of {e.Type.Name} (it is computed in C#, or [NotMapped])";
                        break;
                }
                if (why != null) Report(TranslateId, op.Syntax, $"'{op.Syntax}' can't be translated to SQL: {why}; EF throws when the query runs. Compute it before the query, or after it (AsEnumerable)", isError: true);
            }
        }

        /// <summary>A column or a navigation: an auto-property with a setter, not [NotMapped].</summary>
        private static bool Mapped(IPropertySymbol p, EfModel.Entity e) =>
            e.References.Contains(p) || e.Collections.Contains(p) ||
            FieldEffects.IsHeapField(p) && p.SetMethod != null && !p.GetAttributes().Any(a => a.AttributeClass?.Name == "NotMappedAttribute");

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

        private static readonly HashSet<string> Filtering = new HashSet<string>
        { "First", "FirstOrDefault", "Single", "SingleOrDefault", "Last", "LastOrDefault", "Any", "Count", "LongCount" };

        /// <summary>
        /// M(source, p) on a database, for M one of <see cref="Filtering"/>: M(Where(source, p)), its overload without a
        /// predicate over one lazy Where. (The definitions with a predicate read Where(source, p) twice, and two filters
        /// of one reading of a table aren't known to agree.)
        /// </summary>
        private (IMethodSymbol, List<(IParameterSymbol, object)>)? FilteredFirst(IMethodSymbol definition, IMethodSymbol called, List<(IParameterSymbol, object)> args)
        {
            if (!Filtering.Contains(definition.Name) || definition.Parameters.Length != 2 || !(args[1].Item2 is Lambda) || !(args[0].Item2 is Term source)) return null;
            var defs = definition.ContainingType;
            var where = defs.GetMembers("Where").OfType<IMethodSymbol>().FirstOrDefault(w => w.Parameters.Length == 2 &&
                w.Parameters[1].Type is INamedTypeSymbol p && p.TypeArguments.Length == 2);
            var plain = defs.GetMembers(definition.Name).OfType<IMethodSymbol>().FirstOrDefault(x => x.Parameters.Length == 1);
            if (where == null || plain == null) return null;
            var q = _z3.Fresh("query", Sort.Int);
            AssumeSide(NotNull(q));
            var given = DefinitionInstantiation(definition, called);
            var map = new Dictionary<ITypeSymbol, ITypeSymbol>(SymbolEqualityComparer.Default);
            foreach (var (wp, dp) in where.TypeParameters.Zip(definition.TypeParameters, (a, b) => (a, b)))
                map[wp] = given.TryGetValue(dp, out var t) ? t : dp;
            _lazy[q.S] = new LazyQuery { Definition = where, Args = new List<(IParameterSymbol, object)> { (where.Parameters[0], source), (where.Parameters[1], args[1].Item2) }, Instantiation = map };
            _databaseQueries.Add(q.S);
            return (plain, new List<(IParameterSymbol, object)> { (plain.Parameters[0], q) });
        }

        /// <summary>The Tracker model function of that name (CsVerify.Ef), compiled in with EF Core.</summary>
        private IMethodSymbol TrackerModel(string name) =>
            _model.Compilation.GetTypeByMetadataName("CsVerify.Ef.Tracker")?.GetMembers(name).OfType<IMethodSymbol>().FirstOrDefault();
    }
}
