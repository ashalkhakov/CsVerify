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
            public bool IgnoreFilters;
            /// <summary>The navigations Include loads (at the first level).</summary>
            public HashSet<IPropertySymbol> Includes = new HashSet<IPropertySymbol>(SymbolEqualityComparer.Default);

            public DbTable With(System.Action<DbTable> change)
            {
                var t = new DbTable { Context = Context, Entity = Entity, NoTracking = NoTracking, IgnoreFilters = IgnoreFilters,
                                      Includes = new HashSet<IPropertySymbol>(Includes, SymbolEqualityComparer.Default) };
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

        /// <summary>A context's DbSet property (ctx.Orders): its table.</summary>
        private Term DbSetProperty(IPropertyReferenceOperation pr, Frame f, SpecEnv spec)
        {
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
                    case "AsNoTracking": case "AsNoTrackingWithIdentityResolution": t.NoTracking = true; break;
                    case "AsTracking": t.NoTracking = false; break;
                    case "IgnoreQueryFilters": t.IgnoreFilters = true; break;
                    case "Include":
                        if (inv.Arguments.FirstOrDefault(a => a.Parameter.Ordinal == 1)?.Value is IOperation lambda && Navigation(lambda) is IPropertySymbol nav)
                            t.Includes.Add(nav);
                        break;
                }
            });
            var r = _z3.Fresh("table", Sort.Int);
            _z3.Assume(NotNull(r));
            _tables[r.S] = read;
            return r;
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
                        AssumeSide(OverIndices("forall", T.Int(0), n, i => T.Coerce(InDatabase(() => ApplyValue(body, filter.Symbol.Parameters[0], Row(i), f)), Sort.Bool), Row));
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
                // a navigation not included is null (written into its map, so any read of it at a row sees it)
                foreach (var nav in e.References.Where(p => !t.Includes.Contains(p) && FieldEffects.IsHeapField(p)))
                {
                    var before = FieldMap(f, nav);
                    f.Link = null;
                    f.Fields[FieldEffects.Key(nav)] = Pointwise("materialized", MapSort(nav), $"(ite {IsRow(new Term("y", Sort.Int)).S} 0 (select {before.S} y))");
                }
                // what the context read of them: their concurrency token
                if (TrackerModel("Read") != null && e.Tokens.Count > 0 && FieldEffects.IsHeapField(e.Tokens[0]))
                {
                    var y = new Term("y", Sort.Int);
                    var read = ModelRow("Read", t.Context, f);
                    var tokens = ModelRow("TokenRead", t.Context, f);
                    var token = FieldMap(f, e.Tokens[0]);
                    SetModelRow("Read", t.Context, Pointwise("read", Sort.Row, $"(ite {IsRow(y).S} 1 (select {read.S} y))"), f);
                    SetModelRow("TokenRead", t.Context, Pointwise("tokenRead", Sort.Row, $"(ite {IsRow(y).S} {T.Coerce(T.Select(token, y, ValueSort(e.Tokens[0]) == Sort.Row ? Sort.Row : Sort.Int), Sort.Int).S} (select {tokens.S} y))"), f);
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
                // tracked from here on
                f.Link = null;
                var after = Pointwise("tracked", Sort.Row, $"(ite (and {IsRow(new Term("y", Sort.Int)).S} (= (select {tracked.S} y) 0)) 1 (select {tracked.S} y))");
                f.Fields[FieldEffects.Key(state)] = T.Store(states, t.Context, after);
            }
            return new Sequence { Length = n, Element = Row, ElementType = e.Type, Known = known };
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

        /// <summary>A query's lambda as the database evaluates it: strings compared by its collation.</summary>
        private Term InDatabase(System.Func<Term> body)
        {
            _inDatabase++;
            try { return body(); }
            finally { _inDatabase--; }
        }

        /// <summary>
        /// Two strings equal as the database compares them (cv_collate, <see cref="CollationTheory"/>): an equivalence
        /// that equal strings satisfy, and nothing else is known of (SQL Server's default collation ignores case, and
        /// its = ignores trailing spaces).
        /// </summary>
        private static Term CollationEqual(Term a, Term b) => new Term($"(cv_collate {T.Coerce(a, Sort.Int).S} {T.Coerce(b, Sort.Int).S})", Sort.Bool);

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
            "Distinct", "DistinctBy", "GroupBy", "GroupJoin", "Join", "Union", "UnionBy", "Intersect", "IntersectBy", "Except", "ExceptBy",
            "Contains", "SequenceEqual", "ToDictionary", "ToLookup", "ToHashSet", "CountBy", "AggregateBy", "IndexOf",
        };

        /// <summary>
        /// Does the operator compare values for equality? On a database it compares them as the database does (strings
        /// by its collation, rows by every column), not as LINQ to Objects' definition says: such a query is a library
        /// call, which says nothing of what it gives.
        /// </summary>
        private static bool ComparesByEquality(IMethodSymbol definition) => EqualityOperators.Contains(definition.Name);

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
