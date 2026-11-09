using System.Collections.Generic;
using System.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Entity Framework Core's change tracker, transactions and bulk updates, over the ghost state CsVerify.Ef.Tracker
    /// declares (a context's tracked entities and their states, its unsaved changes, its transaction, a failed save):
    /// - Add, Attach, Update and Remove (and Entry(e).State) must not meet another tracked instance with the same key,
    ///   which EF refuses (CSV1033); Update must not take along what the entity's navigations hold (CSV1033).
    /// - SaveChanges writes what is pending; after one that failed, or a rollback, the context is done with (CSV1033).
    ///   It must not write an entity ExecuteUpdate or ExecuteDelete changed behind the tracker (CSV1033).
    /// - Attach or Update of an entity this context read must find its concurrency token as it was read, and a row
    ///   version is never written by the program (CSV1034).
    /// - BeginTransaction needs none open; Commit needs the changes saved; two saves on one context need one
    ///   transaction around them (CSV1035).
    /// </summary>
    internal partial class MethodVerifier
    {
        internal const string TrackerId = "CSV1033", TokenId = "CSV1034", TransactionId = "CSV1035";

        private const int EfDetached = 0, Unchanged = 1, Deleted = 2, Modified = 3, Added = 4;

        /// <summary>An EntityEntry (Entry(e)) and a PropertyEntry: the context and the entity they are of.</summary>
        private readonly Dictionary<string, (Term context, Term entity, EfModel.Entity type)> _efEntries = new Dictionary<string, (Term, Term, EfModel.Entity)>();
        /// <summary>A DatabaseFacade (ctx.Database), a ChangeTracker, a transaction: the context they belong to.</summary>
        private readonly Dictionary<string, Term> _efFacades = new Dictionary<string, Term>();
        private readonly Dictionary<string, Term> _efTransactions = new Dictionary<string, Term>();

        // ------------------------------------------------------------------ the models

        private Term Model(string name, Term context, Frame f, Term key = null)
        {
            var m = TrackerModel(name);
            return ModelAt(m, key == null ? new[] { context } : new[] { context, key }, f);
        }

        private void SetModel(string name, Term context, Term value, Frame f)
        {
            var m = TrackerModel(name);
            f.Link = null;
            f.Fields[FieldEffects.Key(m)] = T.Store(FieldMap(f, m), T.Coerce(context, Sort.Int), T.Coerce(value, Sort.Int));
        }

        private Term ModelRow(string name, Term context, Frame f) => T.Select(FieldMap(f, TrackerModel(name)), T.Coerce(context, Sort.Int), Sort.Row);

        private void SetModelRow(string name, Term context, Term row, Frame f)
        {
            var m = TrackerModel(name);
            f.Link = null;
            f.Fields[FieldEffects.Key(m)] = T.Store(FieldMap(f, m), T.Coerce(context, Sort.Int), row);
        }

        private void SetModelAt(string name, Term context, Term key, Term value, Frame f) =>
            SetModelRow(name, context, T.Store(ModelRow(name, context, f), T.Coerce(key, Sort.Int), T.Coerce(value, Sort.Int)), f);

        private static readonly string[] TrackerModels = { "State", "Unsaved", "InTransaction", "Failed", "Stale", "Read", "TokenRead", "SavedAlone", "Unshared" };

        /// <summary>
        /// What the method being verified did to a context: saves outside a transaction, a failed save or rollback,
        /// entities it read or bulk updates made stale. Its own record: none at entry, and what it calls doesn't change
        /// it (so these rules are checked within a method, not across calls).
        /// </summary>
        private static readonly string[] MethodLocal = { "Failed", "Stale", "Read", "TokenRead", "SavedAlone", "Unshared" };

        private bool IsMethodLocalModel(ISymbol field) =>
            Ef != null && field is IMethodSymbol m && m.ContainingType?.Name == "Tracker" && m.ContainingNamespace?.ToDisplayString() == "CsVerify.Ef" && MethodLocal.Contains(m.Name);

        private Dictionary<ISymbol, Term> MethodLocalModels(Frame f) =>
            Ef == null || TrackerModel("State") == null ? null
                : MethodLocal.Select(TrackerModel).Where(m => m != null).ToDictionary(m => (ISymbol)FieldEffects.Key(m), m => FieldMap(f, m), SymbolEqualityComparer.Default);

        /// <summary>
        /// At entry: no context has saved alone or read anything yet in this method (both are this method's own record).
        /// An object not yet made was read by none.
        /// </summary>
        private void EfEntry(Frame f)
        {
            if (Ef == null || TrackerModel("SavedAlone") == null) return;
            // (constant maps: nothing for any context)
            foreach (var name in new[] { "SavedAlone", "Failed" })
                f.Fields[FieldEffects.Key(TrackerModel(name))] = new Term("((as const (Array Int Int)) 0)", Sort.Row);
            foreach (var name in new[] { "Read", "Stale" })
                f.Fields[FieldEffects.Key(TrackerModel(name))] = new Term($"((as const (Array Int (Array Int Int))) {T.ZeroRow().S})", Sort.Heap);
            if (TrackerModel("Unshared") is IMethodSymbol unshared)
                f.Fields[FieldEffects.Key(unshared)] = new Term("((as const (Array Int Int)) 0)", Sort.Row);
            f.Link = null;
        }

        /// <summary>A context just made (new, or from an IDbContextFactory): it tracks nothing, and has nothing open.</summary>
        private void NewContext(Term c, Frame f)
        {
            if (TrackerModel("State") == null) return;
            c = T.Coerce(c, Sort.Int);
            SetModelRow("State", c, T.ZeroRow(), f);
            SetModelRow("Stale", c, T.ZeroRow(), f);
            SetModel("Unsaved", c, T.False, f);
            SetModel("InTransaction", c, T.False, f);
            SetModel("Failed", c, T.False, f);
        }

        /// <summary>The tracker's state, kept across an await: a context is this code's alone while it runs (CSV1036).</summary>
        private Dictionary<ISymbol, Term> KeepTracker(Frame f) =>
            Ef == null || TrackerModel("State") == null ? null
                : TrackerModels.Select(TrackerModel).Where(m => m != null).ToDictionary(m => (ISymbol)FieldEffects.Key(m), m => FieldMap(f, m), SymbolEqualityComparer.Default);

        private static void RestoreTracker(Frame f, Dictionary<ISymbol, Term> kept)
        {
            if (kept == null) return;
            foreach (var kv in kept) f.Fields[kv.Key] = kv.Value;
            f.Link = null;
        }

        /// <summary>
        /// The entities' columns before an await, to keep at the unshared ones (<see cref="KeepUnshared"/>), and the
        /// models of lists, for the lists of their collection navigations.
        /// </summary>
        private List<(ISymbol column, Term map)> EntityColumns(Frame f)
        {
            if (Ef == null || TrackerModel("Unshared") == null || !EntitiesStayHere()) return null;
            var columns = Ef.Entities.SelectMany(e => e.Type.GetMembers().OfType<IPropertySymbol>()).Where(FieldEffects.IsHeapField)
                .Distinct<IPropertySymbol>(SymbolEqualityComparer.Default).Select(p => ((ISymbol)p, FieldMap(f, p))).ToList();
            if (ListModels && Ef.Entities.Any(e => e.Collections.Any(c => IsListType(c.Type))))
                foreach (var model in new[] { ListModel("Items"), ListModel("Size") })
                    columns.Add((model, FieldMap(f, model)));
            return columns;
        }

        /// <summary>An await leaves an entity no other code reaches as it was: its columns, its concurrency token among them.</summary>
        private void KeepUnshared(Frame f, List<(ISymbol column, Term map)> before)
        {
            if (before == null || before.Count == 0) return;
            var unshared = FieldMap(f, TrackerModel("Unshared"));
            f.Link = null;
            foreach (var (p, map) in before)
                f.Fields[FieldEffects.Key(p)] = Pointwise(p.Name, MapSort(p), $"(ite (= (select {unshared.S} y) 1) (select {map.S} y) (select {FieldMap(f, p).S} y))");
        }

        private bool? _entitiesStayHere;

        /// <summary>
        /// Does the method keep the entities it has to itself? None is passed to the program's code, to a library call
        /// on something not local, or to a constructor, stored anywhere but in a local, captured by a lambda that isn't
        /// a query's, or yielded. (EF's calls and LINQ's take them without letting other code reach them.)
        /// </summary>
        private bool EntitiesStayHere()
        {
            if (_entitiesStayHere is bool known) return known;
            bool stay = _contract.Declaration != null;
            if (stay)
            {
                bool IsEntity(ITypeSymbol t) => t != null && Ef.Entities.Any(e => Mentions(t, e.Type));
                bool Harmless(IMethodSymbol m) => IsEfMethod(m) || Ef.IsContextType(m.ContainingType) ||
                    m.ContainingNamespace?.ToDisplayString() == "System.Linq";
                bool LocalReceiver(ExpressionSyntax e) => e is IdentifierNameSyntax id && _model.GetSymbolInfo(id).Symbol is ILocalSymbol;
                foreach (var n in _contract.Declaration.DescendantNodes())
                {
                    switch (n)
                    {
                        case InvocationExpressionSyntax call when _model.GetSymbolInfo(call).Symbol is IMethodSymbol m && !Harmless(m):
                            {
                                var receiver = call.Expression is MemberAccessExpressionSyntax ma ? ma.Expression : null;
                                bool argOut = call.ArgumentList.Arguments.Any(a => IsEntity(_model.GetTypeInfo(a.Expression).Type));
                                bool thisOut = receiver != null && !m.IsStatic && IsEntity(_model.GetTypeInfo(receiver).Type) && !IsLibrary(m);
                                if (thisOut || argOut && (!IsLibrary(m) || m.IsStatic || receiver == null || !LocalReceiver(receiver))) stay = false;
                                break;
                            }
                        case BaseObjectCreationExpressionSyntax made when made.ArgumentList != null &&
                                made.ArgumentList.Arguments.Any(a => IsEntity(_model.GetTypeInfo(a.Expression).Type)):
                            stay = false; break;
                        case AssignmentExpressionSyntax assign when IsEntity(_model.GetTypeInfo(assign.Right).Type) &&
                                !(_model.GetSymbolInfo(assign.Left).Symbol is ILocalSymbol):
                            stay = false; break;
                        case YieldStatementSyntax y when y.Expression != null && IsEntity(_model.GetTypeInfo(y.Expression).Type):
                            stay = false; break;
                        case AnonymousFunctionExpressionSyntax lambda when !(lambda.Parent is ArgumentSyntax arg &&
                                arg.Parent?.Parent is InvocationExpressionSyntax q && _model.GetSymbolInfo(q).Symbol is IMethodSymbol qm && Harmless(qm)):
                            foreach (var id in lambda.Body.DescendantNodesAndSelf().OfType<IdentifierNameSyntax>())
                                if (_model.GetSymbolInfo(id).Symbol is ISymbol s && (s is ILocalSymbol || s is IParameterSymbol) &&
                                    IsEntity(s is ILocalSymbol l ? l.Type : ((IParameterSymbol)s).Type) &&
                                    !s.DeclaringSyntaxReferences.Any(r => lambda.Span.Contains(r.Span)))
                                    stay = false;
                            break;
                    }
                    if (!stay) break;
                }
            }
            _entitiesStayHere = stay;
            return stay;
        }

        // ------------------------------------------------------------------ keys

        /// <summary>The value of a key's properties of an object, now.</summary>
        private Term KeyColumn(IPropertySymbol p, Term o, Frame f) =>
            FieldEffects.IsHeapField(p) ? T.Select(FieldMap(f, p), T.Coerce(o, Sort.Int), ValueSort(p) == Sort.Row ? Sort.Row : Sort.Int) : null;

        private Term SameKey(EfModel.Entity e, Term a, Term b, Frame f)
        {
            var parts = e.Key.Select(p => (KeyColumn(p, a, f), KeyColumn(p, b, f))).ToList();
            if (parts.Any(x => x.Item1 == null)) return _z3.Fresh("sameKey", Sort.Bool);
            return T.And(parts.Select(x => T.Eq(x.Item1, x.Item2)).ToArray());
        }

        /// <summary>A key EF generates on insert, not set yet: a single integer key at 0.</summary>
        private Term KeyUnset(EfModel.Entity e, Term o, Frame f) =>
            e.Key.Count == 1 && IsIntegral(e.Key[0].Type) && KeyColumn(e.Key[0], o, f) is Term k ? T.Eq(k, T.Int(0)) : T.False;

        /// <summary>No other instance of the type with o's key is tracked by the context.</summary>
        private Term NoOtherWithKey(Term c, Term o, EfModel.Entity e, Frame f)
        {
            if (e.Key.Count == 0) return T.True;
            var states = Named(ModelRow("State", c, f), "states");
            var yn = _z3.FreshName("y");
            var y = new Term(yn, Sort.Int);
            var clash = T.And(T.Not(T.Eq(T.Select(states, y, Sort.Int), T.Int(EfDetached))), T.Not(T.Eq(y, T.Coerce(o, Sort.Int))), IsEntity(y, e), SameKey(e, y, o, f));
            return new Term($"(forall (({yn} Int)) (! (not {clash.S}) :pattern ((select {states.S} {yn}))))", Sort.Bool);
        }

        private void ProveEf(Term goal, string id, SyntaxNode at, string message) =>
            Prove(T.Implies(T.And(_guards.ToArray()), goal), id, at, message);

        /// <summary>What o's navigations hold: nothing (each reference null, each collection null or empty)?</summary>
        private Term NavigationsEmpty(Term o, EfModel.Entity e, Frame f)
        {
            var parts = new List<Term>();
            foreach (var p in e.References.Where(FieldEffects.IsHeapField))
                parts.Add(T.Eq(T.Select(FieldMap(f, p), T.Coerce(o, Sort.Int), Sort.Int), T.Int(0)));
            foreach (var p in e.Collections.Where(FieldEffects.IsHeapField))
            {
                var list = T.Select(FieldMap(f, p), T.Coerce(o, Sort.Int), Sort.Int);
                parts.Add(IsListType(p.Type) && ListModels
                    ? T.Or(T.Eq(list, T.Int(0)), T.Eq(T.Coerce(ModelAt(ListModel("Size"), new[] { list }, f), Sort.Int), T.Int(0)))
                    : T.Eq(list, T.Int(0)));
            }
            return T.And(parts.ToArray());
        }

        // ------------------------------------------------------------------ calls

        /// <summary>The context a receiver stands for: a context itself, or a DbSet of one.</summary>
        private Term ContextOf(IOperation receiver, Frame f, SpecEnv spec, out EfModel.Entity setEntity)
        {
            setEntity = null;
            if (receiver == null) return null;
            if (Ef.IsContextType(receiver.Type)) { var c = Eval(receiver, f, spec); Deref(receiver, c, receiver.Syntax); return T.Coerce(c, Sort.Int); }
            if (DbSetEntity(receiver.Type) is EfModel.Entity e)
            {
                var t = T.Coerce(Eval(receiver, f, spec), Sort.Int);
                if (_tables.TryGetValue(t.S, out var table)) { setEntity = e; return table.Context; }
            }
            return null;
        }

        /// <summary>Set while an await of an EF call reads it: its value is the awaited one, not the task.</summary>
        private bool _efAwaited;

        /// <summary>
        /// The DbContext, DbSet, DatabaseFacade, transaction, ChangeTracker and EntityEntry calls the tracker models. An
        /// ...Async one not awaited here gives its task (CSV1036 asks that it be awaited at once, or returned).
        /// </summary>
        private Term EfTrackerCall(IInvocationOperation inv, Frame f, SpecEnv spec)
        {
            bool awaited = _efAwaited;
            _efAwaited = false;
            var value = EfTrackerCallCore(inv, f, spec);
            if (value == null || awaited || !inv.TargetMethod.Name.EndsWith("Async")) return value;
            var task = _z3.Fresh("task", Sort.Int);
            _z3.Assume(NotNull(task));
            return task;
        }

        private Term EfTrackerCallCore(IInvocationOperation inv, Frame f, SpecEnv spec)
        {
            if (Ef == null || TrackerModel("State") == null || !_codeMode) return null;
            var m = inv.TargetMethod;
            var name = m.Name.EndsWith("Async") ? m.Name.Substring(0, m.Name.Length - "Async".Length) : m.Name;
            // bulk updates of a query's rows
            if ((name == "ExecuteUpdate" || name == "ExecuteDelete") && IsEfMethod(m))
                return BulkUpdate(inv, f, spec);
            var receiver = inv.Instance;
            if (receiver != null && _efEntries.TryGetValue(T.Coerce(Eval(receiver, f, spec), Sort.Int).S, out var entry) && receiver.Type?.Name == "EntityEntry")
                return EntryCall(inv, name, entry, f, spec);
            if (receiver != null && receiver.Type?.Name == "DatabaseFacade" && _efFacades.TryGetValue(T.Coerce(Eval(receiver, f, spec), Sort.Int).S, out var dbOf))
                return FacadeCall(inv, name, dbOf, f, spec);
            if (receiver != null && receiver.Type?.Name == "ChangeTracker" && _efFacades.TryGetValue(T.Coerce(Eval(receiver, f, spec), Sort.Int).S, out var trackerOf))
            {
                if (name != "Clear") return null;
                SetModelRow("State", trackerOf, T.ZeroRow(), f);
                SetModelRow("Stale", trackerOf, T.ZeroRow(), f);
                SetModel("Unsaved", trackerOf, T.False, f);
                return T.True;
            }
            if (receiver != null && IsTransactionType(receiver.Type) && _efTransactions.TryGetValue(T.Coerce(Eval(receiver, f, spec), Sort.Int).S, out var txOf))
                return TransactionCall(inv, name, txOf, f, spec);
            if (name == "CreateDbContext" && receiver?.Type is INamedTypeSymbol factory && (factory.Name == "IDbContextFactory" || factory.AllInterfaces.Any(i => i.Name == "IDbContextFactory")))
            {
                Eval(receiver, f, spec);
                var made = _z3.Fresh("context", Sort.Int);
                _z3.Assume(NotNull(made));
                NewContext(made, f);
                return made;
            }
            var c = ContextOf(receiver, f, spec, out var setEntity);
            if (c == null) return null;
            var arg = inv.Arguments.FirstOrDefault(a => a.Parameter.Ordinal == 0);
            switch (name)
            {
                case "Add": case "Attach": case "Update": case "Remove":
                {
                    if (arg == null || m.Parameters.Length != (m.Name.EndsWith("Async") ? 2 : 1)) return null;
                    var e = Ef.EntityOf(arg.Value.Type is ITypeParameterSymbol ? m.TypeArguments.FirstOrDefault() ?? arg.Value.Type : Unconverted(arg.Value).Type) ?? setEntity;
                    if (e == null) return null;
                    var o = T.Coerce(Eval(arg.Value, f, spec), Sort.Int);
                    Deref(arg.Value, o, inv.Syntax);
                    Track(name, c, o, e, inv.Syntax, f);
                    return EntryOf(c, o, e);
                }
                case "Entry":
                {
                    if (arg == null) return null;
                    var e = Ef.EntityOf(Unconverted(arg.Value).Type);
                    if (e == null) return null;
                    var o = T.Coerce(Eval(arg.Value, f, spec), Sort.Int);
                    Deref(arg.Value, o, inv.Syntax);
                    return EntryOf(c, o, e);
                }
                case "SaveChanges":
                    return SaveChanges(inv, c, f, spec);
                case "Find":
                    return Find(inv, c, setEntity, f, spec);
                default:
                    return null;
            }
        }

        private Term EntryOf(Term c, Term o, EfModel.Entity e)
        {
            var entry = _z3.Fresh("entry", Sort.Int);
            _z3.Assume(NotNull(entry));
            _efEntries[entry.S] = (c, o, e);
            return entry;
        }

        /// <summary>Add, Attach, Update or Remove of one entity (or Entry(e).State set: as the state says).</summary>
        private void Track(string how, Term c, Term o, EfModel.Entity e, SyntaxNode at, Frame f)
        {
            UsableContext(c, at, f);
            var state = T.Coerce(Model("State", c, f, o), Sort.Int);
            var unset = KeyUnset(e, o, f);
            // another instance of the same row already tracked: EF throws
            if (how != "Add" || e.Key.Count > 0)
                ProveEf(T.Or(T.Not(T.Eq(state, T.Int(EfDetached))), unset, NoOtherWithKey(c, o, e, f)), TrackerId, at,
                    $"'{at}' may meet another {e.Type.Name} with the same key that the context already tracks, and EF throws: use the tracked one, or a context that tracks none");
            // Update and Attach take the whole graph: what o's navigations hold is tracked too (and Update marks it modified)
            if (how == "Update")
                ProveEf(NavigationsEmpty(o, e, f), TrackerId, at,
                    $"'{at}' also marks what the {e.Type.Name}'s navigations hold as modified, and SaveChanges then writes every column of each: " +
                    "update only this entity (Entry(e).State = EntityState.Modified), or load the graph tracked and change what changes");
            // the concurrency token is the one the context read: EF checks the row against it
            if ((how == "Update" || how == "Attach") && e.Tokens.Count > 0 && KeyColumn(e.Tokens[0], o, f) is Term token)
                ProveEf(T.Implies(AsBool(Model("Read", c, f, o)), T.Eq(T.Coerce(token, Sort.Int), T.Coerce(Model("TokenRead", c, f, o), Sort.Int))), TokenId, at,
                    $"'{at}' takes {e.Tokens[0].Name}, the concurrency token, as the value the row had when read, but it was changed since: " +
                    "EF would check the row against the new value. Attach first, then change it");
            Term next;
            switch (how)
            {
                case "Add": next = T.Int(Added); break;
                case "Attach": next = T.Ite(T.Eq(state, T.Int(EfDetached)), T.Ite(unset, T.Int(Added), T.Int(Unchanged)), state); break;
                case "Update": next = T.Ite(unset, T.Int(Added), T.Ite(T.Eq(state, T.Int(Added)), state, T.Int(Modified))); break;
                case "Remove": next = T.Ite(T.Eq(state, T.Int(Added)), T.Int(EfDetached), T.Int(Deleted)); break;
                default: next = state; break;
            }
            var before = ModelRow("State", c, f);
            // what o's navigations lead to may be tracked now too (unless they hold nothing)
            var others = T.Ite(NavigationsEmpty(o, e, f), before, _z3.Fresh("tracked", Sort.Row));
            SetModelRow("State", c, T.Store(others, o, next), f);
            SetModel("Unsaved", c, how == "Attach" ? T.Or(AsBool(Model("Unsaved", c, f)), unset, T.Not(NavigationsEmpty(o, e, f))) : T.True, f);
        }

        /// <summary>A context SaveChanges failed on, or whose transaction rolled back, is done with (CSV1033).</summary>
        private void UsableContext(Term c, SyntaxNode at, Frame f) =>
            ProveEf(T.Not(AsBool(Model("Failed", c, f))), TrackerId, at,
                $"'{at}' uses a context after a failed SaveChanges or a rolled back transaction: what it tracks is no longer what the database holds. Use a new context");

        private Term SaveChanges(IInvocationOperation inv, Term c, Frame f, SpecEnv spec)
        {
            foreach (var a in inv.Arguments) Eval(a.Value, f, spec);
            var at = inv.Syntax;
            UsableContext(c, at, f);
            // nothing ExecuteUpdate changed behind the tracker is written back
            var states = Named(ModelRow("State", c, f), "states");
            var stale = ModelRow("Stale", c, f);
            ProveEf(new Term($"(forall ((y Int)) (! (=> (= (select {states.S} y) {Modified}) (= (select {stale.S} y) 0)) :pattern ((select {states.S} y))))", Sort.Bool), TrackerId, at,
                $"'{at}' writes an entity that ExecuteUpdate or ExecuteDelete may have changed since it was read, overwriting what they wrote: reload it (Entry(e).Reload()) first");
            // two saves: one transaction around both, or the first stays if the second fails
            ProveEf(T.Or(AsBool(Model("InTransaction", c, f)), T.Not(AsBool(Model("SavedAlone", c, f)))), TransactionId, at,
                $"'{at}' saves a second time on this context outside a transaction: if it fails, what the first saved stays. Begin a transaction before the first (Database.BeginTransaction), and commit after the last");
            // it may fail: then the context is done with
            MayRaise(T.True, f, null, (thrown, x) => SetModel("Failed", c, T.True, thrown));
            // the database sets the row versions of what it writes
            foreach (var p in Ef.Entities.SelectMany(e => e.RowVersions).Where(FieldEffects.IsHeapField).Distinct<IPropertySymbol>(SymbolEqualityComparer.Default))
            {
                var before = FieldMap(f, p);
                f.Link = null;
                f.Fields[FieldEffects.Key(p)] = Pointwise(p.Name, MapSort(p), $"(ite (or (= (select {states.S} y) {Added}) (= (select {states.S} y) {Modified})) (select {FreshMap(p).S} y) (select {before.S} y))");
            }
            var saved = Pointwise("saved", Sort.Row, $"(ite (or (= (select {states.S} y) {Added}) (= (select {states.S} y) {Modified})) {Unchanged} (ite (= (select {states.S} y) {Deleted}) {EfDetached} (select {states.S} y)))");
            SetModel("SavedAlone", c, T.Or(AsBool(Model("SavedAlone", c, f)), T.Not(AsBool(Model("InTransaction", c, f)))), f);
            SetModelRow("State", c, saved, f);
            SetModel("Unsaved", c, T.False, f);
            var n = _z3.Fresh("saved", Sort.Int);
            _z3.Assume(T.Le(T.Int(0), n));
            return n;
        }

        /// <summary>Find(key): the tracked entity with that key, or the row read and tracked, or null.</summary>
        private Term Find(IInvocationOperation inv, Term c, EfModel.Entity e, Frame f, SpecEnv spec)
        {
            if (e == null || e.Key.Count != 1) return null;
            var keyArg = inv.Arguments.FirstOrDefault(a => a.Parameter.Ordinal == 0)?.Value;
            if (keyArg is IArrayCreationOperation arr && arr.Initializer?.ElementValues.Length == 1) keyArg = Unwrapped(arr.Initializer.ElementValues[0]);
            if (keyArg == null) return null;
            UsableContext(c, inv.Syntax, f);
            var k = Eval(keyArg, f, spec);
            var r = _z3.Fresh("found", Sort.Int);
            var key = KeyColumn(e.Key[0], r, f);
            _z3.Assume(T.Or(T.Eq(r, T.Int(0)), T.And(IsEntity(r, e), T.Eq(key, T.Coerce(k, key.Sort)))));
            SetModelAt("State", c, r, T.Ite(T.Eq(T.Coerce(Model("State", c, f, r), Sort.Int), T.Int(EfDetached)), T.Int(Unchanged), Model("State", c, f, r)), f);
            MayRaise(T.True, f, null);
            return r;
        }

        private Term EntryCall(IInvocationOperation inv, string name, (Term context, Term entity, EfModel.Entity type) entry, Frame f, SpecEnv spec)
        {
            var (c, o, e) = entry;
            switch (name)
            {
                case "Reload":
                    UsableContext(c, inv.Syntax, f);
                    // the row's values, as the database has them now
                    foreach (var p in e.Type.GetMembers().OfType<IPropertySymbol>().Where(FieldEffects.IsHeapField))
                        f.Fields[FieldEffects.Key(p)] = T.Store(FieldMap(f, p), o, T.Coerce(_z3.Fresh(p.Name, SortOf(p.Type)), ValueSort(p)));
                    f.Link = null;
                    SetModelAt("Stale", c, o, T.False, f);
                    SetModelAt("State", c, o, T.Int(Unchanged), f);
                    MayRaise(T.True, f, null);
                    return T.True;
                case "Property":
                    // a PropertyEntry: its original value may be set, which only tells EF what the row had
                    var pe = _z3.Fresh("property", Sort.Int);
                    _z3.Assume(NotNull(pe));
                    return pe;
                default:
                    return null;
            }
        }

        private static bool IsTransactionType(ITypeSymbol t) =>
            t != null && (t.Name == "IDbContextTransaction" || t.AllInterfaces.Any(i => i.Name == "IDbContextTransaction"));

        private Term FacadeCall(IInvocationOperation inv, string name, Term c, Frame f, SpecEnv spec)
        {
            if (name != "BeginTransaction") return null;
            foreach (var a in inv.Arguments) Eval(a.Value, f, spec);
            UsableContext(c, inv.Syntax, f);
            ProveEf(T.Not(AsBool(Model("InTransaction", c, f))), TransactionId, inv.Syntax,
                $"'{inv.Syntax}' begins a transaction where one may be open already, and EF throws: join it (if Database.CurrentTransaction is not null, use it)");
            MayRaise(T.True, f, null);
            SetModel("InTransaction", c, T.True, f);
            var tx = _z3.Fresh("transaction", Sort.Int);
            _z3.Assume(NotNull(tx));
            _efTransactions[tx.S] = c;
            return tx;
        }

        private Term TransactionCall(IInvocationOperation inv, string name, Term c, Frame f, SpecEnv spec)
        {
            foreach (var a in inv.Arguments) Eval(a.Value, f, spec);
            switch (name)
            {
                case "Commit":
                    ProveEf(T.Not(AsBool(Model("Unsaved", c, f))), TransactionId, inv.Syntax,
                        $"'{inv.Syntax}' commits with changes the context hasn't saved: they aren't in the transaction. SaveChanges first");
                    MayRaise(T.True, f, null, (thrown, x) => { SetModel("InTransaction", c, T.False, thrown); SetModel("Failed", c, T.True, thrown); });
                    SetModel("InTransaction", c, T.False, f);
                    return T.True;
                case "Rollback":
                case "Dispose":
                    // a rollback (and disposing one not committed): the database is as before, the tracker is not
                    var open = AsBool(Model("InTransaction", c, f));
                    SetModel("Failed", c, T.Or(AsBool(Model("Failed", c, f)), open), f);
                    SetModel("InTransaction", c, T.False, f);
                    return T.True;
                default:
                    return null;
            }
        }

        /// <summary>ExecuteUpdate or ExecuteDelete: rows changed in the database, not in the tracker.</summary>
        private Term BulkUpdate(IInvocationOperation inv, Frame f, SpecEnv spec)
        {
            var source = inv.Arguments.FirstOrDefault(a => a.Parameter.Ordinal == 0)?.Value;
            if (source == null) return null;
            var s = T.Coerce(Eval(source, f, spec), Sort.Int);
            var table = _tables.TryGetValue(s.S, out var t) ? t : _databaseQueries.Contains(s.S) ? RootTable(s) : null;
            foreach (var a in inv.Arguments.Where(a => a.Parameter.Ordinal > 0)) Eval(a.Value, f, spec);
            if (table != null)
            {
                UsableContext(table.Context, inv.Syntax, f);
                var states = ModelRow("State", table.Context, f);
                var stale = ModelRow("Stale", table.Context, f);
                var y = new Term("y", Sort.Int);
                SetModelRow("Stale", table.Context, Pointwise("stale", Sort.Row,
                    $"(ite (and (distinct (select {states.S} y) {EfDetached}) {IsEntity(y, table.Entity).S}) 1 (select {stale.S} y))"), f);
            }
            MayRaise(T.True, f, null);
            var n = _z3.Fresh("rows", Sort.Int);
            _z3.Assume(T.Le(T.Int(0), n));
            return n;
        }

        /// <summary>The table a database query reads, through its lazy calls' first sources.</summary>
        private DbTable RootTable(Term q)
        {
            for (int depth = 0; depth < 32; depth++)
            {
                if (_tables.TryGetValue(q.S, out var t)) return t;
                if (!_lazy.TryGetValue(q.S, out var lazy)) return null;
                var next = lazy.Args.Select(a => a.Item2).OfType<Term>().FirstOrDefault(IsDatabaseQuery);
                if (next == null) return null;
                q = T.Coerce(next, Sort.Int);
            }
            return null;
        }

        // ------------------------------------------------------------------ properties and assignments

        /// <summary>ctx.Database, ctx.ChangeTracker, Database.CurrentTransaction, entry.State.</summary>
        private Term EfPropertyRead(IPropertyReferenceOperation pr, Frame f, SpecEnv spec)
        {
            if (Ef == null || TrackerModel("State") == null || pr.Instance == null) return null;
            var name = pr.Property.Name;
            if ((name == "Database" || name == "ChangeTracker") && Ef.IsContextType(pr.Instance.Type))
            {
                var c = T.Coerce(Eval(pr.Instance, f, spec), Sort.Int);
                Deref(pr.Instance, c, pr.Syntax);
                var facade = _z3.Fresh(name, Sort.Int);
                _z3.Assume(NotNull(facade));
                _efFacades[facade.S] = c;
                return facade;
            }
            if (name == "CurrentTransaction" && pr.Instance.Type?.Name == "DatabaseFacade" && _efFacades.TryGetValue(T.Coerce(Eval(pr.Instance, f, spec), Sort.Int).S, out var dbOf))
            {
                var tx = _z3.Fresh("transaction", Sort.Int);
                _z3.Assume(T.Eq(NotNull(tx), AsBool(Model("InTransaction", dbOf, f))));
                _efTransactions[tx.S] = dbOf;
                return tx;
            }
            if (name == "State" && pr.Instance.Type?.Name == "EntityEntry" && _efEntries.TryGetValue(T.Coerce(Eval(pr.Instance, f, spec), Sort.Int).S, out var entry))
                return T.Coerce(Model("State", entry.context, f, entry.entity), Sort.Int);
            return null;
        }

        /// <summary>entry.State = s: as Add, Attach, Update or Remove, by the state (EfDetached stops tracking).</summary>
        private Term EfAssignment(ISimpleAssignmentOperation a, Frame f, SpecEnv spec)
        {
            if (Ef == null || TrackerModel("State") == null || !(a.Target is IPropertyReferenceOperation pr) || pr.Instance == null) return null;
            if (pr.Property.Name != "State" || pr.Instance.Type?.Name != "EntityEntry") return null;
            if (!_efEntries.TryGetValue(T.Coerce(Eval(pr.Instance, f, spec), Sort.Int).S, out var entry)) return null;
            var v = T.Coerce(Eval(a.Value, f, spec), Sort.Int);
            if (a.Value.ConstantValue.HasValue && a.Value.ConstantValue.Value is int s)
            {
                switch (s)
                {
                    case Modified: TrackAs(entry, Modified, a.Syntax, f); return v;
                    case Added: Track("Add", entry.context, entry.entity, entry.type, a.Syntax, f); return v;
                    case Deleted: Track("Remove", entry.context, entry.entity, entry.type, a.Syntax, f); return v;
                    case Unchanged: TrackAs(entry, Unchanged, a.Syntax, f); return v;
                    case EfDetached:
                        SetModelAt("State", entry.context, entry.entity, T.Int(EfDetached), f);
                        return v;
                }
            }
            // a state not known here: anything
            SetModelAt("State", entry.context, entry.entity, v, f);
            SetModel("Unsaved", entry.context, _z3.Fresh("unsaved", Sort.Bool), f);
            return v;
        }

        /// <summary>entry.State = Modified or Unchanged: this entity alone (not its graph), checked for a clash as Attach is.</summary>
        private void TrackAs((Term context, Term entity, EfModel.Entity type) entry, int state, SyntaxNode at, Frame f)
        {
            var (c, o, e) = entry;
            UsableContext(c, at, f);
            var now = T.Coerce(Model("State", c, f, o), Sort.Int);
            ProveEf(T.Or(T.Not(T.Eq(now, T.Int(EfDetached))), NoOtherWithKey(c, o, e, f)), TrackerId, at,
                $"'{at}' may meet another {e.Type.Name} with the same key that the context already tracks, and EF throws: use the tracked one, or a context that tracks none");
            if (state == Modified && e.Tokens.Count > 0 && KeyColumn(e.Tokens[0], o, f) is Term token)
                ProveEf(T.Implies(AsBool(Model("Read", c, f, o)), T.Eq(T.Coerce(token, Sort.Int), T.Coerce(Model("TokenRead", c, f, o), Sort.Int))), TokenId, at,
                    $"'{at}' takes {e.Tokens[0].Name}, the concurrency token, as the value the row had when read, but it was changed since: " +
                    "EF would check the row against the new value. Mark it modified first, then change it");
            SetModelAt("State", c, o, T.Int(state), f);
            if (state == Modified) SetModel("Unsaved", c, T.True, f);
        }

        /// <summary>
        /// A write of an entity's field: a row version is the database's to set (CSV1034); and for a context tracking
        /// the entity unchanged, it is now modified, with changes to save.
        /// </summary>
        private void EfFieldWrite(ISymbol field, Term o, SyntaxNode at, Frame f)
        {
            if (Ef == null || !(field is IPropertySymbol p) || Ef.EntityOf(p.ContainingType) is not EfModel.Entity e) return;
            if (e.RowVersions.Contains(p))
                Report(TokenId, at, $"'{at}' writes {p.Name}, a row version: the database sets it on every write, and EF checks the row against the value read", isError: true);
            if (TrackerModel("State") is not IMethodSymbol stateModel) return;
            // (for every context: the field map of states, over contexts, updated where o is tracked)
            var states = FieldMap(f, stateModel);
            var unsaved = FieldMap(f, TrackerModel("Unsaved"));
            var oo = T.Coerce(o, Sort.Int).S;
            f.Link = null;
            f.Fields[FieldEffects.Key(stateModel)] = Pointwise("written", Sort.Heap,
                $"(store (select {states.S} y) {oo} (ite (= (select (select {states.S} y) {oo}) {Unchanged}) {Modified} (select (select {states.S} y) {oo})))");
            f.Fields[FieldEffects.Key(TrackerModel("Unsaved"))] = Pointwise("written", Sort.Row,
                $"(ite (distinct (select (select {states.S} y) {oo}) {EfDetached}) 1 (select {unsaved.S} y))");
        }
    }
}
