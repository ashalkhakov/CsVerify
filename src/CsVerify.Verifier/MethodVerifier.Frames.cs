using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Dafny-style dynamic frames for ordinary mutable classes. An object keeps a ghost set of the objects it is
    /// made of (<c>Ghost&lt;ObjSet&gt; Repr</c>) and a [Pure] <c>Valid()</c> that reads only them (Spec.Reads).
    /// <list type="bullet">
    /// <item>A method with <c>Spec.Modifies(W)</c> writes fields only of objects in W (on entry) or allocated since
    /// (CSV1017); a call to it changes nothing else, every other object's fields are as before.</item>
    /// <item>A [Pure] function with <c>Spec.Reads(R)</c> reads fields only of objects in R (CSV1017); a change
    /// touching nothing in R leaves its value as it was, so <c>Valid()</c> of one object survives updates of
    /// another whose representation is disjoint.</item>
    /// <item><c>Spec.Fresh(x)</c> in a postcondition: x was allocated by the method.</item>
    /// </list>
    /// [Owned] classes are framed by their views instead; a class is one or the other.
    /// </summary>
    internal sealed partial class MethodVerifier
    {
        private Term _modifiesEntry, _readsEntry, _allocEntry;
        private int _linkDepth;

        private static Term InSet(Term set, Term o) => T.Not(T.Eq(T.Select(set, T.Coerce(o, Sort.Int), Sort.Int), T.Int(0)));

        /// <summary>Before the preconditions: the allocated objects (this and the parameters, unless this is being built).</summary>
        private void EnterAlloc(Frame f)
        {
            // (ownership needs it too: a new object is none of the objects reachable through fields)
            if (!_engine.UsesDynamicFrames && !_engine.UsesOwnership) return;
            f.Alloc = _allocEntry = _z3.Fresh("alloc", Sort.Row);
            foreach (var p in _method.Parameters.Where(p => MayBeNullType(p.Type) && f.Vars.ContainsKey(p)))
                _z3.Assume(T.Implies(NotNull(f.Vars[p]), InSet(f.Alloc, f.Vars[p])));
            if (f.This == null) return;
            if (_method.MethodKind != MethodKind.Constructor) { _z3.Assume(InSet(f.Alloc, f.This)); return; }
            // a constructor's object was allocated just before it ran: fresh with respect to the entry state
            _z3.Assume(T.Not(InSet(f.Alloc, f.This)));
            f.Alloc = T.Store(f.Alloc, f.This, T.Int(1));
        }

        /// <summary>After the preconditions: the method's own frames, as they are on entry.</summary>
        private void EnterFrames(Frame f, SpecEnv spec)
        {
            if ((_contract.Modifies != null || _contract.Reads != null) && SpecSymbols.IsOwned(_method.ContainingType))
                Report("CSV1017", MethodLocationNode(), $"{_method.ContainingType.Name} is [Owned]: its objects are framed by their views, not by Spec.Modifies/Spec.Reads", isError: true);
            if (_contract.Modifies != null) _modifiesEntry = EvalOwnSpec(_contract.Modifies, f, spec);
            if (_contract.Reads != null) _readsEntry = EvalOwnSpec(_contract.Reads, f, spec);
        }

        private bool ChecksFrames => _codeMode && _foreignSpec == 0;

        /// <summary>A write of an (unowned) field: within Spec.Modifies, or of an object allocated since entry.</summary>
        private void CheckWrite(Term o, SyntaxNode at)
        {
            if (_modifiesEntry == null || !ChecksFrames) return;
            Require(T.Or(InSet(_modifiesEntry, o), T.Not(InSet(_allocEntry, o))), "CSV1017", at,
                $"'{at}' writes an object that is not in Spec.Modifies and was not allocated here");
        }

        /// <summary>A read of a field in a [Pure] function with Spec.Reads: within the frame.</summary>
        private void CheckRead(ISymbol field, Term o, SyntaxNode at)
        {
            if (_readsEntry == null || !ChecksFrames) return;
            Require(InSet(_readsEntry, o), "CSV1017", at, $"'{at}' reads an object that is not in Spec.Reads");
        }

        /// <summary>
        /// A call to a method that may write fields: within this method's Spec.Modifies (if it has one). Returns what
        /// the call may change (its Spec.Modifies and what it allocates), or null if that is not known.
        /// </summary>
        private Term CalleeModifies(Contract callee, Frame pre, Frame f, SyntaxNode at)
        {
            var (fields, all) = _engine.Fields.WritesOf(callee.Method);
            if (!all && !fields.Any(x => !IsOwnedField(x))) return null;
            if (callee.Modifies == null)
            {
                if (_modifiesEntry != null && ChecksFrames)
                    Report("CSV1017", at, $"'{callee.Method.Name}' may write fields but has no Spec.Modifies frame, so this method's Spec.Modifies cannot be checked", isError: true);
                return null;
            }
            var frame = T.Coerce(EvalForeignSpec(callee.Modifies, pre, new SpecEnv { Old = pre }), Sort.Row);
            if (_modifiesEntry != null && ChecksFrames)
                Prove(new Term($"(forall ((i Int)) (=> (distinct (select {frame} i) 0) (or (distinct (select {_modifiesEntry} i) 0) (= (select {_allocEntry} i) 0))))", Sort.Bool),
                    "CSV1017", at, $"Spec.Modifies of '{callee.Method.Name}' might not be within this method's");
            return f.Alloc != null ? new Term($"(cv_mod {frame} {f.Alloc})", Sort.Row) : frame;
        }

        /// <summary>A [Pure] call inside a function with Spec.Reads: the callee's reads must be within ours.</summary>
        private void CheckPureCallReads(Contract callee, Frame pre, SyntaxNode at)
        {
            if (_readsEntry == null || !ChecksFrames || _engine.Fields.ReadsOf(callee.Method).Count == 0) return;
            if (callee.Reads == null)
            {
                Report("CSV1017", at, $"'{callee.Method.Name}' reads fields but has no Spec.Reads frame, so this function's Spec.Reads cannot be checked", isError: true);
                return;
            }
            var frame = T.Coerce(EvalForeignSpec(callee.Reads, pre, new SpecEnv { Old = pre }), Sort.Row);
            Prove(new Term($"(cv_subset {frame} {_readsEntry})", Sort.Bool), "CSV1017", at,
                $"Spec.Reads of '{callee.Method.Name}' might not be within this function's");
        }

        /// <summary>After a call that may allocate: more objects are allocated, including any it returns.</summary>
        private void AllocAfterCall(Frame f, params Term[] results)
        {
            if (f.Alloc == null) return;
            var after = _z3.Fresh("alloc", Sort.Row);
            _z3.Assume(new Term($"(cv_subset {f.Alloc} {after})", Sort.Bool));
            f.Alloc = after;
            foreach (var r in results.Where(r => r != null && r.Sort == Sort.Int))
                _z3.Assume(T.Implies(NotNull(r), InSet(after, r)));
        }

        /// <summary>
        /// <c>Spec.Fresh(x)</c>: x is allocated now and was not in the state <c>Spec.Old</c> refers to (not null).
        /// <c>Spec.Fresh(set)</c>: every member is.
        /// </summary>
        private Term Fresh(Term o, Frame f, SpecEnv spec)
        {
            if (spec?.Old?.Alloc == null || f.Alloc == null) return _z3.Fresh("fresh", Sort.Bool);
            if (o.Sort == Sort.Row)
                return new Term($"(forall ((i Int)) (=> (distinct (select {o} i) 0) (and (distinct i 0) (distinct (select {f.Alloc} i) 0) (= (select {spec.Old.Alloc} i) 0))))", Sort.Bool);
            return T.And(NotNull(o), InSet(f.Alloc, o), T.Not(InSet(spec.Old.Alloc, o)));
        }

        /// <summary>
        /// The frame rule for a [Pure] function with Spec.Reads: if the last change of heap fields touched nothing it
        /// reads (in the state before the change), its value is what it was then. Followed back along the changes.
        /// </summary>
        private void LinkPure(Contract callee, Term receiver, Term[] args, Sort sort, Frame state, Term app)
        {
            if (callee.Reads == null || state?.Link == null || _linkDepth >= 16) return;
            var link = state.Link;
            _linkDepth++;
            try
            {
                var before = PureApply(callee, receiver, args, link.Before.Heap, sort, null, link.Before);
                if (before.S == T.Coerce(app, sort).S) return;
                var frame = CalleeFrame(callee, receiver, args, link.Before.Heap, link.Before);
                var reads = T.Coerce(EvalForeignSpec(callee.Reads, frame, new SpecEnv { Old = frame }), Sort.Row);
                AssumeSide(T.Implies(new Term($"(cv_disjoint {reads} {link.Changed})", Sort.Bool), T.Eq(T.Coerce(app, sort), before)));
            }
            finally { _linkDepth--; }
        }
    }
}
