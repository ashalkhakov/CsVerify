using System;
using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.FlowAnalysis;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Exceptions. An exception is an object (not null, of the type thrown) whose dynamic type the handlers test:
    /// <list type="bullet">
    /// <item>it is raised by <c>throw</c>, by a call (any callee may throw anything: methods are verified for partial
    /// correctness; its Spec.EnsuresOnThrow says what then holds), and by operations that throw (checked overflow,
    /// a failed cast, Math.Abs(MinValue));</item>
    /// <item>the enclosing try regions are searched: a catch whose type it is an instance of (and whose filter holds)
    /// handles it; a finally runs on the way, then the search goes on; leaving the method, its own
    /// Spec.EnsuresOnThrow clauses must hold;</item>
    /// <item>a call that throws gives nothing back: views lent by ref are lost, invariants and postconditions are
    /// not known (only its exceptional postconditions);</item>
    /// <item>a finally also runs on every normal way out of its try (a continuation on the path, Frame.Pending).</item>
    /// </list>
    /// An exceptional path is explored only where something sees it (a try around, or exceptional postconditions):
    /// elsewhere a throw just ends the path, as before. Proofs (lemmas, [Pure]) may not throw at all.
    /// </summary>
    internal sealed partial class MethodVerifier
    {
        private ControlFlowGraph _cfg;
        private BasicBlock _block;        // the block whose operations are being executed
        private Frame _current;           // and the state of the path there
        private System.Collections.Generic.HashSet<int> _onPath;

        /// <summary>Would an exception raised here be seen: a try around it, or exceptional postconditions to prove?</summary>
        private bool ExceptionsObserved =>
            _block != null && !ProofCode && _codeMode && _foreignSpec == 0 &&
            (_contract.ThrowEnsures.Count > 0 || InTry(_block.EnclosingRegion));

        private static bool Enclosing(ControlFlowRegion r, ControlFlowRegionKind kind)
        {
            for (; r != null; r = r.EnclosingRegion) if (r.Kind == kind) return true;
            return false;
        }

        private INamedTypeSymbol KnownType(string metadataName) => _model.Compilation.GetTypeByMetadataName(metadataName);

        /// <summary>A new exception object of (at least) the given type.</summary>
        private Term NewException(ITypeSymbol type)
        {
            var x = _z3.Fresh("exception", Sort.Int);
            _z3.Assume(NotNull(x));
            HasType(x, type ?? KnownType("System.Exception"));
            return x;
        }

        /// <summary>
        /// Here, in state <paramref name="f"/>, an exception may be raised when <paramref name="when"/> holds: that
        /// path is followed to its handler (or out of the method), then the current one goes on (without it).
        /// <paramref name="prepare"/> turns the state into the one the exception leaves (a call's, say), and may
        /// assume what is known of the exception object then.
        /// </summary>
        private void MayRaise(Term when, Frame f, ITypeSymbol type, Action<Frame, Term> prepare = null)
        {
            if (!ExceptionsObserved) return;
            var (block, current, onPath, codeMode) = (_block, _current, _onPath, _codeMode);
            _z3.Push();
            try
            {
                _z3.Assume(T.And(_guards.Concat(new[] { when }).ToArray()));
                if (_z3.Check(T.True) == "unsat") return;
                var thrown = f.Clone();
                var x = NewException(type);
                prepare?.Invoke(thrown, x);
                var guards = _guards.ToList();
                _guards.Clear();
                try { Raise(x, thrown, block.EnclosingRegion); }
                finally { _guards.AddRange(guards); }
            }
            finally
            {
                _z3.Pop();
                (_block, _current, _onPath, _codeMode) = (block, current, onPath, codeMode);
            }
        }

        /// <summary>The exception <paramref name="x"/> is raised inside <paramref name="from"/>: find its handler.</summary>
        private void Raise(Term x, Frame f, ControlFlowRegion from)
        {
            for (var r = from; r != null; r = r.EnclosingRegion)
            {
                // (a lambda's graph has the regions around the lambda above it. It leaves by throwing: what's around it runs when someone calls it.)
                if (r == _cfg.Root) break;
                // an exception in a filter does not escape it: the filter is false
                if (r.Kind == ControlFlowRegionKind.Filter) { Resume(f); return; }
                var parent = r.EnclosingRegion;
                if (r.Kind != ControlFlowRegionKind.Try || parent == null || _erasedTry.Contains(parent)) continue;
                if (parent.Kind == ControlFlowRegionKind.TryAndCatch)
                {
                    // (collected, where its try is: its handlers run once, from all the raises' states merged)
                    if (_collecting.TryGetValue(parent, out var collector))
                    {
                        collector.Raises.Add((x, f.Clone(), _z3.Recorded(collector.BaseDepth)));
                        return;
                    }
                    TryHandlers(parent, 1, x, f);
                    return;
                }
                if (parent.Kind == ControlFlowRegionKind.TryAndFinally)
                {
                    // the finally runs, then the search goes on outside
                    var g = f.Clone();
                    g.Exception = x;
                    g.Pending = g.Pending.Push(after => Raise(x, after, parent));
                    Exec(_cfg.Blocks[parent.NestedRegions[1].FirstBlockOrdinal], g, _onPath);
                    return;
                }
            }
            ExceptionalExit(x, f);
        }

        // ================================================================== state merging at a handler

        /// <summary>The raises a try collects while its body is explored: the exception, the state, what was assumed.</summary>
        private sealed class Collector
        {
            public int BaseDepth;
            public readonly List<(Term x, Frame f, List<Term> facts)> Raises = new List<(Term, Frame, List<Term>)>();
        }

        private readonly Dictionary<ControlFlowRegion, Collector> _collecting = new Dictionary<ControlFlowRegion, Collector>();

        /// <summary>The try/catch whose try begins at <paramref name="block"/>, if one does and its handlers are seen.</summary>
        private ControlFlowRegion TryEntry(BasicBlock block)
        {
            var r = block.EnclosingRegion;
            for (; r != null; r = r.EnclosingRegion)
            {
                if (r.FirstBlockOrdinal != block.Ordinal) return null;
                if (r.Kind == ControlFlowRegionKind.Try && r.EnclosingRegion is ControlFlowRegion tc &&
                    tc.Kind == ControlFlowRegionKind.TryAndCatch && !_erasedTry.Contains(tc) && !_collecting.ContainsKey(tc))
                    return tc;
            }
            return null;
        }

        /// <summary>
        /// A try/catch, explored as symbolic executors with state merging do (KeY's merge rule; Viper's Silicon): its
        /// body is explored (and on, along its normal paths) with the raises that reach this handler collected rather
        /// than followed; then, back where the try began, the handlers run once for all of them, from their states
        /// merged. A fresh selector picks one raise: each part of the state is the selected raise's (an if-term
        /// where they differ), and what was assumed on the way to each holds where it is selected. That is exact:
        /// the merged state stands for each raise's state and for nothing else. (Followed one by one, each raise
        /// ran the handler and the rest of the method again: in a try, every call may raise, so each doubled the
        /// paths.) Raises whose states differ in more than values (which views are held, what is pending) are merged
        /// with their like only.
        /// </summary>
        private void CollectTry(ControlFlowRegion tryAndCatch, BasicBlock block, Frame f, HashSet<int> onPath)
        {
            var collector = new Collector();
            _z3.Push();
            _z3.StartRecording();
            collector.BaseDepth = _z3.Depth;
            _collecting[tryAndCatch] = collector;
            try { Exec(block, f, onPath); }
            finally
            {
                _collecting.Remove(tryAndCatch);
                _z3.StopRecording();
                _z3.Pop();
            }
            var (saved, current, savedPath, codeMode) = (_block, _current, _onPath, _codeMode);
            var guards = _guards.ToList();
            _guards.Clear();
            try
            {
                foreach (var group in collector.Raises.GroupBy(r => Shape(r.f)))
                {
                    var raises = group.ToList();
                    _z3.Push();
                    try
                    {
                        if (raises.Count == 1)
                        {
                            foreach (var fact in raises[0].facts) _z3.Assume(fact);
                            _onPath = onPath;
                            TryHandlers(tryAndCatch, 1, raises[0].x, raises[0].f);
                            continue;
                        }
                        var sel = _z3.Fresh("raise", Sort.Int);
                        _z3.Assume(T.Or(raises.Select((_, i) => T.Eq(sel, T.Int(i))).ToArray()));
                        for (int i = 0; i < raises.Count; i++)
                            _z3.Assume(T.Implies(T.Eq(sel, T.Int(i)), T.And(raises[i].facts.ToArray())));
                        var merged = Merge(raises.Select(r => r.f).ToList(), sel);
                        var x = Pick(raises.Select(r => r.x).ToList(), sel);
                        merged.Exception = x;
                        _onPath = onPath;
                        TryHandlers(tryAndCatch, 1, x, merged);
                    }
                    finally { _z3.Pop(); }
                }
            }
            finally
            {
                _guards.AddRange(guards);
                (_block, _current, _onPath, _codeMode) = (saved, current, savedPath, codeMode);
            }
        }

        /// <summary>ite(sel == 0, t0, ite(sel == 1, t1, ...)): the selected one (itself, where they are all one term).</summary>
        private static Term Pick(List<Term> ts, Term sel)
        {
            if (ts.All(t => t?.S == ts[0]?.S)) return ts[0];
            var r = ts[ts.Count - 1];
            for (int i = ts.Count - 2; i >= 0; i--) r = T.Ite(T.Eq(sel, T.Int(i)), ts[i], r);
            return r;
        }

        /// <summary>
        /// What must be the same in states that are merged: all but values, and but what the merge can make one (the
        /// resources in hand, held only if every raise holds them; the flow graph's captures, the try's own; field
        /// maps, made where a state has none yet).
        /// </summary>
        private static string Shape(Frame f)
        {
            string Keys<K, V>(Dictionary<K, V> d) => string.Join(",", d.Keys.Select(k => k.ToString()).OrderBy(k => k, StringComparer.Ordinal));
            string Set<K>(HashSet<K> h) => string.Join(",", h.Select(k => k.ToString()).OrderBy(k => k, StringComparer.Ordinal));
            string Nulls(params Term[] ts) => string.Concat(ts.Select(t => t == null ? "0" : "1"));
            return string.Join("|",
                Set(f.ActiveLoops),
                Keys(f.Refs) + ":" + string.Join(",", f.Refs.Values.Select(r => $"{r.Variable}/{r.Arr?.S}/{r.Idx?.S}")),
                Keys(f.ForEach), Keys(f.LoopMeasures), Keys(f.LoopPermFrames), Keys(f.LoopFactEntry), Keys(f.ViewSequences),
                string.Join(";", f.LoopFacts.OrderBy(kv => kv.Key).Select(kv => kv.Key + "=" + string.Join(",", kv.Value))),
                f.FieldEpoch.ToString(), System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(f.Pending).ToString(), f.ReturnSyntax?.SpanStart.ToString() ?? "-",
                Nulls(f.This, f.Heap, f.Root, f.Alloc, f.Perm, f.Inst, f.Owner, f.ArrPerm, f.COwner, f.FPerm, f.FOwner, f.Result));
        }

        /// <summary>One state for states of one shape: each value the selected one's.</summary>
        private Frame Merge(List<Frame> fs, Term sel)
        {
            Term P(Func<Frame, Term> part) => fs.Any(x => part(x) == null) ? null : Pick(fs.Select(part).ToList(), sel);
            var m = fs[0].Clone();
            m.Link = null; // (no earlier state is this one: the frame rule starts afresh)
            // (a task is awaited if it is on every path, and still running if it may be on one)
            foreach (var x in fs.Skip(1))
                foreach (var kv in x.Started)
                    m.Started[kv.Key] = m.Started.TryGetValue(kv.Key, out var t) && (t.Awaited && kv.Value.Awaited) ? t : kv.Value.Awaited && t.Result != null ? t : kv.Value;
            foreach (var k in fs[0].Vars.Keys.Where(k => fs.All(x => x.Vars.ContainsKey(k))).ToList()) m.Vars[k] = Pick(fs.Select(x => x.Vars[k]).ToList(), sel);
            foreach (var k in fs[0].Vars.Keys.Where(k => !fs.All(x => x.Vars.ContainsKey(k))).ToList()) m.Vars.Remove(k); // (declared in some only: the try's own)
            // (a field map a state has not made yet is the one it would make: its epoch's)
            foreach (var k in fs.SelectMany(x => x.Fields.Keys).Distinct(SymbolEqualityComparer.Default).ToList())
                m.Fields[k] = Pick(fs.Select(x => x.Fields.TryGetValue(k, out var map) ? map : FieldMap(x, k)).ToList(), sel);
            m.Captures.Clear();
            foreach (var k in fs[0].Captures.Keys.Where(k => fs.All(x => x.Captures.ContainsKey(k))).ToList())
                m.Captures[k] = Pick(fs.Select(x => x.Captures[k]).ToList(), sel);
            // (a resource is in hand only if every raise has it: fewer in hand is sound, a lost view is lost)
            m.LiveViews.IntersectWith(fs.SelectMany(x => x.LiveViews).Where(v => fs.All(x => x.LiveViews.Contains(v))).ToList());
            m.LivePackages.IntersectWith(fs.SelectMany(x => x.LivePackages).Where(v => fs.All(x => x.LivePackages.Contains(v))).ToList());
            m.LiveMemViews.IntersectWith(fs.SelectMany(x => x.LiveMemViews).Where(v => fs.All(x => x.LiveMemViews.Contains(v))).ToList());
            foreach (var k in fs[0].ForEach.Keys.ToList())
                m.ForEach[k] = (Pick(fs.Select(x => x.ForEach[k].arr).ToList(), sel), Pick(fs.Select(x => x.ForEach[k].idx).ToList(), sel));
            foreach (var k in fs[0].LoopFactEntry.Keys.ToList()) m.LoopFactEntry[k] = Pick(fs.Select(x => x.LoopFactEntry[k]).ToList(), sel);
            foreach (var k in fs[0].LoopMeasures.Keys.ToList())
                m.LoopMeasures[k] = Enumerable.Range(0, fs[0].LoopMeasures[k].Length).Select(i => Pick(fs.Select(x => x.LoopMeasures[k][i]).ToList(), sel)).ToArray();
            foreach (var k in fs[0].LoopPermFrames.Keys.ToList())
                m.LoopPermFrames[k] = (P(x => x.LoopPermFrames[k].perm), P(x => x.LoopPermFrames[k].inst), P(x => x.LoopPermFrames[k].arr), P(x => x.LoopPermFrames[k].fperm));
            m.This = P(x => x.This);
            m.Heap = P(x => x.Heap);
            m.Root = P(x => x.Root);
            m.Alloc = P(x => x.Alloc);
            m.Perm = P(x => x.Perm);
            m.Inst = P(x => x.Inst);
            m.Owner = P(x => x.Owner);
            m.ArrPerm = P(x => x.ArrPerm);
            m.COwner = P(x => x.COwner);
            m.FPerm = P(x => x.FPerm);
            m.FOwner = P(x => x.FOwner);
            m.Result = P(x => x.Result);
            // (the view sequences cached for loops: one only if they are one)
            foreach (var k in fs[0].ViewSequences.Keys.ToList())
                if (!fs.All(x => ReferenceEquals(x.ViewSequences[k], fs[0].ViewSequences[k]))) m.ViewSequences.Remove(k);
            return m;
        }

        /// <summary>Handler <paramref name="index"/> of a try/catch, and the ones after it, for exception x.</summary>
        private void TryHandlers(ControlFlowRegion tryAndCatch, int index, Term x, Frame f)
        {
            if (index >= tryAndCatch.NestedRegions.Length) { Raise(x, f, tryAndCatch); return; }
            var handler = tryAndCatch.NestedRegions[index];
            var type = handler.ExceptionType;
            bool all = type == null || type.SpecialType == SpecialType.System_Object || type.ToDisplayString() == "System.Exception";
            var matches = all ? T.True : ClassTest(x, type) ?? T.True;
            if (!all && ClassTest(x, type) == null)
            {
                NotModeled(_cfg.Blocks[handler.FirstBlockOrdinal].Operations.FirstOrDefault()?.Syntax ?? MethodLocationNode(), $"catch of '{type}' is not supported (a generic exception type)");
                return;
            }
            Fork(matches, () =>
            {
                var g = f.Clone();
                g.Exception = x;
                if (handler.Kind == ControlFlowRegionKind.FilterAndHandler)
                {
                    // the filter decides; false, the search goes on with the next handler
                    g.Pending = g.Pending.Push(after => TryHandlers(tryAndCatch, index + 1, x, after));
                    Exec(_cfg.Blocks[handler.NestedRegions[0].FirstBlockOrdinal], g, _onPath);
                }
                else Exec(_cfg.Blocks[handler.FirstBlockOrdinal], g, _onPath);
            });
            if (!all) Fork(T.Not(matches), () => TryHandlers(tryAndCatch, index + 1, x, f.Clone()));
        }

        private void Fork(Term cond, Action then)
        {
            _z3.Push();
            try
            {
                _z3.Assume(cond);
                if (_z3.Check(T.True) != "unsat") then();
            }
            finally { _z3.Pop(); }
        }

        /// <summary>The end of a finally (or a false filter): what it interrupted goes on.</summary>
        private void Resume(Frame f)
        {
            if (f.Pending.IsEmpty)
            {
                NotModeled(MethodLocationNode(), "the end of a finally or filter with nothing to resume");
                return;
            }
            var next = f.Pending.Peek();
            f.Pending = f.Pending.Pop();
            next(f);
        }

        /// <summary>A branch that leaves try regions: their finally blocks run first, innermost first, then the branch.</summary>
        private void ThroughFinally(ControlFlowBranch succ, int index, Frame f, Action<Frame> then)
        {
            if (index >= succ.FinallyRegions.Length) { then(f); return; }
            if (_erasedTry.Contains(succ.FinallyRegions[index].EnclosingRegion)) { ThroughFinally(succ, index + 1, f, then); return; }
            f.Pending = f.Pending.Push(after => ThroughFinally(succ, index + 1, after, then));
            Exec(_cfg.Blocks[succ.FinallyRegions[index].FirstBlockOrdinal], f, _onPath);
        }

        /// <summary>The exception leaves the method: its exceptional postconditions for the exception's type hold.</summary>
        private void ExceptionalExit(Term x, Frame f)
        {
            bool wasCode = _codeMode;
            _codeMode = true;
            try
            {
                foreach (var (type, condition, syntax) in _contract.ThrowEnsures)
                {
                    bool all = type.ToDisplayString() == "System.Exception";
                    var applies = all ? T.True : ClassTest(x, type) ?? T.True;
                    var holds = AsBool(EvalOwnSpec(condition, f, new SpecEnv { Old = _entry }));
                    Prove(T.Implies(applies, holds), "CSV1002", syntax,
                        $"postcondition on throw '{syntax}' might not hold when '{_method.Name}' throws");
                }
            }
            finally { _codeMode = wasCode; }
        }

        /// <summary>
        /// A call may throw (unless it is a proof): the state then is the call's, but it gives nothing back (views
        /// lent by ref or coming out are not ours), and only its exceptional postconditions are known.
        /// </summary>
        private void CallMayThrow(Contract callee, Term receiver, Term[] args, System.Collections.Generic.IEnumerable<Microsoft.CodeAnalysis.Operations.IArgumentOperation> arguments, Frame f, Frame pre)
        {
            if (!ExceptionsObserved || callee.IsPure || callee.IsLemma) return;
            MayRaise(T.True, f, null, (thrown, x) =>
            {
                foreach (var a in arguments.Where(a => a.Parameter != null && (a.Parameter.RefKind == RefKind.Ref || a.Parameter.RefKind == RefKind.Out)))
                {
                    if (!(VariableOf(a.Value) is ISymbol v)) continue;
                    if (IsViewVariable(v)) Release(thrown, v);
                    if (IsMemView(TypeOf(v))) ReleaseMemView(thrown, v);
                    thrown.LivePackages.Remove(v);
                }
                AllocAfterCall(thrown);
                if (callee.ThrowEnsures.Count > 0)
                    AssumeOnThrow(callee, x, CalleeFrame(callee, receiver, args, thrown.Heap, thrown), pre ?? thrown);
            });
        }

        /// <summary>A call threw: what its exceptional postconditions say of the exception it threw.</summary>
        private void AssumeOnThrow(Contract callee, Term x, Frame calleeState, Frame pre)
        {
            foreach (var (type, condition, _) in callee.ThrowEnsures)
            {
                bool all = type.ToDisplayString() == "System.Exception";
                var applies = all ? T.True : ClassTest(x, type) ?? T.False;
                _z3.Assume(T.Implies(applies, AsBool(EvalForeignSpec(condition, calleeState, new SpecEnv { Old = pre }))));
            }
        }
    }
}
