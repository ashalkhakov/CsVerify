using System;
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
                // an exception in a filter does not escape it: the filter is false
                if (r.Kind == ControlFlowRegionKind.Filter) { Resume(f); return; }
                var parent = r.EnclosingRegion;
                if (r.Kind != ControlFlowRegionKind.Try || parent == null || _erasedTry.Contains(parent)) continue;
                if (parent.Kind == ControlFlowRegionKind.TryAndCatch)
                {
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
