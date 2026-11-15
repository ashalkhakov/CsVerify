using System.Collections.Generic;
using System.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.FlowAnalysis;
using static CsVerify.Verifier.Boogie.KernelTypes;
using static CsVerify.Verifier.Boogie.KOp;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>Exceptions and finally: where a throw goes, catch dispatch by type and filter, edges through finally blocks.</summary>
    internal sealed partial class Lowering
    {
        /// <summary>
        /// A cast where exceptions are seen: where it fails, an InvalidCastException, which the handlers may catch; past
        /// it, it succeeded.
        /// </summary>
        private void CastThrows(KExpr ok, bool inSpec)
        {
            if (inSpec || _cfgBlock == null || !(ThrowTarget(_cfgBlock.EnclosingRegion) is string to))
            {
                return;
            }
            Emit(new KFork
            {
                Overflow = ok,
                Target = to,
                Exception = null,
            });
            Emit(KAssume.Of(ok));
        }

        // ------------------------------------------------------------------ exceptions

        private ControlFlowGraph _cfg;
        private BasicBlock _cfgBlock;
        private bool _exitUsed;
        private readonly Dictionary<ControlFlowRegion, string> _dispatch = new Dictionary<ControlFlowRegion, string>();

        /// <summary>The innermost try a region is in (not a handler of it: an exception there goes past it); null if none.</summary>
        private ControlFlowRegion TryOf(ControlFlowRegion r)
        {
            for (; r != null && !Outside(r); r = r.EnclosingRegion)
            {
                if (r.Kind == ControlFlowRegionKind.Try && r.EnclosingRegion?.Kind == ControlFlowRegionKind.TryAndCatch)
                {
                    return r;
                }
                if (r.Kind == ControlFlowRegionKind.Catch)
                {
                    r = r.EnclosingRegion; // (its TryAndCatch: go on outside it)
                } // (its TryAndCatch: go on outside it)
                else if (r.Kind == ControlFlowRegionKind.Finally)
                {
                    r = r.EnclosingRegion;
                }
            }
            return null;
        }

        /// <summary>
        /// Where an exception thrown in this region goes: its try's handlers, or the method's exit where it has
        /// EnsuresOnThrow; null where exceptions aren't seen (the path just ends).
        /// </summary>
        private string ThrowTarget(ControlFlowRegion r)
        {
            if (_p.Ghost || _contract.IsPure || _contract.IsLemma || _cfg == null)
            {
                return null; // (proofs may not throw)
            } // (proofs may not throw)
            // (in a filter, before any try of its own: the exception is swallowed, the filter false)
            for (var q = r; q != null && q.Kind != ControlFlowRegionKind.Try; q = q.EnclosingRegion)
            {
                if (q.Kind == ControlFlowRegionKind.Filter)
                {
                    return FilterFalse(q);
                }
            }
            var t = TryOf(r);
            // (a try with a finally, inside the handlers' try, or with none: the finally runs, then the exception goes on)
            var f = FinallyTryOf(r);
            if (f != null && (t == null || IsInside(f, t)))
            {
                if (_throughFinally.TryGetValue(f, out var known))
                {
                    return known;
                }
                var outer = ThrowTarget(f.EnclosingRegion.EnclosingRegion ?? f.EnclosingRegion);
                var via = (KGoto)ThroughFinally(f.EnclosingRegion.NestedRegions.First(x => x.Kind == ControlFlowRegionKind.Finally), outer == null ? new KStop() : new KGoto(outer), f.FirstBlockOrdinal);
                Declare("ex$", _model.Compilation.GetTypeByMetadataName("System.Exception"));
                return _throughFinally[f] = via.Targets[0];
            }
            if (t == null)
            {
                if (_contract.ThrowEnsures.Count == 0)
                {
                    return null;
                }
                if (!_exitUsed)
                {
                    Declare("ex$", _model.Compilation.GetTypeByMetadataName("System.Exception"));
                }
                _exitUsed = true;
                return "x$exit";
            }
            return Dispatch(t);
        }

        private readonly Dictionary<ControlFlowRegion, string> _throughFinally = new Dictionary<ControlFlowRegion, string>();

        /// <summary>The innermost try with a finally a region is in (not its finally: an exception there goes past it); null if none.</summary>
        private ControlFlowRegion FinallyTryOf(ControlFlowRegion r)
        {
            for (; r != null && !Outside(r); r = r.EnclosingRegion)
            {
                if (r.Kind == ControlFlowRegionKind.Try && r.EnclosingRegion?.Kind == ControlFlowRegionKind.TryAndFinally && !_erased.Contains(r.EnclosingRegion))
                {
                    return r;
                }
                if (r.Kind == ControlFlowRegionKind.Finally)
                {
                    r = r.EnclosingRegion;
                }
            }
            return null;
        }

        /// <summary>A region of another graph (a lambda's is in its method's): an exception leaves the lambda before it.</summary>
        private bool Outside(ControlFlowRegion r)
        {
            if (_cfg == null)
            {
                return false;
            }
            if (_ownRegions == null)
            {
                _ownRegions = new HashSet<ControlFlowRegion>(AllRegions(_cfg.Root).Append(_cfg.Root));
            }
            return !_ownRegions.Contains(r);
        }

        private HashSet<ControlFlowRegion> _ownRegions;

        /// <summary>Is region a inside region b?</summary>
        private static bool IsInside(ControlFlowRegion a, ControlFlowRegion b)
        {
            for (var r = a; r != null; r = r.EnclosingRegion)
            {
                if (r == b)
                {
                    return true;
                }
            }
            return false;
        }

        private readonly Dictionary<ControlFlowRegion, string> _filterFalse = new Dictionary<ControlFlowRegion, string>();

        /// <summary>Where a filter that's false goes: its try's next handler, or outward.</summary>
        private string FilterFalse(ControlFlowRegion filter)
        {
            Dispatch(filter.EnclosingRegion.EnclosingRegion.NestedRegions.First(x => x.Kind == ControlFlowRegionKind.Try));
            return _filterFalse[filter];
        }

        /// <summary>A try's handlers, in order: each catch tests the exception's type (and its filter); none taken, it goes on outward.</summary>
        private string Dispatch(ControlFlowRegion tryRegion)
        {
            if (_dispatch.TryGetValue(tryRegion, out var label))
            {
                return label;
            }
            label = $"x${tryRegion.FirstBlockOrdinal}";
            _dispatch[tryRegion] = label;
            var outer = ThrowTarget(tryRegion.EnclosingRegion.EnclosingRegion ?? tryRegion.EnclosingRegion);
            var handlers = tryRegion.EnclosingRegion.NestedRegions.Where(x => x.Kind is ControlFlowRegionKind.Catch or ControlFlowRegionKind.FilterAndHandler).ToList();
            var ex = new KVar("ex$");
            Declare("ex$", _model.Compilation.GetTypeByMetadataName("System.Exception"));
            // (handler k: taken where the type matches, else on to the next; past the last, outward)
            for (int k = 0; k < handlers.Count; k++)
            {
                var h = handlers[k];
                var all = h.ExceptionType == null || h.ExceptionType.ToDisplayString() == "System.Exception";
                if (!all)
                {
                    _p.AddExceptionType(h.ExceptionType);
                }
                var test = all ? (KExpr)KLit.True : new KOp("sub", new KOp("dtype", ex), new KLit(TypeConst(h.ExceptionType)));
                string here = k == 0 ? label : $"{label}$n{k - 1}", take = $"{label}$h{k}", pass = $"{label}$t{k}";
                if (k > 0)
                {
                    _p.Blocks.Last(x => x.Label == here).Jump = new KGoto(take, pass);
                }
                else
                {
                    _p.AddBlock(KBlock.Of(here, tryRegion.FirstBlockOrdinal, jump: new KGoto(take, pass)));
                }
                _p.AddBlock(new KBlock
                {
                    Label = take,
                    Ordinal = tryRegion.FirstBlockOrdinal,
                    Stmts = { KAssume.Of(test) },
                    Jump = new KGoto($"b{h.FirstBlockOrdinal}"),
                });
                var next = new KBlock
                {
                    Label = pass,
                    Ordinal = tryRegion.FirstBlockOrdinal,
                    Stmts = { KAssume.Of(Not(test)) },
                };
                _p.AddBlock(next);
                if (k == handlers.Count - 1)
                {
                    next.Jump = outer == null ? new KStop() : new KGoto(outer);
                }
                else
                {
                    next.Jump = new KGoto($"{label}$n{k}");
                    _p.AddBlock(KBlock.Of($"{label}$n{k}", tryRegion.FirstBlockOrdinal));
                }
                // (a filter: its type matched, it runs; false, on to the next handler as if the type hadn't)
                if (h.Kind == ControlFlowRegionKind.FilterAndHandler)
                {
                    var filter = h.NestedRegions.First(x => x.Kind == ControlFlowRegionKind.Filter);
                    _filterFalse[filter] = $"{label}$f{k}";
                    _p.AddBlock(KBlock.Of(
                        $"{label}$f{k}",
                        tryRegion.FirstBlockOrdinal,
                        jump: k == handlers.Count - 1 ? (outer == null ? new KStop() : new KGoto(outer)) : new KGoto($"{label}$n{k}")));
                }
            }
            if (handlers.Count == 0)
            {
                _p.AddBlock(KBlock.Of(label, tryRegion.FirstBlockOrdinal, jump: outer == null ? new KStop() : new KGoto(outer)));
            }
            return label;
        }

        private static IEnumerable<ControlFlowRegion> AllRegions(ControlFlowRegion r) => r.NestedRegions.Concat(r.NestedRegions.SelectMany(AllRegions));

        // ------------------------------------------------------------------ finally

        /// <summary>Each finally's ways on: by the number its continuation variable holds, where to go after it.</summary>
        private readonly Dictionary<ControlFlowRegion, List<(int id, KJump then)>> _finExits = new Dictionary<ControlFlowRegion, List<(int, KJump)>>();
        private readonly List<(ControlFlowRegion fin, KBlock end)> _finEnds = new List<(ControlFlowRegion, KBlock)>();
        private int _edges;

        /// <summary>The finally a block is in (not one of a foreach's enumerator, which isn't there).</summary>
        private ControlFlowRegion FinallyOf(ControlFlowRegion r)
        {
            for (; r != null; r = r.EnclosingRegion)
            {
                if (r.Kind == ControlFlowRegionKind.Finally)
                {
                    return _erased.Contains(r.EnclosingRegion) ? null : r;
                }
            }
            return null;
        }

        private string Continuation(ControlFlowRegion fin) => Declare($"fin${fin.FirstBlockOrdinal}", _model.Compilation.GetSpecialType(SpecialType.System_Int32));

        /// <summary>Runs this finally, then goes on as given.</summary>
        private KJump ThroughFinally(ControlFlowRegion fin, KJump then, int ordinal)
        {
            if (!_finExits.TryGetValue(fin, out var exits))
            {
                _finExits[fin] = exits = new List<(int, KJump)>();
            }
            var id = exits.Count;
            exits.Add((id, then));
            var label = $"e${_edges++}";
            _p.AddBlock(new KBlock
            {
                Label = label,
                Ordinal = ordinal,
                Stmts =
                {
                    KAssign.Of(Continuation(fin), new KLit(id.ToString())),
                },
                Jump = new KGoto($"b{fin.FirstBlockOrdinal}"),
            });
            return new KGoto(label);
        }

        /// <summary>A way out of a block: through the finallies it leaves (innermost first), then to where it goes.</summary>
        private KJump Edge(BasicBlock from, ControlFlowBranch branch)
        {
            // (a filter's false: on to the next handler)
            if (branch != null && branch.Destination == null && branch.Semantics == ControlFlowBranchSemantics.StructuredExceptionHandling &&
                from.EnclosingRegion.Kind == ControlFlowRegionKind.Filter)
            {
                return new KGoto(FilterFalse(from.EnclosingRegion));
            }
            var target = To(from, branch?.Destination);
            if (branch == null)
            {
                return target;
            }
            var fins = branch.FinallyRegions.Where(f => !_erased.Contains(f.EnclosingRegion)).ToList();
            for (int k = fins.Count - 1; k >= 0; k--)
            {
                target = ThroughFinally(fins[k], target, from.Ordinal);
            }
            return target;
        }

        /// <summary>Each finally's end: to each way on, where its continuation says (nowhere, if nothing runs it).</summary>
        private void FinallyEnds()
        {
            foreach (var (fin, end) in _finEnds)
            {
                var exits = _finExits.TryGetValue(fin, out var x) ? x : new List<(int id, KJump then)>();
                if (exits.Count == 0)
                {
                    end.Jump = new KStop();
                    continue;
                }
                var v = Continuation(fin);
                var labels = new List<string>();
                foreach (var (id, then) in exits)
                {
                    var label = $"{end.Label}$f{id}";
                    labels.Add(label);
                    var fb = new KBlock
                    {
                        Label = label,
                        Ordinal = end.Ordinal,
                        Stmts = { KAssume.Of(Eq(new KVar(v), new KLit(id.ToString()))) },
                        Jump = then,
                    };
                    // (a return through the finally: the tasks are awaited by now, CSV1026)
                    if (then is KReturn)
                    {
                        TasksAwaited(fb);
                    }
                    _p.AddBlock(fb);
                }
                end.Jump = new KGoto(labels.ToArray());
            }
        }

        /// <summary>A jump to a block, or a return where it is to the exit.</summary>
        private KJump To(BasicBlock from, BasicBlock to)
        {
            if (to == null)
            {
                return new KStop();
            }
            if (to.Kind == BasicBlockKind.Exit)
            {
                // (where a return is reported: the return statement or its value; a return; at its block's
                // last operation; falling off the end, at the method)
                var at = from.BranchValue?.Syntax.Parent as ReturnStatementSyntax as SyntaxNode ?? from.BranchValue?.Syntax ??
                         (from.FallThroughSuccessor?.Semantics == ControlFlowBranchSemantics.Return ? from.Operations.LastOrDefault()?.Syntax : null) ?? _decl;
                return KReturn.Of(at);
            }
            return new KGoto($"b{to.Ordinal}");
        }
    }
}
