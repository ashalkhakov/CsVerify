using System.Collections.Generic;
using System.Linq;
using Microsoft.CodeAnalysis;
using static CsVerify.Verifier.Boogie.KernelTypes;
using static CsVerify.Verifier.Boogie.MOp;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>Snapshots: a predicate instance's snapshot, and the functions over it defined from its body.</summary>
    internal sealed partial class Checks
    {
        // ------------------------------------------------------------------ functions over predicates (snapshots, as Carbon's)

        private static readonly HashSet<string> Snaps = new HashSet<string> { "psnap" };

        /// <summary>The snapshot of the instance a function over a predicate is applied to, at these arguments.</summary>
        private static MExpr Snap(IMethodSymbol pred, int[] map, MExpr[] args)
        {
            var instArgs = new MExpr[pred.Parameters.Length];
            for (int k = 0; k < map.Length; k++)
            {
                if (map[k] >= 0)
                {
                    instArgs[map[k]] = args[k];
                }
            }
            return Sel("psnap", Instance(pred, instArgs));
        }

        /// <summary>
        /// A new snapshot of an instance (received, or folded): nothing is known of the functions over it yet. Unless a
        /// copy is in hand already: two copies have no footprint (its permissions would be had twice), so the functions
        /// over them are the same.
        /// </summary>
        /// <summary>
        /// The facts of a predicate's body (not its permissions) hold in the state of an instance's snapshot: it is of the
        /// footprint as it was folded, when they held. (Those that read no other function of the memory.)
        /// </summary>
        private void SnapFacts(IMethodSymbol pred, MExpr[] args, MExpr g)
        {
            var sig = _program.Signature(pred);
            if (sig.FunctionBody == null)
            {
                return;
            }
            var snap = new MOp("$sst", Sel("psnap", Instance(pred, args)));
            var given = pred.Parameters.Select((x, k) => (x, k)).ToDictionary(x => Local(x.x), x => args[x.k]);
            var facts = new List<(MExpr g, MExpr f)>();
            var saved = _old;
            Walk(sig.FunctionBody, given, g, (_, __) => { }, (gg, f) => facts.Add((gg, f)));
            foreach (var (gg, f) in facts.Where(x => IsPlain(x.f) && IsPlain(x.g)))
            {
                _p.UsesState = true;
                Assume(Implication(InSnapshot(gg, snap), InSnapshot(f, snap)));
            }
        }

        // (of no memory now, no old(...), no other snapshot)
        private bool IsPlain(MExpr e) => e.Subterms().All(x => x is not (MFnApp { Plain: false } or MOp { Op: "old" } or MVar { Name: "psnap" }));

        // (every map read, a library function's arguments' too: those Plain lets through are of its arguments alone)
        private MExpr InSnapshot(MExpr e, MOp snap) => e.Rewrite(x => x is MVar v && (v.Name.StartsWith("$E.") || v.Name.StartsWith("$F.")) ? new MOp("$st." + v.Name, snap) : null);

        /// <summary>
        /// The functions over a predicate, of an instance whose footprint is in hand as it was folded (folding it,
        /// unfolding it): where its precondition holds, the value of its snapshot is its body, read now.
        /// </summary>
        private void Define(IMethodSymbol pred, MExpr[] instArgs, MExpr p)
        {
            foreach (var f in _program.FunctionsOver(pred))
            {
                if (!(_program.OverPredicate(f) is (IMethodSymbol, int[] map)))
                {
                    continue;
                }
                var sig = _program.Signature(f);
                if (sig.FunctionBody == null)
                {
                    continue;
                }
                // (its parameters not of the instance: for every value of them)
                var args = map.Select((j, k) => j >= 0 ? instArgs[j] : new MVar($"q$x{k}")).ToArray();
                var given = f.Parameters.Select((x, k) => (x, k)).ToDictionary(x => Local(x.x), x => args[x.k]);
                var pre = ConjAll(sig.Requires.Select(r => SpecGiven(r.Expr, given)));
                var app = new MFnApp
                {
                    Callee = f,
                    Function = FunctionName(f),
                    Args = args,
                    Snap = Sel("psnap", p),
                };
                MExpr fact = Implication(pre, Eq(app, SpecGiven(sig.FunctionBody, given)));
                for (int k = map.Length - 1; k >= 0; k--)
                {
                    if (map[k] < 0)
                    {
                        fact = MQuant.ForAll($"q$x{k}", TypeOf(f.Parameters[k].Type), fact);
                    }
                }
                Assume(fact);
            }
        }

        private MExpr SpecGiven(KExpr x, Dictionary<string, MExpr> given)
        {
            var v = Spec(x, out _);
            _facts.Clear();
            return v.Substitute(given);
        }
    }
}
