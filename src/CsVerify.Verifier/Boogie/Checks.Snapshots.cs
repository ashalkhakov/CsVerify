using System;
using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using static CsVerify.Verifier.Boogie.KernelTypes;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>Snapshots: a predicate instance's snapshot, and the functions over it defined from its body.</summary>
    internal sealed partial class Checks
    {
        // ------------------------------------------------------------------ functions over predicates (snapshots, as Carbon's)

        private static readonly HashSet<string> Snaps = new HashSet<string> { "psnap" };

        /// <summary>The snapshot of the instance a function over a predicate is applied to, at these arguments.</summary>
        private static KExpr Snap(IMethodSymbol pred, int[] map, KExpr[] args)
        {
            var instArgs = new KExpr[pred.Parameters.Length];
            for (int k = 0; k < map.Length; k++) if (map[k] >= 0) instArgs[map[k]] = args[k];
            return new KOp("sel", new KVar("psnap"), Instance(pred, instArgs));
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
        private void SnapFacts(IMethodSymbol pred, KExpr[] args, KExpr g)
        {
            var sig = _program.Signature(pred);
            if (sig.FunctionBody == null) return;
            var snap = new KOp("$sst", new KOp("sel", new KVar("psnap"), Instance(pred, args)));
            KExpr In(KExpr e) => MathTerms.Map(e, x => x switch
            {
                KVar v when v.Name.StartsWith("$E.") || v.Name.StartsWith("$F.") => new KOp("$st." + v.Name, snap),
                // (not into a function's arguments: a map read there stays the memory's now. TODO: of the snapshot too?)
                KFnApp => x,
                _ => null,
            });
            // (of no memory now, no old(...), no other snapshot)
            bool Plain(KExpr e) => MathTerms.Subterms(e).All(x => x is not (KFnApp { Plain: false } or KOp { Op: "old" } or KVar { Name: "psnap" }));
            var given = pred.Parameters.Select((x, k) => (x, k)).ToDictionary(x => Local(x.x), x => args[x.k]);
            var facts = new List<(KExpr g, KExpr f)>();
            var saved = _old;
            Walk(sig.FunctionBody, given, g, (_, __) => { }, (gg, f) => facts.Add((gg, f)));
            foreach (var (gg, f) in facts.Where(x => Plain(x.f) && Plain(x.g)))
            {
                _p.UsesState = true;
                Assume(Implies(In(gg), In(f)));
            }
        }

        /// <summary>
        /// The functions over a predicate, of an instance whose footprint is in hand as it was folded (folding it,
        /// unfolding it): where its precondition holds, the value of its snapshot is its body, read now.
        /// </summary>
        private void Define(IMethodSymbol pred, KExpr[] instArgs, KExpr p)
        {
            foreach (var f in _program.FunctionsOver(pred))
            {
                if (!(_program.OverPredicate(f) is (IMethodSymbol, int[] map))) continue;
                var sig = _program.Signature(f);
                if (sig.FunctionBody == null) continue;
                // (its parameters not of the instance: for every value of them)
                var args = map.Select((j, k) => j >= 0 ? instArgs[j] : new KVar($"q$x{k}")).ToArray();
                var given = f.Parameters.Select((x, k) => (x, k)).ToDictionary(x => Local(x.x), x => args[x.k]);
                KExpr M(KExpr x) { var v = Spec(x, out _); _facts.Clear(); return Subst(v, given); }
                var pre = sig.Requires.Select(r => M(r.Expr)).Aggregate((KExpr)new KLit("true"), Conj);
                var app = new KFnApp { Callee = f, Function = FunctionName(f), Args = args, Snap = new KOp("sel", new KVar("psnap"), p) };
                KExpr fact = Implies(pre, new KOp("==", app, M(sig.FunctionBody)));
                for (int k = map.Length - 1; k >= 0; k--)
                    if (map[k] < 0) fact = new KQuant { Forall = true, Var = $"q$x{k}", Type = TypeOf(f.Parameters[k].Type), Body = fact };
                Assume(fact);
            }
        }
    }
}
