using System;
using System.Collections.Generic;
using System.Linq;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>
    /// The traversal of the kernel's mathematics (KLit, KVar, KOp, KQuant, KFnApp), in one place: Rewrite rewrites, Subterms
    /// queries. Any other kind, met here, is an error: no walk skips one it doesn't know.
    /// </summary>
    internal abstract partial class KExpr
    {
        /// <summary>
        /// This rewritten: a node for which <paramref name="at"/> gives an expression is replaced by it; any other is rebuilt
        /// of its rewritten parts (a new node, but a literal or variable, which is kept). A quantifier's triggers are
        /// rewritten too; a function application keeps all but its arguments and snapshot.
        /// </summary>
        public KExpr Rewrite(Func<KExpr, KExpr> at)
        {
            if (at(this) is KExpr given)
            {
                return given;
            }
            KExpr R(KExpr x) => x.Rewrite(at);
            return this switch
            {
                KLit or KVar => this,
                KOp op => new KOp(op.Op, op.Args.Select(R).ToArray()),
                KQuant q => new KQuant
                {
                    Forall = q.Forall,
                    Var = q.Var,
                    Type = q.Type,
                    Range = q.Range == null ? null : R(q.Range),
                    Body = R(q.Body),
                    Trigger = q.Trigger?.Select(R).ToArray(),
                },
                KFnApp f => new KFnApp
                {
                    Callee = f.Callee,
                    Function = f.Function,
                    Plain = f.Plain,
                    MapsAt = f.MapsAt,
                    Layer = f.Layer,
                    Fields = f.Fields,
                    Args = f.Args.Select(R).ToArray(),
                    Snap = f.Snap == null ? null : R(f.Snap),
                },
                _ => throw KernelTerms.NotMath(this),
            };
        }

        /// <summary>
        /// This and every expression in it, outermost first; below a node <paramref name="into"/> refuses, nothing (it is
        /// still given). A quantifier's triggers are left out: hints to the solver, not part of what it says.
        /// </summary>
        public IEnumerable<KExpr> Subterms(Func<KExpr, bool> into = null)
        {
            var stack = new Stack<KExpr>();
            stack.Push(this);
            while (stack.Count > 0)
            {
                var x = stack.Pop();
                yield return x;
                if (into != null && !into(x))
                {
                    continue;
                }
                var children = x.Children().ToList();
                for (int k = children.Count - 1; k >= 0; k--)
                {
                    stack.Push(children[k]);
                }
            }
        }

        /// <summary>Its immediate parts, as Subterms takes them.</summary>
        public IEnumerable<KExpr> Children() => this switch
        {
            KLit or KVar => Enumerable.Empty<KExpr>(),
            KOp op => op.Args,
            KQuant q => q.Range == null ? new[] { q.Body } : new[] { q.Range, q.Body },
            KFnApp f => f.Snap == null ? f.Args : f.Args.Append(f.Snap),
            _ => throw KernelTerms.NotMath(this),
        };

        /// <summary>Is it mathematics through and through?</summary>
        public bool IsMath() => this switch
        {
            KLit or KVar => true,
            KOp op => op.Args.All(a => a.IsMath()),
            KQuant q => (q.Range == null || q.Range.IsMath()) && q.Body.IsMath() && (q.Trigger == null || q.Trigger.All(t => t.IsMath())),
            KFnApp f => f.Args.All(a => a.IsMath()) && (f.Snap == null || f.Snap.IsMath()),
            _ => false,
        };

        /// <summary>Its conjuncts: the operands of its &&s, left to right (itself, if it isn't one).</summary>
        public IEnumerable<KExpr> Conjuncts() => this is KOp { Op: "&&" } and ? and.Args.SelectMany(a => a.Conjuncts()) : new[] { this };

        /// <summary>A permission assertion's permissions: its atoms, through its operators (not into a quantifier).</summary>
        public IEnumerable<KExpr> Atoms() => this switch
        {
            KCells or KAcc or KInst or KFieldAcc => new[] { this },
            KOp op => op.Args.SelectMany(a => a.Atoms()),
            _ => Enumerable.Empty<KExpr>(),
        };
    }

    /// <summary>Level 2's mathematics in the kernel.</summary>
    internal static class KernelTerms
    {
        /// <summary>Level 2's mathematics in the kernel, which holds all of it.</summary>
        public static KExpr Of(MExpr e) => e switch
        {
            null => null,
            MLit l => new KLit(l.Text),
            MVar v => new KVar(v.Name),
            MOp op => new KOp(op.Op, op.Args.Select(Of).ToArray()),
            MQuant q => new KQuant
            {
                Forall = q.Forall,
                Var = q.Var,
                Type = q.Type,
                Range = Of(q.Range),
                Body = Of(q.Body),
                Trigger = q.Trigger?.Select(Of).ToArray(),
            },
            MFnApp f => new KFnApp
            {
                Callee = f.Callee,
                Function = f.Function,
                Layer = f.Layer,
                Fields = f.Fields,
                Args = f.Args.Select(Of).ToArray(),
                Snap = Of(f.Snap),
                Plain = f.Plain,
                MapsAt = f.MapsAt,
            },
            _ => throw new System.InvalidOperationException("not mathematics: " + e.GetType().Name),
        };

        public static Exception NotMath(KExpr e) => new InvalidOperationException("not mathematics, where mathematics is: " + e?.GetType().Name);
    }
}
