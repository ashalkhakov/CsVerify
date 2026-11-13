using System;
using System.Collections.Generic;
using System.Linq;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>
    /// The traversal of mathematics (what Checks makes of the kernel's expressions: KLit, KVar, KOp, KQuant, KFnApp), in
    /// one place: Map rewrites, Subterms queries. Any other kind, met here, is an error: no walk skips one it doesn't know.
    /// </summary>
    internal static class MathTerms
    {
        /// <summary>
        /// e rewritten: a node for which <paramref name="at"/> gives an expression is replaced by it; any other is rebuilt
        /// of its rewritten parts (a new node, but a literal or variable, which is kept). A quantifier's triggers are
        /// rewritten too; a function application keeps all but its arguments and snapshot.
        /// </summary>
        public static KExpr Map(KExpr e, Func<KExpr, KExpr> at)
        {
            if (at(e) is KExpr given) return given;
            KExpr M(KExpr x) => Map(x, at);
            return e switch
            {
                KLit or KVar => e,
                KOp op => new KOp(op.Op, op.Args.Select(M).ToArray()),
                KQuant q => new KQuant
                {
                    Forall = q.Forall, Var = q.Var, Type = q.Type,
                    Range = q.Range == null ? null : M(q.Range), Body = M(q.Body), Trigger = q.Trigger?.Select(M).ToArray(),
                },
                KFnApp f => new KFnApp
                {
                    Callee = f.Callee, Function = f.Function, Plain = f.Plain, MapsAt = f.MapsAt, Layer = f.Layer, Fields = f.Fields,
                    Args = f.Args.Select(M).ToArray(), Snap = f.Snap == null ? null : M(f.Snap),
                },
                _ => throw NotMath(e),
            };
        }

        /// <summary>
        /// e and every expression in it, outermost first; below a node <paramref name="into"/> refuses, nothing (it is
        /// still given). A quantifier's triggers are left out: hints to the solver, not part of what it says.
        /// </summary>
        public static IEnumerable<KExpr> Subterms(KExpr e, Func<KExpr, bool> into = null)
        {
            var stack = new Stack<KExpr>();
            stack.Push(e);
            while (stack.Count > 0)
            {
                var x = stack.Pop();
                yield return x;
                if (into != null && !into(x)) continue;
                var children = Children(x).ToList();
                for (int k = children.Count - 1; k >= 0; k--) stack.Push(children[k]);
            }
        }

        /// <summary>Its immediate parts, as Subterms takes them.</summary>
        public static IEnumerable<KExpr> Children(KExpr e) => e switch
        {
            KLit or KVar => Enumerable.Empty<KExpr>(),
            KOp op => op.Args,
            KQuant q => q.Range == null ? new[] { q.Body } : new[] { q.Range, q.Body },
            KFnApp f => f.Snap == null ? f.Args : f.Args.Append(f.Snap),
            _ => throw NotMath(e),
        };

        /// <summary>Is e mathematics through and through?</summary>
        public static bool IsMath(KExpr e) => e switch
        {
            KLit or KVar => true,
            KOp op => op.Args.All(IsMath),
            KQuant q => (q.Range == null || IsMath(q.Range)) && IsMath(q.Body) && (q.Trigger == null || q.Trigger.All(IsMath)),
            KFnApp f => f.Args.All(IsMath) && (f.Snap == null || IsMath(f.Snap)),
            _ => false,
        };

        public static Exception NotMath(KExpr e) => new InvalidOperationException("not mathematics, where mathematics is: " + e?.GetType().Name);
    }
}
