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
        public static MExpr Map(MExpr e, Func<MExpr, MExpr> at)
        {
            if (at(e) is MExpr given) return given;
            MExpr M(MExpr x) => Map(x, at);
            return e switch
            {
                MLit or MVar => e,
                MOp op => new MOp(op.Op, op.Args.Select(M).ToArray()),
                MQuant q => new MQuant
                {
                    Forall = q.Forall, Var = q.Var, Type = q.Type,
                    Range = q.Range == null ? null : M(q.Range), Body = M(q.Body), Trigger = q.Trigger?.Select(M).ToArray(),
                },
                MFnApp f => new MFnApp
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
        public static IEnumerable<MExpr> Subterms(MExpr e, Func<MExpr, bool> into = null)
        {
            var stack = new Stack<MExpr>();
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
        public static IEnumerable<MExpr> Children(MExpr e) => e switch
        {
            MLit or MVar => Enumerable.Empty<MExpr>(),
            MOp op => op.Args,
            MQuant q => q.Range == null ? new[] { q.Body } : new[] { q.Range, q.Body },
            MFnApp f => f.Snap == null ? f.Args : f.Args.Append(f.Snap),
            _ => throw NotMath(e),
        };

        /// <summary>
        /// A kernel expression that is mathematics through and through (what Lowering makes as such: a check's condition,
        /// a lambda's contract), as level 2's; null where it holds code (an element, a field, a call), which Checks lowers.
        /// </summary>
        public static MExpr ToMath(KExpr e)
        {
            MExpr[] All(KExpr[] es)
            {
                var r = es.Select(ToMath).ToArray();
                return r.Any(x => x == null) ? null : r;
            }
            switch (e)
            {
                case KLit l: return new MLit(l.Text);
                case KVar v: return new MVar(v.Name);
                case KOp op: return All(op.Args) is MExpr[] operands ? new MOp(op.Op, operands) : null;
                case KQuant q:
                {
                    var range = q.Range == null ? null : ToMath(q.Range);
                    var body = ToMath(q.Body);
                    var trigger = q.Trigger == null ? null : All(q.Trigger);
                    if (q.Range != null && range == null || body == null || q.Trigger != null && trigger == null) return null;
                    return new MQuant { Forall = q.Forall, Var = q.Var, Type = q.Type, Range = range, Body = body, Trigger = trigger };
                }
                case KFnApp f:
                {
                    var args = All(f.Args);
                    var snap = f.Snap == null ? null : ToMath(f.Snap);
                    if (args == null || f.Snap != null && snap == null) return null;
                    return new MFnApp { Callee = f.Callee, Function = f.Function, Layer = f.Layer, Fields = f.Fields, Args = args, Snap = snap, Plain = f.Plain, MapsAt = f.MapsAt };
                }
                default: return null;
            }
        }

        /// <summary>A kernel expression Lowering made as mathematics: level 2's (an error where it holds code).</summary>
        public static MExpr Math(KExpr e) => e == null ? null : ToMath(e) ?? throw new InvalidOperationException("code where mathematics is: " + e.GetType().Name);

        public static Exception NotMath(MExpr e) => new InvalidOperationException("not mathematics, where mathematics is: " + e?.GetType().Name);
    }
}
