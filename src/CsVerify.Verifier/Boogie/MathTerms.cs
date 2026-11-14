using System;
using System.Collections.Generic;
using System.Linq;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>
    /// The traversal of level 2's mathematics (MLit, MVar, MOp, MQuant, MFnApp), in one place: Rewrite rewrites, Subterms
    /// queries, and the queries made of them. Any other kind, met here, is an error: no walk skips one it doesn't know.
    /// </summary>
    internal abstract partial class MExpr
    {
        /// <summary>
        /// This rewritten: a node for which <paramref name="at"/> gives an expression is replaced by it; any other is rebuilt
        /// of its rewritten parts (a new node, but a literal or variable, which is kept). A quantifier's triggers are
        /// rewritten too; a function application keeps all but its arguments and snapshot.
        /// </summary>
        public MExpr Rewrite(Func<MExpr, MExpr> at)
        {
            if (at(this) is MExpr given)
            {
                return given;
            }
            return this switch
            {
                MLit or MVar => this,
                MOp op => new MOp(op.Op, op.Args.Select(x => x.Rewrite(at)).ToArray()),
                MQuant q => q.WithParts(q.Range?.Rewrite(at), q.Body.Rewrite(at), q.Trigger?.Select(x => x.Rewrite(at)).ToArray()),
                MFnApp f => f.WithArgs(f.Args.Select(x => x.Rewrite(at)).ToArray(), f.Snap?.Rewrite(at)),
                _ => throw MathTerms.NotMath(this),
            };
        }

        /// <summary>
        /// This and every expression in it, outermost first; below a node <paramref name="into"/> refuses, nothing (it is
        /// still given). A quantifier's triggers are left out: hints to the solver, not part of what it says.
        /// </summary>
        public IEnumerable<MExpr> Subterms(Func<MExpr, bool> into = null)
        {
            var stack = new Stack<MExpr>();
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
        public IEnumerable<MExpr> Children() => this switch
        {
            MLit or MVar => Enumerable.Empty<MExpr>(),
            MOp op => op.Args,
            MQuant q => q.Range == null ? new[] { q.Body } : new[] { q.Range, q.Body },
            MFnApp f => f.Snap == null ? f.Args : f.Args.Append(f.Snap),
            _ => throw MathTerms.NotMath(this),
        };

        public bool IsTrue => this is MLit { Text: "true" };

        /// <summary>Its conjuncts: the operands of its &&s, left to right (itself, if it isn't one).</summary>
        public IEnumerable<MExpr> Conjuncts() => this is MOp { Op: "&&" } and ? and.Args.SelectMany(a => a.Conjuncts()) : new[] { this };

        /// <summary>Does it mention any of these variables?</summary>
        public bool Mentions(HashSet<string> vars) => Subterms().Any(x => x is MVar v && vars.Contains(v.Name));

        /// <summary>Variables given values (mathematics in, mathematics out).</summary>
        public MExpr Substitute(Dictionary<string, MExpr> given) => Rewrite(x => x is MVar v && given.TryGetValue(v.Name, out var value) ? value : null);

        /// <summary>A variable given a value.</summary>
        public MExpr Substitute(string name, MExpr value) => Substitute(new Dictionary<string, MExpr> { [name] = value });

        /// <summary>Its function applications, outermost first, through its operators (not into a quantifier or a snapshot).</summary>
        public IEnumerable<MFnApp> Applications() => this switch
        {
            MFnApp f => new[] { f }.Concat(f.Args.SelectMany(a => a.Applications())),
            MOp op => op.Args.SelectMany(a => a.Applications()),
            // (not into a nested quantifier: its applications are of its own variable, unfolded there)
            _ => Enumerable.Empty<MFnApp>(),
        };
    }

    /// <summary>Level 1's mathematics as level 2's.</summary>
    internal static class MathTerms
    {
        /// <summary>
        /// A kernel expression that is mathematics through and through (what Lowering makes as such: a check's condition,
        /// a lambda's contract), as level 2's; null where it holds code (an element, a field, a call), which Checks lowers.
        /// </summary>
        public static MExpr ToMath(KExpr e)
        {
            switch (e)
            {
                case KLit l: return new MLit(l.Text);
                case KVar v: return new MVar(v.Name);
                case KOp op: return AllToMath(op.Args) is MExpr[] operands ? new MOp(op.Op, operands) : null;
                case KQuant q:
                {
                    var range = q.Range == null ? null : ToMath(q.Range);
                    var body = ToMath(q.Body);
                    var trigger = q.Trigger == null ? null : AllToMath(q.Trigger);
                    if (q.Range != null && range == null || body == null || q.Trigger != null && trigger == null)
                    {
                        return null;
                    }
                    return MQuant.Of(q, range, body, trigger);
                }
                case KFnApp f:
                {
                    var args = AllToMath(f.Args);
                    var snap = f.Snap == null ? null : ToMath(f.Snap);
                    if (args == null || f.Snap != null && snap == null)
                    {
                        return null;
                    }
                    return MFnApp.Of(f, args, snap);
                }
                default: return null;
            }
        }

        private static MExpr[] AllToMath(KExpr[] es)
        {
            var r = es.Select(ToMath).ToArray();
            return r.Any(x => x == null) ? null : r;
        }

        /// <summary>A kernel expression Lowering made as mathematics: level 2's (an error where it holds code).</summary>
        public static MExpr Math(KExpr e) => e == null ? null : ToMath(e) ?? throw new InvalidOperationException("code where mathematics is: " + e.GetType().Name);

        public static Exception NotMath(MExpr e) => new InvalidOperationException("not mathematics, where mathematics is: " + e?.GetType().Name);
    }
}
