using System;
using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using static CsVerify.Verifier.Boogie.KernelTypes;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>What Checks needs to know of the rest of the program.</summary>
    internal interface IProgramFacts
    {
        bool CheckOverflow { get; }
        /// <summary>Is a call of b from a recursive (b calls a back, or is a)?</summary>
        bool Recursive(IMethodSymbol a, IMethodSymbol b);
        Contract ContractOf(IMethodSymbol m);
        /// <summary>A callee's requires and measure, lowered over its parameters.</summary>
        KProcedure Signature(IMethodSymbol m);
    }

    /// <summary>
    /// Pass 2: C#'s meaning made mathematics, and each obligation an assert, in the order C# evaluates. In code: an
    /// array's element or length checked not null and in bounds; arithmetic and conversions in their context (an
    /// obligation, the path's end, wrap-around, or mathematics in ghost code); division checked by zero; a call's
    /// non-null arguments, its termination in its recursion group, its precondition (the call's). In specifications:
    /// what makes them well-defined (CSV1012), under the guards of &amp;&amp;, || and ?: and the quantifiers' ranges, as
    /// Dafny's. And where the contract is checked: the requires well-defined at entry; invariants (and each loop's
    /// measure taken) at its head; the measure gone down on each back edge; at each return, the result not null and
    /// each postcondition well-defined and holding. After it, only Heap's array writes and allocations are left.
    /// </summary>
    internal sealed class Checks
    {
        private readonly KProcedure _p;
        private readonly IProgramFacts _facts;
        private List<KStmt> _out;

        private Checks(KProcedure p, IProgramFacts facts) { _p = p; _facts = facts; }

        public static void Run(KProcedure p, IProgramFacts facts) => new Checks(p, facts).Run();

        private Check At(string id, SyntaxNode at, string message, string reportAs = null) =>
            new Check { Id = id, Message = message, Span = at.GetLocation().GetLineSpan(), Method = _p.Result, ReportAs = reportAs };

        private void Emit(KStmt s) => _out.Add(s);

        private void Assert(KExpr cond, Check check, bool notAssumedAfter = false) =>
            Emit(new KAssert { Cond = cond, Check = check, NotAssumedAfter = notAssumedAfter });

        private void Assume(KExpr cond) => Emit(new KAssume { Cond = cond });

        private static KExpr And(IEnumerable<KExpr> xs)
        {
            var list = xs.ToList();
            return list.Count == 0 ? new KLit("true") : list.Aggregate((a, b) => new KOp("&&", a, b));
        }

        private void Run()
        {
            var m = _p.Method;
            // the contract as mathematics (each with what makes it well-defined)
            var requires = _p.Requires.Select(r => (spec: r, math: Spec(r.Expr, out var wf), wf)).ToList();
            var ensures = _p.Ensures.Select(e => (spec: e, math: Spec(e.Expr, out var wf), wf)).ToList();
            foreach (var r in requires)
            {
                r.spec.Expr = r.math;
                r.spec.Check = At(BoogieTranslator.Aux, r.spec.At, $"precondition '{r.spec.At}' of '{m.Name}'", "CSV1001");
            }
            foreach (var e in ensures) e.spec.Expr = e.math;
            var decreases = _p.Decreases?.Select(d => Spec(d, out _)).ToList();
            if (_p.FunctionBody != null) _p.FunctionBody = Spec(_p.FunctionBody, out _);
            var invariants = _p.Invariants.ToDictionary(kv => kv.Key, kv => kv.Value.Select(i => (spec: i, math: Spec(i.Expr, out var wf), wf)).ToList());
            var measures = _p.Measures.ToDictionary(kv => kv.Key, kv => kv.Value.Select(x => Spec(x.Expr, out _)).ToList());

            // at entry: the requires well-defined, in order (each under those before it)
            _out = _p.Entry;
            var before = new List<KExpr>();
            foreach (var r in requires)
            {
                WellDefined(r.wf, r.spec.At, before);
                before.Add(r.math);
            }

            foreach (var b in _p.Blocks)
            {
                var stmts = b.Stmts;
                b.Stmts = _out = new List<KStmt>();
                bool head = b.Label == $"b{b.Ordinal}";
                if (head && invariants.TryGetValue(b.Ordinal, out var invs))
                    foreach (var inv in invs)
                    {
                        WellDefined(inv.wf, inv.spec.At, null);
                        Assert(inv.math, At("CSV1005", inv.spec.At, $"loop invariant '{inv.spec.At}'"));
                    }
                if (head && measures.TryGetValue(b.Ordinal, out var measure))
                    for (int k = 0; k < measure.Count; k++) Emit(new KAssign { Var = $"m${b.Ordinal}${k}", Value = measure[k] });
                foreach (var s in stmts) Statement(s, decreases);
                switch (b.Jump)
                {
                    case KReturn ret:
                        Return(ret, ensures);
                        break;
                    case KGoto g:
                        foreach (var target in g.Targets)
                            if (target.StartsWith("b") && int.TryParse(target.Substring(1), out var to) && to <= b.Ordinal && measures.TryGetValue(to, out var now))
                            {
                                var spec = _p.Measures[to];
                                var then = Enumerable.Range(0, now.Count).Select(k => (KExpr)new KVar($"m${to}${k}")).ToList();
                                // (not assumed after: the loop's invariant is checked on this edge whether or not the measure went down)
                                Assert(Lexicographic(now, then), At("CSV1007", spec[0].At.Parent?.Parent ?? spec[0].At,
                                    $"loop measure '{string.Join(", ", spec.Select(x => x.At))}' might not decrease or might be negative"), true);
                            }
                        break;
                }
            }
            _p.Obligations = _p.Entry.Concat(_p.Blocks.SelectMany(b => b.Stmts)).Count(s => s is KAssert a && a.Check != null || s is KCall)
                             + _p.Contract.Ensures.Count;
        }

        /// <summary>A specification's well-definedness, asserted (CSV1012) where it is evaluated, under what holds before it.</summary>
        private void WellDefined(List<KExpr> wf, SyntaxNode at, List<KExpr> before)
        {
            if (wf.Count == 0) return;
            var cond = And(wf);
            if (before != null && before.Count > 0) cond = new KOp("==>", And(before), cond);
            // (checked, not assumed after: what an ill-defined specification says is unknown, as in CsVerify's engine)
            Assert(cond, At("CSV1012", at, $"specification might not be well-defined: '{at}'"), true);
        }

        /// <summary>A return: the result checked not null, the postconditions well-defined and holding, here.</summary>
        private void Return(KReturn ret, List<(KSpec spec, KExpr math, List<KExpr> wf)> ensures)
        {
            var m = _p.Method;
            if (!m.ReturnsVoid && IsArray(m.ReturnType) && NotNullable(m.ReturnType))
                Assert(new KOp("!=", new KVar("result"), new KLit("null")), At("CSV1014", ret.At, $"'{m.Name}' might return null, but its return type '{m.ReturnType}' is not nullable"));
            var before = new List<KExpr>();
            foreach (var e in ensures)
            {
                WellDefined(e.wf, e.spec.At, before);
                Assert(e.math, At("CSV1002", ret.At, $"postcondition '{e.spec.At}' might not hold on this return path"));
                before.Add(e.math);
            }
        }

        // ------------------------------------------------------------------ statements

        private void Statement(KStmt s, List<KExpr> decreases)
        {
            switch (s)
            {
                case KAssign a:
                    Emit(new KAssign { Var = a.Var, Value = Code(a.Value) });
                    return;
                case KStore st:
                {
                    var value = Code(st.Value);
                    var a = Code(st.Array);
                    var i = Code(st.Index);
                    InBounds(a, i, st.At, st.ArrayAt);
                    Emit(new KStore { Array = a, Index = i, Value = value, ArrayType = st.ArrayType, At = st.At, ArrayAt = st.ArrayAt, Checked = true });
                    return;
                }
                case KNew n:
                    Emit(new KNew { Var = n.Var, ArrayType = n.ArrayType, Size = Code(n.Size), Elements = n.Elements?.Select(Code).ToArray() });
                    return;
                case KCall c:
                    Call(c, decreases);
                    return;
                case KAssume a:
                    Emit(new KAssume { Cond = Code(a.Cond) });
                    return;
                case KSpecStmt ss:
                {
                    var term = Spec(ss.Spec, out var wf);
                    WellDefined(wf, ss.ArgumentAt, null);
                    if (ss.Assume) Assume(term);
                    else Assert(term, At("CSV1004", ss.At, $"assertion '{ss.ArgumentAt}'"));
                    return;
                }
                default:
                    Emit(s);
                    return;
            }
        }

        private void Call(KCall c, List<KExpr> decreases)
        {
            var callee = c.Callee;
            var args = new KExpr[c.Args.Length];
            for (int k = 0; k < args.Length; k++)
            {
                args[k] = Code(c.Args[k]);
                var param = callee.Parameters[k];
                if (IsArray(param.Type) && NotNullable(param.Type))
                    Assert(new KOp("!=", args[k], new KLit("null")), At("CSV1014", c.ArgsAt[k], $"'{c.ArgsAt[k]}' might be null, but parameter '{param.Name}' of '{callee.Name}' is not nullable"));
            }
            Termination(c, args, decreases);
            Emit(new KCall { Callee = callee, Args = args, Result = c.Result, At = c.At, ArgsAt = c.ArgsAt, Check = At("CSV1001", c.At, $"'{c.At}'") });
        }

        /// <summary>
        /// A call back into its own recursion group: the callee's measure, at the arguments, below the caller's,
        /// lexicographically (CSV1008). A [Pure] function or lemma that recurses without one doesn't terminate
        /// (CSV1011); an ordinary method needn't (partial correctness).
        /// </summary>
        private void Termination(KCall c, KExpr[] args, List<KExpr> mine)
        {
            if (!_facts.Recursive(_p.Method, c.Callee)) return;
            var theirs = _facts.ContractOf(c.Callee);
            if (mine != null && theirs?.Decreases != null)
            {
                var sig = _facts.Signature(c.Callee);
                var given = Given(c.Callee, args);
                var next = sig.Decreases.Select(d => Subst(Spec(d, out _), given)).ToList();
                Assert(Lexicographic(next, mine), At("CSV1008", c.At,
                    $"cannot prove termination: measure '{string.Join(", ", theirs.Decreases.Select(d => d.Syntax))}' of '{c.Callee.Name}' might not decrease or might be negative"));
            }
            else if (_p.Contract.IsPure || _p.Contract.IsLemma)
                Assert(new KLit("false"), At("CSV1011", c.At, $"recursive lemma or [Pure] function '{_p.Method.Name}' needs Spec.Decreases"));
        }

        private static Dictionary<string, KExpr> Given(IMethodSymbol callee, KExpr[] args) =>
            callee.Parameters.Select((p, k) => (p, k)).ToDictionary(x => Local(x.p), x => args[x.k]);

        /// <summary>
        /// next below before, lexicographically, each part bounded below by 0 where it goes down (Dafny's rule: the
        /// part before isn't negative, the next is less, which is well-founded; the next may be negative).
        /// </summary>
        private static KExpr Lexicographic(List<KExpr> next, List<KExpr> before)
        {
            int n = Math.Min(next.Count, before.Count);
            KExpr Below(int k)
            {
                var down = new KOp("&&", new KOp("<=", new KLit("0"), before[k]), new KOp("<", next[k], before[k]));
                return k == n - 1 ? down : new KOp("||", down, new KOp("&&", new KOp("==", next[k], before[k]), Below(k + 1)));
            }
            return n == 0 ? new KLit("false") : Below(0);
        }

        // ------------------------------------------------------------------ code

        /// <summary>An expression at run time as mathematics, its checks emitted first, in the order C# evaluates.</summary>
        private KExpr Code(KExpr e)
        {
            switch (e)
            {
                case null: return null;
                case KLit _: case KVar _: return e;
                case KOp op: return new KOp(op.Op, op.Args.Select(Code).ToArray());
                case KElem el:
                {
                    var a = Code(el.Array);
                    var i = Code(el.Index);
                    InBounds(a, i, el.At, el.ArrayAt);
                    return new KOp("sel", new KVar(Elements(el.ArrayType)), a, i);
                }
                case KLen len:
                {
                    var a = Code(len.Array);
                    Assert(new KOp("!=", a, new KLit("null")), At("CSV1013", len.At, $"'{len.ArrayAt}' might be null in '{len.At}'"));
                    return new KOp("len", a);
                }
                case KArith ar: return Arith(ar, Code(ar.Left), Code(ar.Right));
                case KConv cv: return Convert(cv, Code(cv.Value));
                default: throw new NotTranslated("in code: " + e.GetType().Name);
            }
        }

        private void InBounds(KExpr a, KExpr i, SyntaxNode at, SyntaxNode arrayAt)
        {
            Assert(new KOp("!=", a, new KLit("null")), At("CSV1013", at, $"'{arrayAt}' might be null in '{at}'"));
            Assert(new KOp("&&", new KOp("<=", new KLit("0"), i), new KOp("<", i, new KOp("len", a))), At("CSV1003", at, $"index in '{at}' might be out of range"));
        }

        /// <summary>
        /// Integer arithmetic at run time: division by zero is an obligation; overflow is one in the default context,
        /// ends the path in a checked one (it throws), as MinValue / -1 does anywhere, and wraps around in an
        /// unchecked one (two's complement); ghost code's is mathematics.
        /// </summary>
        private KExpr Arith(KArith ar, KExpr l, KExpr r)
        {
            if (ar.Op == "/" || ar.Op == "%")
            {
                Assert(new KOp("!=", r, new KLit("0")), At("CSV1009", ar.At, $"division by zero in '{ar.At}'"));
                // (MinValue / -1 throws in .NET, checked or not)
                Assume(new KOp("!", new KOp("&&", new KOp("==", l, Number(Range(ar.Type).lo)), new KOp("==", r, new KLit("(-1)")))));
                return new KOp(ar.Op == "/" ? "div" : "rem", l, r);
            }
            var value = new KOp(ar.Op, l, r);
            return Fit(value, ar.Type, ar.Mode, ar.At, $"arithmetic '{ar.At}' might overflow {ar.Type.Name}");
        }

        /// <summary>An explicit conversion between integer types: as arithmetic where it narrows; a widening one is the value.</summary>
        private KExpr Convert(KConv cv, KExpr value)
        {
            var (lo, hi) = Range(cv.To);
            var (flo, fhi) = Range(cv.From);
            if (flo >= lo && fhi <= hi) return value;
            return Fit(value, cv.To, cv.Mode, cv.At, $"conversion '{cv.At}' might overflow {cv.To.Name}");
        }

        private KExpr Fit(KExpr value, ITypeSymbol type, KMode mode, SyntaxNode at, string message)
        {
            switch (mode)
            {
                case KMode.Unchecked: return Wrap(value, type);
                case KMode.Math: return value;
                case KMode.Default when _facts.CheckOverflow:
                    Assert(InRange(value, type), At("CSV1010", at, message));
                    return value;
                default:
                    Assume(InRange(value, type));
                    return value;
            }
        }

        // ------------------------------------------------------------------ specifications

        /// <summary>A specification as mathematics, and what makes it well-defined (each a condition, in order).</summary>
        private KExpr Spec(KExpr e, out List<KExpr> wf)
        {
            wf = new List<KExpr>();
            return Spec(e, wf, new List<KExpr>());
        }

        /// <summary>
        /// e as a formula; what makes it well-defined is added to <paramref name="wf"/>, under <paramref name="guard"/>
        /// (what &amp;&amp; || ?: make hold where it is evaluated, and the bounds of the quantifiers around it).
        /// </summary>
        private KExpr Spec(KExpr e, List<KExpr> wf, List<KExpr> guard)
        {
            void Need(KExpr cond) => wf.Add(guard.Count == 0 ? cond : new KOp("==>", And(guard), cond));
            KExpr Under(KExpr g, KExpr x)
            {
                guard.Add(g);
                try { return Spec(x, wf, guard); }
                finally { guard.RemoveAt(guard.Count - 1); }
            }
            switch (e)
            {
                case KLit _: case KVar _: case KFnApp _: return e;
                case KOp { Op: "ite" } ite:
                {
                    var c = Spec(ite.Args[0], wf, guard);
                    return new KOp("ite", c, Under(c, ite.Args[1]), Under(new KOp("!", c), ite.Args[2]));
                }
                case KOp { Op: "&&" } and:
                {
                    // (the right only where the left lets it be evaluated)
                    var l = Spec(and.Args[0], wf, guard);
                    return new KOp("&&", l, Under(l, and.Args[1]));
                }
                case KOp { Op: "||" } or:
                {
                    var l = Spec(or.Args[0], wf, guard);
                    return new KOp("||", l, Under(new KOp("!", l), or.Args[1]));
                }
                case KOp op:
                {
                    var args = op.Args.Select(a => Spec(a, wf, guard)).ToArray();
                    // (& and | of bools: both sides evaluated)
                    return new KOp(op.Op == "&" ? "&&" : op.Op == "|" ? "||" : op.Op, args);
                }
                case KArith ar: // (/ and %: the rest is mathematics already)
                {
                    var l = Spec(ar.Left, wf, guard);
                    var r = Spec(ar.Right, wf, guard);
                    Need(new KOp("!=", r, new KLit("0")));
                    return new KOp(ar.Op == "/" ? "div" : "rem", l, r);
                }
                case KElem el:
                {
                    var a = Spec(el.Array, wf, guard);
                    var i = Spec(el.Index, wf, guard);
                    Need(new KOp("&&", new KOp("&&", new KOp("!=", a, new KLit("null")), new KOp("<=", new KLit("0"), i)), new KOp("<", i, new KOp("len", a))));
                    return new KOp("sel", new KVar(Elements(el.ArrayType)), a, i);
                }
                case KLen len:
                {
                    var a = Spec(len.Array, wf, guard);
                    Need(new KOp("!=", a, new KLit("null")));
                    return new KOp("len", a);
                }
                case KQuant q:
                {
                    // (Range is lo <= q && q < hi, from Lowering)
                    var lo = Spec(((KOp)((KOp)q.Range).Args[0]).Args[0], wf, guard);
                    var hi = Spec(((KOp)((KOp)q.Range).Args[1]).Args[1], wf, guard);
                    var range = new KOp("&&", new KOp("<=", lo, new KVar(q.Var)), new KOp("<", new KVar(q.Var), hi));
                    // (its body well-defined over the range: each condition quantified the same way)
                    var inner = new List<KExpr>();
                    var body = Spec(q.Body, inner, new List<KExpr> { range });
                    foreach (var c in inner) Need(new KQuant { Forall = true, Var = q.Var, Range = null, Body = c });
                    return new KQuant { Forall = q.Forall, Var = q.Var, Range = range, Body = body };
                }
                case KFnCall fn:
                {
                    var args = fn.Args.Select(a => Spec(a, wf, guard)).ToArray();
                    // (well-defined where its precondition holds, at the arguments)
                    var given = Given(fn.Callee, args);
                    foreach (var r in _facts.Signature(fn.Callee).Requires) Need(Subst(Spec(r.Expr, out _), given));
                    return new KFnApp { Function = FunctionName(fn.Callee), Args = args };
                }
                default: throw new NotTranslated("in a specification: " + e.GetType().Name);
            }
        }

        /// <summary>Parameters given values (mathematics in, mathematics out).</summary>
        private static KExpr Subst(KExpr e, Dictionary<string, KExpr> given) => e switch
        {
            KVar v when given.TryGetValue(v.Name, out var x) => x,
            KOp op => new KOp(op.Op, op.Args.Select(a => Subst(a, given)).ToArray()),
            KQuant q => new KQuant { Forall = q.Forall, Var = q.Var, Range = q.Range == null ? null : Subst(q.Range, given), Body = Subst(q.Body, given) },
            KFnApp f => new KFnApp { Function = f.Function, Layer = f.Layer, Args = f.Args.Select(a => Subst(a, given)).ToArray() },
            _ => e,
        };
    }
}
