using System;
using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using static CsVerify.Verifier.Boogie.KernelTypes;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>Permissions: inhale and exhale of permission assertions, fold and unfold of predicates, field permissions, write frames.</summary>
    internal sealed partial class Checks
    {
        // ------------------------------------------------------------------ permissions (Viper's, over perm, pinst and owner)

        private List<KExpr> _rawRequires = new List<KExpr>(), _rawEnsures = new List<KExpr>();
        private Dictionary<int, List<(KExpr expr, SyntaxNode at)>> _rawInvariants = new Dictionary<int, List<(KExpr, SyntaxNode)>>();
        /// <summary>Reading a permission as a condition (Spec.Assert, Spec.Assume): in hand. Elsewhere it is given or got, and reads as true.</summary>
        private bool _held;
        private int _frames;
        /// <summary>What old(...) means where a permission assertion is read: at a return, the entry; after a call, before it.</summary>
        private Func<KExpr, KExpr> _old;

        internal static KExpr Instance(IMethodSymbol pred, KExpr[] args) =>
            new KOp("inst", new[] { (KExpr)new KLit(InstanceName(pred)) }.Concat(args).ToArray());

        public static string InstanceName(IMethodSymbol pred) => "i$" + Name(pred);

        private static readonly KExpr None = new KLit("i#none");

        private static KExpr Ite(KExpr c, KExpr a, KExpr b) => new KOp("ite", c, a, b);
        private static KExpr Implies(KExpr g, KExpr c) => g is KLit { Text: "true" } ? c : new KOp("==>", g, c);
        private static KExpr Conj(KExpr a, KExpr b) => a is KLit { Text: "true" } ? b : b is KLit { Text: "true" } ? a : new KOp("&&", a, b);

        private static bool HasAtoms(KExpr e) => Atoms(e).Any();

        /// <summary>
        /// Walks a permission assertion left to right: &amp;&amp; and the branches of ?: are
        /// followed, each permission goes to <paramref name="atom"/> under the condition it holds in, every other part
        /// is a fact. Its parameters given values by <paramref name="given"/>. Returns its facts, as a condition.
        /// </summary>
        private KExpr Walk(KExpr e, Dictionary<string, KExpr> given, KExpr guard, Action<KExpr, KExpr> atom, Action<KExpr, KExpr> fact)
        {
            KExpr M(KExpr x)
            {
                var v = Spec(x, out _);
                // (what holds of the memory wherever it's read: a field's reference allocated, a non-nullable field set; assumed)
                var known = _facts.ToList();
                _facts.Clear();
                KExpr At(KExpr y) { y = given == null ? y : Subst(y, given); return _old == null ? y : _old(y); }
                foreach (var k in known) Assume(Implies(guard, At(k)));
                return At(v);
            }
            switch (e)
            {
                case KOp { Op: "&&" } and:
                {
                    var l = Walk(and.Args[0], given, guard, atom, fact);
                    var r = Walk(and.Args[1], given, Conj(guard, l), atom, fact);
                    return Conj(l, r);
                }
                case KOp { Op: "ite" } ite when HasAtoms(ite.Args[1]) || HasAtoms(ite.Args[2]):
                {
                    var c = M(ite.Args[0]);
                    var t = Walk(ite.Args[1], given, Conj(guard, c), atom, fact);
                    var f = Walk(ite.Args[2], given, Conj(guard, new KOp("!", c)), atom, fact);
                    return Ite(c, t, f);
                }
                case KAcc acc:
                    atom(guard, new KAcc { Obj = M(acc.Obj), Type = acc.Type, At = acc.At });
                    return new KLit("true");
                case KInst inst:
                    atom(guard, new KInst { Pred = inst.Pred, Args = inst.Args.Select(M).ToArray(), At = inst.At });
                    return new KLit("true");
                case KCells cl:
                    atom(guard, new KCells { Arr = M(cl.Arr), Lo = M(cl.Lo), Hi = M(cl.Hi), Read = cl.Read, At = cl.At });
                    return new KLit("true");
                case KFieldAcc fa:
                    atom(guard, new KFieldAcc { Obj = M(fa.Obj), Field = fa.Field, Type = fa.Type, At = fa.At });
                    return new KLit("true");
                case KLit { Text: "true" }: return e;
            }
            if (HasAtoms(e)) throw new NotTranslated("a permission that isn't a conjunct, or in a branch of ?:");
            var v = M(e);
            fact?.Invoke(guard, v);
            return v;
        }

        private void SetPerm(KExpr o, KExpr value) => Emit(new KAssign { Var = "perm", Value = new KOp("store", new KVar("perm"), o, value) });

        private void AddInst(KExpr q, KExpr guard, int by) =>
            Emit(new KAssign { Var = "pinst", Value = new KOp("store", new KVar("pinst"), q,
                new KOp(by > 0 ? "+" : "-", new KOp("sel", new KVar("pinst"), q), Ite(guard, new KLit("1"), new KLit("0")))) });

        /// <summary>Receives an assertion's permissions (a precondition at entry, a postcondition after a call, an invariant at a loop head).</summary>
        private bool _atLoopHead;

        private void Inhale(KExpr e, Dictionary<string, KExpr> given, KExpr _)
        {
            if (!HasAtoms(e)) return;
            Walk(e, given, new KLit("true"), (g, a) =>
            {
                if (a is KCells cl) { if (_p.UsesCells) InhaleCells(g, cl); return; }
                if (a is KFieldAcc fa) { TakeField(fa, g); return; }
                if (a is KAcc acc)
                {
                    // two whole permissions to one object can't both be in hand, and one in hand is folded nowhere
                    Assume(Implies(g, new KOp("&&", new KOp("&&", new KOp("!=", acc.Obj, new KLit("null")), new KOp("!", Held(acc.Obj))),
                                                  new KOp("==", new KOp("sel", new KVar("owner"), acc.Obj), None))));
                    NoFieldsHeld(g, acc.Obj, acc.Type);
                    SetPerm(acc.Obj, new KOp("||", Held(acc.Obj), g));
                    if (Invariant(acc.Type, acc.Obj) is KExpr inv) Assume(Implies(g, inv));
                }
                else
                {
                    var inst = (KInst)a;
                    // (the guard as it is before the snapshot changes: it may read it)
                    var held = Hold(g);
                    if (!_atLoopHead) Refresh(Instance(inst.Pred, inst.Args), held);
                    SnapFacts(inst.Pred, inst.Args, held);
                    // (one that holds an object's Spec.Acc can't be held twice: the object's permission is one)
                    if (PredicateExclusive(inst.Pred)) Assume(Implies(g, new KOp("==", new KOp("sel", new KVar("pinst"), Instance(inst.Pred, inst.Args)), new KLit("0"))));
                    AddInst(Instance(inst.Pred, inst.Args), g, +1);
                }
            }, null);
        }

        /// <summary>Gives an assertion's permissions up (a callee's precondition at a call, a postcondition at a return, an invariant on the way into a loop's head): each must be in hand.</summary>
        private void Exhale(KExpr e, Dictionary<string, KExpr> given, SyntaxNode at, List<(KExpr, KExpr)> gave)
        {
            if (!HasAtoms(e)) return;
            Walk(e, given, new KLit("true"), (g, a) =>
            {
                gave?.Add((g, a));
                if (a is KCells cl) { if (_p.UsesCells) ExhaleCells(g, cl, at, $"'{cl.At}' is needed here, but those cells are not all in hand"); return; }
                if (a is KFieldAcc fa) { GiveField(fa, g, at, $"'{fa.At}' is needed here, but that permission is not in hand"); return; }
                if (a is KAcc acc)
                {
                    Assert(Implies(g, Held(acc.Obj)), At("CSV1016", at, $"'{acc.At}' is needed here, but that permission is not in hand"));
                    if (Invariant(acc.Type, acc.Obj) is KExpr inv)
                        Assert(Implies(g, inv), At("CSV1015", at, $"invariant of {acc.Type.Name} might not hold when '{acc.At}' is given up"));
                    SetPerm(acc.Obj, new KOp("&&", Held(acc.Obj), new KOp("!", g)));
                }
                else
                {
                    var inst = (KInst)a;
                    var q = Instance(inst.Pred, inst.Args);
                    Assert(Implies(g, new KOp(">=", new KOp("sel", new KVar("pinst"), q), new KLit("1"))), At("CSV1016", at, $"'{inst.At}' is needed here, but it is not held"));
                    AddInst(q, g, -1);
                }
            }, null);
        }

        /// <summary>
        /// Spec.Fold(P(args)): the body's permissions go into the instance (each in hand), its facts hold (CSV1019), its
        /// objects' invariants too; their owner is the instance now, and so is that of what the instances in it own.
        /// Spec.Unfold: the instance (held) gives them back, and its facts hold; the footprint splits among the instances in it.
        /// </summary>
        private void Fold(KFold fold)
        {
            var sig = _program.Signature(fold.Inst.Pred);
            if (sig.FunctionBody == null) throw new NotTranslated("a predicate without a body");
            var args = fold.Inst.Args.Select(a => { var v = Spec(a, out _); _facts.Clear(); return v; }).ToArray();
            var given = fold.Inst.Pred.Parameters.Select((x, k) => (x, k)).ToDictionary(x => Local(x.x), x => args[x.k]);
            var p = Instance(fold.Inst.Pred, args);
            var at = fold.At;
            if (!fold.Unfold)
            {
                Walk(sig.FunctionBody, given, new KLit("true"), (g, a) =>
                {
                    if (a is KFieldAcc fa)
                    {
                        GiveField(fa, g, at, $"folding needs '{fa.At}', but that permission is not in hand here");
                        var k = new KLit(_program.FieldId(fa.Field).ToString());
                        Emit(new KAssign { Var = "fowner", Value = new KOp("store", new KVar("fowner"), fa.Obj,
                            new KOp("store", new KOp("sel", new KVar("fowner"), fa.Obj), k, Ite(g, p, new KOp("sel", new KVar("fowner"), fa.Obj, k)))) });
                        return;
                    }
                    if (a is KCells cl)
                    {
                        if (!_p.UsesCells) return;
                        ExhaleCells(g, cl, at, $"'{cl.At}' is needed here, but those cells are not all in hand");
                        Emit(new KAssign { Var = "cowner", Value = new KOp("lambda", new KLit("x$: Ref"), new KOp("lambda", new KLit("i$: int"),
                            Ite(InCells(g, cl, new KVar("x$"), new KVar("i$")), p, new KOp("sel", new KVar("cowner"), new KVar("x$"), new KVar("i$"))))) });
                        return;
                    }
                    if (a is KAcc acc)
                    {
                        Assert(Implies(g, Held(acc.Obj)), At("CSV1016", at, $"folding needs '{acc.At}', but that permission is not in hand here"));
                        if (Invariant(acc.Type, acc.Obj) is KExpr inv)
                            Assert(Implies(g, inv), At("CSV1015", at, $"invariant of {acc.Type.Name} might not hold when it is folded into '{fold.InstAt}'"));
                        SetPerm(acc.Obj, new KOp("&&", Held(acc.Obj), new KOp("!", g)));
                        Emit(new KAssign { Var = "owner", Value = new KOp("store", new KVar("owner"), acc.Obj, Ite(g, p, new KOp("sel", new KVar("owner"), acc.Obj))) });
                    }
                    else
                    {
                        var inst = (KInst)a;
                        var q = Instance(inst.Pred, inst.Args);
                        Assert(Implies(g, new KOp(">=", new KOp("sel", new KVar("pinst"), q), new KLit("1"))), At("CSV1016", at, $"folding needs '{inst.At}', which is not held here"));
                        AddInst(q, g, -1);
                        var y = new KVar("y$");
                        Emit(new KAssign { Var = "owner", Value = new KOp("lambda", new KLit("y$: Ref"),
                            Ite(Conj(g, new KOp("==", new KOp("sel", new KVar("owner"), y), q)), p, new KOp("sel", new KVar("owner"), y))) });
                    }
                }, (g, fact) => Assert(Implies(g, fact), At("CSV1019", at, $"'{fold.InstAt}' might not hold when folding it: its body's facts")));
                // (folded now: a snapshot of its own, of which the functions over it are what their bodies say now)
                Refresh(p, new KLit("true"));
                SnapFacts(fold.Inst.Pred, args, new KLit("true"));
                AddInst(p, new KLit("true"), +1);
                Define(fold.Inst.Pred, args, p);
                return;
            }
            Assert(new KOp(">=", new KOp("sel", new KVar("pinst"), p), new KLit("1")), At("CSV1016", at, $"'{fold.InstAt}' is not held here"));
            AddInst(p, new KLit("true"), -1);
            foreach (var (name, raw) in new[] { ("footprint$", "[Ref]Inst"), ("choice$", "[Ref]int") })
                if (!_p.Locals.Any(l => l.Name == name)) _p.Locals.Add(new KLocal { Name = name, Raw = raw });
            Emit(new KAssign { Var = "footprint$", Value = new KVar("owner") });
            var own = new List<(KExpr g, KExpr o)>();
            var nested = new List<(KExpr g, KExpr q)>();
            var ownCells = new List<(KExpr g, KCells c)>();
            if (_p.UsesCells)
            {
                Emit(new KAssign { Var = "cfootprint$", Value = new KVar("cowner") });
                foreach (var (name, raw) in new[] { ("cfootprint$", "[Ref][int]Inst"), ("cchoice$", "[Ref][int]int") })
                    if (!_p.Locals.Any(l => l.Name == name)) _p.Locals.Add(new KLocal { Name = name, Raw = raw });
            }
            Walk(sig.FunctionBody, given, new KLit("true"), (g, a) =>
            {
                if (a is KCells cl) { if (_p.UsesCells) InhaleCells(g, cl); ownCells.Add((g, cl)); return; }
                if (a is KFieldAcc fa)
                {
                    Assume(Implies(g, new KOp("==", new KOp("sel", new KVar("fowner"), fa.Obj, new KLit(_program.FieldId(fa.Field).ToString())), p)));
                    TakeField(fa, g);
                    // (folded nowhere now: the body's own)
                    Emit(new KAssign { Var = "fowner", Value = new KOp("store", new KVar("fowner"), fa.Obj,
                        new KOp("store", new KOp("sel", new KVar("fowner"), fa.Obj), new KLit(_program.FieldId(fa.Field).ToString()), Ite(g, None, new KOp("sel", new KVar("fowner"), fa.Obj, new KLit(_program.FieldId(fa.Field).ToString()))))) });
                    return;
                }
                if (a is KAcc acc)
                {
                    Assume(Implies(g, new KOp("&&", new KOp("&&", new KOp("!=", acc.Obj, new KLit("null")), new KOp("==", new KOp("sel", new KVar("footprint$"), acc.Obj), p)), new KOp("!", Held(acc.Obj)))));
                    SetPerm(acc.Obj, new KOp("||", Held(acc.Obj), g));
                    if (Invariant(acc.Type, acc.Obj) is KExpr inv) Assume(Implies(g, inv));
                    own.Add((g, acc.Obj));
                }
                else
                {
                    var inst = (KInst)a;
                    var q = Instance(inst.Pred, inst.Args);
                    var held = Hold(g);
                    Refresh(q, held);
                    SnapFacts(inst.Pred, inst.Args, held);
                    if (PredicateExclusive(inst.Pred)) Assume(Implies(g, new KOp("==", new KOp("sel", new KVar("pinst"), q), new KLit("0"))));
                    AddInst(q, g, +1);
                    nested.Add((g, q));
                }
            }, (g, fact) => Assume(Implies(g, fact)));
            // (what was folded hasn't changed: the functions over it are what their bodies say of it now)
            Define(fold.Inst.Pred, args, p);
            // the footprint splits: the body's own objects are free now, the rest belongs to one of its instances
            var yv = new KVar("y$");
            KExpr Footprint(KExpr y) => new KOp("sel", new KVar("footprint$"), y);
            if (nested.Count > 1) Emit(new KHavoc { Var = "choice$" });
            KExpr to = None;
            for (int k = nested.Count - 1; k >= 0; k--)
            {
                var pick = nested.Count > 1 ? Conj(nested[k].g, new KOp("==", new KOp("sel", new KVar("choice$"), yv), new KLit(k.ToString()))) : nested[k].g;
                to = Ite(pick, nested[k].q, to);
            }
            foreach (var (g, o) in own) to = Ite(Conj(g, new KOp("==", yv, o)), None, to);
            KExpr elsewhere = Footprint(yv);
            if (nested.Count > 0)
                elsewhere = Ite(nested.Select(n => (KExpr)new KOp("==", Footprint(yv), n.q)).Aggregate((a, b) => new KOp("||", a, b)), None, Footprint(yv));
            Emit(new KAssign { Var = "owner", Value = new KOp("lambda", new KLit("y$: Ref"), Ite(new KOp("==", Footprint(yv), p), to, elsewhere)) });
            // cells likewise: the body's own are free, the rest go to its instances
            if (!_p.UsesCells) return;
            var (xv, iv) = (new KVar("x$"), new KVar("i$"));
            KExpr CFoot() => new KOp("sel", new KVar("cfootprint$"), xv, iv);
            if (nested.Count > 1) Emit(new KHavoc { Var = "cchoice$" });
            KExpr cto = None;
            for (int k = nested.Count - 1; k >= 0; k--)
            {
                var pick = nested.Count > 1 ? Conj(nested[k].g, new KOp("==", new KOp("sel", new KVar("cchoice$"), xv, iv), new KLit(k.ToString()))) : nested[k].g;
                cto = Ite(pick, nested[k].q, cto);
            }
            foreach (var (g, c) in ownCells) cto = Ite(InCells(g, c, xv, iv), None, cto);
            KExpr celsewhere = CFoot();
            if (nested.Count > 0)
                celsewhere = Ite(nested.Select(n => (KExpr)new KOp("==", CFoot(), n.q)).Aggregate((a, b) => new KOp("||", a, b)), None, CFoot());
            Emit(new KAssign { Var = "cowner", Value = new KOp("lambda", new KLit("x$: Ref"), new KOp("lambda", new KLit("i$: int"), Ite(new KOp("==", CFoot(), p), cto, celsewhere))) });
        }

        // ------------------------------------------------------------------ functions under quantifiers

        private int _unfolding;

        /// <summary>
        /// A function's application under a quantifier, of its variable: its definition, unfolded once, for every value
        /// in its range. That quantified equation applies again to the applications in
        /// its body, so recursion over the range unfolds as far as it needs to (a concrete array's sum).
        /// </summary>
        private void Unfoldings(string var, KExpr range, KExpr body)
        {
            if (_unfolding > 0) return;
            _unfolding++;
            try
            {
                foreach (var app in Apps(body).Where(a => a.Snap == null && !a.Plain && a.Layer == null && a.Args.Any(x => Mentions(x, new HashSet<string> { var })) &&
                                                         !a.Args.Any(x => Mentions(x, _bound))).ToList())
                {
                    var sig = _program.Signature(app.Callee);
                    if (sig.FunctionBody == null || !app.Callee.IsStatic) continue;
                    var given = app.Callee.Parameters.Select((x, k) => (x, k)).ToDictionary(x => Local(x.x), x => app.Args[x.k]);
                    KExpr M(KExpr x) { var v = Spec(x, out _); _facts.Clear(); return Subst(v, given); }
                    // (the facts so far kept: the definition's own are left out)
                    var saved = _facts.ToList();
                    var pre = sig.Requires.Select(r => M(r.Expr)).Aggregate((KExpr)new KLit("true"), Conj);
                    var definition = new KOp("==", app, M(sig.FunctionBody));
                    _facts.Clear();
                    _facts.AddRange(saved);
                    _facts.Add(new KQuant { Forall = true, Var = var, Range = null, Body = Implies(Conj(range, pre), definition) });
                }
            }
            finally { _unfolding--; }
        }

        private static IEnumerable<KFnApp> Apps(KExpr e) => e switch
        {
            KFnApp f => new[] { f }.Concat(f.Args.SelectMany(Apps)),
            KOp op => op.Args.SelectMany(Apps),
            // (not into a nested quantifier: its applications are of its own variable, unfolded there)
            _ => Enumerable.Empty<KFnApp>(),
        };

        // ------------------------------------------------------------------ frames (Dafny's Spec.Modifies)

        /// <summary>A write of an (unowned) object's field or an array's cell: within Spec.Modifies as of entry, or allocated since (CSV1017).</summary>
        private void WithinFrame(KExpr o, SyntaxNode at)
        {
            if (_p.Frame == null) return;
            Assert(new KOp("||", new KOp("sel", new KVar("w$entry"), o), new KOp("!", new KOp("sel", new KVar("alloc$entry"), o))),
                At("CSV1017", at, $"'{at}' writes an object that is not in Spec.Modifies and was not allocated here"));
        }

        private int _holds;

        /// <summary>A condition's value now, in a local of its own (true stays true).</summary>
        private KExpr Hold(KExpr g)
        {
            if (g is KLit { Text: "true" }) return g;
            var name = "g$h" + _holds++;
            _p.Locals.Add(new KLocal { Name = name, Raw = "bool" });
            Emit(new KAssign { Var = name, Value = g });
            return new KVar(name);
        }

        private void Refresh(KExpr q, KExpr g)
        {
            g = Conj(g, new KOp("==", new KOp("sel", new KVar("pinst"), q), new KLit("0")));
            if (!_p.Locals.Any(l => l.Name == "snap$")) _p.Locals.Add(new KLocal { Name = "snap$", Raw = "int" });
            Emit(new KHavoc { Var = "snap$" });
            Emit(new KAssign { Var = "psnap", Value = new KOp("store", new KVar("psnap"), q, Ite(g, new KVar("snap$"), new KOp("sel", new KVar("psnap"), q))) });
        }

        // ------------------------------------------------------------------ single fields (Viper's acc(o.f))

        private KExpr FieldHeld(KExpr o, ISymbol field) => new KOp("sel", new KVar("fperm"), o, new KLit(_program.FieldId(field).ToString()));

        /// <summary>Write permission to o.F: the whole object, or that field.</summary>
        private KExpr CanWrite(KExpr o, ISymbol field) => _p.UsesFields ? new KOp("||", Held(o), FieldHeld(o, field)) : Held(o);

        private void SetField(KExpr o, ISymbol field, KExpr value) =>
            Emit(new KAssign { Var = "fperm", Value = new KOp("store", new KVar("fperm"), o,
                new KOp("store", new KOp("sel", new KVar("fperm"), o), new KLit(_program.FieldId(field).ToString()), value)) });

        /// <summary>A whole object received is nobody else's, field by field either.</summary>
        private void NoFieldsHeld(KExpr g, KExpr o, ITypeSymbol type)
        {
            if (!_p.UsesFields) return;
            foreach (var f in WholeFields(type)) Assume(Implies(g, new KOp("!", FieldHeld(o, f))));
        }

        /// <summary>Gives o.F up: from its own permission, or split off the whole object (whose other fields stay, one by one).</summary>
        private void GiveField(KFieldAcc fa, KExpr g, SyntaxNode at, string message)
        {
            if (!_p.UsesFields) return;
            Assert(Implies(g, CanWrite(fa.Obj, fa.Field)), At("CSV1016", at, message));
            Emit(new KAssign { Var = "own$", Value = FieldHeld(fa.Obj, fa.Field) });
            if (!_p.Locals.Any(l => l.Name == "own$")) _p.Locals.Add(new KLocal { Name = "own$", Raw = "bool" });
            var split = Conj(g, new KOp("!", new KVar("own$")));
            SetPerm(fa.Obj, new KOp("&&", Held(fa.Obj), new KOp("!", split)));
            foreach (var other in WholeFields(fa.Type).Where(f => !SymbolEqualityComparer.Default.Equals(f, fa.Field)))
                SetField(fa.Obj, other, new KOp("||", FieldHeld(fa.Obj, other), split));
            SetField(fa.Obj, fa.Field, new KOp("&&", FieldHeld(fa.Obj, fa.Field), new KOp("!", Conj(g, new KVar("own$")))));
        }

        /// <summary>Receives o.F; with every field in hand, the object is whole again.</summary>
        private void TakeField(KFieldAcc fa, KExpr g)
        {
            if (!_p.UsesFields) return;
            // (nobody else can hold it: not the whole object, not the field)
            Assume(Implies(g, new KOp("&&", new KOp("&&", new KOp("!=", fa.Obj, new KLit("null")), new KOp("!", Held(fa.Obj))), new KOp("!", FieldHeld(fa.Obj, fa.Field)))));
            SetField(fa.Obj, fa.Field, new KOp("||", FieldHeld(fa.Obj, fa.Field), g));
            var fields = WholeFields(fa.Type);
            Emit(new KAssign { Var = "all$", Value = fields.Select(f => FieldHeld(fa.Obj, f)).Aggregate(g, (a, b) => Conj(a, b)) });
            if (!_p.Locals.Any(l => l.Name == "all$")) _p.Locals.Add(new KLocal { Name = "all$", Raw = "bool" });
            foreach (var f in fields) SetField(fa.Obj, f, new KOp("&&", FieldHeld(fa.Obj, f), new KOp("!", new KVar("all$"))));
            SetPerm(fa.Obj, new KOp("||", Held(fa.Obj), new KVar("all$")));
        }

        // ------------------------------------------------------------------ cells (Viper's quantified permissions over a range)

        private const string Share = "0.000001";

        private static KExpr Amount(KCells c) => new KLit(c.Read ? Share : "1.0");

        /// <summary>Does a predicate's body (or one it names) hold cells?</summary>
        /// <summary>Does a predicate hold an object's Spec.Acc unconditionally (a conjunct of its body's)?</summary>
        private bool PredicateExclusive(IMethodSymbol pred)
        {
            var body = _program.Signature(pred).FunctionBody;
            IEnumerable<KExpr> Conjuncts(KExpr e) => e is KOp { Op: "&&" } and ? and.Args.SelectMany(Conjuncts) : new[] { e };
            return body != null && Conjuncts(body).Any(c => c is KAcc);
        }

        /// <summary>Does the loop at this head exchange permissions (fold, unfold, or call what gives or takes them)?</summary>
        private bool Exchanges(int head)
        {
            if (!_p.UsesPerm || !_p.LoopBodies.TryGetValue(head, out var last)) return false;
            if (!_exchanges.TryGetValue(head, out var known))
                _exchanges[head] = known = _bodies.Where(b => b.Ordinal >= head && b.Ordinal <= last).SelectMany(b => b.Stmts).Any(s =>
                    s is KFold || s is KOwn { Kind: "fromacc" } ||
                    s is KCall c && !_program.ContractOf(c.Callee).IsPure &&
                    _program.Signature(c.Callee) is KProcedure sig && sig.Requires.Concat(sig.Ensures).Any(x => HasAtoms(x.Expr)));
            if (known && !_p.Locals.Any(l => l.Name == $"l${head}$perm"))
            {
                _p.Locals.Add(new KLocal { Name = $"l${head}$perm", Raw = "[Ref]bool" });
                _p.Locals.Add(new KLocal { Name = $"l${head}$pinst", Raw = "[Inst]int" });
                if (_p.UsesCells) _p.Locals.Add(new KLocal { Name = $"l${head}$cells", Raw = "[Ref][int]real" });
                if (_p.UsesFields) _p.Locals.Add(new KLocal { Name = $"l${head}$fperm", Raw = "[Ref][int]bool" });
            }
            return known;
        }

        private readonly Dictionary<int, bool> _exchanges = new Dictionary<int, bool>();
        /// <summary>The blocks as Lowering made them (Exchanges reads the loops' statements before they are checked).</summary>
        private List<KBlock> _bodies;
    }
}
