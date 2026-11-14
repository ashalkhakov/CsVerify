using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.CodeAnalysis;
using static CsVerify.Verifier.Boogie.KernelTypes;
using static CsVerify.Verifier.Boogie.MOp;

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
        private Func<MExpr, MExpr> _old;

        internal static MExpr Instance(IMethodSymbol pred, MExpr[] args) =>
            new MOp("inst", new[] { (MExpr)new MLit(InstanceName(pred)) }.Concat(args).ToArray());

        public static string InstanceName(IMethodSymbol pred) => "i$" + Name(pred);

        private static readonly MExpr None = new MLit("i#none");

        /// <summary>g ==> c, or c alone where g is true.</summary>
        private static MExpr Implication(MExpr g, MExpr c) => g.IsTrue ? c : Implies(g, c);
        private static MExpr Conj(MExpr a, MExpr b) => a.IsTrue ? b : b.IsTrue ? a : AndAlso(a, b);

        /// <summary>These conjoined by Conj, left to right (true, of none).</summary>
        private static MExpr ConjAll(IEnumerable<MExpr> xs)
        {
            MExpr all = MLit.True;
            foreach (var x in xs)
            {
                all = Conj(all, x);
            }
            return all;
        }

        private static bool HasAtoms(KExpr e) => e.Atoms().Any();

        /// <summary>
        /// Walks a permission assertion left to right: &amp;&amp; and the branches of ?: are
        /// followed, each permission goes to <paramref name="atom"/> under the condition it holds in, every other part
        /// is a fact. Its parameters given values by <paramref name="given"/>. Returns its facts, as a condition.
        /// </summary>
        private MExpr Walk(KExpr e, Dictionary<string, MExpr> given, MExpr guard, Action<MExpr, MExpr> atom, Action<MExpr, MExpr> fact)
        {
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
                    var c = WalkSpec(ite.Args[0], guard, given);
                    var t = Walk(ite.Args[1], given, Conj(guard, c), atom, fact);
                    var f = Walk(ite.Args[2], given, Conj(guard, Not(c)), atom, fact);
                    return Ite(c, t, f);
                }
                case KAcc acc:
                    atom(guard, new MAcc
                    {
                        Obj = WalkSpec(acc.Obj, guard, given),
                        Type = acc.Type,
                        At = acc.At,
                    });
                    return MLit.True;
                case KInst inst:
                    atom(guard, new MInst
                    {
                        Pred = inst.Pred,
                        Args = inst.Args.Select(x => WalkSpec(x, guard, given)).ToArray(),
                        At = inst.At,
                    });
                    return MLit.True;
                case KCells cl:
                    atom(guard, new MCells
                    {
                        Arr = WalkSpec(cl.Arr, guard, given),
                        Lo = WalkSpec(cl.Lo, guard, given),
                        Hi = WalkSpec(cl.Hi, guard, given),
                        Read = cl.Read,
                        At = cl.At,
                    });
                    return MLit.True;
                case KFieldAcc fa:
                    var obj = WalkSpec(fa.Obj, guard, given);
                    atom(guard, MFieldAcc.Of(fa, obj));
                    return MLit.True;
                case KLit { Text: "true" }: return MLit.True;
            }
            if (HasAtoms(e))
            {
                throw new NotTranslated("a permission that isn't a conjunct, or in a branch of ?:");
            }
            var v = WalkSpec(e, guard, given);
            fact?.Invoke(guard, v);
            return v;
        }

        private MExpr WalkSpec(KExpr x, MExpr guard, Dictionary<string, MExpr> given)
        {
            var v = Spec(x, out _);
            // (what holds of the memory wherever it's read: a field's reference allocated, a non-nullable field set; assumed)
            var known = _facts.ToList();
            _facts.Clear();
            foreach (var k in known)
            {
                Assume(Implication(guard, AsGiven(k, given)));
            }
            return AsGiven(v, given);
        }

        private MExpr AsGiven(MExpr y, Dictionary<string, MExpr> given)
        {
            y = given == null ? y : y.Substitute(given);
            return _old == null ? y : _old(y);
        }

        private void SetPerm(MExpr o, MExpr value) => Emit(MAssign.Of("perm", Store("perm", o, value)));

        private void AddInst(MExpr q, MExpr guard, int by) =>
            Emit(MAssign.Of(
                "pinst",
                Store("pinst", q,
        new MOp(by > 0 ? "+" : "-", Sel("pinst", q), Ite(guard, MLit.One, MLit.Zero)))));

        /// <summary>Receives an assertion's permissions (a precondition at entry, a postcondition after a call, an invariant at a loop head).</summary>
        private bool _atLoopHead;

        private void Inhale(KExpr e, Dictionary<string, MExpr> given, MExpr _)
        {
            if (!HasAtoms(e))
            {
                return;
            }
            Walk(e, given, MLit.True, (g, a) =>
            {
                if (a is MCells cl)
                {
                    if (_p.UsesCells)
                    {
                        InhaleCells(g, cl);
                    }
                    return;
                }
                if (a is MFieldAcc fa)
                {
                    TakeField(fa, g);
                    return;
                }
                if (a is MAcc acc)
                {
                    // two whole permissions to one object can't both be in hand, and one in hand is folded nowhere
                    Assume(Implication(g, AndAlso(AndAlso(NotNull(acc.Obj), Not(Held(acc.Obj))),
                                                  Eq(Sel("owner", acc.Obj), None))));
                    NoFieldsHeld(g, acc.Obj, acc.Type);
                    SetPerm(acc.Obj, OrElse(Held(acc.Obj), g));
                    if (Invariant(acc.Type, acc.Obj) is MExpr inv)
                    {
                        Assume(Implication(g, inv));
                    }
                }
                else
                {
                    var inst = (MInst)a;
                    // (the guard as it is before the snapshot changes: it may read it)
                    var held = Hold(g);
                    if (!_atLoopHead)
                    {
                        Refresh(Instance(inst.Pred, inst.Args), held);
                    }
                    SnapFacts(inst.Pred, inst.Args, held);
                    // (one that holds an object's Spec.Acc can't be held twice: the object's permission is one)
                    if (PredicateExclusive(inst.Pred))
                    {
                        Assume(Implication(g, Eq(Sel("pinst", Instance(inst.Pred, inst.Args)), MLit.Zero)));
                    }
                    AddInst(Instance(inst.Pred, inst.Args), g, +1);
                }
            }, null);
        }

        /// <summary>Gives an assertion's permissions up (a callee's precondition at a call, a postcondition at a return, an invariant on the way into a loop's head): each must be in hand.</summary>
        private void Exhale(KExpr e, Dictionary<string, MExpr> given, SyntaxNode at, List<(MExpr, MExpr)> gave)
        {
            if (!HasAtoms(e))
            {
                return;
            }
            Walk(e, given, MLit.True, (g, a) =>
            {
                gave?.Add((g, a));
                if (a is MCells cl)
                {
                    if (_p.UsesCells)
                    {
                        ExhaleCells(g, cl, at, $"'{cl.At}' is needed here, but those cells are not all in hand");
                    }
                    return;
                }
                if (a is MFieldAcc fa)
                {
                    GiveField(fa, g, at, $"'{fa.At}' is needed here, but that permission is not in hand");
                    return;
                }
                if (a is MAcc acc)
                {
                    Assert(Implication(g, Held(acc.Obj)), At("CSV1016", at, $"'{acc.At}' is needed here, but that permission is not in hand"));
                    if (Invariant(acc.Type, acc.Obj) is MExpr inv)
                    {
                        Assert(Implication(g, inv), At("CSV1015", at, $"invariant of {acc.Type.Name} might not hold when '{acc.At}' is given up"));
                    }
                    SetPerm(acc.Obj, AndAlso(Held(acc.Obj), Not(g)));
                }
                else
                {
                    var inst = (MInst)a;
                    var q = Instance(inst.Pred, inst.Args);
                    Assert(Implication(g, Ge(Sel("pinst", q), MLit.One)), At("CSV1016", at, $"'{inst.At}' is needed here, but it is not held"));
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
            if (sig.FunctionBody == null)
            {
                throw new NotTranslated("a predicate without a body");
            }
            var args = fold.Inst.Args.Select(a =>
            {
                var v = Spec(a, out _);
                _facts.Clear();
                return v;
            }).ToArray();
            var given = fold.Inst.Pred.Parameters.Select((x, k) => (x, k)).ToDictionary(x => Local(x.x), x => args[x.k]);
            var p = Instance(fold.Inst.Pred, args);
            if (fold.Unfold)
            {
                Unfold(fold, sig, given, args, p);
            }
            else
            {
                FoldInto(fold, sig, given, args, p);
            }
        }

        /// <summary>Spec.Fold: each permission of the body given into the instance p, each fact of it holding; then p in hand, new.</summary>
        private void FoldInto(KFold fold, KProcedure sig, Dictionary<string, MExpr> given, MExpr[] args, MExpr p)
        {
            var at = fold.At;
            Walk(sig.FunctionBody, given, MLit.True, (g, a) => FoldAtom(fold, p, g, a),
                (g, fact) => Assert(Implication(g, fact), At("CSV1019", at, $"'{fold.InstAt}' might not hold when folding it: its body's facts")));
            // (folded now: a snapshot of its own, of which the functions over it are what their bodies say now)
            Refresh(p, MLit.True);
            SnapFacts(fold.Inst.Pred, args, MLit.True);
            AddInst(p, MLit.True, +1);
            Define(fold.Inst.Pred, args, p);
        }

        /// <summary>One permission of a body being folded into p, where g holds: in hand, then p's (its owner p).</summary>
        private void FoldAtom(KFold fold, MExpr p, MExpr g, MExpr a)
        {
            var at = fold.At;
            switch (a)
            {
                case MFieldAcc fa:
                {
                    GiveField(fa, g, at, $"folding needs '{fa.At}', but that permission is not in hand here");
                    var k = new MLit(_program.FieldId(fa.Field).ToString());
                    Emit(MAssign.Of(
                        "fowner",
                        Store("fowner", fa.Obj,
                Store(Sel("fowner", fa.Obj), k, Ite(g, p, Sel("fowner", fa.Obj, k))))));
                    return;
                }
                case MCells cl:
                    if (!_p.UsesCells)
                    {
                        return;
                    }
                    ExhaleCells(g, cl, at, $"'{cl.At}' is needed here, but those cells are not all in hand");
                    Emit(MAssign.Of(
                        "cowner",
                        MapLambda("x$: Ref", MapLambda("i$: int",
                Ite(InCells(g, cl, new MVar("x$"), new MVar("i$")), p, Sel("cowner", new MVar("x$"), new MVar("i$")))))));
                    return;
                case MAcc acc:
                    Assert(Implication(g, Held(acc.Obj)), At("CSV1016", at, $"folding needs '{acc.At}', but that permission is not in hand here"));
                    if (Invariant(acc.Type, acc.Obj) is MExpr inv)
                    {
                        Assert(Implication(g, inv), At("CSV1015", at, $"invariant of {acc.Type.Name} might not hold when it is folded into '{fold.InstAt}'"));
                    }
                    SetPerm(acc.Obj, AndAlso(Held(acc.Obj), Not(g)));
                    Emit(MAssign.Of("owner", Store("owner", acc.Obj, Ite(g, p, Sel("owner", acc.Obj)))));
                    return;
                default:
                {
                    // (an instance in the body: held, then folded into p, and what it owns, p's)
                    var inst = (MInst)a;
                    var q = Instance(inst.Pred, inst.Args);
                    Assert(Implication(g, Ge(Sel("pinst", q), MLit.One)), At("CSV1016", at, $"folding needs '{inst.At}', which is not held here"));
                    AddInst(q, g, -1);
                    var y = new MVar("y$");
                    Emit(MAssign.Of(
                        "owner",
                        MapLambda("y$: Ref",
                Ite(Conj(g, Eq(Sel("owner", y), q)), p, Sel("owner", y)))));
                    return;
                }
            }
        }

        /// <summary>
        /// Spec.Unfold: the instance p, held, gives the body's permissions back, its facts holding; the footprint splits: the
        /// body's own objects and cells free, the rest each of one of the instances in it.
        /// </summary>
        private void Unfold(KFold fold, KProcedure sig, Dictionary<string, MExpr> given, MExpr[] args, MExpr p)
        {
            var at = fold.At;
            Assert(Ge(Sel("pinst", p), MLit.One), At("CSV1016", at, $"'{fold.InstAt}' is not held here"));
            AddInst(p, MLit.True, -1);
            foreach (var (name, raw) in new[] { ("footprint$", "[Ref]Inst"), ("choice$", "[Ref]int") })
            {
                if (!_p.Locals.Any(l => l.Name == name))
                {
                    _p.AddLocal(KLocal.Of(name, raw));
                }
            }
            Emit(MAssign.Of("footprint$", new MVar("owner")));
            var own = new List<(MExpr g, MExpr o)>();
            var nested = new List<(MExpr g, MExpr q)>();
            var ownCells = new List<(MExpr g, MCells c)>();
            if (_p.UsesCells)
            {
                Emit(MAssign.Of("cfootprint$", new MVar("cowner")));
                foreach (var (name, raw) in new[] { ("cfootprint$", "[Ref][int]Inst"), ("cchoice$", "[Ref][int]int") })
                {
                    if (!_p.Locals.Any(l => l.Name == name))
                    {
                        _p.AddLocal(KLocal.Of(name, raw));
                    }
                }
            }
            Walk(sig.FunctionBody, given, MLit.True, (g, a) => UnfoldAtom(p, g, a, own, nested, ownCells), (g, fact) => Assume(Implication(g, fact)));
            // (what was folded hasn't changed: the functions over it are what their bodies say of it now)
            Define(fold.Inst.Pred, args, p);
            SplitFootprint(p, own, nested);
            if (_p.UsesCells)
            {
                SplitCells(p, ownCells, nested);
            }
        }

        /// <summary>
        /// One permission of a body being unfolded from p, where g holds: in hand again (it was p's, and nobody else's);
        /// the objects, cells and instances the body holds, noted for the footprint's split.
        /// </summary>
        private void UnfoldAtom(MExpr p, MExpr g, MExpr a, List<(MExpr g, MExpr o)> own, List<(MExpr g, MExpr q)> nested, List<(MExpr g, MCells c)> ownCells)
        {
            switch (a)
            {
                case MCells cl:
                    if (_p.UsesCells)
                    {
                        InhaleCells(g, cl);
                    }
                    ownCells.Add((g, cl));
                    return;
                case MFieldAcc fa:
                    Assume(Implication(g, Eq(Sel("fowner", fa.Obj, new MLit(_program.FieldId(fa.Field).ToString())), p)));
                    TakeField(fa, g);
                    // (folded nowhere now: the body's own)
                    Emit(MAssign.Of(
                        "fowner",
                        Store("fowner", fa.Obj,
                Store(Sel("fowner", fa.Obj), new MLit(_program.FieldId(fa.Field).ToString()), Ite(g, None, Sel("fowner", fa.Obj, new MLit(_program.FieldId(fa.Field).ToString())))))));
                    return;
                case MAcc acc:
                    Assume(Implication(g, AndAlso(AndAlso(NotNull(acc.Obj), Eq(Sel("footprint$", acc.Obj), p)), Not(Held(acc.Obj)))));
                    SetPerm(acc.Obj, OrElse(Held(acc.Obj), g));
                    if (Invariant(acc.Type, acc.Obj) is MExpr inv)
                    {
                        Assume(Implication(g, inv));
                    }
                    own.Add((g, acc.Obj));
                    return;
                default:
                {
                    // (an instance in the body: in hand, of a snapshot of its own)
                    var inst = (MInst)a;
                    var q = Instance(inst.Pred, inst.Args);
                    var held = Hold(g);
                    Refresh(q, held);
                    SnapFacts(inst.Pred, inst.Args, held);
                    if (PredicateExclusive(inst.Pred))
                    {
                        Assume(Implication(g, Eq(Sel("pinst", q), MLit.Zero)));
                    }
                    AddInst(q, g, +1);
                    nested.Add((g, q));
                    return;
                }
            }
        }

        /// <summary>
        /// The footprint of p, unfolded, splits: the body's own objects are free now, the rest belongs to one of its
        /// instances (which one not known, where there are several); what was another instance's stays so.
        /// </summary>
        private void SplitFootprint(MExpr p, List<(MExpr g, MExpr o)> own, List<(MExpr g, MExpr q)> nested)
        {
            var yv = new MVar("y$");
            if (nested.Count > 1)
            {
                Emit(MHavoc.Of("choice$"));
            }
            MExpr to = None;
            for (int k = nested.Count - 1; k >= 0; k--)
            {
                var pick = nested.Count > 1 ? Conj(nested[k].g, Eq(Sel("choice$", yv), new MLit(k.ToString()))) : nested[k].g;
                to = Ite(pick, nested[k].q, to);
            }
            foreach (var (g, o) in own)
            {
                to = Ite(Conj(g, Eq(yv, o)), None, to);
            }
            MExpr elsewhere = Footprint(yv);
            if (nested.Count > 0)
            {
                elsewhere = Ite(OrAny(nested.Select(n => (MExpr)Eq(Footprint(yv), n.q))), None, Footprint(yv));
            }
            Emit(MAssign.Of("owner", MapLambda("y$: Ref", Ite(Eq(Footprint(yv), p), to, elsewhere))));
        }

        private MExpr Footprint(MExpr y) => Sel("footprint$", y);

        /// <summary>The cells of p's footprint, likewise: the body's own are free, the rest go to its instances.</summary>
        private void SplitCells(MExpr p, List<(MExpr g, MCells c)> ownCells, List<(MExpr g, MExpr q)> nested)
        {
            var (xv, iv) = (new MVar("x$"), new MVar("i$"));
            if (nested.Count > 1)
            {
                Emit(MHavoc.Of("cchoice$"));
            }
            MExpr cto = None;
            for (int k = nested.Count - 1; k >= 0; k--)
            {
                var pick = nested.Count > 1 ? Conj(nested[k].g, Eq(Sel("cchoice$", xv, iv), new MLit(k.ToString()))) : nested[k].g;
                cto = Ite(pick, nested[k].q, cto);
            }
            foreach (var (g, c) in ownCells)
            {
                cto = Ite(InCells(g, c, xv, iv), None, cto);
            }
            MExpr celsewhere = CellFootprint(xv, iv);
            if (nested.Count > 0)
            {
                celsewhere = Ite(OrAny(nested.Select(n => (MExpr)Eq(CellFootprint(xv, iv), n.q))), None, CellFootprint(xv, iv));
            }
            Emit(MAssign.Of(
                "cowner",
                MapLambda("x$: Ref", MapLambda("i$: int", Ite(Eq(CellFootprint(xv, iv), p), cto, celsewhere)))));
        }

        private MExpr CellFootprint(MVar xv, MVar iv) => Sel("cfootprint$", xv, iv);

        // ------------------------------------------------------------------ functions under quantifiers

        private int _unfolding;

        /// <summary>
        /// A function's application under a quantifier, of its variable: its definition, unfolded once, for every value
        /// in its range. That quantified equation applies again to the applications in
        /// its body, so recursion over the range unfolds as far as it needs to (a concrete array's sum).
        /// </summary>
        private void Unfoldings(string var, MExpr range, MExpr body)
        {
            if (_unfolding > 0)
            {
                return;
            }
            _unfolding++;
            try
            {
                foreach (var app in body.Applications().Where(a => a.Snap == null && !a.Plain && a.Layer == null && a.Args.Any(x => x.Mentions(new HashSet<string> { var })) &&
                                                         !a.Args.Any(x => x.Mentions(_bound))).ToList())
                {
                    var sig = _program.Signature(app.Callee);
                    if (sig.FunctionBody == null || !app.Callee.IsStatic)
                    {
                        continue;
                    }
                    var given = app.Callee.Parameters.Select((x, k) => (x, k)).ToDictionary(x => Local(x.x), x => app.Args[x.k]);
                    // (the facts so far kept: the definition's own are left out)
                    var saved = _facts.ToList();
                    var pre = ConjAll(sig.Requires.Select(r => SpecGiven(r.Expr, given)));
                    var definition = Eq(app, SpecGiven(sig.FunctionBody, given));
                    _facts.Clear();
                    _facts.AddRange(saved);
                    _facts.Add(MQuant.ForAll(var, Implication(Conj(range, pre), definition)));
                }
            }
            finally
            {
                _unfolding--;
            }
        }

        // ------------------------------------------------------------------ frames (Dafny's Spec.Modifies)

        /// <summary>A write of an (unowned) object's field or an array's cell: within Spec.Modifies as of entry, or allocated since (CSV1017).</summary>
        private void WithinFrame(MExpr o, SyntaxNode at)
        {
            if (_p.Frame == null)
            {
                return;
            }
            Assert(OrElse(Sel("w$entry", o), Not(Sel("alloc$entry", o))),
                At("CSV1017", at, $"'{at}' writes an object that is not in Spec.Modifies and was not allocated here"));
        }

        private int _holds;

        /// <summary>A condition's value now, in a local of its own (true stays true).</summary>
        private MExpr Hold(MExpr g)
        {
            if (g.IsTrue)
            {
                return g;
            }
            var name = "g$h" + _holds++;
            _p.AddLocal(KLocal.Of(name, "bool"));
            Emit(MAssign.Of(name, g));
            return new MVar(name);
        }

        private void Refresh(MExpr q, MExpr g)
        {
            g = Conj(g, Eq(Sel("pinst", q), MLit.Zero));
            if (!_p.Locals.Any(l => l.Name == "snap$"))
            {
                _p.AddLocal(KLocal.Of("snap$", "int"));
            }
            Emit(MHavoc.Of("snap$"));
            Emit(MAssign.Of("psnap", Store("psnap", q, Ite(g, new MVar("snap$"), Sel("psnap", q)))));
        }

        // ------------------------------------------------------------------ single fields (Viper's acc(o.f))

        private MExpr FieldHeld(MExpr o, ISymbol field) => Sel("fperm", o, new MLit(_program.FieldId(field).ToString()));

        /// <summary>Write permission to o.F: the whole object, or that field.</summary>
        private MExpr CanWrite(MExpr o, ISymbol field) => _p.UsesFields ? OrElse(Held(o), FieldHeld(o, field)) : Held(o);

        private void SetField(MExpr o, ISymbol field, MExpr value) =>
            Emit(MAssign.Of(
                "fperm",
                Store("fperm", o,
        Store(Sel("fperm", o), new MLit(_program.FieldId(field).ToString()), value))));

        /// <summary>A whole object received is nobody else's, field by field either.</summary>
        private void NoFieldsHeld(MExpr g, MExpr o, ITypeSymbol type)
        {
            if (!_p.UsesFields)
            {
                return;
            }
            foreach (var f in WholeFields(type))
            {
                Assume(Implication(g, Not(FieldHeld(o, f))));
            }
        }

        /// <summary>Gives o.F up: from its own permission, or split off the whole object (whose other fields stay, one by one).</summary>
        private void GiveField(MFieldAcc fa, MExpr g, SyntaxNode at, string message)
        {
            if (!_p.UsesFields)
            {
                return;
            }
            Assert(Implication(g, CanWrite(fa.Obj, fa.Field)), At("CSV1016", at, message));
            Emit(MAssign.Of("own$", FieldHeld(fa.Obj, fa.Field)));
            if (!_p.Locals.Any(l => l.Name == "own$"))
            {
                _p.AddLocal(KLocal.Of("own$", "bool"));
            }
            var split = Conj(g, Not(new MVar("own$")));
            SetPerm(fa.Obj, AndAlso(Held(fa.Obj), Not(split)));
            foreach (var other in WholeFields(fa.Type).Where(f => !SymbolEqualityComparer.Default.Equals(f, fa.Field)))
            {
                SetField(fa.Obj, other, OrElse(FieldHeld(fa.Obj, other), split));
            }
            SetField(fa.Obj, fa.Field, AndAlso(FieldHeld(fa.Obj, fa.Field), Not(Conj(g, new MVar("own$")))));
        }

        /// <summary>Receives o.F; with every field in hand, the object is whole again.</summary>
        private void TakeField(MFieldAcc fa, MExpr g)
        {
            if (!_p.UsesFields)
            {
                return;
            }
            // (nobody else can hold it: not the whole object, not the field)
            Assume(Implication(g, AndAlso(AndAlso(NotNull(fa.Obj), Not(Held(fa.Obj))), Not(FieldHeld(fa.Obj, fa.Field)))));
            SetField(fa.Obj, fa.Field, OrElse(FieldHeld(fa.Obj, fa.Field), g));
            var fields = WholeFields(fa.Type);
            Emit(MAssign.Of("all$", ConjAll(fields.Select(f => FieldHeld(fa.Obj, f)).Prepend(g))));
            if (!_p.Locals.Any(l => l.Name == "all$"))
            {
                _p.AddLocal(KLocal.Of("all$", "bool"));
            }
            foreach (var f in fields)
            {
                SetField(fa.Obj, f, AndAlso(FieldHeld(fa.Obj, f), Not(new MVar("all$"))));
            }
            SetPerm(fa.Obj, OrElse(Held(fa.Obj), new MVar("all$")));
        }

        // ------------------------------------------------------------------ cells (Viper's quantified permissions over a range)

        private const string Share = "0.000001";

        private static MExpr Amount(bool read) => new MLit(read ? Share : "1.0");

        /// <summary>Does a predicate hold an object's Spec.Acc unconditionally (a conjunct of its body's)?</summary>
        private bool PredicateExclusive(IMethodSymbol pred)
        {
            var body = _program.Signature(pred).FunctionBody;
            return body != null && body.Conjuncts().Any(c => c is KAcc);
        }

        /// <summary>Does the loop at this head exchange permissions (fold, unfold, or call what gives or takes them)?</summary>
        private bool Exchanges(int head)
        {
            if (!_p.UsesPerm || !_p.LoopBodies.TryGetValue(head, out var last))
            {
                return false;
            }
            if (!_exchanges.TryGetValue(head, out var known))
            {
                _exchanges[head] = known = _bodies.Where(b => b.Ordinal >= head && b.Ordinal <= last).SelectMany(b => b.Stmts).Any(s =>
                    s is KFold || s is KOwn { Kind: "fromacc" } ||
                    s is KCall c && !_program.ContractOf(c.Callee).IsPure &&
                    _program.Signature(c.Callee) is KProcedure sig && sig.Requires.Concat(sig.Ensures).Any(x => HasAtoms(x.Expr)));
            }
            if (known && !_p.Locals.Any(l => l.Name == $"l${head}$perm"))
            {
                _p.AddLocal(KLocal.Of($"l${head}$perm", "[Ref]bool"));
                _p.AddLocal(KLocal.Of($"l${head}$pinst", "[Inst]int"));
                if (_p.UsesCells)
                {
                    _p.AddLocal(KLocal.Of($"l${head}$cells", "[Ref][int]real"));
                }
                if (_p.UsesFields)
                {
                    _p.AddLocal(KLocal.Of($"l${head}$fperm", "[Ref][int]bool"));
                }
            }
            return known;
        }

        private readonly Dictionary<int, bool> _exchanges = new Dictionary<int, bool>();
        /// <summary>The blocks as Lowering made them (Exchanges reads the loops' statements before they are checked).</summary>
        private List<KBlock> _bodies;
    }
}
