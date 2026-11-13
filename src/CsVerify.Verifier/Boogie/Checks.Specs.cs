using System;
using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using static CsVerify.Verifier.Boogie.KernelTypes;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>Specifications: as mathematics, their well-definedness (CSV1012); library stubs' models; substitution.</summary>
    internal sealed partial class Checks
    {
        /// <summary>
        /// The objects a function's body (as mathematics) reads the fields and cells of, as a set: null where it reads
        /// anything else (another function, the allocation, an object named by a quantifier's variable).
        /// </summary>
        private static KExpr InferReads(KExpr body)
        {
            var objects = new List<KExpr>();
            var keys = new HashSet<string>();
            var bound = new HashSet<string>();
            bool Walk(KExpr e)
            {
                switch (e)
                {
                    case KLit _: return true;
                    case KVar v: return v.Name != "$Alloc";
                    case KOp { Op: "sel" } s when s.Args[0] is KVar map && (map.Name.StartsWith("$F.") || map.Name.StartsWith("$E.")):
                        if (Mentions(s.Args[1], bound)) return false;
                        if (keys.Add(Key(s.Args[1]))) objects.Add(s.Args[1]);
                        return s.Args.Skip(1).All(Walk);
                    case KOp op: return op.Args.All(Walk);
                    case KQuant q:
                        bound.Add(q.Var);
                        try { return (q.Range == null || Walk(q.Range)) && Walk(q.Body); }
                        finally { bound.Remove(q.Var); }
                    default: return false;
                }
            }
            string Key(KExpr e) => e switch
            {
                KVar v => v.Name,
                KLit l => l.Text,
                KOp op => op.Op + "(" + string.Join(",", op.Args.Select(Key)) + ")",
                _ => "?" + System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(e),
            };
            if (!Walk(body) || objects.Count == 0) return null;
            return objects.Select(o => (KExpr)new KOp("set.of", o)).Aggregate((a, b) => new KOp("set.union", a, b));
        }

        private static bool Mentions(KExpr e, HashSet<string> vars) => MathTerms.Subterms(e).Any(x => x is KVar v && vars.Contains(v.Name));

        /// <summary>A specification's well-definedness, asserted (CSV1012) where it is evaluated, under what holds before it.</summary>
        private void WellDefined(List<KExpr> wf, SyntaxNode at, List<KExpr> before)
        {
            if (wf.Count == 0) return;
            var cond = And(wf);
            if (before != null && before.Count > 0) cond = new KOp("==>", And(before), cond);
            // (checked, not assumed after: what an ill-defined specification says is unknown)
            Assert(cond, At("CSV1012", at, $"specification might not be well-defined: '{at}'"), true);
        }

        // ------------------------------------------------------------------ exceptions

        /// <summary>Is the exception of this type (any is a System.Exception)?</summary>
        internal static KExpr Is(KExpr ex, ITypeSymbol type) =>
            type.ToDisplayString() == "System.Exception" ? new KLit("true") : new KOp("sub", new KOp("dtype", ex), new KLit(TypeConst(type)));

        // ------------------------------------------------------------------ strings

        /// <summary>
        /// Two strings compared: of one length, and different, they differ at some index (a string is its characters).
        /// </summary>
        private static KExpr Extensional(KExpr x, KExpr y)
        {
            var at = new KOp("sdiff", x, y);
            return new KOp("==>", new KOp("&&", new KOp("&&", new KOp("&&", new KOp("!=", x, new KLit("null")), new KOp("!=", y, new KLit("null"))), new KOp("!=", x, y)),
                                             new KOp("==", new KOp("slen", x), new KOp("slen", y))),
                new KOp("&&", new KOp("&&", new KOp("<=", new KLit("0"), at), new KOp("<", at, new KOp("slen", x))), new KOp("!=", new KOp("sat", x, at), new KOp("sat", y, at))));
        }

        /// <summary>A stub's parameters given values: its receiver (@this, first), then the member's arguments.</summary>
        private Dictionary<string, KExpr> StubGiven(IMethodSymbol callee, KExpr receiver, KExpr[] args)
        {
            var stub = _program.ContractOf(callee).Stub;
            var values = (receiver == null ? args : new[] { receiver }.Concat(args)).ToArray();
            var given = stub.Parameters.Select((x, k) => (x, k)).Where(x => x.k < values.Length).ToDictionary(x => Local(x.x), x => values[x.k]);
            // (an instance member's stub, @this: this, as its contract reads it)
            if (receiver != null && !callee.IsStatic) given["this"] = receiver;
            return given;
        }

        private KExpr StubApp(IMethodSymbol callee, KExpr receiver, KExpr[] args) =>
            new KFnApp { Callee = callee, Function = StubName(callee), Plain = true,
                         Args = StubModels(callee, _program.ContractOf(callee)).Select(m => (KExpr)new KVar(m.Name)).Concat(receiver == null ? args : new[] { receiver }.Concat(args)).ToArray() };

        /// <summary>The models a collection's [Pure] member is a function of (its version aside); none for another stub's.</summary>
        public static List<ModelMap> StubModels(IMethodSymbol callee, Contract contract)
        {
            var models = IsCollection(callee.ContainingType) ? ModelsOf((INamedTypeSymbol)callee.ContainingType).Where(m => m.Name != VersionMap).ToList() : new List<ModelMap>();
            // (and the models its stub declares, that its contract reads)
            if (contract != null)
                foreach (var m in contract.Requires.Concat(contract.Ensures.Select(e => e.Expr)).Where(x => x != null).SelectMany(x => Microsoft.CodeAnalysis.Operations.OperationExtensions.DescendantsAndSelf(x)).OfType<Microsoft.CodeAnalysis.Operations.IInvocationOperation>()
                             .Where(i => SpecSymbols.IsModel(i.TargetMethod.OriginalDefinition) && i.TargetMethod.IsStatic && i.Arguments.Length >= 1 && (!IsCollection(callee.ContainingType) || ModelOf(i.TargetMethod.Name, (INamedTypeSymbol)callee.ContainingType) == null))
                             .Select(i => UserModel(i.TargetMethod.OriginalDefinition)).OrderBy(x => x.Name, System.StringComparer.Ordinal))
                    if (!models.Any(x => x.Name == m.Name)) models.Add(m);
            return models;
        }

        public static string StubName(IMethodSymbol m) => "lib$" + Name(m);

        /// <summary>A specification as mathematics, outside any procedure (a stub's contract, for its axioms).</summary>
        public static KExpr MathOf(KExpr e, IProgramFacts program, IMethodSymbol m)
        {
            var c = new Checks(new KProcedure { Method = m }, program);
            return c.Spec(e, out _);
        }

        // ------------------------------------------------------------------ specifications

        /// <summary>A specification as mathematics, and what makes it well-defined (each a condition, in order).</summary>
        /// <summary>The facts the last specifications read gave, taken.</summary>
        private List<KExpr> Take()
        {
            var taken = _facts.ToList();
            _facts.Clear();
            return taken;
        }

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
                case KOp { Op: "old" } old:
                {
                    // (what it needs to be well-defined, it needs in the old state too)
                    var inner = new List<KExpr>();
                    var v = Spec(old.Args[0], inner, new List<KExpr>());
                    foreach (var c in inner) Need(new KOp("old", c));
                    return new KOp("old", v);
                }
                // (a value defined only where its condition holds: a float cast to an integer, which must fit)
                case KOp { Op: "$need" } nd:
                {
                    Need(Spec(nd.Args[0], wf, guard));
                    return Spec(nd.Args[1], wf, guard);
                }
                case KOp { Op: "streq" } eq:
                {
                    var (l, r) = (Spec(eq.Args[0], wf, guard), Spec(eq.Args[1], wf, guard));
                    if (!Mentions(l, _bound) && !Mentions(r, _bound)) _facts.Add(Extensional(l, r));
                    return new KOp("==", l, r);
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
                case KIfc si:
                {
                    var x = Spec(si.Of, wf, guard);
                    var i = si.Index == null ? null : Spec(si.Index, wf, guard);
                    var count = IfcRead(x, null, si.Element);
                    Need(i == null ? new KOp("!=", x, new KLit("null")) : new KOp("&&", new KOp("!=", x, new KLit("null")), new KOp("&&", new KOp("<=", new KLit("0"), i), new KOp("<", i, count))));
                    return i == null ? count : IfcRead(x, i, si.Element);
                }
                case KLet let:
                {
                    var value = Spec(let.Value, wf, guard);
                    int from = wf.Count, facts = _facts.Count;
                    var body = Spec(let.Body, wf, guard);
                    // (what makes the body well-defined, and what it knows, are of the local's value too)
                    var bound = new Dictionary<string, KExpr> { [let.Var] = value };
                    for (int k = from; k < wf.Count; k++) wf[k] = Subst(wf[k], bound);
                    for (int k = facts; k < _facts.Count; k++) _facts[k] = Subst(_facts[k], bound);
                    // (a fact of the local's value that now names a quantifier's variable isn't one of the state: dropped)
                    for (int k = _facts.Count - 1; k >= facts; k--) if (Mentions(_facts[k], _bound)) _facts.RemoveAt(k);
                    return Subst(body, bound);
                }
                case KMultiset ms:
                {
                    // (well-defined within the array: 0 <= n <= a.Length; its contents as of where it's read)
                    var a = Spec(ms.Array, wf, guard);
                    var n = Spec(ms.Count, wf, guard);
                    Need(new KOp("&&", new KOp("&&", new KOp("!=", a, new KLit("null")), new KOp("<=", new KLit("0"), n)), new KOp("<=", n, new KOp("len", a))));
                    KExpr fuel = new KLit("$LZ");
                    for (int k = 0; k < ms.Levels; k++) fuel = new KOp("$LS", fuel);
                    return new KOp("$bag", fuel, new KOp("sel", new KVar(Elements(ms.ArrayType)), a), n);
                }
                case KElem { Model: string model } le:
                {
                    // (a collection's element, of its model: where its indexer's precondition holds)
                    var a = Spec(le.Array, wf, guard);
                    var i = Spec(le.Index, wf, guard);
                    Need(le.Domain != null
                        ? new KOp("&&", new KOp("!=", a, new KLit("null")), new KOp("sel", new KVar(le.Domain), a, i))
                        : new KOp("&&", new KOp("&&", new KOp("!=", a, new KLit("null")), new KOp("<=", new KLit("0"), i)), new KOp("<", i, new KOp("sel", new KVar(SizeMap), a))));
                    return new KOp("sel", new KVar(model), a, i);
                }
                case KElem el:
                {
                    var a = Spec(el.Array, wf, guard);
                    var i = Spec(el.Index, wf, guard);
                    Need(el.Unchecked ? (el.NoNull ? new KLit("true") : new KOp("!=", a, new KLit("null"))) : new KOp("&&", new KOp("&&", new KOp("!=", a, new KLit("null")), new KOp("<=", new KLit("0"), i)), new KOp("<", i, new KOp(el.String ? "slen" : "len", a))));
                    return el.String ? new KOp("sat", a, i) : new KOp("sel", new KVar(Elements(el.ArrayType)), a, i);
                }
                case KDataField df:
                {
                    var v = Spec(df.Value, wf, guard);
                    if (!df.Struct) Need(new KOp("!=", v, new KLit("null")));
                    return new KOp(df.Function, v);
                }
                case KCast cast:
                {
                    var v = Spec(cast.Value, wf, guard);
                    Need(Spec(cast.Test, wf, guard));
                    return v;
                }
                case KLen len:
                {
                    var a = Spec(len.Array, wf, guard);
                    Need(new KOp("!=", a, new KLit("null")));
                    return new KOp(len.String ? "slen" : "len", a);
                }
                case KFnCall { Stub: true } st:
                {
                    KExpr receiver = null;
                    if (st.Receiver != null)
                    {
                        receiver = Spec(st.Receiver, wf, guard);
                        Need(new KOp("!=", receiver, new KLit("null")));
                    }
                    var args = st.Args.Select(a => Spec(a, wf, guard)).ToArray();
                    var given = StubGiven(st.Callee, receiver, args);
                    var saved = _facts.ToList();
                    foreach (var r in _program.Signature(st.Callee).Requires) Need(Subst(Spec(r.Expr, out _), given));
                    _facts.Clear();
                    _facts.AddRange(saved);
                    _p.Stubs.Add(st.Callee);
                    return StubApp(st.Callee, receiver, args);
                }
                case KAcc acc:
                {
                    var o = Spec(acc.Obj, wf, guard);
                    return _held ? Held(o) : new KLit("true");
                }
                case KFieldAcc fa:
                {
                    var o = Spec(fa.Obj, wf, guard);
                    return _held ? CanWrite(o, fa.Field) : new KLit("true");
                }
                case KCells cl:
                {
                    var a = Spec(cl.Arr, wf, guard);
                    var lo = Spec(cl.Lo, wf, guard);
                    var hi = Spec(cl.Hi, wf, guard);
                    // (in hand, as a condition: a method that keeps no cell permissions holds every cell)
                    if (!_held || !_p.UsesCells) return new KLit("true");
                    var i = new KVar("i$");
                    return new KQuant { Forall = true, Var = "i$", Range = null,
                        Body = Implies(new KOp("&&", new KOp("<=", lo, i), new KOp("<", i, hi)), new KOp(">=", Cell(a, i), Amount(cl))) };
                }
                case KInst inst:
                {
                    var q = Instance(inst.Pred, inst.Args.Select(a => Spec(a, wf, guard)).ToArray());
                    return _held ? new KOp(">=", new KOp("sel", new KVar("pinst"), q), new KLit("1")) : new KLit("true");
                }
                case KField fd:
                {
                    if (fd.Instance == null)
                    {
                        var sv = new KOp("sel", new KVar(FieldMap(fd.Field)), new KLit("null"));
                        if (NonNullField(fd.Field)) _facts.Add(new KOp("!=", sv, new KLit("null")));
                        return sv;
                    }
                    var o = Spec(fd.Instance, wf, guard);
                    if (!fd.OnThis && !fd.NoNull) Need(new KOp("!=", o, new KLit("null")));
                    var v = new KOp("sel", new KVar(FieldMap(fd.Field)), o);
                    if (NonNullField(fd.Field) && !(_p.IsCtor && fd.OnThis) && !Mentions(o, _bound))
                        _facts.Add(new KOp("==>", new KOp("!=", o, new KLit("null")), new KOp("!=", v, new KLit("null"))));
                    if (IsRef(FieldType(fd.Field)) && !Mentions(o, _bound)) _facts.Add(Allocated(o, v));
                    return v;
                }
                case KQuant q when q.Range == null:
                {
                    // (over all of its type: a delegate's arguments)
                    bool added = _bound.Add(q.Var);
                    try { return new KQuant { Forall = q.Forall, Var = q.Var, Type = q.Type, Body = Spec(q.Body, new List<KExpr>(), new List<KExpr>()) }; }
                    finally { if (added) _bound.Remove(q.Var); }
                }
                case KQuant q:
                {
                    // (Range is lo <= q && q < hi, from Lowering)
                    var lo = Spec(((KOp)((KOp)q.Range).Args[0]).Args[0], wf, guard);
                    var hi = Spec(((KOp)((KOp)q.Range).Args[1]).Args[1], wf, guard);
                    var range = new KOp("&&", new KOp("<=", lo, new KVar(q.Var)), new KOp("<", new KVar(q.Var), hi));
                    // (its body well-defined over the range: each condition quantified the same way)
                    var inner = new List<KExpr>();
                    bool added = _bound.Add(q.Var);
                    KExpr body;
                    KExpr[] trigger = null;
                    try
                    {
                        body = Spec(q.Body, inner, new List<KExpr> { range });
                        trigger = q.Trigger?.Select(t => Spec(t, new List<KExpr>(), new List<KExpr>())).ToArray();
                    }
                    finally { if (added) _bound.Remove(q.Var); }
                    foreach (var c in inner) Need(new KQuant { Forall = true, Var = q.Var, Range = null, Body = c });
                    if (!Mentions(range, _bound)) Unfoldings(q.Var, range, body);
                    return new KQuant { Forall = q.Forall, Var = q.Var, Type = q.Type, Range = range, Body = body, Trigger = trigger };
                }
                case KFnCall fn:
                {
                    KExpr receiver = null;
                    if (fn.Receiver != null)
                    {
                        receiver = Spec(fn.Receiver, wf, guard);
                        if (!fn.ReceiverIsThis && !IsStruct(fn.Callee.ContainingType)) Need(new KOp("!=", receiver, new KLit("null")));
                    }
                    var args = fn.Args.Select(a => Spec(a, wf, guard)).ToArray();
                    // (well-defined where its precondition holds, at the arguments)
                    var given = Given(fn.Callee, receiver, args);
                    var saved = _facts.ToList();
                    foreach (var r in _program.Signature(fn.Callee).Requires) Need(Subst(Spec(r.Expr, out _), given));
                    _facts.Clear();
                    _facts.AddRange(saved);
                    // (over a predicate: its value is of the instance's snapshot)
                    if (_program.OverPredicate(fn.Callee) is (IMethodSymbol pred, int[] map))
                        return new KFnApp { Callee = fn.Callee, Function = FunctionName(fn.Callee), Args = args, Snap = Snap(pred, map, args) };
                    // (the fields it reads are the procedure's too: what's known of them, a reference field's object allocated, holds)
                    foreach (var ff in _program.FunctionFieldSymbols(fn.Callee)) _p.Fields.Add(ff);
                    return new KFnApp { Callee = fn.Callee, Function = FunctionName(fn.Callee), Fields = _program.FunctionFields(fn.Callee),
                                        Args = (receiver == null ? args : new[] { receiver }.Concat(args)).ToArray() };
                }
                default: throw new NotTranslated("in a specification: " + e.GetType().Name);
            }
        }

        /// <summary>A variable given a value (mathematics).</summary>
        internal static KExpr Rename(KExpr e, string name, KExpr value) => Subst(e, new Dictionary<string, KExpr> { [name] = value });
        internal static KExpr Rename(KExpr e, Dictionary<string, KExpr> given) => Subst(e, given);

        /// <summary>Parameters given values (mathematics in, mathematics out).</summary>
        private static KExpr Subst(KExpr e, Dictionary<string, KExpr> given) => MathTerms.Map(e, x => x is KVar v && given.TryGetValue(v.Name, out var value) ? value : null);
    }
}
