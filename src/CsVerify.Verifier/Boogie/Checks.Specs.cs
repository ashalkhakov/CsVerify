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
        private static MExpr InferReads(MExpr body)
        {
            var objects = new List<MExpr>();
            var keys = new HashSet<string>();
            var bound = new HashSet<string>();
            bool Walk(MExpr e)
            {
                switch (e)
                {
                    case MLit _: return true;
                    case MVar v: return v.Name != "$Alloc";
                    case MOp { Op: "sel" } s when s.Args[0] is MVar map && (map.Name.StartsWith("$F.") || map.Name.StartsWith("$E.")):
                        if (Mentions(s.Args[1], bound))
                        {
                            return false;
                        }
                        if (keys.Add(Key(s.Args[1])))
                        {
                            objects.Add(s.Args[1]);
                        }
                        return s.Args.Skip(1).All(Walk);
                    case MOp op: return op.Args.All(Walk);
                    case MQuant q:
                        bound.Add(q.Var);
                        try
                        {
                            return (q.Range == null || Walk(q.Range)) && Walk(q.Body);
                        }
                        finally
                        {
                            bound.Remove(q.Var);
                        }
                    default: return false;
                }
            }
            string Key(MExpr e) => e switch
            {
                MVar v => v.Name,
                MLit l => l.Text,
                MOp op => op.Op + "(" + string.Join(",", op.Args.Select(Key)) + ")",
                _ => "?" + System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(e),
            };
            if (!Walk(body) || objects.Count == 0)
            {
                return null;
            }
            return objects.Select(o => (MExpr)new MOp("set.of", o)).Aggregate((a, b) => new MOp("set.union", a, b));
        }

        private static bool Mentions(MExpr e, HashSet<string> vars) => MathTerms.Subterms(e).Any(x => x is MVar v && vars.Contains(v.Name));

        /// <summary>A specification's well-definedness, asserted (CSV1012) where it is evaluated, under what holds before it.</summary>
        private void WellDefined(List<MExpr> wf, SyntaxNode at, List<MExpr> before)
        {
            if (wf.Count == 0)
            {
                return;
            }
            var cond = And(wf);
            if (before != null && before.Count > 0)
            {
                cond = new MOp("==>", And(before), cond);
            }
            // (checked, not assumed after: what an ill-defined specification says is unknown)
            Assert(cond, At("CSV1012", at, $"specification might not be well-defined: '{at}'"), true);
        }

        // ------------------------------------------------------------------ exceptions

        /// <summary>Is the exception of this type (any is a System.Exception)?</summary>
        internal static MExpr Is(MExpr ex, ITypeSymbol type) =>
            type.ToDisplayString() == "System.Exception" ? new MLit("true") : new MOp("sub", new MOp("dtype", ex), new MLit(TypeConst(type)));

        // ------------------------------------------------------------------ strings

        /// <summary>
        /// Two strings compared: of one length, and different, they differ at some index (a string is its characters).
        /// </summary>
        private static MExpr Extensional(MExpr x, MExpr y)
        {
            var at = new MOp("sdiff", x, y);
            return new MOp("==>", new MOp("&&", new MOp("&&", new MOp("&&", new MOp("!=", x, new MLit("null")), new MOp("!=", y, new MLit("null"))), new MOp("!=", x, y)),
                                             new MOp("==", new MOp("slen", x), new MOp("slen", y))),
                new MOp("&&", new MOp("&&", new MOp("<=", new MLit("0"), at), new MOp("<", at, new MOp("slen", x))), new MOp("!=", new MOp("sat", x, at), new MOp("sat", y, at))));
        }

        /// <summary>A stub's parameters given values: its receiver (@this, first), then the member's arguments.</summary>
        private Dictionary<string, MExpr> StubGiven(IMethodSymbol callee, MExpr receiver, MExpr[] args)
        {
            var stub = _program.ContractOf(callee).Stub;
            var values = (receiver == null ? args : new[] { receiver }.Concat(args)).ToArray();
            var given = stub.Parameters.Select((x, k) => (x, k)).Where(x => x.k < values.Length).ToDictionary(x => Local(x.x), x => values[x.k]);
            // (an instance member's stub, @this: this, as its contract reads it)
            if (receiver != null && !callee.IsStatic)
            {
                given["this"] = receiver;
            }
            return given;
        }

        private MExpr StubApp(IMethodSymbol callee, MExpr receiver, MExpr[] args) =>
            new MFnApp
            {
                Callee = callee,
                Function = StubName(callee),
                Plain = true,
                Args = StubModels(callee, _program.ContractOf(callee)).Select(m => (MExpr)new MVar(m.Name)).Concat(receiver == null ? args : new[] { receiver }.Concat(args)).ToArray(),
            };

        /// <summary>The models a collection's [Pure] member is a function of (its version aside); none for another stub's.</summary>
        public static List<ModelMap> StubModels(IMethodSymbol callee, Contract contract)
        {
            var models = IsCollection(callee.ContainingType) ? ModelsOf((INamedTypeSymbol)callee.ContainingType).Where(m => m.Name != VersionMap).ToList() : new List<ModelMap>();
            // (and the models its stub declares, that its contract reads)
            if (contract != null)
            {
                foreach (var m in contract.Requires.Concat(contract.Ensures.Select(e => e.Expr)).Where(x => x != null).SelectMany(x => Microsoft.CodeAnalysis.Operations.OperationExtensions.DescendantsAndSelf(x)).OfType<Microsoft.CodeAnalysis.Operations.IInvocationOperation>()
                             .Where(i => SpecSymbols.IsModel(i.TargetMethod.OriginalDefinition) && i.TargetMethod.IsStatic && i.Arguments.Length >= 1 && (!IsCollection(callee.ContainingType) || ModelOf(i.TargetMethod.Name, (INamedTypeSymbol)callee.ContainingType) == null))
                             .Select(i => UserModel(i.TargetMethod.OriginalDefinition)).OrderBy(x => x.Name, System.StringComparer.Ordinal))
                {
                    if (!models.Any(x => x.Name == m.Name))
                    {
                        models.Add(m);
                    }
                }
            }
            return models;
        }

        public static string StubName(IMethodSymbol m) => "lib$" + Name(m);

        /// <summary>A specification as mathematics, outside any procedure (a stub's contract, for its axioms).</summary>
        public static MExpr MathOf(KExpr e, IProgramFacts program, IMethodSymbol m)
        {
            var c = new Checks(new KProcedure { Method = m }, program);
            return c.Spec(e, out _);
        }

        // ------------------------------------------------------------------ specifications

        /// <summary>A specification as mathematics, and what makes it well-defined (each a condition, in order).</summary>
        /// <summary>The facts the last specifications read gave, taken.</summary>
        private List<MExpr> Take()
        {
            var taken = _facts.ToList();
            _facts.Clear();
            return taken;
        }

        private MExpr Spec(KExpr e, out List<MExpr> wf)
        {
            wf = new List<MExpr>();
            return Spec(e, wf, new List<MExpr>());
        }

        /// <summary>
        /// e as a formula; what makes it well-defined is added to <paramref name="wf"/>, under <paramref name="guard"/>
        /// (what &amp;&amp; || ?: make hold where it is evaluated, and the bounds of the quantifiers around it).
        /// </summary>
        private MExpr Spec(KExpr e, List<MExpr> wf, List<MExpr> guard)
        {
            void Need(MExpr cond) => wf.Add(guard.Count == 0 ? cond : new MOp("==>", And(guard), cond));
            MExpr Under(MExpr g, KExpr x)
            {
                guard.Add(g);
                try
                {
                    return Spec(x, wf, guard);
                }
                finally
                {
                    guard.RemoveAt(guard.Count - 1);
                }
            }
            switch (e)
            {
                case KLit _: case KVar _: case KFnApp _: return MathTerms.Math(e);
                case KOp { Op: "ite" } ite:
                {
                    var c = Spec(ite.Args[0], wf, guard);
                    return new MOp("ite", c, Under(c, ite.Args[1]), Under(new MOp("!", c), ite.Args[2]));
                }
                case KOp { Op: "&&" } and:
                {
                    // (the right only where the left lets it be evaluated)
                    var l = Spec(and.Args[0], wf, guard);
                    return new MOp("&&", l, Under(l, and.Args[1]));
                }
                case KOp { Op: "||" } or:
                {
                    var l = Spec(or.Args[0], wf, guard);
                    return new MOp("||", l, Under(new MOp("!", l), or.Args[1]));
                }
                case KOp { Op: "old" } old:
                {
                    // (what it needs to be well-defined, it needs in the old state too)
                    var inner = new List<MExpr>();
                    var v = Spec(old.Args[0], inner, new List<MExpr>());
                    foreach (var c in inner)
                    {
                        Need(new MOp("old", c));
                    }
                    return new MOp("old", v);
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
                    if (!Mentions(l, _bound) && !Mentions(r, _bound))
                    {
                        _facts.Add(Extensional(l, r));
                    }
                    return new MOp("==", l, r);
                }
                case KOp op:
                {
                    var args = op.Args.Select(a => Spec(a, wf, guard)).ToArray();
                    // (& and | of bools: both sides evaluated)
                    return new MOp(op.Op == "&" ? "&&" : op.Op == "|" ? "||" : op.Op, args);
                }
                case KArith ar: // (/ and %: the rest is mathematics already)
                {
                    var l = Spec(ar.Left, wf, guard);
                    var r = Spec(ar.Right, wf, guard);
                    Need(new MOp("!=", r, new MLit("0")));
                    return new MOp(ar.Op == "/" ? "div" : "rem", l, r);
                }
                case KIfc si:
                {
                    var x = Spec(si.Of, wf, guard);
                    var i = si.Index == null ? null : Spec(si.Index, wf, guard);
                    var count = MathTypes.IfcRead(x, null, si.Element);
                    Need(i == null ? new MOp("!=", x, new MLit("null")) : new MOp("&&", new MOp("!=", x, new MLit("null")), new MOp("&&", new MOp("<=", new MLit("0"), i), new MOp("<", i, count))));
                    return i == null ? count : MathTypes.IfcRead(x, i, si.Element);
                }
                case KLet let:
                {
                    var value = Spec(let.Value, wf, guard);
                    int from = wf.Count, facts = _facts.Count;
                    var body = Spec(let.Body, wf, guard);
                    // (what makes the body well-defined, and what it knows, are of the local's value too)
                    var bound = new Dictionary<string, MExpr> { [let.Var] = value };
                    for (int k = from; k < wf.Count; k++)
                    {
                        wf[k] = Subst(wf[k], bound);
                    }
                    for (int k = facts; k < _facts.Count; k++)
                    {
                        _facts[k] = Subst(_facts[k], bound);
                    }
                    // (a fact of the local's value that now names a quantifier's variable isn't one of the state: dropped)
                    for (int k = _facts.Count - 1; k >= facts; k--)
                    {
                        if (Mentions(_facts[k], _bound))
                        {
                            _facts.RemoveAt(k);
                        }
                    }
                    return Subst(body, bound);
                }
                case KMultiset ms:
                {
                    // (well-defined within the array: 0 <= n <= a.Length; its contents as of where it's read)
                    var a = Spec(ms.Array, wf, guard);
                    var n = Spec(ms.Count, wf, guard);
                    Need(new MOp("&&", new MOp("&&", new MOp("!=", a, new MLit("null")), new MOp("<=", new MLit("0"), n)), new MOp("<=", n, new MOp("len", a))));
                    MExpr fuel = new MLit("$LZ");
                    for (int k = 0; k < ms.Levels; k++)
                    {
                        fuel = new MOp("$LS", fuel);
                    }
                    return new MOp("$bag", fuel, new MOp("sel", new MVar(Elements(ms.ArrayType)), a), n);
                }
                case KElem { Model: string model } le:
                {
                    // (a collection's element, of its model: where its indexer's precondition holds)
                    var a = Spec(le.Array, wf, guard);
                    var i = Spec(le.Index, wf, guard);
                    Need(le.Domain != null
                        ? new MOp("&&", new MOp("!=", a, new MLit("null")), new MOp("sel", new MVar(le.Domain), a, i))
                        : new MOp("&&", new MOp("&&", new MOp("!=", a, new MLit("null")), new MOp("<=", new MLit("0"), i)), new MOp("<", i, new MOp("sel", new MVar(SizeMap), a))));
                    return new MOp("sel", new MVar(model), a, i);
                }
                case KElem el:
                {
                    var a = Spec(el.Array, wf, guard);
                    var i = Spec(el.Index, wf, guard);
                    Need(el.Unchecked ? (el.NoNull ? new MLit("true") : new MOp("!=", a, new MLit("null"))) : new MOp("&&", new MOp("&&", new MOp("!=", a, new MLit("null")), new MOp("<=", new MLit("0"), i)), new MOp("<", i, new MOp(el.String ? "slen" : "len", a))));
                    return el.String ? new MOp("sat", a, i) : new MOp("sel", new MVar(Elements(el.ArrayType)), a, i);
                }
                case KDataField df:
                {
                    var v = Spec(df.Value, wf, guard);
                    if (!df.Struct)
                    {
                        Need(new MOp("!=", v, new MLit("null")));
                    }
                    return new MOp(df.Function, v);
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
                    Need(new MOp("!=", a, new MLit("null")));
                    return new MOp(len.String ? "slen" : "len", a);
                }
                case KFnCall { Stub: true } st:
                {
                    MExpr receiver = null;
                    if (st.Receiver != null)
                    {
                        receiver = Spec(st.Receiver, wf, guard);
                        Need(new MOp("!=", receiver, new MLit("null")));
                    }
                    var args = st.Args.Select(a => Spec(a, wf, guard)).ToArray();
                    var given = StubGiven(st.Callee, receiver, args);
                    var saved = _facts.ToList();
                    foreach (var r in _program.Signature(st.Callee).Requires)
                    {
                        Need(Subst(Spec(r.Expr, out _), given));
                    }
                    _facts.Clear();
                    _facts.AddRange(saved);
                    _p.Stubs.Add(st.Callee);
                    return StubApp(st.Callee, receiver, args);
                }
                case KAcc acc:
                {
                    var o = Spec(acc.Obj, wf, guard);
                    return _held ? Held(o) : new MLit("true");
                }
                case KFieldAcc fa:
                {
                    var o = Spec(fa.Obj, wf, guard);
                    return _held ? CanWrite(o, fa.Field) : new MLit("true");
                }
                case KCells cl:
                {
                    var a = Spec(cl.Arr, wf, guard);
                    var lo = Spec(cl.Lo, wf, guard);
                    var hi = Spec(cl.Hi, wf, guard);
                    // (in hand, as a condition: a method that keeps no cell permissions holds every cell)
                    if (!_held || !_p.UsesCells)
                    {
                        return new MLit("true");
                    }
                    var i = new MVar("i$");
                    return MQuant.ForAll(
                        "i$",
                        Implies(new MOp("&&", new MOp("<=", lo, i), new MOp("<", i, hi)), new MOp(">=", Cell(a, i), Amount(cl.Read))));
                }
                case KInst inst:
                {
                    var q = Instance(inst.Pred, inst.Args.Select(a => Spec(a, wf, guard)).ToArray());
                    return _held ? new MOp(">=", new MOp("sel", new MVar("pinst"), q), new MLit("1")) : new MLit("true");
                }
                case KField fd:
                {
                    if (fd.Instance == null)
                    {
                        var sv = new MOp("sel", new MVar(FieldMap(fd.Field)), new MLit("null"));
                        if (NonNullField(fd.Field))
                        {
                            _facts.Add(new MOp("!=", sv, new MLit("null")));
                        }
                        return sv;
                    }
                    var o = Spec(fd.Instance, wf, guard);
                    if (!fd.OnThis && !fd.NoNull)
                    {
                        Need(new MOp("!=", o, new MLit("null")));
                    }
                    var v = new MOp("sel", new MVar(FieldMap(fd.Field)), o);
                    if (NonNullField(fd.Field) && !(_p.IsCtor && fd.OnThis) && !Mentions(o, _bound))
                    {
                        _facts.Add(new MOp("==>", new MOp("!=", o, new MLit("null")), new MOp("!=", v, new MLit("null"))));
                    }
                    if (IsRef(FieldType(fd.Field)) && !Mentions(o, _bound))
                    {
                        _facts.Add(Allocated(o, v));
                    }
                    return v;
                }
                case KQuant q when q.Range == null:
                {
                    // (over all of its type: a delegate's arguments)
                    bool added = _bound.Add(q.Var);
                    try
                    {
                        return new MQuant
                        {
                            Forall = q.Forall,
                            Var = q.Var,
                            Type = q.Type,
                            Body = Spec(q.Body, new List<MExpr>(), new List<MExpr>()),
                        };
                    }
                    finally
                    {
                        if (added)
                        {
                            _bound.Remove(q.Var);
                        }
                    }
                }
                case KQuant q:
                {
                    // (Range is lo <= q && q < hi, from Lowering)
                    var lo = Spec(((KOp)((KOp)q.Range).Args[0]).Args[0], wf, guard);
                    var hi = Spec(((KOp)((KOp)q.Range).Args[1]).Args[1], wf, guard);
                    var range = new MOp("&&", new MOp("<=", lo, new MVar(q.Var)), new MOp("<", new MVar(q.Var), hi));
                    // (its body well-defined over the range: each condition quantified the same way)
                    var inner = new List<MExpr>();
                    bool added = _bound.Add(q.Var);
                    MExpr body;
                    MExpr[] trigger = null;
                    try
                    {
                        body = Spec(q.Body, inner, new List<MExpr> { range });
                        trigger = q.Trigger?.Select(t => Spec(t, new List<MExpr>(), new List<MExpr>())).ToArray();
                    }
                    finally
                    {
                        if (added)
                        {
                            _bound.Remove(q.Var);
                        }
                    }
                    foreach (var c in inner)
                    {
                        Need(MQuant.ForAll(q.Var, c));
                    }
                    if (!Mentions(range, _bound))
                    {
                        Unfoldings(q.Var, range, body);
                    }
                    return new MQuant
                    {
                        Forall = q.Forall,
                        Var = q.Var,
                        Type = q.Type,
                        Range = range,
                        Body = body,
                        Trigger = trigger,
                    };
                }
                case KFnCall fn:
                {
                    MExpr receiver = null;
                    if (fn.Receiver != null)
                    {
                        receiver = Spec(fn.Receiver, wf, guard);
                        if (!fn.ReceiverIsThis && !IsStruct(fn.Callee.ContainingType))
                        {
                            Need(new MOp("!=", receiver, new MLit("null")));
                        }
                    }
                    var args = fn.Args.Select(a => Spec(a, wf, guard)).ToArray();
                    return FunctionApp(fn, receiver, args, Need);
                }
                default: throw new NotTranslated("in a specification: " + e.GetType().Name);
            }
        }

        /// <summary>A function's application, its receiver and arguments made: what it needs, its precondition at them.</summary>
        private MExpr FunctionApp(KFnCall fn, MExpr receiver, MExpr[] args, Action<MExpr> need)
        {
            // (well-defined where its precondition holds, at the arguments)
            var given = Given(fn.Callee, receiver, args);
            var saved = _facts.ToList();
            foreach (var r in _program.Signature(fn.Callee).Requires)
            {
                need(Subst(Spec(r.Expr, out _), given));
            }
            _facts.Clear();
            _facts.AddRange(saved);
            // (over a predicate: its value is of the instance's snapshot)
            if (_program.OverPredicate(fn.Callee) is (IMethodSymbol pred, int[] map))
            {
                return new MFnApp
                {
                    Callee = fn.Callee,
                    Function = FunctionName(fn.Callee),
                    Args = args,
                    Snap = Snap(pred, map, args),
                };
            }
            // (the fields it reads are the procedure's too: what's known of them, a reference field's object allocated, holds)
            foreach (var ff in _program.FunctionFieldSymbols(fn.Callee))
            {
                _p.Fields.Add(ff);
            }
            return new MFnApp
            {
                Callee = fn.Callee,
                Function = FunctionName(fn.Callee),
                Fields = _program.FunctionFields(fn.Callee),
                Args = (receiver == null ? args : new[] { receiver }.Concat(args)).ToArray(),
            };
        }

        /// <summary>A variable given a value (mathematics).</summary>
        internal static MExpr Rename(MExpr e, string name, MExpr value) => Subst(e, new Dictionary<string, MExpr> { [name] = value });
        internal static MExpr Rename(MExpr e, Dictionary<string, MExpr> given) => Subst(e, given);

        /// <summary>Parameters given values (mathematics in, mathematics out).</summary>
        private static MExpr Subst(MExpr e, Dictionary<string, MExpr> given) => MathTerms.Map(e, x => x is MVar v && given.TryGetValue(v.Name, out var value) ? value : null);
    }
}
