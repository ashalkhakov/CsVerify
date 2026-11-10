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
        /// <summary>The field maps a function reads (it, or the functions it calls).</summary>
        List<string> FunctionFields(IMethodSymbol m);
        /// <summary>Is the method a function too (so its value can be named)?</summary>
        bool IsFunction(IMethodSymbol m);
        /// <summary>Does the program use permissions (Spec.Acc, Spec.AccRead) at all? Then array writes are checked against cells.</summary>
        bool UsesPermissions { get; }
        /// <summary>Does the program use single-field permissions (Spec.Acc(o, nameof(C.F)))?</summary>
        bool UsesFieldPermissions { get; }
        /// <summary>A field's id, for its single-field permission.</summary>
        int FieldId(ISymbol field);
        /// <summary>
        /// A function over a predicate (its precondition holds one instance, of its parameters): the predicate, and
        /// for each of the function's parameters, the instance's argument it is. Null for any other.
        /// </summary>
        (IMethodSymbol pred, int[] arg)? OverPredicate(IMethodSymbol f);
        /// <summary>The functions over a predicate.</summary>
        IEnumerable<IMethodSymbol> FunctionsOver(IMethodSymbol pred);
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
        private readonly IProgramFacts _program;
        private List<KStmt> _out;

        private Checks(KProcedure p, IProgramFacts program) { _p = p; _program = program; }

        public static void Run(KProcedure p, IProgramFacts facts) => new Checks(p, facts).Run();

        private Check At(string id, SyntaxNode at, string message, string reportAs = null) =>
            new Check { Id = id, Message = message, Span = at.GetLocation().GetLineSpan(), Method = _p.Result, ReportAs = reportAs };

        private void Emit(KStmt s) => _out.Add(s);

        private void Assert(KExpr cond, Check check, bool notAssumedAfter = false) =>
            Emit(new KAssert { Cond = cond, Check = check, NotAssumedAfter = notAssumedAfter });

        private void Assume(KExpr cond) => Emit(new KAssume { Cond = cond });

        /// <summary>
        /// What reading a specification lets one assume (a non-nullable field of a built object isn't null), as
        /// CsVerify's engine assumes it where it reads one; quantified ones are left out.
        /// </summary>
        private readonly List<KExpr> _facts = new List<KExpr>();
        private readonly HashSet<string> _bound = new HashSet<string>();

        private void Facts()
        {
            foreach (var f in _facts) Assume(f);
            _facts.Clear();
        }

        private static KExpr Allocated(KExpr o, KExpr v) =>
            new KOp("==>", new KOp("&&", new KOp("sel", new KVar("$Alloc"), o), new KOp("!=", v, new KLit("null"))), new KOp("sel", new KVar("$Alloc"), v));

        /// <summary>A field whose value, once its object is built, is never null.</summary>
        private static bool NonNullField(ISymbol field) => !field.IsStatic && IsNullable(FieldType(field)) && NotNullable(FieldType(field));

        private static bool Mentions(KExpr e, HashSet<string> vars) => e switch
        {
            KVar v => vars.Contains(v.Name),
            KOp op => op.Args.Any(a => Mentions(a, vars)),
            KQuant q => Mentions(q.Range, vars) || Mentions(q.Body, vars),
            KFnApp f => f.Args.Any(a => Mentions(a, vars)) || f.Snap != null && Mentions(f.Snap, vars),
            _ => false,
        };

        private static KExpr And(IEnumerable<KExpr> xs)
        {
            var list = xs.ToList();
            return list.Count == 0 ? new KLit("true") : list.Aggregate((a, b) => new KOp("&&", a, b));
        }

        private void Run()
        {
            if (_p.IsPredicate) { RunPredicate(); return; }
            var m = _p.Method;
            // (what the contract gives and takes: its permissions, read from the specifications as written)
            _rawRequires = _p.Requires.Select(r => r.Expr).ToList();
            _rawEnsures = _p.Ensures.Select(e => e.Expr).ToList();
            _rawInvariants = _p.Invariants.ToDictionary(kv => kv.Key, kv => kv.Value.Select(i => (i.Expr, i.At)).ToList());
            if (_p.ReadsFrame != null)
            {
                _p.ReadsFrame = Spec(_p.ReadsFrame, out _);
                _facts.Clear();
                _p.Locals.Add(new KLocal { Name = "r$entry", Raw = "[Ref]bool" });
            }
            if (_p.Frame != null)
            {
                _p.Frame = Spec(_p.Frame, out _);
                _facts.Clear();
                _p.Locals.Add(new KLocal { Name = "w$entry", Raw = "[Ref]bool" });
                _p.Locals.Add(new KLocal { Name = "alloc$entry", Raw = "[Ref]bool" });
            }
            // cells: a method whose contract names some holds none but those it gets (it is in array mode); one that
            // exchanges some (a call, a fold) keeps them; any other holds every cell, which nothing then changes
            if (_program.UsesPermissions)
            {
                var stmts = _p.Blocks.SelectMany(b => b.Stmts).ToList();
                bool foldsCells = stmts.OfType<KFold>().Any(f => PredicateHasCells(f.Inst.Pred));
                bool callsCells(Func<KProcedure, IEnumerable<KExpr>> specs) => stmts.OfType<KCall>().Any(c => !_program.ContractOf(c.Callee).IsPure && NamesCells(specs(_program.Signature(c.Callee))));
                _p.ArrayMode = NamesCells(_rawRequires.Concat(_rawEnsures)) || foldsCells ||
                               callsCells(sig => sig.Ensures.Select(e => e.Expr).SelectMany(Atoms).OfType<KInst>().Where(q => PredicateHasCells(q.Pred)));
                _p.UsesCells = _p.ArrayMode || callsCells(sig => sig.Requires.Concat(sig.Ensures).Select(x => x.Expr));
                if (_p.UsesCells) _p.UsesPerm = true;
            }
            _p.UsesFields = _p.UsesPerm && _program.UsesFieldPermissions;
            // the contract as mathematics (each with what makes it well-defined)
            var requires = _p.Requires.Select(r => (spec: r, math: Spec(r.Expr, out var wf), wf, facts: Take())).ToList();
            var ensures = _p.Ensures.Select(e => (spec: e, math: OldAtEntry(Spec(e.Expr, out var wf)), wf, facts: Take())).ToList();
            foreach (var r in requires)
            {
                r.spec.Expr = r.math;
                r.spec.Check = At(BoogieTranslator.Aux, r.spec.At, $"precondition '{r.spec.At}' of '{m.Name}'", "CSV1001");
            }
            foreach (var e in ensures) e.spec.Expr = e.math;
            var decreases = _p.Decreases?.Select(d => Spec(d, out _)).ToList();
            if (_p.FunctionBody != null) _p.FunctionBody = Spec(_p.FunctionBody, out _);
            // (a function's axioms are about every state: what they say can't be of a procedure's snapshots)
            if (_p.FunctionBody != null && _program.OverPredicate(m) == null &&
                new[] { _p.FunctionBody }.Concat(requires.Select(r => r.math)).Concat(ensures.Select(e => e.math)).Any(x => Mentions(x, Snaps)))
                throw new NotTranslated("a function that reads a function over a predicate");
            var invariants = _p.Invariants.ToDictionary(kv => kv.Key, kv => kv.Value.Select(i => (spec: i, math: Spec(i.Expr, out var wf), wf, facts: Take())).ToList());
            var measures = _p.Measures.ToDictionary(kv => kv.Key, kv => kv.Value.Select(x => Spec(x.Expr, out _)).ToList());
            _facts.Clear();

            // at entry: the requires well-defined, in order (each under those before it)
            _out = _p.Entry;
            // (the preconditions are well-defined given what entry gives: the views received hold their invariants)
            if (_p.UsesPerm) ViewsAtEntry(grant: false);
            var before = new List<KExpr>();
            // (an abstract member: nothing of its own to check, its contract is what calls of it use)
            if (_p.Abstract) { _p.Entry.Clear(); _p.Obligations = 0; return; }
            foreach (var r in requires)
            {
                foreach (var f in r.facts) Assume(f);
                WellDefined(r.wf, r.spec.At, before);
                before.Add(r.math);
            }
            // behavioural subtyping: an override requires no more than what it overrides promises its callers, and
            // changes no more than that allows (CSV1018); checked here, where its own precondition isn't assumed
            var decl = _p.Method.DeclaringSyntaxReferences[0].GetSyntax();
            KExpr Conjunction(IEnumerable<KExpr> xs) => xs.Select(x => { var v = Spec(x, out _); _facts.Clear(); return v; }).Aggregate((KExpr)new KLit("true"), Conj);
            foreach (var (b, reqs) in _p.BaseRequires)
                Assert(new KOp("==>", Conjunction(reqs), Conjunction(_p.OwnRequires)),
                    At("CSV1018", decl, $"'{m.Name}' requires more than {b.ContainingType.Name}.{b.Name}, which it overrides, promises its callers"), true);
            foreach (var (b, frame) in _p.BaseFrames.Where(_ => _p.Frame != null))
            {
                var allowed = Conjunction(new[] { frame });
                var r = new KVar("r$");
                Assert(new KQuant { Forall = true, Var = "r$", Type = "Ref", Range = null, Body = new KOp("==>", new KOp("sel", _p.Frame, r), new KOp("sel", allowed, r)) },
                    At("CSV1018", decl, $"Spec.Modifies of '{m.Name}' might not be within that of {b.ContainingType.Name}.{b.Name}, which it overrides"), true);
            }

            _bodies = _p.Blocks.Select(b => new KBlock { Label = b.Label, Ordinal = b.Ordinal, Stmts = b.Stmts.ToList(), Jump = b.Jump }).ToList();
            foreach (var b in _p.Blocks)
            {
                var stmts = b.Stmts;
                b.Stmts = _out = new List<KStmt>();
                if (b == _p.Blocks[0] && _p.UsesPerm)
                {
                    EnterOwned();
                    foreach (var r in _rawRequires) Inhale(r, null, null);
                    // (what the preconditions say of snapshots: Boogie's requires can't name them)
                    Emit(new KAssign { Var = "psnap$entry", Value = new KVar("psnap") });
                    foreach (var r in requires.Where(r => Mentions(r.math, Snaps))) Assume(r.math);
                }
                if (b == _p.Blocks[0] && _p.ReadsFrame != null) Emit(new KAssign { Var = "r$entry", Value = _p.ReadsFrame });
                if (b == _p.Blocks[0] && _p.Frame != null)
                {
                    // (the frame as it is on entry, and what was allocated then)
                    Emit(new KAssign { Var = "w$entry", Value = _p.Frame });
                    // (a constructor's object was allocated just before it ran: new, as far as its frame is concerned)
                    Emit(new KAssign { Var = "alloc$entry", Value = _p.IsCtor ? new KOp("store", new KVar("$Alloc"), new KVar("this"), new KLit("false")) : new KVar("$Alloc") });
                }
                bool head = b.Label == $"b{b.Ordinal}";
                if (head && invariants.TryGetValue(b.Ordinal, out var invs))
                    foreach (var inv in invs)
                    {
                        foreach (var f in inv.facts) Assume(f);
                        WellDefined(inv.wf, inv.spec.At, null);
                        Assert(inv.math, At("CSV1005", inv.spec.At, $"loop invariant '{inv.spec.At}'"));
                    }
                if (head && measures.TryGetValue(b.Ordinal, out var measure))
                    for (int k = 0; k < measure.Count; k++) Emit(new KAssign { Var = $"m${b.Ordinal}${k}", Value = measure[k] });
                // a loop that exchanges permissions: what it holds at its head is what was held outside it, and its invariant's
                if (head && Exchanges(b.Ordinal))
                {
                    Emit(new KAssign { Var = "perm", Value = new KVar($"l${b.Ordinal}$perm") });
                    Emit(new KAssign { Var = "pinst", Value = new KVar($"l${b.Ordinal}$pinst") });
                    Emit(new KHavoc { Var = "owner" });
                    if (_p.UsesFields)
                    {
                        Emit(new KAssign { Var = "fperm", Value = new KVar($"l${b.Ordinal}$fperm") });
                        Emit(new KHavoc { Var = "fowner" });
                    }
                    if (_p.UsesCells)
                    {
                        Emit(new KAssign { Var = "cells", Value = new KVar($"l${b.Ordinal}$cells") });
                        Emit(new KHavoc { Var = "cowner" });
                    }
                    foreach (var (inv, _) in _rawInvariants.GetValueOrDefault(b.Ordinal) ?? new List<(KExpr, SyntaxNode)>()) Inhale(inv, null, null);
                }
                foreach (var s in stmts) Statement(s, decreases);
                switch (b.Jump)
                {
                    case KReturn ret:
                        Return(ret, ensures);
                        break;
                    case KGoto g:
                        foreach (var target in g.Targets)
                            if (target.StartsWith("b") && int.TryParse(target.Substring(1), out var into) && Exchanges(into))
                            {
                                // the invariant's permissions go round the loop: given up on each way into its head
                                foreach (var (inv, at) in _rawInvariants.GetValueOrDefault(into) ?? new List<(KExpr, SyntaxNode)>()) Exhale(inv, null, at, null);
                                if (into > b.Ordinal)
                                {
                                    Emit(new KAssign { Var = $"l${into}$perm", Value = new KVar("perm") });
                                    Emit(new KAssign { Var = $"l${into}$pinst", Value = new KVar("pinst") });
                                    if (_p.UsesCells) Emit(new KAssign { Var = $"l${into}$cells", Value = new KVar("cells") });
                                    if (_p.UsesFields) Emit(new KAssign { Var = $"l${into}$fperm", Value = new KVar("fperm") });
                                }
                                else
                                    Assert(new KLit($"(forall y: Ref :: l${into}$perm[y] ==> perm[y]) && (forall q: Inst :: pinst[q] >= l${into}$pinst[q])" +
                                                    (_p.UsesCells ? $" && (forall x$: Ref, i$: int :: cells[x$][i$] >= l${into}$cells[x$][i$])" : "") +
                                                    (_p.UsesFields ? $" && (forall y$: Ref, k$: int :: l${into}$fperm[y$][k$] ==> fperm[y$][k$])" : "")),
                                        At("CSV1016", _p.LoopSyntax.GetValueOrDefault(into) ?? _p.Method.DeclaringSyntaxReferences[0].GetSyntax(), "the loop body might use up permissions held outside it (only its invariant's go round the loop)"));
                            }
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
        private void Return(KReturn ret, List<(KSpec spec, KExpr math, List<KExpr> wf, List<KExpr> facts)> ensures)
        {
            var m = _p.Method;
            // the views given back hold their invariants again
            foreach (var param in m.Parameters.Where(x => IsView(x.Type) && x.RefKind is RefKind.Ref or RefKind.Out))
                ProveInvariant(ViewOf(param.Type), new KVar(Local(param)), ret.At, $"when the view '{param.Name}' is given back");
            if (_p.ThisIsView && !_p.IsCtor) ProveInvariant(m.ContainingType, new KVar("this"), ret.At, $"when '{m.Name}' returns");
            // a non-nullable ref or out parameter is given back not null
            foreach (var param in m.Parameters.Where(x => x.RefKind is RefKind.Ref or RefKind.Out && IsNullable(x.Type) && NotNullable(x.Type)))
                Assert(new KOp("!=", new KVar(Local(param)), new KLit("null")), At("CSV1014", ret.At, $"'{param.Name}' might be null on return, but its type '{param.Type}' is not nullable"));
            // a constructor has set the fields that may not be null (but the required ones, which its callers set)
            if (_p.IsCtor)
                foreach (var field in InstanceFields(m.ContainingType).Where(NonNullField))
                    if (!IsRequired(field) || m.GetAttributes().Any(a => a.AttributeClass?.Name == "SetsRequiredMembersAttribute"))
                        Assert(new KOp("!=", new KOp("sel", new KVar(FieldMap(field)), new KVar("this")), new KLit("null")),
                            At("CSV1014", ret.At, $"field '{field.Name}' is not nullable, but might be null when the constructor of {m.ContainingType.Name} returns"));
            if (Returns(m) != null && IsNullable(Returns(m)) && NotNullable(Returns(m)))
                Assert(new KOp("!=", new KVar("result"), new KLit("null")), At("CSV1014", ret.At, $"'{m.Name}' might return null, but its return type '{m.ReturnType}' is not nullable"));
            // the permissions the postconditions give back are in hand
            if (_p.UsesPerm)
            {
                _old = OldAtEntry;
                try { foreach (var e in _rawEnsures) Exhale(e, null, ret.At, null); }
                finally { _old = null; }
            }
            var before = new List<KExpr>();
            foreach (var e in ensures)
            {
                foreach (var f in e.facts) Assume(f);
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
                {
                    var value = Code(a.Value);
                    if (a.NotNullAt != null)
                        Assert(new KOp("!=", value, new KLit("null")), At("CSV1014", a.NotNullAt, $"'{a.NotNullAt}' might store null, but '{a.NotNullName}' is not nullable"));
                    Emit(new KAssign { Var = a.Var, Value = value });
                    return;
                }
                case KFieldStore fs:
                {
                    var value = Code(fs.Value);
                    var o = fs.Instance == null ? new KLit("null") : Code(fs.Instance);
                    if (fs.Instance != null && !fs.OnThis)
                        Assert(new KOp("!=", o, new KLit("null")), At("CSV1013", fs.At, $"'{fs.InstanceAt}' might be null in '{fs.At}'"));
                    if (fs.Instance != null && !IsOwnedField(fs.Field)) WithinFrame(o, fs.At);
                    if (IsOwnedField(fs.Field))
                        Assert(CanWrite(o, fs.Field), At("CSV1016", fs.At, $"'{fs.At}' changes an [Owned] {fs.Field.ContainingType.Name} without holding its view (Own<{fs.Field.ContainingType.Name}>, with no read shares out) or a frame lent to it"));
                    if (NonNullField(fs.Field))
                        Assert(new KOp("!=", value, new KLit("null")), At("CSV1014", fs.At, $"'{fs.At}' might store null, but field '{fs.Field.Name}' is not nullable"));
                    Emit(new KFieldStore { Field = fs.Field, Instance = o, Value = value, OnThis = fs.OnThis, At = fs.At, InstanceAt = fs.InstanceAt });
                    return;
                }
                case KOwn { Kind: "new" } own:
                {
                    // a view is made of a new object: its invariant holds, and nobody else has its view
                    var o = Code(own.Obj);
                    ProveInvariant(own.Type, o, own.At, "when its view is made");
                    Emit(new KAssign { Var = own.View, Value = o });
                    Receive(o);
                    return;
                }
                case KOwn { Kind: "fromacc" } from:
                {
                    var o = Code(from.Obj);
                    Assert(Held(o), At("CSV1016", from.At, $"'{from.At}' has no permission in hand to make a view of"));
                    Emit(new KAssign { Var = from.View, Value = o });
                    return;
                }
                case KFold fold:
                    Fold(fold);
                    return;
                case KThrow th:
                {
                    // (throwing null throws a NullReferenceException instead: CsVerify's engine checks it, but in a proof)
                    var v = Code(th.Value);
                    if (!(_p.Ghost || _p.Contract.IsPure || _p.Contract.IsLemma))
                        Assert(new KOp("!=", v, new KLit("null")), At("CSV1013", th.At, $"'{th.At}' might be null: throwing it would throw a NullReferenceException"));
                    if (th.Seen) Emit(new KAssign { Var = "ex$", Value = v });
                    return;
                }
                case KInvoke iv:
                {
                    // (a call of a delegate: not null, and it accepts the arguments; what it gives is its $post)
                    var d = Code(iv.Delegate);
                    var args = iv.Args.Select(Code).ToArray();
                    Assert(new KOp("!=", d, new KLit("null")), At("CSV1013", iv.At, $"'{iv.DelegateAt}' might be null in '{iv.At}'"));
                    Assert(new KOp("$preS." + iv.Key, new[] { d, new KOp("$state") }.Concat(args).ToArray()),
                        At("CSV1001", iv.At, $"'{iv.DelegateAt}' might not accept these arguments: say what it accepts with Spec.Requires(Spec.Pre({iv.DelegateAt}, ...))"));
                    Emit(new KInvoke { Result = iv.Result, Delegate = d, Args = args, Key = iv.Key, At = iv.At, DelegateAt = iv.DelegateAt });
                    return;
                }
                case KCheck ck:
                {
                    var cond = Spec(ck.Cond, out _);
                    _facts.Clear();
                    Assert(cond, At(ck.Id, ck.At, ck.Message), ck.NotAssumedAfter);
                    return;
                }
                case KLambda lam:
                {
                    // (its facts are mathematics of its parameters and of what never changes)
                    var r = new Dictionary<string, KExpr> { ["result"] = new KVar("q$r") };
                    foreach (var kv in lam.Rename) r[kv.Key] = kv.Value;
                    KExpr M(KExpr x) { var v = Spec(x, out _); _facts.Clear(); return Subst(v, r); }
                    Emit(new KLambda { Var = lam.Var, Key = lam.Key, Params = lam.Params, ResultType = lam.ResultType, NoChange = lam.NoChange, Steady = lam.Steady,
                                       Pre = lam.Pre == null ? null : M(lam.Pre), Posts = lam.Posts.Select(M).ToList(),
                                       PreS = lam.PreS == null ? null : M(lam.PreS), Reads = lam.Reads == null ? null : M(lam.Reads), Changes = lam.Changes == null ? null : M(lam.Changes) });
                    return;
                }
                case KAwait aw when aw.When != null:
                    Emit(new KAwait { Keep = aw.Keep, When = Code(aw.When) });
                    return;
                case KThrowExit _:
                    // leaving by an exception: its own clauses for the exception's type hold
                    foreach (var (type, cond, at) in _p.ThrowEnsures)
                    {
                        var holds = OldAtEntry(Spec(cond, out _));
                        _facts.Clear();
                        Assert(new KOp("==>", Is(new KVar("ex$"), type), holds), At("CSV1002", at, $"postcondition on throw '{at}' might not hold when '{_p.Method.Name}' throws"));
                    }
                    return;
                case KOwn { Kind: "drop" } drop:
                    Emit(new KMapUpdate { Map = "perm", Ref = Code(drop.Obj), Value = new KLit("false") });
                    return;
                case KNewObj n:
                {
                    var args = Arguments(n.Ctor, n.Args, n.ArgsAt);
                    // (a constructor exchanges permissions as any call does: about the new object, as this)
                    var sig = n.Ctor != null && _p.UsesPerm ? _program.Signature(n.Ctor) : null;
                    var given = sig == null ? null : Given(n.Ctor, new KVar(n.Var), args);
                    if (sig != null) foreach (var r in sig.Requires) Exhale(r.Expr, given, n.At, null);
                    Emit(new KNewObj { Var = n.Var, Type = n.Type, Ctor = n.Ctor, Args = args, ArgsAt = n.ArgsAt, At = n.At,
                                       Check = n.Ctor == null ? null : At("CSV1001", n.At, $"'{n.At}'") });
                    if (sig != null) foreach (var e in sig.Ensures) Inhale(e.Expr, given, null);
                    return;
                }
                case KStore st:
                {
                    var value = Code(st.Value);
                    var a = Code(st.Array);
                    var i = Code(st.Index);
                    InBounds(a, i, st.At, st.ArrayAt);
                    WithinFrame(a, st.At);
                    if (_p.UsesCells) Assert(new KOp(">=", Cell(a, i), new KLit("1.0")), At("CSV1016", st.At, $"'{st.At}' writes a cell this method has no Spec.Acc for"));
                    Emit(new KStore { Array = a, Index = i, Value = value, ArrayType = st.ArrayType, At = st.At, ArrayAt = st.ArrayAt, Checked = true });
                    return;
                }
                case KNew n:
                    Emit(new KNew { Var = n.Var, ArrayType = n.ArrayType, Size = Code(n.Size), Elements = n.Elements?.Select(Code).ToArray() });
                    // (a new array's cells are all in hand)
                    if (_p.UsesCells) Emit(new KAssign { Var = "cells", Value = new KOp("store", new KVar("cells"), new KVar(n.Var), new KLit("(lambda i$: int :: 1.0)")) });
                    return;
                case KCall c:
                    Call(c, decreases);
                    return;
                case KAssume a:
                    Emit(new KAssume { Cond = Code(a.Cond) });
                    return;
                case KSpecStmt ss:
                {
                    // (a permission as a condition: in hand)
                    _held = true;
                    KExpr term;
                    List<KExpr> wf;
                    try { term = Spec(ss.Spec, out wf); }
                    finally { _held = false; }
                    Facts();
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
            KExpr receiver = null;
            if (c.Receiver != null)
            {
                receiver = Code(c.Receiver);
                if (!c.ReceiverIsThis) Assert(new KOp("!=", receiver, new KLit("null")), At("CSV1013", c.At, $"'{c.ReceiverAt}' might be null in '{c.At}'"));
            }
            var args = Arguments(callee, c.Args, c.ArgsAt);
            Termination(c, receiver, args, decreases);
            // the views it gets are handed over: whole, their invariants holding (a method of an [Owned] class gets its receiver's)
            bool ownedReceiver = receiver != null && IsOwnedClass(callee.ContainingType) && !_program.ContractOf(callee).IsPure;
            if (ownedReceiver)
            {
                Assert(Held(receiver), At("CSV1016", c.At, $"'{c.At}' changes an [Owned] {callee.ContainingType.Name} without holding its view (Own<{callee.ContainingType.Name}>, with no read shares out) or a frame lent to it"));
                ProveInvariant(callee.ContainingType, receiver, c.At, $"when '{callee.Name}' is called on it");
            }
            foreach (var param in callee.Parameters.Where(x => IsView(x.Type) && x.RefKind != RefKind.Out))
            {
                var x = args[param.Ordinal];
                ProveInvariant(ViewOf(param.Type), x, c.ArgsAt[param.Ordinal], $"when its view is handed to '{callee.Name}'");
                Assert(Held(x), At("CSV1016", c.ArgsAt[param.Ordinal], $"'{c.ArgsAt[param.Ordinal]}' might not be whole: join its read shares back (Own.Unshare) and get back any fields given away before handing the view over"));
                Emit(new KMapUpdate { Map = "perm", Ref = x, Value = new KLit("false") });
            }
            // the permissions its preconditions ask for are given to it; what the caller keeps, the call can't change
            var sig = _program.Signature(callee);
            var given = Given(callee, receiver, args);
            bool pure = _program.ContractOf(callee).IsPure;
            // (what reading its preconditions here gives: the unfoldings of functions under their quantifiers)
            foreach (var r in sig.Requires)
            {
                _facts.Clear();
                Subst(Spec(r.Expr, out _), given);
                foreach (var f in _facts.ToList()) Assume(Subst(f, given));
                _facts.Clear();
            }
            // (a frame of ours: the callee's within it, or it changes nothing a frame would tell)
            if (_p.Frame != null && !pure)
            {
                if (sig.Frame == null)
                {
                    Emit(new KAssert { Cond = new KLit("false"), UnlessWritesArrays = callee, UnlessKind = "arrays",
                                       Check = At("CSV1017", c.At, $"'{callee.Name}' may write arrays but has no Spec.Modifies frame, so this method's Spec.Modifies cannot be checked") });
                    Emit(new KAssert { Cond = new KLit("false"), UnlessWritesArrays = callee, UnlessKind = "fields",
                                       Check = At("CSV1017", c.At, $"'{callee.Name}' may write fields but has no Spec.Modifies frame, so this method's Spec.Modifies cannot be checked") });
                }
                else
                {
                    var theirs = Subst(Spec(sig.Frame, out _), given);
                    _facts.Clear();
                    var r = new KVar("r$");
                    Emit(new KAssert
                    {
                        Cond = new KQuant { Forall = true, Var = "r$", Type = "Ref", Range = null, Body = new KOp("==>", new KOp("sel", theirs, r),
                            new KOp("||", new KOp("sel", new KVar("w$entry"), r), new KOp("!", new KOp("sel", new KVar("alloc$entry"), r)))) },
                        UnlessWritesArrays = callee, UnlessKind = "any",
                        Check = At("CSV1017", c.At, $"Spec.Modifies of '{callee.Name}' might not be within this method's"),
                    });
                }
            }
            var gave = new List<(KExpr, KExpr)>();
            if (_p.UsesPerm && !pure) foreach (var r in sig.Requires) Exhale(r.Expr, given, c.At, gave);
            bool cellCall = _p.UsesCells && !pure && NamesCells(sig.Requires.Concat(sig.Ensures).Select(x => x.Expr));
            // (in array mode, a call that may write any array: which cells it writes is unknown)
            if (_p.ArrayMode && !cellCall && !pure)
                Emit(new KAssert { Cond = new KLit("false"), UnlessWritesArrays = callee, Check = At("CSV1016", c.At, $"'{callee.Name}' may write any array: give it a contract with Spec.Acc for the cells it writes") });
            var frame = _p.UsesPerm ? new KCallFrame { Id = _frames++, Receiver = ownedReceiver ? receiver : null, Callee = callee, Cells = cellCall, Given = gave, Fields = _p.UsesFields } : null;
            // (what its preconditions say of snapshots: checked here, as Boogie's requires can't name them)
            if (_p.UsesPerm)
                foreach (var r in sig.Requires)
                {
                    var math = Subst(Spec(r.Expr, out _), given);
                    _facts.Clear();
                    if (Mentions(math, Snaps)) Assert(math, At("CSV1001", c.At, $"'{c.At}': its precondition '{r.At}'"));
                }
            // (where exceptions are seen: or it throws, and gives back only what its EnsuresOnThrow says)
            if (c.ThrowsTo != null)
                Emit(new KFork { Call = new KCall { Callee = callee, Receiver = receiver, Args = args, RefOuts = c.RefOuts }, Target = c.ThrowsTo });
            if (frame != null) Emit(frame);
            Emit(new KCall { Callee = callee, Receiver = receiver, ReceiverIsThis = c.ReceiverIsThis, ReceiverAt = c.ReceiverAt, Args = args, Result = c.Result, At = c.At, ArgsAt = c.ArgsAt,
                             RefOuts = c.RefOuts, Check = At("CSV1001", c.At, $"'{c.At}'") });
            // and the views it gives back are in hand again, their invariants holding
            foreach (var (ordinal, var) in c.RefOuts.Where(x => IsView(callee.Parameters[x.param].Type)))
            {
                var v = new KVar(var);
                Assume(new KOp("!=", v, new KLit("null")));
                AssumeInvariant(ViewOf(callee.Parameters[ordinal].Type), v);
                Receive(v);
            }
            if (ownedReceiver) AssumeInvariant(callee.ContainingType, receiver);
            if (frame != null)
            {
                Emit(new KCallFrame { Id = frame.Id, After = true, Receiver = frame.Receiver, Callee = callee, Maps = frame.Maps, Cells = frame.Cells, Given = frame.Given, ElementMaps = frame.ElementMaps, Fields = frame.Fields, FieldIds = frame.FieldIds });
                // and those its postconditions give back are in hand (its result and ref and out arguments, as they came back)
                var back = new Dictionary<string, KExpr>(given);
                if (c.Result != null) back["result"] = new KVar(c.Result);
                foreach (var (ordinal, var) in c.RefOuts) back[Local(callee.Parameters[ordinal])] = new KVar(var);
                _old = x => OldBefore(x, frame);
                try { if (!pure) foreach (var e in sig.Ensures) Inhale(e.Expr, back, null); }
                finally { _old = null; }
                foreach (var e in sig.Ensures)
                {
                    var math = Subst(Spec(e.Expr, out _), back);
                    _facts.Clear();
                    if (Mentions(math, Snaps)) Assume(OldBefore(math, frame));
                }
            }
        }

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

        private static bool HasAtoms(KExpr e) => e switch
        {
            KAcc _ => true, KInst _ => true, KCells _ => true, KFieldAcc _ => true,
            KOp op => op.Args.Any(HasAtoms),
            _ => false,
        };

        /// <summary>
        /// Walks a permission assertion left to right, as CsVerify's engine does: &amp;&amp; and the branches of ?: are
        /// followed, each permission goes to <paramref name="atom"/> under the condition it holds in, every other part
        /// is a fact. Its parameters given values by <paramref name="given"/>. Returns its facts, as a condition.
        /// </summary>
        private KExpr Walk(KExpr e, Dictionary<string, KExpr> given, KExpr guard, Action<KExpr, KExpr> atom, Action<KExpr, KExpr> fact)
        {
            KExpr M(KExpr x)
            {
                var v = Spec(x, out _);
                _facts.Clear();
                v = given == null ? v : Subst(v, given);
                return _old == null ? v : _old(v);
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
                    Refresh(Instance(inst.Pred, inst.Args), g);
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
                    Refresh(q, g);
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
        /// in its range, as CsVerify's engine says it. That quantified equation applies again to the applications in
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
                    var pre = sig.Requires.Select(r => M(r.Expr)).Aggregate((KExpr)new KLit("true"), Conj);
                    var saved = _facts.ToList();
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

        // ------------------------------------------------------------------ exceptions

        /// <summary>Is the exception of this type (any is a System.Exception)?</summary>
        internal static KExpr Is(KExpr ex, ITypeSymbol type) =>
            type.ToDisplayString() == "System.Exception" ? new KLit("true") : new KOp("sub", new KOp("dtype", ex), new KLit(TypeConst(type)));

        // ------------------------------------------------------------------ strings

        /// <summary>
        /// Two strings compared: of one length, and different, they differ at some index (a string is its characters),
        /// as CsVerify's engine says where it compares two.
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
            return stub.Parameters.Select((x, k) => (x, k)).Where(x => x.k < values.Length).ToDictionary(x => Local(x.x), x => values[x.k]);
        }

        private static KExpr StubApp(IMethodSymbol callee, KExpr receiver, KExpr[] args) =>
            new KFnApp { Callee = callee, Function = StubName(callee), Plain = true, Args = (receiver == null ? args : new[] { receiver }.Concat(args)).ToArray() };

        public static string StubName(IMethodSymbol m) => "lib$" + Name(m);

        /// <summary>A specification as mathematics, outside any procedure (a stub's contract, for its axioms).</summary>
        public static KExpr MathOf(KExpr e, IProgramFacts program, IMethodSymbol m)
        {
            var c = new Checks(new KProcedure { Method = m }, program);
            return c.Spec(e, out _);
        }

        // ------------------------------------------------------------------ functions over predicates (snapshots, as Carbon's)

        private static readonly HashSet<string> Snaps = new HashSet<string> { "psnap" };

        /// <summary>The snapshot of the instance a function over a predicate is applied to, at these arguments.</summary>
        private static KExpr Snap(IMethodSymbol pred, int[] map, KExpr[] args)
        {
            var instArgs = new KExpr[pred.Parameters.Length];
            for (int k = 0; k < map.Length; k++) instArgs[map[k]] = args[k];
            return new KOp("sel", new KVar("psnap"), Instance(pred, instArgs));
        }

        /// <summary>
        /// A new snapshot of an instance (received, or folded): nothing is known of the functions over it yet. Unless a
        /// copy is in hand already: two copies have no footprint (its permissions would be had twice), so the functions
        /// over them are the same.
        /// </summary>
        private void Refresh(KExpr q, KExpr g)
        {
            g = Conj(g, new KOp("==", new KOp("sel", new KVar("pinst"), q), new KLit("0")));
            if (!_p.Locals.Any(l => l.Name == "snap$")) _p.Locals.Add(new KLocal { Name = "snap$", Raw = "int" });
            Emit(new KHavoc { Var = "snap$" });
            Emit(new KAssign { Var = "psnap", Value = new KOp("store", new KVar("psnap"), q, Ite(g, new KVar("snap$"), new KOp("sel", new KVar("psnap"), q))) });
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
                var args = map.Select(j => instArgs[j]).ToArray();
                var given = f.Parameters.Select((x, k) => (x, k)).ToDictionary(x => Local(x.x), x => args[x.k]);
                KExpr M(KExpr x) { var v = Spec(x, out _); _facts.Clear(); return Subst(v, given); }
                var pre = sig.Requires.Select(r => M(r.Expr)).Aggregate((KExpr)new KLit("true"), Conj);
                var app = new KFnApp { Callee = f, Function = FunctionName(f), Args = args, Snap = new KOp("sel", new KVar("psnap"), p) };
                Assume(Implies(pre, new KOp("==", app, M(sig.FunctionBody))));
            }
        }

        /// <summary>old(...) of a procedure's snapshots is of those it had at entry.</summary>
        private static KExpr OldAtEntry(KExpr e) => e switch
        {
            KOp { Op: "old" } old => new KOp("old", Subst(old.Args[0], new Dictionary<string, KExpr> { ["psnap"] = new KVar("psnap$entry") })),
            KOp op => new KOp(op.Op, op.Args.Select(OldAtEntry).ToArray()),
            KQuant q => new KQuant { Forall = q.Forall, Var = q.Var, Type = q.Type, Range = q.Range == null ? null : OldAtEntry(q.Range), Body = OldAtEntry(q.Body) },
            _ => e,
        };

        /// <summary>A callee's postcondition, in the caller after the call: old(...) of its snapshots is of the caller's before it (and of nothing else, here).</summary>
        private static KExpr OldBefore(KExpr e, KCallFrame frame) => e switch
        {
            KOp { Op: "old" } old => Before(old.Args[0], frame),
            KOp op => new KOp(op.Op, op.Args.Select(a => OldBefore(a, frame)).ToArray()),
            KQuant q => new KQuant { Forall = q.Forall, Var = q.Var, Type = q.Type, Range = q.Range == null ? null : OldBefore(q.Range, frame), Body = OldBefore(q.Body, frame) },
            KFnApp f => new KFnApp { Callee = f.Callee, Function = f.Function, Layer = f.Layer, Fields = f.Fields, Args = f.Args.Select(a => OldBefore(a, frame)).ToArray(), Snap = f.Snap == null ? null : OldBefore(f.Snap, frame) },
            _ => e,
        };

        /// <summary>What a callee's old(...) reads, as it was just before the call: the snapshots the frame took then.</summary>
        private static KExpr Before(KExpr e, KCallFrame frame)
        {
            switch (e)
            {
                case KVar v when v.Name == "psnap": return new KVar($"s{frame.Id}$psnap");
                case KVar v when v.Name.StartsWith("$"):
                    frame.OldGlobals.Add(v.Name);
                    return new KVar($"s{frame.Id}{v.Name}");
                case KOp op: return new KOp(op.Op, op.Args.Select(a => Before(a, frame)).ToArray());
                case KQuant q: return new KQuant { Forall = q.Forall, Var = q.Var, Type = q.Type, Range = q.Range == null ? null : Before(q.Range, frame), Body = Before(q.Body, frame) };
                case KFnApp f when f.Snap != null: return new KFnApp { Callee = f.Callee, Function = f.Function, Args = f.Args.Select(a => Before(a, frame)).ToArray(), Snap = Before(f.Snap, frame) };
                case KFnApp _: throw new NotTranslated("a callee's postcondition that reads a function's value as it was, and a snapshot");
                default: return e;
            }
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

        /// <summary>Is cell (x, i) among c's, where g holds?</summary>
        internal static KExpr InCells(KExpr g, KCells c, KExpr x, KExpr i) =>
            Conj(g, new KOp("&&", new KOp("&&", new KOp("==", x, c.Arr), new KOp("<=", c.Lo, i)), new KOp("<", i, c.Hi)));

        private static KExpr Cell(KExpr x, KExpr i) => new KOp("sel", new KVar("cells"), x, i);

        private void ChangeCells(KExpr g, KCells c, string op)
        {
            var (x, i) = (new KVar("x$"), new KVar("i$"));
            Emit(new KAssign { Var = "cells", Value = new KOp("lambda", new KLit("x$: Ref"), new KOp("lambda", new KLit("i$: int"),
                Ite(InCells(g, c, x, i), new KOp(op, Cell(x, i), Amount(c)), Cell(x, i)))) });
        }

        private void InhaleCells(KExpr g, KCells c)
        {
            // two whole permissions to one cell can't both be in hand (a method that holds every cell learns nothing)
            if (_p.ArrayMode)
            {
                var i = new KVar("i$");
                var room = c.Read ? new KOp("<=", Cell(c.Arr, i), new KLit("1.0 - " + Share)) : new KOp("<", Cell(c.Arr, i), new KLit("1.0"));
                Assume(new KQuant { Forall = true, Var = "i$", Range = null, Body = Implies(InCells(g, c, c.Arr, i), room) });
                var lo = c.Read ? new KOp("<=", Cell(c.Arr, c.Lo), new KLit("1.0 - " + Share)) : new KOp("<", Cell(c.Arr, c.Lo), new KLit("1.0"));
                Assume(Implies(InCells(g, c, c.Arr, c.Lo), lo));
            }
            ChangeCells(g, c, "+");
        }

        private void ExhaleCells(KExpr g, KCells c, SyntaxNode at, string message)
        {
            var i = new KVar("i$");
            Assert(new KQuant { Forall = true, Var = "i$", Range = null, Body = Implies(InCells(g, c, c.Arr, i), new KOp(">=", Cell(c.Arr, i), Amount(c))) }, At("CSV1016", at, message));
            ChangeCells(g, c, "-");
        }

        /// <summary>Does a predicate's body (or one it names) hold cells?</summary>
        private bool PredicateHasCells(IMethodSymbol pred, HashSet<IMethodSymbol> seen = null)
        {
            seen ??= new HashSet<IMethodSymbol>(SymbolEqualityComparer.Default);
            if (!seen.Add(pred)) return false;
            var body = _program.Signature(pred).FunctionBody;
            return body != null && Atoms(body).Any(a => a is KCells || a is KInst q && PredicateHasCells(q.Pred, seen));
        }

        private static IEnumerable<KExpr> Atoms(KExpr e) => e switch
        {
            KCells _ or KAcc _ or KInst _ or KFieldAcc _ => new[] { e },
            KOp op => op.Args.SelectMany(Atoms),
            _ => Enumerable.Empty<KExpr>(),
        };

        /// <summary>Do these specifications name cells (directly, or in a predicate that holds some)?</summary>
        private bool NamesCells(IEnumerable<KExpr> specs) => specs.SelectMany(Atoms).Any(a => a is KCells || a is KInst q && PredicateHasCells(q.Pred));

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

        /// <summary>
        /// A predicate's own check: its body read left to right, as code (its arithmetic and reads checked, each under
        /// the conditions before it), each read of a field needing a Spec.Acc to its left (CSV1016).
        /// </summary>
        private void RunPredicate()
        {
            _out = _p.Blocks[0].Stmts;
            Emit(new KAssign { Var = "perm", Value = new KLit("(lambda o: Ref :: false)") });
            _p.UsesCells = _program.UsesPermissions;
            _p.UsesFields = _program.UsesFieldPermissions;
            if (_p.UsesFields) Emit(new KAssign { Var = "fperm", Value = new KLit("(lambda y$: Ref :: (lambda k$: int :: false))") });
            if (_p.UsesCells) Emit(new KAssign { Var = "cells", Value = new KLit("(lambda x$: Ref :: (lambda i$: int :: 0.0))") });
            CWalk(_p.FunctionBody, new KLit("true"));
            _p.FunctionBody = null;
            _p.Obligations = _p.Blocks[0].Stmts.Count(s => s is KAssert a && a.Check != null);
        }

        private KExpr CWalk(KExpr e, KExpr guard)
        {
            switch (e)
            {
                case KOp { Op: "&&" } and:
                {
                    var l = CWalk(and.Args[0], guard);
                    var r = CWalk(and.Args[1], Conj(guard, l));
                    return Conj(l, r);
                }
                case KOp { Op: "||" } or:
                {
                    var l = CWalk(or.Args[0], guard);
                    var r = CWalk(or.Args[1], Conj(guard, new KOp("!", l)));
                    return new KOp("||", l, r);
                }
                case KOp { Op: "ite" } ite:
                {
                    var c = CWalk(ite.Args[0], guard);
                    var t = CWalk(ite.Args[1], Conj(guard, c));
                    var f = CWalk(ite.Args[2], Conj(guard, new KOp("!", c)));
                    return Ite(c, t, f);
                }
                case KAcc acc:
                {
                    var o = CWalk(acc.Obj, guard);
                    // (no permission to null is ever held)
                    Assume(Implies(guard, new KOp("!=", o, new KLit("null"))));
                    SetPerm(o, new KOp("||", Held(o), guard));
                    return new KLit("true");
                }
                case KInst inst:
                    foreach (var a in inst.Args) CWalk(a, guard);
                    return new KLit("true");
                case KFieldAcc fa:
                {
                    var o = CWalk(fa.Obj, guard);
                    Assume(Implies(guard, new KOp("!=", o, new KLit("null"))));
                    if (_p.UsesFields) SetField(o, fa.Field, new KOp("||", FieldHeld(o, fa.Field), guard));
                    return new KLit("true");
                }
                case KCells cl:
                {
                    var c = new KCells { Arr = CWalk(cl.Arr, guard), Lo = CWalk(cl.Lo, guard), Hi = CWalk(cl.Hi, guard), Read = cl.Read, At = cl.At };
                    if (cl.Read) Assert(new KLit("false"), At("CSV1016", cl.At, "a predicate holds whole permissions: Spec.AccRead is for contracts"));
                    if (_p.UsesCells) ChangeCells(guard, c, "+");
                    return new KLit("true");
                }
                case KElem el:
                {
                    var a = CWalk(el.Array, guard);
                    var i = CWalk(el.Index, guard);
                    var v = Guarded(guard, () => Code(new KElem { String = el.String, Array = a, Index = i, ArrayType = el.ArrayType, At = el.At, ArrayAt = el.ArrayAt }));
                    if (_p.UsesCells && !el.String)
                        Assert(Implies(guard, new KOp(">", Cell(a, i), new KLit("0.0"))), At("CSV1016", el.At, $"'{el.At}' reads a cell this predicate has no Spec.Acc for (to its left): its value could change while the predicate is folded"));
                    return v;
                }
                case KOp op:
                    return new KOp(op.Op, op.Args.Select(a => CWalk(a, guard)).ToArray());
                case KLit _: case KVar _: return e;
                case KField fd: return Guarded(guard, () => Code(new KField { Field = fd.Field, Instance = fd.Instance == null ? null : CWalk(fd.Instance, guard), OnThis = fd.OnThis, At = fd.At, InstanceAt = fd.InstanceAt }));
                case KQuant q: return Guarded(guard, () => Code(q));
                case KFnCall fn: return Guarded(guard, () => Code(fn));
                case KLen len: return Guarded(guard, () => Code(new KLen { String = len.String, Array = CWalk(len.Array, guard), At = len.At, ArrayAt = len.ArrayAt }));
                case KArith ar: return Guarded(guard, () => Code(new KArith { Op = ar.Op, Left = CWalk(ar.Left, guard), Right = CWalk(ar.Right, guard), Type = ar.Type, Mode = ar.Mode, At = ar.At }));
                default: throw new NotTranslated("in a predicate's body: " + e.GetType().Name);
            }
        }

        /// <summary>Code's checks, each under the guard (where the code is evaluated at all).</summary>
        private KExpr Guarded(KExpr guard, Func<KExpr> code)
        {
            var outer = _out;
            _out = new List<KStmt>();
            KExpr v;
            try { v = code(); }
            finally
            {
                var inner = _out;
                _out = outer;
                foreach (var s in inner)
                    Emit(s switch
                    {
                        KAssert a => new KAssert { Cond = Implies(guard, a.Cond), Check = a.Check, NotAssumedAfter = a.NotAssumedAfter },
                        KAssume a => new KAssume { Cond = Implies(guard, a.Cond) },
                        _ => s,
                    });
            }
            return v;
        }

        // ------------------------------------------------------------------ ownership

        /// <summary>Is the object's view in hand (full permission)?</summary>
        private static KExpr Held(KExpr o) => new KOp("sel", new KVar("perm"), o);

        /// <summary>A view received: nobody else has it (views are linear), so it isn't one in hand already; now it is.</summary>
        private void Receive(KExpr o)
        {
            Assume(new KOp("!", Held(o)));
            Emit(new KMapUpdate { Map = "perm", Ref = o, Value = new KLit("true") });
        }

        /// <summary>The class's [Invariant]s of o (null if it has none).</summary>
        private KExpr Invariant(ITypeSymbol type, KExpr o)
        {
            var parts = new List<KExpr>();
            foreach (var inv in DataTypes.Invariants(type))
            {
                var m = inv.OriginalDefinition;
                if (!_program.IsFunction(m)) throw new NotTranslated("the invariant " + m.Name);
                parts.Add(new KFnApp { Callee = m, Function = FunctionName(m), Fields = _program.FunctionFields(m), Args = new[] { o } });
            }
            return parts.Count == 0 ? null : And(parts);
        }

        private void ProveInvariant(ITypeSymbol type, KExpr o, SyntaxNode at, string when)
        {
            if (Invariant(type, o) is KExpr inv) Assert(inv, At("CSV1015", at, $"invariant of {type.Name} might not hold {when}"));
        }

        private void AssumeInvariant(ITypeSymbol type, KExpr o)
        {
            if (Invariant(type, o) is KExpr inv) Assume(inv);
        }

        /// <summary>
        /// At entry: the views received are in hand (this, in a method of an [Owned] class that isn't [Pure], or its
        /// constructor; each view parameter), each not null, holding its invariant, and different from the others.
        /// </summary>
        private void EnterOwned()
        {
            Emit(new KAssign { Var = "perm", Value = new KLit("(lambda o: Ref :: false)") });
            // (no instances held yet: the preconditions bring them; who owns what is unknown)
            Emit(new KAssign { Var = "pinst", Value = new KLit("(lambda q: Inst :: 0)") });
            Emit(new KHavoc { Var = "owner" });
            Emit(new KHavoc { Var = "psnap" });
            if (_p.UsesFields)
            {
                Emit(new KAssign { Var = "fperm", Value = new KLit("(lambda y$: Ref :: (lambda k$: int :: false))") });
                Emit(new KHavoc { Var = "fowner" });
            }
            if (_p.UsesCells)
            {
                Emit(new KAssign { Var = "cells", Value = new KLit($"(lambda x$: Ref :: (lambda i$: int :: {(_p.ArrayMode ? "0.0" : "1.0")}))") });
                Emit(new KHavoc { Var = "cowner" });
            }
            if (_p.ThisIsView) Emit(new KMapUpdate { Map = "perm", Ref = new KVar("this"), Value = new KLit("true") });
            ViewsAtEntry(grant: true);
        }

        private void ViewsAtEntry(bool grant)
        {
            var m = _p.Method;
            foreach (var param in m.Parameters.Where(x => IsView(x.Type) && x.RefKind != RefKind.Out))
            {
                var v = new KVar(Local(param));
                Assume(new KOp("!=", v, new KLit("null")));
                AssumeInvariant(ViewOf(param.Type), v);
                if (grant) Receive(v);
            }
            if (_p.ThisIsView && !_p.IsCtor) AssumeInvariant(m.ContainingType, new KVar("this"));
        }

        /// <summary>A call's arguments, each checked, then not null where its parameter may not be (CSV1014).</summary>
        private KExpr[] Arguments(IMethodSymbol callee, KExpr[] given, SyntaxNode[] at)
        {
            var args = new KExpr[given.Length];
            for (int k = 0; k < args.Length; k++)
            {
                args[k] = Code(given[k]);
                var param = callee?.Parameters[k];
                if (param != null && param.RefKind != RefKind.Out && IsNullable(param.Type) && NotNullable(param.Type))
                    Assert(new KOp("!=", args[k], new KLit("null")), At("CSV1014", at[k], $"'{at[k]}' might be null, but parameter '{param.Name}' of '{callee.Name}' is not nullable"));
            }
            return args;
        }

        /// <summary>
        /// A call back into its own recursion group: the callee's measure, at the arguments, below the caller's,
        /// lexicographically (CSV1008). A [Pure] function or lemma that recurses without one doesn't terminate
        /// (CSV1011); an ordinary method needn't (partial correctness).
        /// </summary>
        private void Termination(KCall c, KExpr receiver, KExpr[] args, List<KExpr> mine)
        {
            if (!_program.Recursive(_p.Method, c.Callee)) return;
            var theirs = _program.ContractOf(c.Callee);
            if (mine != null && theirs?.Decreases != null)
            {
                var sig = _program.Signature(c.Callee);
                var given = Given(c.Callee, receiver, args);
                var next = sig.Decreases.Select(d => Subst(Spec(d, out _), given)).ToList();
                Assert(Lexicographic(next, mine), At("CSV1008", c.At,
                    $"cannot prove termination: measure '{string.Join(", ", theirs.Decreases.Select(d => d.Syntax))}' of '{c.Callee.Name}' might not decrease or might be negative"));
            }
            else if (_p.Contract.IsPure || _p.Contract.IsLemma)
                Assert(new KLit("false"), At("CSV1011", c.At, $"recursive lemma or [Pure] function '{_p.Method.Name}' needs Spec.Decreases"));
        }

        private static Dictionary<string, KExpr> Given(IMethodSymbol callee, KExpr receiver, KExpr[] args)
        {
            var given = callee.Parameters.Select((p, k) => (p, k)).ToDictionary(x => Local(x.p), x => args[x.k]);
            if (receiver != null) given["this"] = receiver;
            return given;
        }

        internal static bool IsRequired(ISymbol field) =>
            (field is IFieldSymbol f ? f.IsRequired : field is IPropertySymbol p && p.IsRequired) ||
            field.GetAttributes().Any(a => a.AttributeClass?.Name == "JsonRequiredAttribute");

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
                case KLit _: case KVar _: case KFnApp _: return e;
                case KOp { Op: "scat" } cat:
                {
                    var (l, r) = (Code(cat.Args[0]), Code(cat.Args[1]));
                    // (a concatenation too long for a string throws: the path ends)
                    Assume(new KOp("<=", new KOp("+", new KOp("sl", l), new KOp("sl", r)), new KLit("2147483647")));
                    return new KOp("scat", l, r);
                }
                case KOp { Op: "streq" } eq:
                {
                    var (l, r) = (Code(eq.Args[0]), Code(eq.Args[1]));
                    Assume(Extensional(l, r));
                    return new KOp("==", l, r);
                }
                case KOp op: return new KOp(op.Op, op.Args.Select(Code).ToArray());
                case KElem { String: true } sc:
                {
                    var s = Code(sc.Array);
                    var i = Code(sc.Index);
                    Assert(new KOp("!=", s, new KLit("null")), At("CSV1013", sc.At, $"'{sc.ArrayAt}' might be null in '{sc.At}'"));
                    Assert(new KOp("&&", new KOp("<=", new KLit("0"), i), new KOp("<", i, new KOp("slen", s))), At("CSV1003", sc.At, $"index in '{sc.At}' might be out of range"));
                    return new KOp("sat", s, i);
                }
                case KElem el:
                {
                    var a = Code(el.Array);
                    var i = Code(el.Index);
                    InBounds(a, i, el.At, el.ArrayAt);
                    return new KOp("sel", new KVar(Elements(el.ArrayType)), a, i);
                }
                case KDataField df:
                {
                    var v = Code(df.Value);
                    Assert(new KOp("!=", v, new KLit("null")), At("CSV1013", df.At, $"'{df.ValueAt}' might be null in '{df.At}'"));
                    return new KOp(df.Function, v);
                }
                case KCast cast:
                {
                    // (in code, a failing cast throws, which ends the path; a proof must show it doesn't)
                    var v = Code(cast.Value);
                    var test = Code(cast.Test);
                    if (_p.Ghost || _p.Contract.IsPure || _p.Contract.IsLemma) Assert(test, At("CSV1011", cast.At, $"cast '{cast.At}' might fail"));
                    else Assume(test);
                    return v;
                }
                case KLen len:
                {
                    var a = Code(len.Array);
                    Assert(new KOp("!=", a, new KLit("null")), At("CSV1013", len.At, $"'{len.ArrayAt}' might be null in '{len.At}'"));
                    return new KOp(len.String ? "slen" : "len", a);
                }
                case KQuant q when q.Range is KOp { Op: "&&" } range:
                {
                    // its bounds evaluated, then its body's checks, each for every value in its range (and under the guards in it)
                    var lo = Code(((KOp)range.Args[0]).Args[0]);
                    var hi = Code(((KOp)range.Args[1]).Args[1]);
                    var v = new KVar(q.Var);
                    var mathRange = new KOp("&&", new KOp("<=", lo, v), new KOp("<", v, hi));
                    var outer = _out;
                    _out = new List<KStmt>();
                    KExpr body;
                    try { body = CWalk(q.Body, mathRange); }
                    finally
                    {
                        var inner = _out;
                        _out = outer;
                        foreach (var s in inner)
                            Emit(s switch
                            {
                                KAssert a => new KAssert { Cond = new KQuant { Forall = true, Var = q.Var, Range = null, Body = a.Cond }, Check = a.Check, NotAssumedAfter = a.NotAssumedAfter },
                                KAssume a => new KAssume { Cond = new KQuant { Forall = true, Var = q.Var, Range = null, Body = a.Cond } },
                                _ => throw new NotTranslated("a quantifier whose body changes state"),
                            });
                    }
                    return new KQuant { Forall = q.Forall, Var = q.Var, Type = q.Type, Range = mathRange, Body = body };
                }
                case KFnCall fc when !fc.Stub:
                {
                    // a function's application in code (in a quantifier, a function's body): its precondition checked there
                    // (CSV1001), its value the function's
                    var mark = _out.Count;
                    var receiver = fc.Receiver == null ? null : Code(fc.Receiver);
                    var args = fc.Args.Select(Code).ToArray();
                    var app = Spec(new KFnCall { Callee = fc.Callee, Receiver = receiver, ReceiverIsThis = fc.ReceiverIsThis, ReceiverAt = fc.ReceiverAt, Args = args, At = fc.At }, out var wf);
                    _facts.Clear();
                    foreach (var w in wf) Assert(w, At("CSV1001", fc.At, $"precondition of '{fc.Callee.Name}' might not hold in '{fc.At}'"));
                    return app;
                }
                case KFnCall { Stub: true } st:
                {
                    // a library member's call: its receiver not null, its precondition holding (CSV1001); its value the function's
                    KExpr receiver = null;
                    if (st.Receiver != null)
                    {
                        receiver = Code(st.Receiver);
                        Assert(new KOp("!=", receiver, new KLit("null")), At("CSV1013", st.At, $"'{st.ReceiverAt}' might be null in '{st.At}'"));
                    }
                    var args = st.Args.Select(Code).ToArray();
                    var given = StubGiven(st.Callee, receiver, args);
                    foreach (var r in _program.Signature(st.Callee).Requires)
                    {
                        var pre = Subst(Spec(r.Expr, out _), given);
                        _facts.Clear();
                        Assert(pre, At("CSV1001", st.At, $"'{st.At}' might throw: its precondition '{r.At}' might not hold"));
                    }
                    _p.Stubs.Add(st.Callee);
                    return StubApp(st.Callee, receiver, args);
                }
                case KArith ar: return Arith(ar, Code(ar.Left), Code(ar.Right));
                case KConv cv: return Convert(cv, Code(cv.Value));
                case KField fd:
                {
                    if (fd.Instance == null) return new KOp("sel", new KVar(FieldMap(fd.Field)), new KLit("null"));
                    var o = Code(fd.Instance);
                    if (!fd.OnThis) Assert(new KOp("!=", o, new KLit("null")), At("CSV1013", fd.At, $"'{fd.InstanceAt}' might be null in '{fd.At}'"));
                    // (a function with Spec.Reads reads only objects in it, as of entry: CSV1017)
                    if (_p.ReadsFrame != null && !fd.Field.IsStatic)
                        Assert(new KOp("sel", new KVar("r$entry"), o), At("CSV1017", fd.At, $"'{fd.At}' reads an object that is not in Spec.Reads"));
                    // (in a predicate's body: read only what a Spec.Acc to its left holds, so it can't change while folded)
                    if (_p.IsPredicate)
                        Assert(CanWrite(o, fd.Field), At("CSV1016", fd.At, $"'{fd.At}' reads an object this predicate has no Spec.Acc for (to its left): its value could change while the predicate is folded"));
                    var v = new KOp("sel", new KVar(FieldMap(fd.Field)), o);
                    // (a non-nullable field of a built object: not this one's, while its constructor builds it)
                    if (NonNullField(fd.Field) && !(_p.IsCtor && fd.OnThis)) Assume(new KOp("!=", v, new KLit("null")));
                    // (a field of an allocated object refers to an allocated object, as CsVerify's engine assumes where it reads one)
                    if (IsRef(FieldType(fd.Field))) Assume(Allocated(o, v));
                    return v;
                }
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
                if (ar.ThrowsTo != null)
                    Emit(new KFork { Overflow = new KOp("!", new KOp("&&", new KOp("==", l, Number(Range(ar.Type).lo)), new KOp("==", r, new KLit("(-1)")))), Target = ar.ThrowsTo });
                // (MinValue / -1 throws in .NET, checked or not)
                Assume(new KOp("!", new KOp("&&", new KOp("==", l, Number(Range(ar.Type).lo)), new KOp("==", r, new KLit("(-1)")))));
                return new KOp(ar.Op == "/" ? "div" : "rem", l, r);
            }
            var value = new KOp(ar.Op, l, r);
            // (checked: out of range, it throws an OverflowException, which the handlers may catch)
            if (ar.ThrowsTo != null && ar.Mode == KMode.Checked) Emit(new KFork { Overflow = InRange(value, ar.Type), Target = ar.ThrowsTo });
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
                case KMode.Default when _program.CheckOverflow:
                    Assert(InRange(value, type), At("CSV1010", at, message));
                    return value;
                default:
                    Assume(InRange(value, type));
                    return value;
            }
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
                    Need(new KOp("&&", new KOp("&&", new KOp("!=", a, new KLit("null")), new KOp("<=", new KLit("0"), i)), new KOp("<", i, new KOp(el.String ? "slen" : "len", a))));
                    return el.String ? new KOp("sat", a, i) : new KOp("sel", new KVar(Elements(el.ArrayType)), a, i);
                }
                case KDataField df:
                {
                    var v = Spec(df.Value, wf, guard);
                    Need(new KOp("!=", v, new KLit("null")));
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
                    if (fd.Instance == null) return new KOp("sel", new KVar(FieldMap(fd.Field)), new KLit("null"));
                    var o = Spec(fd.Instance, wf, guard);
                    if (!fd.OnThis) Need(new KOp("!=", o, new KLit("null")));
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
                    try { body = Spec(q.Body, inner, new List<KExpr> { range }); }
                    finally { if (added) _bound.Remove(q.Var); }
                    foreach (var c in inner) Need(new KQuant { Forall = true, Var = q.Var, Range = null, Body = c });
                    if (!Mentions(range, _bound)) Unfoldings(q.Var, range, body);
                    return new KQuant { Forall = q.Forall, Var = q.Var, Type = q.Type, Range = range, Body = body };
                }
                case KFnCall fn:
                {
                    KExpr receiver = null;
                    if (fn.Receiver != null)
                    {
                        receiver = Spec(fn.Receiver, wf, guard);
                        if (!fn.ReceiverIsThis) Need(new KOp("!=", receiver, new KLit("null")));
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
                    return new KFnApp { Callee = fn.Callee, Function = FunctionName(fn.Callee), Fields = _program.FunctionFields(fn.Callee),
                                        Args = (receiver == null ? args : new[] { receiver }.Concat(args)).ToArray() };
                }
                default: throw new NotTranslated("in a specification: " + e.GetType().Name);
            }
        }

        /// <summary>A variable given a value (mathematics).</summary>
        internal static KExpr Rename(KExpr e, string name, KExpr value) => Subst(e, new Dictionary<string, KExpr> { [name] = value });

        /// <summary>Parameters given values (mathematics in, mathematics out).</summary>
        private static KExpr Subst(KExpr e, Dictionary<string, KExpr> given) => e switch
        {
            KVar v when given.TryGetValue(v.Name, out var x) => x,
            KOp op => new KOp(op.Op, op.Args.Select(a => Subst(a, given)).ToArray()),
            KQuant q => new KQuant { Forall = q.Forall, Var = q.Var, Type = q.Type, Range = q.Range == null ? null : Subst(q.Range, given), Body = Subst(q.Body, given) },
            KFnApp f => new KFnApp { Callee = f.Callee, Function = f.Function, Layer = f.Layer, Fields = f.Fields, Args = f.Args.Select(a => Subst(a, given)).ToArray(), Snap = f.Snap == null ? null : Subst(f.Snap, given) },
            _ => e,
        };
    }
}
