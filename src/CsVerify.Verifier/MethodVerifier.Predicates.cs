using System;
using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Predicates (Viper's, ATS's dataviews) over the permission mask. <c>Spec.Acc(o)</c> is write permission to an
    /// [Owned] object; a [Predicate] packages permissions and facts under a name, as an instance <c>P(args)</c>:
    /// <list type="bullet">
    /// <item>an instance has an identity (an injective function of its arguments) and an amount held (Frame.Inst);
    /// the objects of its footprint record it as their owner (Frame.Owner), with their ownership trees;</item>
    /// <item><c>Spec.Fold(P(args))</c> gives up the body's permissions (each must be in hand, the facts must hold) for
    /// the instance; <c>Spec.Unfold</c> trades it back, and the facts hold again: nobody can write a folded footprint,
    /// and a body reads only what it has permission to (checked where the predicate is declared), so they cannot
    /// have changed;</item>
    /// <item>in a contract, permissions are given up by the caller (exhaled) and received by the callee (inhaled),
    /// and back for postconditions; a call changes only what it got; in a loop invariant, they go round the loop;</item>
    /// <item>as a condition anywhere else, <c>Spec.Acc(o)</c> and <c>P(args)</c> say "in hand".</item>
    /// </list>
    /// Iso-recursive: an instance is never unfolded except by Spec.Unfold, so predicates may be recursive.
    /// </summary>
    internal sealed partial class MethodVerifier
    {
        private bool _framingCheck; // verifying a predicate's body: a field read needs a Spec.Acc before it
        private int _atomsTrue;     // evaluating a permission assertion's facts: its permissions read as true
        private readonly List<Term> _lentRoots = new List<Term>();

        internal static bool IsAccCall(IOperation op, out IInvocationOperation inv)
        {
            inv = Unconverted(op) as IInvocationOperation;
            return inv != null && SpecSymbols.IsSpecClass(inv.TargetMethod.ContainingType) && (inv.TargetMethod.Name == "Acc" || inv.TargetMethod.Name == "AccRead");
        }

        private static bool IsPredicateCall(IOperation op, out IInvocationOperation inv)
        {
            inv = Unconverted(op) as IInvocationOperation;
            return inv != null && SpecSymbols.IsPredicate(inv.TargetMethod.OriginalDefinition);
        }

        private static bool HasPermissions(IOperation op) =>
            op != null && op.DescendantsAndSelf().Any(o => IsAccCall(o, out _) || IsPredicateCall(o, out _));

        /// <summary>Does a contract give or take permissions (Spec.Acc or a predicate in a pre- or postcondition)?</summary>
        private static bool MentionsPermissions(Contract c) =>
            c.Requires.Any(HasPermissions) || c.Ensures.Any(e => HasPermissions(e.Expr));

        private Term Instance(IMethodSymbol pred, IEnumerable<Term> args) =>
            _z3.Apply("inst:" + pred.OriginalDefinition.ToDisplayString(), Sort.Int, args.Select(a => T.Coerce(a, Sort.Int)).ToArray());

        /// <summary>No instance, and no owner either: what a footprint given away is when a copy of it stays in hand.</summary>
        private Term NoInstance() => _z3.Apply("inst-none", Sort.Int, Array.Empty<Term>());

        private static Term Held(Frame f, Term q) => new Term($"(>= (select {f.Inst} {q}) 1.0)", Sort.Bool);
        private static Term OwnerOf(Frame f, Term o) => T.Select(f.Owner, T.Coerce(o, Sort.Int), Sort.Int);
        private static Term BelowWhole(Frame f, Term o) => new Term($"(< (select {f.Perm} {T.Coerce(o, Sort.Int)}) 1.0)", Sort.Bool);

        private Term Change(Term mask, Term at, Term guard, string op)
        {
            var i = T.Coerce(at, Sort.Int);
            return _z3.Define("perm", new Term($"(store {mask} {i} ({op} (select {mask} {i}) (ite {guard} 1.0 0.0)))", Sort.Perm));
        }

        /// <summary>At entry: no instances held yet (the preconditions bring them); who owns what is unknown.</summary>
        private void EnterPredicates(Frame f)
        {
            if (f.Perm == null) return;
            f.Inst = new Term("((as const (Array Int Real)) 0.0)", Sort.Perm);
            f.FPerm = new Term("((as const (Array Int (Array Int Real))) ((as const (Array Int Real)) 0.0))", Sort.PermHeap);
            f.FOwner = _z3.Fresh("fowner", Sort.Heap);
            f.Owner = _z3.Fresh("owner", Sort.Row);
            _z3.Assume(T.Not(T.Eq(NoInstance(), T.Int(0))));
            // instances are not 0 (no owner), and two are the same only if they are of one predicate with the same arguments
            int kind = 0;
            var relevant = RelevantPredicates();
            foreach (var p in _engine.Predicates)
            {
                kind++;
                if (!relevant.Contains(p)) continue; // (axioms nobody needs would only change Z3's search elsewhere)
                var xs = p.Parameters.Select((_, i) => new Term("x" + i, Sort.Int)).ToArray();
                var app = Instance(p, xs);
                var facts = new List<string> { $"(distinct {app} 0)", $"(distinct {app} {NoInstance()})", $"(= {_z3.Apply("inst-kind", Sort.Int, new[] { app })} {kind})" };
                for (int i = 0; i < xs.Length; i++)
                    facts.Add($"(= {_z3.Apply("inst-arg" + i + ":" + p.ToDisplayString(), Sort.Int, new[] { app })} x{i})");
                var body = "(and " + string.Join(" ", facts) + ")";
                _z3.Assume(new Term(xs.Length == 0 ? body
                    : $"(forall ({string.Join(" ", xs.Select(x => $"({x.S} Int)"))}) (! {body} :pattern ({app.S})))", Sort.Bool));
            }
        }

        /// <summary>
        /// The predicates this method can meet: named in its own declaration, or in the contracts of what it calls,
        /// and those named in their bodies, transitively.
        /// </summary>
        private HashSet<IMethodSymbol> RelevantPredicates()
        {
            var found = new HashSet<IMethodSymbol>(SymbolEqualityComparer.Default);
            var work = new Stack<IMethodSymbol>();
            void Named(IOperation op)
            {
                if (op == null) return;
                foreach (var inv in op.DescendantsAndSelf().OfType<IInvocationOperation>())
                    if (SpecSymbols.IsPredicate(inv.TargetMethod.OriginalDefinition) && found.Add(inv.TargetMethod.OriginalDefinition))
                        work.Push(inv.TargetMethod.OriginalDefinition);
            }
            foreach (var inv in _contract.Declaration.DescendantNodes().OfType<Microsoft.CodeAnalysis.CSharp.Syntax.InvocationExpressionSyntax>())
            {
                if (!(_model.GetSymbolInfo(inv).Symbol is IMethodSymbol m)) continue;
                if (SpecSymbols.IsPredicate(m.OriginalDefinition)) { if (found.Add(m.OriginalDefinition)) work.Push(m.OriginalDefinition); continue; }
                if (SpecSymbols.IsSpecClass(m.ContainingType) || !m.OriginalDefinition.DeclaringSyntaxReferences.Any()) continue;
                var c = _engine.ContractOf(m);
                foreach (var r in c.Requires) Named(r);
                foreach (var e in c.Ensures) Named(e.Expr);
            }
            if (SpecSymbols.IsPredicate(_method) && found.Add(_method.OriginalDefinition)) work.Push(_method.OriginalDefinition);
            while (work.Count > 0) Named(_engine.ContractOf(work.Pop()).PureBody);
            return found;
        }

        // ------------------------------------------------------------------------------------------ walking assertions

        private sealed class Atom
        {
            public Term Guard;
            public Term Obj;          // Spec.Acc(Obj)
            public ISymbol Field;     // or Spec.Acc(Obj, nameof(Field))
            public ITypeSymbol Type;
            public Term Inst;         // or a predicate instance
            public IMethodSymbol Pred; // (of this predicate)
            public Term Arr, Lo, Hi;  // or array cells: Spec.Acc(Arr, Lo, Hi)
            public bool Read;         // (Spec.AccRead: a share of them, to read)
            public SyntaxNode At;
        }

        /// <summary>
        /// Walks a permission assertion left to right: <c>&amp;&amp;</c> and the branches of <c>?:</c> are followed, each
        /// permission is passed to <paramref name="atom"/> under the condition it holds in, and every other part is a
        /// fact, passed to <paramref name="fact"/>. Returns the assertion's facts, as a condition.
        /// </summary>
        /// <param name="own">evaluate as code of this method (obligations, the framing check), not as a foreign specification</param>
        private Term Walk(IOperation e, Frame f, SpecEnv spec, Term guard, bool own, Action<Atom> atom, Action<Term, Term, SyntaxNode> fact)
        {
            var op = Unconverted(e);
            Term Value(IOperation x)
            {
                Term r = null;
                _atomsTrue++;
                try { WithGuard(guard, () => r = AsBool(own ? Eval(x, f, spec) : EvalForeignSpec(x, f, spec))); }
                finally { _atomsTrue--; }
                return r;
            }
            Term Arg(IOperation x, Term g)
            {
                Term r = null;
                WithGuard(g, () => r = own ? Eval(x, f, spec) : EvalForeignSpec(x, f, spec));
                return r;
            }
            switch (op)
            {
                case IBinaryOperation b when b.OperatorKind == BinaryOperatorKind.ConditionalAnd:
                {
                    var left = Walk(b.LeftOperand, f, spec, guard, own, atom, fact);
                    var right = Walk(b.RightOperand, f, spec, T.And(guard, left), own, atom, fact);
                    return T.And(left, right);
                }
                case IConditionalOperation c when c.WhenFalse != null && (HasPermissions(c.WhenTrue) || HasPermissions(c.WhenFalse)):
                {
                    var cond = Value(c.Condition);
                    var whenTrue = Walk(c.WhenTrue, f, spec, T.And(guard, cond), own, atom, fact);
                    var whenFalse = Walk(c.WhenFalse, f, spec, T.And(guard, T.Not(cond)), own, atom, fact);
                    return T.Ite(cond, whenTrue, whenFalse);
                }
            }
            if (IsAccCall(op, out var acc))
            {
                var target = Unconverted(acc.Arguments[0].Value);
                if (acc.TargetMethod.Name == "AccRead" && !(target.Type is IArrayTypeSymbol))
                {
                    Report("CSV1016", acc.Syntax, $"Spec.AccRead is a share of array cells; '{target.Syntax}' is not an array", isError: true);
                    return T.True;
                }
                if (target.Type is IArrayTypeSymbol)
                {
                    var arr = Arg(target, guard);
                    bool whole = acc.Arguments.Length == 1;
                    atom(new Atom
                    {
                        Guard = guard, Arr = arr, At = acc.Syntax, Read = acc.TargetMethod.Name == "AccRead",
                        Lo = whole ? T.Int(0) : Arg(acc.Arguments[1].Value, guard),
                        Hi = whole ? Len(arr) : Arg(acc.Arguments[2].Value, guard),
                    });
                    return T.True;
                }
                if (acc.Arguments.Length == 2 && SpecSymbols.IsOwned(target.Type))
                {
                    if (!(acc.Arguments[1].Value.ConstantValue is { HasValue: true, Value: string name }))
                    {
                        Report("CSV1016", acc.Syntax, "the field of Spec.Acc(o, field) must be a constant: nameof(C.F)", isError: true);
                        return T.True;
                    }
                    var field = AccField(target.Type, name, acc.Syntax);
                    if (field != null) atom(new Atom { Guard = guard, Obj = Arg(target, guard), Type = target.Type, Field = field, At = acc.Syntax });
                    return T.True;
                }
                if (!SpecSymbols.IsOwned(target.Type))
                {
                    Report("CSV1016", acc.Syntax, $"Spec.Acc is permission to an [Owned] object or to array cells; '{target.Syntax}' is neither", isError: true);
                    return T.True;
                }
                atom(new Atom { Guard = guard, Obj = Arg(target, guard), Type = target.Type, At = acc.Syntax });
                return T.True;
            }
            if (IsPredicateCall(op, out var pc))
            {
                var args = pc.Arguments.Select(a => Arg(a.Value, guard)).ToList();
                atom(new Atom { Guard = guard, Inst = Instance(pc.TargetMethod, args), Pred = pc.TargetMethod.OriginalDefinition, At = pc.Syntax });
                return T.True;
            }
            if (op is ILiteralOperation lit && lit.ConstantValue.HasValue && lit.ConstantValue.Value is true) return T.True;
            if (HasPermissions(op))
                Report("CSV1016", op.Syntax, "a permission (Spec.Acc or a predicate) may appear only as a conjunct (&&) or in a branch of ?:", isError: true);
            var v = Value(op);
            fact?.Invoke(guard, v, op.Syntax);
            return v;
        }

        /// <summary>The frame a predicate's body is read in: its parameters bound to the instance's arguments, the state of f.</summary>
        private Frame PredicateFrame(Contract pred, Term[] args, Frame f)
        {
            var pf = CalleeFrame(pred, null, args, f.Heap, f);
            pf.Perm = f.Perm;
            pf.Inst = f.Inst;
            pf.Owner = f.Owner;
            return pf;
        }

        private (Contract pred, Term[] args, Term inst) InstanceAt(IOperation arg, Frame f, SpecEnv spec, SyntaxNode at)
        {
            if (!IsPredicateCall(arg, out var pc))
            {
                Report("CSV1016", at, "Spec.Fold and Spec.Unfold take a predicate instance: a call of a [Predicate] method", isError: true);
                return (null, null, null);
            }
            var pred = _engine.ContractOf(pc.TargetMethod);
            if (pred.PureBody == null)
            {
                NotModeled(at, $"[Predicate] '{pc.TargetMethod.Name}' needs a body of one expression");
                return (null, null, null);
            }
            var args = pc.Arguments.Select(a => EvalOwnSpec(a.Value, f, spec)).ToArray();
            return (pred, args, Instance(pc.TargetMethod, args));
        }

        // ------------------------------------------------------------------------------------------ fold and unfold

        /// <summary>
        /// <c>Spec.Fold(P(args))</c>: the body's permissions go into the instance (each must be in hand, as a root of
        /// its ownership tree, not lent here), its facts must hold, and its objects' invariants (they are at rest).
        /// </summary>
        private void Fold(IInvocationOperation stmt, Frame f, SpecEnv spec)
        {
            var at = stmt.Syntax;
            var (pred, args, p) = InstanceAt(stmt.Arguments[0].Value, f, spec, at);
            if (pred == null || f.Inst == null) return;
            var pf = PredicateFrame(pred, args, f);
            Walk(pred.PureBody, pf, new SpecEnv { Old = pf }, T.True, own: false,
                atom: a =>
                {
                    if (a.Arr != null)
                    {
                        if (f.ArrPerm == null) return;
                        ExhaleCells(f, a, at);
                        FoldCells(f, a, p);
                        return;
                    }
                    if (a.Field != null)
                    {
                        NotLent(a.Obj, a.Guard, f, at);
                        GiveField(f, a.Obj, a.Field, a.Guard, at, $"folding needs '{a.At}', but that permission is not in hand here");
                        FoldField(f, a.Obj, a.Field, a.Guard, p);
                        return;
                    }
                    if (a.Obj != null)
                    {
                        Require(T.Implies(a.Guard, CanWrite(f, a.Obj)), "CSV1016", at, $"folding needs '{a.At}', but that permission is not in hand here");
                        Require(T.Implies(a.Guard, T.Eq(RootOf(f, a.Obj), a.Obj)), "CSV1016", at, $"folding needs '{a.At}', but that object is owned by another one: take it out first");
                        NotLent(a.Obj, a.Guard, f, at);
                        if (DataTypes.Invariants(a.Type).Any())
                            Prove(T.Implies(a.Guard, OwnedInvariant(a.Type, a.Obj, f)), "CSV1015", at, $"invariant of {a.Type.Name} might not hold when it is folded into '{stmt.Arguments[0].Value.Syntax}'");
                        f.Perm = Change(f.Perm, a.Obj, a.Guard, "-");
                        f.Owner = _z3.Define("owner", T.Store(f.Owner, T.Coerce(a.Obj, Sort.Int), T.Ite(a.Guard, p, OwnerOf(f, a.Obj))));
                    }
                    else
                    {
                        Require(T.Implies(a.Guard, Held(f, a.Inst)), "CSV1016", at, $"folding needs '{a.At}', which is not held here");
                        f.Inst = Change(f.Inst, a.Inst, a.Guard, "-");
                        f.Owner = _z3.Define("owner", new Term($"(lambda ((y Int)) (ite (and {a.Guard} (= (select {f.Owner} y) {a.Inst})) {p} (select {f.Owner} y)))", Sort.Row));
                        if (f.FOwner != null)
                            f.FOwner = _z3.Define("fowner", new Term($"(lambda ((y Int)) (lambda ((k Int)) (ite (and {a.Guard} (= (select (select {f.FOwner} y) k) {a.Inst})) {p} (select (select {f.FOwner} y) k))))", Sort.Heap));
                    }
                },
                fact: (g, v, node) => Require(T.Implies(g, v), "CSV1019", at, $"'{node}' might not hold when folding '{stmt.Arguments[0].Value.Syntax}'"));
            f.Inst = Change(f.Inst, p, T.True, "+");
        }

        /// <summary>
        /// <c>Spec.Unfold(P(args))</c>: the instance (held) gives its body's permissions back, and its facts hold. The
        /// objects of its footprint that are not the body's own go to the instances in the body.
        /// </summary>
        private void Unfold(IInvocationOperation stmt, Frame f, SpecEnv spec)
        {
            var at = stmt.Syntax;
            var (pred, args, p) = InstanceAt(stmt.Arguments[0].Value, f, spec, at);
            if (pred == null || f.Inst == null) return;
            Require(Held(f, p), "CSV1016", at, $"'{stmt.Arguments[0].Value.Syntax}' is not held here");
            f.Inst = Change(f.Inst, p, T.True, "-");
            var footprint = f.Owner;
            var fieldFootprint = f.FOwner;
            var cellFootprint = f.COwner;
            var ownCells = new List<Atom>();
            var ownFields = new List<(Term guard, Term obj, int field)>();
            var own = new List<(Term guard, Term obj)>();
            var nested = new List<(Term guard, Term inst)>();
            var pf = PredicateFrame(pred, args, f);
            Walk(pred.PureBody, pf, new SpecEnv { Old = pf }, T.True, own: false,
                atom: a =>
                {
                    if (a.Arr != null)
                    {
                        if (f.ArrPerm == null) return;
                        InhaleCells(f, a);
                        ownCells.Add(a);
                        return;
                    }
                    if (a.Field != null)
                    {
                        _z3.Assume(T.Implies(a.Guard, new Term($"(= (select (select {fieldFootprint} {T.Coerce(a.Obj, Sort.Int)}) {FieldId(a.Field)}) {p})", Sort.Bool)));
                        TakeField(f, a.Obj, a.Field, a.Guard);
                        ownFields.Add((a.Guard, a.Obj, FieldId(a.Field)));
                        return;
                    }
                    if (a.Obj != null)
                    {
                        _z3.Assume(T.Implies(a.Guard, T.And(NotNull(a.Obj), T.Eq(T.Select(footprint, T.Coerce(a.Obj, Sort.Int), Sort.Int), p), BelowWhole(f, a.Obj), T.Eq(RootOf(f, a.Obj), a.Obj), NoFieldsHeld(f, a.Obj, a.Type))));
                        f.Perm = Change(f.Perm, a.Obj, a.Guard, "+");
                        if (DataTypes.Invariants(a.Type).Any()) _z3.Assume(T.Implies(a.Guard, OwnedInvariant(a.Type, a.Obj, f)));
                        own.Add((a.Guard, a.Obj));
                    }
                    else
                    {
                        f.Inst = Change(f.Inst, a.Inst, a.Guard, "+");
                        nested.Add((a.Guard, a.Inst));
                    }
                },
                fact: (g, v, _) => _z3.Assume(T.Implies(g, v)));
            // the footprint is split: the body's own objects are free now, the rest belongs to one of its instances
            var choice = nested.Count > 1 ? _z3.Fresh("unfold", Sort.Row) : null;
            var to = "0";
            for (int k = nested.Count - 1; k >= 0; k--)
            {
                var pick = choice == null ? nested[k].guard.S : $"(and {nested[k].guard} (= (select {choice} y) {k}))";
                to = $"(ite {pick} {nested[k].inst} {to})";
            }
            foreach (var (guard, obj) in own) to = $"(ite (and {guard} (= y {T.Coerce(obj, Sort.Int)})) 0 {to})";
            // (an object outside p's footprint cannot be in one of the instances coming out of it: an instance with
            // objects in it is not held twice, and was in p)
            var elsewhere = nested.Count == 0 ? $"(select {footprint} y)"
                : $"(ite (or {string.Join(" ", nested.Select(n => $"(= (select {footprint} y) {n.inst})"))}) 0 (select {footprint} y))";
            f.Owner = _z3.Define("owner", new Term($"(lambda ((y Int)) (ite (= (select {footprint} y) {p}) {to} {elsewhere}))", Sort.Row));
            // cells likewise: the body's own are free, the rest go to its instances
            if (cellFootprint != null)
            {
                var cchoice = nested.Count > 1 ? _z3.Fresh("unfold", Sort.Heap) : null;
                var cto = "0";
                for (int k = nested.Count - 1; k >= 0; k--)
                {
                    var pick = cchoice == null ? nested[k].guard.S : $"(and {nested[k].guard} (= (select (select {cchoice} x) i) {k}))";
                    cto = $"(ite {pick} {nested[k].inst} {cto})";
                }
                foreach (var a in ownCells) cto = $"(ite {InCells(a, "x", "i")} 0 {cto})";
                var cold = $"(select (select {cellFootprint} x) i)";
                var celsewhere = nested.Count == 0 ? cold : $"(ite (or {string.Join(" ", nested.Select(n => $"(= {cold} {n.inst})"))}) 0 {cold})";
                f.COwner = _z3.Define("cowner", new Term($"(lambda ((x Int)) (lambda ((i Int)) (ite (= {cold} {p}) {cto} {celsewhere})))", Sort.Heap));
            }
            // single fields likewise: the body's own are free, the rest go to its instances
            if (fieldFootprint == null) return;
            var fchoice = nested.Count > 1 ? _z3.Fresh("unfold", Sort.Heap) : null;
            var fto = "0";
            for (int k = nested.Count - 1; k >= 0; k--)
            {
                var pick = fchoice == null ? nested[k].guard.S : $"(and {nested[k].guard} (= (select (select {fchoice} y) k) {k}))";
                fto = $"(ite {pick} {nested[k].inst} {fto})";
            }
            foreach (var (guard, obj, field) in ownFields) fto = $"(ite (and {guard} (= y {T.Coerce(obj, Sort.Int)}) (= k {field})) 0 {fto})";
            var fold = $"(select (select {fieldFootprint} y) k)";
            var felsewhere = nested.Count == 0 ? fold : $"(ite (or {string.Join(" ", nested.Select(n => $"(= {fold} {n.inst})"))}) 0 {fold})";
            f.FOwner = _z3.Define("fowner", new Term($"(lambda ((y Int)) (lambda ((k Int)) (ite (= {fold} {p}) {fto} {felsewhere})))", Sort.Heap));
        }

        // ------------------------------------------------------------------------------------------ contracts

        /// <summary>Receives an assertion's permissions (a precondition at entry, a callee's postcondition after the call).</summary>
        private void Inhale(IOperation e, Frame ef, SpecEnv spec, Frame f)
        {
            if (f.Inst == null && f.ArrPerm == null || !HasPermissions(e)) return;
            Walk(e, ef, spec, T.True, own: false, atom: a =>
            {
                if (a.Arr != null) { if (f.ArrPerm != null) InhaleCells(f, a); return; }
                if (f.Inst == null) return;
                if (a.Field != null) { TakeField(f, a.Obj, a.Field, a.Guard); return; }
                if (a.Obj != null)
                {
                    // two whole permissions to one object cannot both be in hand
                    _z3.Assume(T.Implies(a.Guard, T.And(NotNull(a.Obj), BelowWhole(f, a.Obj), T.Eq(RootOf(f, a.Obj), a.Obj), NoFieldsHeld(f, a.Obj, a.Type))));
                    // (and it is folded into no instance: a permission in hand is not in a footprint)
                    if (f.Owner != null) _z3.Assume(T.Implies(a.Guard, T.Eq(OwnerOf(f, a.Obj), T.Int(0))));
                    f.Perm = Change(f.Perm, a.Obj, a.Guard, "+");
                    if (DataTypes.Invariants(a.Type).Any()) _z3.Assume(T.Implies(a.Guard, OwnedInvariant(a.Type, a.Obj, f)));
                }
                else f.Inst = Change(f.Inst, a.Inst, a.Guard, "+");
            }, fact: null);
        }

        /// <summary>
        /// Gives an assertion's permissions up (a callee's precondition at the call, a postcondition at a return, a
        /// loop invariant): each must be in hand. What is given may change: its objects join <paramref name="touched"/>,
        /// its instances <paramref name="touchedInst"/>.
        /// </summary>
        /// <param name="checkOnly">only check they are in hand (a [Pure] callee reads them: nothing is given)</param>
        private void Exhale(IOperation e, Frame ef, SpecEnv spec, Frame f, SyntaxNode at, List<Term> touched, List<Term> touchedInst, List<Atom> touchedCells = null, bool checkOnly = false,
            List<(Term obj, ISymbol field)> touchedFields = null)
        {
            if (f.Inst == null && f.ArrPerm == null || !HasPermissions(e)) return;
            bool wasCode = _codeMode;
            _codeMode = true;
            try
            {
                Walk(e, ef, spec, T.True, own: false, atom: a =>
                {
                    if (a.Arr != null) { if (f.ArrPerm != null) { ExhaleCells(f, a, at); if (!a.Read) touchedCells?.Add(a); } return; }
                    if (f.Inst == null) return;
                    if (a.Field != null)
                    {
                        if (!checkOnly) NotLent(a.Obj, a.Guard, f, at);
                        GiveField(f, a.Obj, a.Field, a.Guard, at, $"'{a.At}' is needed here, but that permission is not in hand");
                        touchedFields?.Add((a.Obj, a.Field));
                        return;
                    }
                    if (a.Obj != null)
                    {
                        Require(T.Implies(a.Guard, CanWrite(f, a.Obj)), "CSV1016", at, $"'{a.At}' is needed here, but that permission is not in hand");
                        if (!checkOnly)
                        {
                            NotLent(a.Obj, a.Guard, f, at);
                            if (DataTypes.Invariants(a.Type).Any())
                                Prove(T.Implies(a.Guard, OwnedInvariant(a.Type, a.Obj, f)), "CSV1015", at, $"invariant of {a.Type.Name} might not hold when '{a.At}' is given up");
                        }
                        f.Perm = Change(f.Perm, a.Obj, a.Guard, "-");
                        touched?.Add(a.Obj);
                    }
                    else
                    {
                        Require(T.Implies(a.Guard, Held(f, a.Inst)), "CSV1016", at, $"'{a.At}' is needed here, but it is not held");
                        f.Inst = Change(f.Inst, a.Inst, a.Guard, "-");
                        // two copies of an instance in hand have no footprint (its permissions would be had twice):
                        // giving one away while the other stays changes nothing
                        var given = T.Ite(Held(f, a.Inst), NoInstance(), a.Inst);
                        touchedInst?.Add(given);
                        if (a.Pred != null && PredicateHasFields(a.Pred)) _instancesWithFields.Add(given.S);
                        if (a.Pred != null && PredicateHasCells(a.Pred)) _instancesWithCells.Add(given.S);
                    }
                }, fact: null);
            }
            finally { _codeMode = wasCode; }
        }

        /// <summary>
        /// A [Pure] callee whose preconditions name permissions reads what they cover: the caller must hold them
        /// (nothing is given). In a specification, where the state has them.
        /// </summary>
        private void CheckPurePermissions(Contract callee, Frame calleeFrame, SpecEnv env, Frame state, SyntaxNode at)
        {
            if (state?.Inst == null && state?.ArrPerm == null || !callee.Requires.Any(HasPermissions)) return;
            var probe = state.Clone();
            foreach (var req in callee.Requires) Exhale(req, calleeFrame, env, probe, at, null, null, null, checkOnly: true);
        }

        /// <summary>An object lent to this method (through Spec.Modifies(Own.Tree(..))) goes back to its lender: it cannot be folded or given away.</summary>
        private void NotLent(Term o, Term guard, Frame f, SyntaxNode at)
        {
            foreach (var root in _lentRoots)
                Require(T.Implies(guard, T.Not(T.Eq(RootOf(f, o), root))), "CSV1016", at, "that object is in a tree lent to this method: it goes back to the lender, it cannot be folded or given away");
        }

        /// <summary>
        /// A [Pure] function whose preconditions hold permissions, and that declares no Spec.Reads, reads their
        /// footprint (Viper's functions over predicates): changes elsewhere leave its value as it was.
        /// </summary>
        private static bool ReadsFootprint(Contract c) => c.IsPure && c.Reads == null && !ReadsItsTree(c) && c.Requires.Any(HasPermissions);

        /// <summary>The footprint of a function's preconditions, in the state of its frame (parameters bound).</summary>
        private Term FootprintOf(Contract c, Frame frame)
        {
            var parts = new List<string>();
            if (frame.Owner != null && frame.Root != null)
                foreach (var req in c.Requires.Where(HasPermissions))
                    Walk(req, frame, new SpecEnv { Old = frame }, T.True, own: false, atom: a => { if (a.Field != null) parts.Add($"(and {a.Guard} (= y {T.Coerce(a.Obj, Sort.Int)}))"); else if (a.Arr == null) parts.Add(a.Obj != null
                        ? $"(and {a.Guard} (= (select {frame.Root} y) {RootOf(frame, a.Obj)}))"
                        : $"(and {a.Guard} {InFootprint(frame.Owner, frame.Root, "y", a.Inst)})"); }, fact: null);
            return new Term($"(lambda ((y Int)) (ite {(parts.Count == 0 ? "false" : $"(or {string.Join(" ", parts)})")} 1 0))", Sort.Row);
        }

        /// <summary>The predicate instances a function's preconditions name are held in the frame's state (its Inst).</summary>
        private Term FootprintHeld(Contract c, Frame frame)
        {
            if (frame.Inst == null) return T.False;
            var held = new List<Term>();
            foreach (var req in c.Requires.Where(HasPermissions))
                Walk(req, frame, new SpecEnv { Old = frame }, T.True, own: false,
                    atom: a => { if (a.Inst != null) held.Add(T.Implies(a.Guard, Held(frame, a.Inst))); }, fact: null);
            return T.And(held.ToArray());
        }

        // ------------------------------------------------------------------------------------------ loops

        /// <summary>A loop that exchanges permissions: its invariant's permissions go round it, everything else stays outside.</summary>
        private bool LoopExchangesPermissions(SyntaxNode loopSyntax) =>
            (_engine.UsesOwnership || _engine.UsesPermissions) && loopSyntax.DescendantNodesAndSelf().OfType<Microsoft.CodeAnalysis.CSharp.Syntax.InvocationExpressionSyntax>()
                .Any(inv => _model.GetSymbolInfo(inv).Symbol is IMethodSymbol m &&
                            (SpecSymbols.IsSpecClass(m.ContainingType) ? m.Name == "Fold" || m.Name == "Unfold"
                             : SpecSymbols.IsCsVerifyType(m.ContainingType, "Own") ? m.Name == "ToAcc" || m.Name == "FromAcc"
                             : MentionsPermissions(_engine.ContractOf(m)) && !_engine.ContractOf(m).IsPure)); // (a [Pure] callee gives nothing)

        /// <summary>On entry: the invariant's permissions are set apart; at the head, they are what the loop holds besides the rest.</summary>
        private void LoopPermissionsEntry(int loop, IReadOnlyList<IOperation> invariants, Frame f, SpecEnv spec)
        {
            foreach (var inv in invariants) Exhale(inv, f, spec, f, inv.Syntax, null, null);
            f.LoopPermFrames[loop] = (f.Perm, f.Inst, f.ArrPerm, f.FPerm);
            if (f.FOwner != null) f.FOwner = _z3.Fresh("fowner", Sort.Heap);
            if (f.COwner != null) f.COwner = _z3.Fresh("cowner", Sort.Heap);
            f.Owner = _z3.Fresh("owner", Sort.Row);
        }

        private void LoopPermissionsHead(IReadOnlyList<IOperation> invariants, Frame f, SpecEnv spec)
        {
            foreach (var inv in invariants) Inhale(inv, f, spec, f);
        }

        /// <summary>At the back edge: the invariant's permissions are in hand, and the loop kept nothing it found outside it.</summary>
        private void LoopPermissionsBackEdge(int loop, IReadOnlyList<IOperation> invariants, Frame f, SpecEnv spec, SyntaxNode at)
        {
            var after = f.Clone();
            foreach (var inv in invariants) Exhale(inv, after, spec, after, inv.Syntax, null, null);
            var (perm, inst, arr, fperm) = f.LoopPermFrames[loop];
            var kept = new List<string>();
            if (perm != null) kept.Add($"(>= (select {after.Perm} y) (select {perm} y)) (>= (select {after.Inst} y) (select {inst} y))");
            if (fperm != null) kept.Add($"(forall ((k Int)) (>= (select (select {after.FPerm} y) k) (select (select {fperm} y) k)))");
            if (arr != null) kept.Add($"(forall ((i Int)) (>= (select (select {after.ArrPerm} y) i) (select (select {arr} y) i)))");
            if (kept.Count == 0) return;
            Prove(new Term($"(forall ((y Int)) (and {string.Join(" ", kept)}))", Sort.Bool),
                "CSV1016", at, "the loop body might use up permissions held outside it (only its invariant's go round the loop)");
        }

        // ------------------------------------------------------------------------------------------ array cells

        private bool _arrayMode; // this method's contract gives it array permissions: it holds no cells but those
        private readonly HashSet<string> _instancesWithCells = new HashSet<string>();
        private readonly Dictionary<IMethodSymbol, bool> _predicateHasCells = new Dictionary<IMethodSymbol, bool>(SymbolEqualityComparer.Default);

        internal static bool IsCellAcc(IOperation op) =>
            IsAccCall(op, out var acc) && Unconverted(acc.Arguments[0].Value).Type is IArrayTypeSymbol;

        /// <summary>Does a contract give or take array cells (Spec.Acc of an array, or a predicate holding some, in a pre- or postcondition)?</summary>
        private bool MentionsCells(Contract c) =>
            c.Requires.Concat(c.Ensures.Select(e => e.Expr)).Any(e => e != null && e.DescendantsAndSelf().Any(o =>
                IsCellAcc(o) || IsPredicateCall(o, out var pc) && PredicateHasCells(pc.TargetMethod)));

        /// <summary>
        /// Does this method fold or unfold a predicate holding cells, or get one from a call? Then it holds no cells but
        /// those it is given: holding every cell, as other methods do, it would hold the instance's twice.
        /// </summary>
        private bool HandlesCellPredicates() =>
            _contract.Declaration.DescendantNodes().OfType<Microsoft.CodeAnalysis.CSharp.Syntax.InvocationExpressionSyntax>().Any(inv =>
                _model.GetOperation(inv) is IInvocationOperation op &&
                (SpecSymbols.IsSpecClass(op.TargetMethod.ContainingType) && (op.TargetMethod.Name == "Fold" || op.TargetMethod.Name == "Unfold") &&
                 op.Arguments.Length == 1 && IsPredicateCall(op.Arguments[0].Value, out var pc) && PredicateHasCells(pc.TargetMethod) ||
                 !SpecSymbols.IsSpecClass(op.TargetMethod.ContainingType) && _engine.ContractOf(op.TargetMethod).Ensures.Any(e =>
                     e.Expr != null && e.Expr.DescendantsAndSelf().Any(o => IsPredicateCall(o, out var q) && PredicateHasCells(q.TargetMethod)))));

        /// <summary>Does a predicate's body (or one it names, transitively) hold array cells?</summary>
        private bool PredicateHasCells(IMethodSymbol pred)
        {
            pred = pred.OriginalDefinition;
            if (_predicateHasCells.TryGetValue(pred, out var known)) return known;
            _predicateHasCells[pred] = false;
            var body = _engine.ContractOf(pred).PureBody;
            bool has = body != null && body.DescendantsAndSelf().Any(o => IsCellAcc(o) || IsPredicateCall(o, out var inner) && PredicateHasCells(inner.TargetMethod));
            return _predicateHasCells[pred] = has;
        }

        private static string InCells(Atom a, string arr, string i) =>
            $"(and {a.Guard} (= {arr} {a.Arr}) (<= {a.Lo} {i}) (< {i} {a.Hi}))";

        /// <summary>At entry: a method with array permissions holds none until its preconditions give them; any other holds every cell.</summary>
        private void EnterCells(Frame f)
        {
            if (!_engine.UsesPermissions && !_engine.UsesMemory) return;
            _arrayMode = _engine.UsesPermissions && (MentionsCells(_contract) || HandlesCellPredicates());
            f.COwner = _z3.Fresh("cowner", Sort.Heap);
            f.ArrPerm = new Term($"((as const (Array Int (Array Int Real))) ((as const (Array Int Real)) {(_arrayMode ? "0.0" : "1.0")}))", Sort.PermHeap);
            // memory cells are held only through their views, whatever the method
            f.ArrPerm = T.Store(f.ArrPerm, MemRow, new Term("((as const (Array Int Real)) 0.0)", Sort.Perm));
            foreach (var p in _method.Parameters.Where(p => IsMemView(p.Type) && p.RefKind != RefKind.Out && f.Vars.ContainsKey(p)))
            {
                GrantView(f, f.Vars[p], p.Type);
                f.LiveMemViews.Add(p);
            }
        }

        private static string CellPerm(Frame f, Term arr, Term i) =>
            $"(select (select {f.ArrPerm} {T.Coerce(arr, Sort.Int)}) {T.Coerce(i, Sort.Int)})";

        private void ChangeCells(Frame f, Atom a, string op) =>
            f.ArrPerm = _z3.Define("cells", new Term($"(lambda ((x Int)) (lambda ((i Int)) (ite {InCells(a, "x", "i")} ({op} (select (select {f.ArrPerm} x) i) {CellAmount(a)}) (select (select {f.ArrPerm} x) i))))", Sort.PermHeap));

        private static string CellAmount(Atom a) => a.Read ? ShareAmount : FullAmount;

        private void InhaleCells(Frame f, Atom a)
        {
            // two whole permissions to one cell cannot both be in hand (a method without array permissions holds
            // every cell already: nothing follows there)
            if (_arrayMode)
            {
                // (a share is below what it would take to fill it up)
                var room = a.Read ? $"(- 1.0 {ShareAmount})" : "1.0";
                var op = a.Read ? "<=" : "<";
                _z3.Assume(new Term($"(forall ((i Int)) (=> {InCells(a, a.Arr.S, "i")} ({op} (select (select {f.ArrPerm} {a.Arr}) i) {room})))", Sort.Bool));
                // (and at its first cell, which no term may trigger: a cell given apart from others is none of them)
                _z3.Assume(new Term($"(=> {InCells(a, a.Arr.S, a.Lo.S)} ({op} (select (select {f.ArrPerm} {a.Arr}) {a.Lo}) {room}))", Sort.Bool));
            }
            ChangeCells(f, a, "+");
        }

        private void ExhaleCells(Frame f, Atom a, SyntaxNode at)
        {
            Require(new Term($"(forall ((i Int)) (=> {InCells(a, a.Arr.S, "i")} (>= (select (select {f.ArrPerm} {a.Arr}) i) {CellAmount(a)})))", Sort.Bool),
                "CSV1016", at, $"'{a.At}' is needed here, but those cells are not all in hand");
            ChangeCells(f, a, "-");
        }

        /// <summary>
        /// A write of a[i]: the cell must be in hand (CSV1016). A method without array permissions holds every cell,
        /// except those it gave away (to a callee, or folded into a predicate).
        /// </summary>
        private void CheckCellWrite(Term arr, Term i, Frame f, SyntaxNode at)
        {
            CheckWrite(arr, at);
            CheckCellWriteShared(arr, i, f, at);
            if (!_codeMode || _foreignSpec > 0 || f.ArrPerm == null) return;
            Require(new Term($"(>= {CellPerm(f, arr, i)} 1.0)", Sort.Bool), "CSV1016", at, $"'{at}' writes a cell this method has no Spec.Acc for");
        }

        /// <summary>A new array: all its cells are in hand, and it is none of the arrays allocated before.</summary>
        private void NewCells(Frame f, Term arr)
        {
            if (f.ArrPerm != null) f.ArrPerm = T.Store(f.ArrPerm, arr, new Term("((as const (Array Int Real)) 1.0)", Sort.Perm));
            if (f.Alloc != null)
            {
                _z3.Assume(T.Not(InSet(f.Alloc, arr)));
                f.Alloc = T.Store(f.Alloc, arr, T.Int(1));
            }
        }

        /// <summary>
        /// After a call to a method with array permissions: the cells it got may have changed, and arrays it allocated
        /// are unknown; every other cell is as it was.
        /// </summary>
        private Term HavocCells(Frame f, IReadOnlyList<Atom> cells, Term allocBefore, IReadOnlyList<Term> touchedInst)
        {
            var fresh = _z3.Fresh("heap", Sort.Heap);
            var parts = cells.Select(a => InCells(a, "x", "i")).ToList();
            // and the cells folded into the instances it got
            if (f.COwner != null)
                parts.AddRange(touchedInst.Where(q => _instancesWithCells.Contains(q.S)).Select(q => $"(= (select (select {f.COwner} x) i) {q})"));
            var changed = parts.Count == 0 ? "false" : $"(or {string.Join(" ", parts)})";
            // (a cell still in hand was given to nobody, nor folded anywhere)
            if (parts.Count > 0) changed = $"(and {changed} (< (select (select {f.ArrPerm} x) i) 1.0))";
            if (f.COwner != null)
            {
                // which instance owns a cell may change where the call got it, and in arrays it allocates
                var owned = parts.Count == 0 ? "false" : changed;
                var fresher = allocBefore != null ? $"(or {owned} (= (select {allocBefore} x) 0))" : owned;
                f.COwner = _z3.Define("cowner", new Term($"(lambda ((x Int)) (lambda ((i Int)) (ite {fresher} (select (select {_z3.Fresh("cowner", Sort.Heap)} x) i) (select (select {f.COwner} x) i))))", Sort.Heap));
            }
            var old = allocBefore != null ? $"(distinct (select {allocBefore} x) 0)" : "true";
            // a heap of its own, defined cell by cell (not a lambda term: quantified facts about the callee's cells,
            // its postconditions, are instantiated through select terms of the heap they name)
            var after = _z3.Fresh("heap", Sort.Heap);
            _z3.Assume(new Term($"(forall ((x Int) (i Int)) (! (= (select (select {after} x) i) (ite (and {old} (not {changed})) (select (select {f.Heap} x) i) (select (select {fresh} x) i))) :pattern ((select (select {after} x) i))))", Sort.Bool));
            return after;
        }

        /// <summary>Folds the cells of <paramref name="a"/> into instance p: their owner is p.</summary>
        private void FoldCells(Frame f, Atom a, Term p)
        {
            if (f.COwner == null) return;
            f.COwner = _z3.Define("cowner", new Term($"(lambda ((x Int)) (lambda ((i Int)) (ite {InCells(a, "x", "i")} {p} (select (select {f.COwner} x) i))))", Sort.Heap));
        }

        /// <summary>In a predicate's body: a read of a[i] needs a permission to the cell to its left.</summary>
        private void CheckCellFraming(Term arr, Term i, Frame f, SyntaxNode at)
        {
            if (!_framingCheck || f.ArrPerm == null) return;
            Require(new Term($"(> {CellPerm(f, arr, i)} 0.0)", Sort.Bool), "CSV1016", at,
                $"'{at}' reads a cell this predicate has no Spec.Acc for (to its left): its value could change while the predicate is folded");
        }

        // ------------------------------------------------------------------------------------------ declarations

        /// <summary>
        /// A predicate's body is checked once, where it is declared: it reads only fields of objects it has
        /// permission to, granted by a Spec.Acc to its left (self-framing), so what it says cannot change while it is folded.
        /// </summary>
        private void VerifyPredicate()
        {
            if (!_method.IsStatic || _method.ReturnType.SpecialType != SpecialType.System_Boolean || _contract.PureBody == null)
            {
                Report("CSV1016", MethodLocationNode(), $"[Predicate] '{_method.Name}' must be a static bool method whose body is one expression", isError: true);
                return;
            }
            if (!_engine.UsesOwnership) return;
            _z3.Push();
            try
            {
                var f = new Frame
                {
                    Heap = _z3.Fresh("heap", Sort.Heap),
                    Root = _z3.Fresh("root", Sort.Row),
                    Perm = new Term("((as const (Array Int Real)) 0.0)", Sort.Perm),
                };
                if (_engine.UsesPermissions)
                    f.ArrPerm = new Term("((as const (Array Int (Array Int Real))) ((as const (Array Int Real)) 0.0))", Sort.PermHeap);
                EnterPredicates(f);
                foreach (var p in _method.Parameters) f.Vars[p] = FreshOf(p.Type, p.Name);
                _codeMode = true;
                _framingCheck = true;
                Walk(_contract.PureBody, f, new SpecEnv { Old = f }, T.True, own: true,
                    atom: a =>
                    {
                        // (no permission to null is ever held)
                        if (a.Obj != null) _z3.Assume(T.Implies(a.Guard, NotNull(a.Obj)));
                        if (a.Read) Report("CSV1016", a.At, "a predicate holds whole permissions: Spec.AccRead is for contracts", isError: true);
                        if (a.Arr != null) { if (f.ArrPerm != null) ChangeCells(f, a, "+"); }
                        else if (a.Field != null) ChangeField(f, a.Obj, FieldId(a.Field), a.Guard, "+");
                        else if (a.Obj != null) f.Perm = Change(f.Perm, a.Obj, a.Guard, "+");
                    }, fact: null);
            }
            finally { _framingCheck = false; _z3.Pop(); }
        }

    }
}
