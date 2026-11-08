using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Atomic fields (<see cref="Atomics"/>). A field map's value at an atomic field is what this thread last saw or wrote
    /// there; specifications speak of that. A read in code first lets the others take steps (a fresh value, the same or a
    /// step on), and a write is proved a step from the value it replaces, which the others may also have moved: so a plain
    /// <c>x = x + 1</c> isn't one, and only <c>Interlocked</c> reads and writes in one step.
    /// </summary>
    internal sealed partial class MethodVerifier
    {
        private const string AtomicId = "CSV1030";
        private readonly HashSet<IMethodSymbol> _stepsDefined = new HashSet<IMethodSymbol>(SymbolEqualityComparer.Default);
        // inside Spec.Old: the entry state, which nothing changes after the fact
        private int _inOld;
        // the variables a loop's head has just forgotten
        private ICollection<ISymbol> _forgottenVars;

        private void CheckAtomics()
        {
            foreach (var (at, message) in _engine.Atomics.Misdeclared(_engine.Fields))
                if (_engine.Atomics.Claim(at)) Report(AtomicId, at, message, isError: true);
            foreach (var field in _engine.Atomics.SteppedBy(_method).Where(x => Atomics.StepOf(x) != null).Take(1))
                ProveTransitive(field);
        }

        /// <summary>A step after a step is a step: so what any number of other threads do between two reads is one step.</summary>
        private void ProveTransitive(IFieldSymbol field)
        {
            _z3.Push();
            try
            {
                var type = field.Type;
                Term Value(string hint)
                {
                    var v = FreshOf(type, hint);
                    if (IsIntegral(type)) _z3.Assume(T.InRange(v, RangeOf(type).lo, RangeOf(type).hi));
                    return v;
                }
                Term a = Value("a"), b = Value("b"), c = Value("c");
                Prove(T.Implies(T.And(Step(field, a, b), Step(field, b, c)), Step(field, a, c)), AtomicId, MethodLocationNode(),
                      $"step '{_method.Name}' of [Atomic] '{field.Name}' might not be transitive: two steps of other threads in a row must make one", assume: false);
            }
            finally { _z3.Pop(); }
        }

        /// <summary>Is <paramref name="now"/> one step of the field on from <paramref name="old"/>? Null when any change is.</summary>
        private Term Step(ISymbol field, Term old, Term now)
        {
            var m = Atomics.StepOf(field);
            if (m == null) return null;
            m = m.OriginalDefinition;
            var sort = SortOf(m.Parameters[0].Type);
            if (_stepsDefined.Add(m)) DefineStep(m, sort);
            return _z3.Apply("pure:" + m.ToDisplayString(), Sort.Bool, new[] { T.Coerce(old, sort), T.Coerce(now, sort) });
        }

        /// <summary>The step's definition for all values, as an axiom: it holds of values only quantifiers know (every object's).</summary>
        private void DefineStep(IMethodSymbol m, Sort sort)
        {
            Term a = new Term(_z3.FreshName("old"), sort), b = new Term(_z3.FreshName("now"), sort);
            int unfold = _unfoldDepth, quant = _quantDepth;
            _unfoldDepth = 0; _quantDepth++;
            _quantFacts.Push(new List<Term>());
            List<Term> facts;
            try { PureApply(_engine.ContractOf(m), null, new[] { a, b }, null, Sort.Bool); }
            finally { facts = _quantFacts.Pop(); _unfoldDepth = unfold; _quantDepth = quant; }
            var all = T.And(facts.ToArray());
            if (all != T.True)
                _z3.Assume(new Term($"(forall (({a.S} {T.SortName(sort)}) ({b.S} {T.SortName(sort)})) {all.S})", Sort.Bool));
        }

        private static bool IsAtomic(ISymbol field) => Atomics.IsAtomic(field);

        /// <summary>The object a constructor is building, which no other thread has yet: its fields are as it writes them.</summary>
        private bool BeingBuilt(Term o, Frame f) =>
            o != null && _method.MethodKind == MethodKind.Constructor && f.This != null && o.S == f.This.S;

        /// <summary>
        /// Let the others take their steps: the field at <paramref name="o"/> is now the same or a step on from what this
        /// thread last knew. Its new value, in range and of its type.
        /// </summary>
        private Term OthersStep(ISymbol field, Term o, Frame f)
        {
            var key = FieldEffects.Key(field);
            var map = FieldMap(f, key);
            var last = T.Select(map, o, ValueSort(field));
            var type = FieldType(field);
            var now = _z3.Fresh(field.Name + "$now", ValueSort(field));
            var typed = T.Coerce(now, SortOf(type));
            if (IsIntegral(type)) _z3.Assume(T.InRange(now, RangeOf(type).lo, RangeOf(type).hi));
            if (SortOf(type) == Sort.Bool) _z3.Assume(T.Or(T.Eq(now, T.Int(0)), T.Eq(now, T.Int(1))));
            HasType(now, type);
            AssumeNonNullRead(field, null, now);
            var step = Step(field, last, now);
            if (step != null) _z3.Assume(T.Or(T.Eq(now, last), step));
            var before = f.Clone();
            f.Fields[key] = T.Store(map, o, now);
            f.Link = new StateLink { Before = before, Changed = T.Store(T.ZeroRow(), o, T.Int(1)) };
            return typed;
        }

        /// <summary>A read of an atomic field in code: what the others have made it by now. Plain, it must be volatile.</summary>
        private void AtomicRead(ISymbol field, Term o, SyntaxNode at, Frame f)
        {
            if (!_codeMode || _inOld > 0 || BeingBuilt(o, f) || SpecSymbols.IsInGhostContext(at, _model)) return;
            if (field is IFieldSymbol x && !x.IsVolatile)
                Report(AtomicId, at, $"'{at}' reads [Atomic] '{field.Name}' plainly, which the compiler may reorder or keep from an earlier read: declare it volatile, or read it with Volatile.Read or Interlocked", isError: true);
            OthersStep(field, o ?? Statics, f);
        }

        /// <summary>A plain write of an atomic field: one step from whatever the others have made it, which this thread doesn't read first.</summary>
        private void AtomicWrite(ISymbol field, Term o, Term v, SyntaxNode at, Frame f)
        {
            if (!_codeMode || BeingBuilt(o, f) || IsInitializer(at)) return;
            if (field is IFieldSymbol x && !x.IsVolatile)
                Report(AtomicId, at, $"'{at}' writes [Atomic] '{field.Name}' plainly, which the compiler may reorder: declare it volatile, or write it with Volatile.Write or Interlocked", isError: true);
            var cur = OthersStep(field, o ?? Statics, f);
            ProveStep(field, cur, v, at, $"this write of [Atomic] '{field.Name}' might not be a step from what it overwrites, which another thread may have changed since this one read it: write it with Interlocked.CompareExchange, or a value any it could replace allows");
        }

        private static bool IsInitializer(SyntaxNode at) =>
            at is VariableDeclaratorSyntax || at.Parent is AssignmentExpressionSyntax a && a.Left == at && a.Parent is InitializerExpressionSyntax;

        private void ProveStep(ISymbol field, Term from, Term to, SyntaxNode at, string message, Term when = null)
        {
            var step = Step(field, from, to);
            if (step == null) return;
            var sort = SortOf(FieldType(field));
            var ok = T.Or(T.Eq(T.Coerce(from, sort), T.Coerce(to, sort)), step);
            Prove(T.Implies(T.And(_guards.Concat(when == null ? new Term[0] : new[] { when }).ToArray()), ok), AtomicId, at, message);
        }

        /// <summary>
        /// <c>Volatile.Read</c>/<c>Write</c> and <c>Interlocked</c>'s operations on an atomic field: each one step, taken
        /// after the others' steps. What it writes is proved a step from what it replaces. Increments wrap, as at run time.
        /// A field that isn't [Atomic] is passed by ref as to any call, which is refused.
        /// </summary>
        private Term AtomicCall(IInvocationOperation inv, Frame f, SpecEnv spec)
        {
            var m = inv.TargetMethod;
            var owner = m.ContainingType?.ToDisplayString();
            if (owner != "System.Threading.Interlocked" && owner != "System.Threading.Volatile") return null;
            if (inv.Arguments.Length == 0 || inv.Arguments[0].Parameter?.RefKind == RefKind.None) return null;
            if (!(Uncaptured(inv.Arguments[0].Value) is IFieldReferenceOperation fr)) return null;
            var field = fr.Field;
            if (!IsAtomic(field)) return null; // (a ref to a plain field: refused as any other, and in concurrent code unheld)
            if (!_codeMode) { NotModeled(inv.Syntax, $"'{inv.Syntax}' changes state: it can't be in a specification"); return Unknown(inv.Type); }
            Term o = null;
            if (!field.IsStatic)
            {
                o = Eval(fr.Instance, f, spec);
                Deref(fr.Instance, o, inv.Syntax);
            }
            var args = inv.Arguments.Skip(1).Select(a => Eval(a.Value, f, spec)).ToArray();
            var type = FieldType(field);
            var sort = SortOf(type);
            var cur = OthersStep(field, o ?? Statics, f);
            string what = $"'{inv.Syntax}' might not be a step of [Atomic] '{field.Name}'";
            void Write(Term v, Term when = null)
            {
                ProveStep(field, cur, v, inv.Syntax, what, when);
                                var key = FieldEffects.Key(field);
                var before = f.Clone();
                var written = when == null ? v : T.Ite(when, T.Coerce(v, sort), cur);
                CheckNonNullWrite(field, written, inv.Syntax);
                f.Fields[key] = T.Store(FieldMap(f, key), o ?? Statics, T.Coerce(written, ValueSort(field)));
                f.Link = new StateLink { Before = before, Changed = T.Store(T.ZeroRow(), o ?? Statics, T.Int(1)) };
            }
            Term Wrap(Term v)
            {
                var (lo, hi) = RangeOf(type);
                return new Term($"(+ (mod (- {v} {T.Int(lo)}) {T.Int(hi - lo + 1)}) {T.Int(lo)})", Sort.Int);
            }
            switch (owner == "System.Threading.Volatile" ? "Volatile." + m.Name : m.Name)
            {
                case "Volatile.Read":
                case "Read":
                    return cur;
                case "Volatile.Write":
                    Write(T.Coerce(args[0], sort));
                    return T.True;
                case "Increment":
                case "Decrement":
                case "Add":
                {
                    var delta = m.Name == "Increment" ? T.Int(1) : m.Name == "Decrement" ? T.Int(-1) : args[0];
                    var now = Wrap(T.Add(cur, delta));
                    Write(now);
                    return now;
                }
                case "Exchange":
                    Write(T.Coerce(args[0], sort));
                    return cur;
                case "CompareExchange":
                {
                    var same = T.Eq(cur, T.Coerce(args[1], sort));
                    Write(T.Coerce(args[0], sort), same);
                    return cur;
                }
                case "And":
                case "Or":
                    Write(Bitwise(m.Name == "And" ? BinaryOperatorKind.And : BinaryOperatorKind.Or, cur, args[0], type));
                    return cur;
                default:
                    NotModeled(inv.Syntax, $"'{m.Name}' of [Atomic] '{field.Name}' isn't modeled");
                    return Unknown(inv.Type);
            }
        }

        /// <summary>
        /// Wherever this thread forgets an atomic field (a call, a loop's head, an await), what it knew still went by steps:
        /// the field at each object that was there before is the same or a step on.
        /// </summary>
        private void KeepSteps(ISymbol field, Term before, Term after, Term allocBefore, IReadOnlyList<Term> held)
        {
            if (before.S == after.S || Atomics.StepOf(field) == null) return;
            var vs = ValueSort(field);
            Term At(Term map, string y) => new Term($"(select {map.S} {y})", vs);
            if (FieldEffects.IsStaticField(field))
            {
                _z3.Assume(T.Or(T.Eq(At(after, Statics.S), At(before, Statics.S)), Step(field, At(before, Statics.S), At(after, Statics.S))));
                return;
            }
            var y = _z3.FreshName("y");
            var moved = T.Or(T.Eq(At(after, y), At(before, y)), Step(field, At(before, y), At(after, y)));
            if (allocBefore != null)
                _z3.Assume(new Term($"(forall (({y} Int)) (! (=> (distinct (select {allocBefore.S} {y}) 0) {moved.S}) :pattern ((select {after.S} {y}))))", Sort.Bool));
            else
                foreach (var o in held)
                    _z3.Assume(T.Implies(NotNull(o), T.Or(T.Eq(At(after, o.S), At(before, o.S)), Step(field, At(before, o.S), At(after, o.S)))));
        }

        /// <summary>
        /// Objects that exist here, where allocation isn't tracked: this (but a constructor's own, still being made), and
        /// what the variables hold, but those in <paramref name="except"/>, which are about to be forgotten.
        /// </summary>
        private List<Term> HeldObjects(Frame f, ICollection<ISymbol> except = null)
        {
            except ??= _forgottenVars;
            var held = new List<Term>();
            if (f.This != null && _method.MethodKind != MethodKind.Constructor) held.Add(f.This);
            foreach (var kv in f.Vars)
                if ((kv.Key is ILocalSymbol || kv.Key is IParameterSymbol) && kv.Value.Sort == Sort.Int && TypeOf(kv.Key)?.IsReferenceType == true &&
                    (except == null || !except.Contains(kv.Key)) && !held.Any(h => h.S == kv.Value.S))
                    held.Add(kv.Value);
            return held;
        }

        /// <summary>The stepped atomic fields' maps as they are, to keep their steps across what forgets them.</summary>
        private List<(ISymbol field, Term map)> SteppedMaps(Frame f) =>
            _engine.Atomics.Stepped.Select(x => ((ISymbol)FieldEffects.Key(x), FieldMap(f, x))).ToList();
    }
}
