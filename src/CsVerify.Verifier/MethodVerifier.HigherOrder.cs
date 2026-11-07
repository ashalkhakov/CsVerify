using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.FlowAnalysis;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// What a delegate without a contract (a Func, an Action, a delegate type with no [ContractClassFor]) accepts and
    /// gives, as Dafny's <c>f.requires</c> and <c>f.ensures</c>: <c>Spec.Pre(f, x)</c> and <c>Spec.Post(f, x, r)</c>,
    /// functions of the delegate value and its arguments, the same in every state; <c>Spec.Total(f)</c> is Spec.Pre
    /// for every argument.
    /// <list type="bullet">
    /// <item>A call <c>f(x)</c> proves <c>Spec.Pre(f, x)</c> and gives a result r with <c>Spec.Post(f, x, r)</c>.</item>
    /// <item>No delegate is taken to be total: what one from a parameter, a field or a call accepts is what a
    /// specification says, and nothing otherwise, as in ATS.</item>
    /// <item>A lambda made a delegate defines them: its Spec.Pre is its own Spec.Requires (total without one, since its
    /// body is proved for every argument), and its Spec.Post implies what it ensures and, for an expression, its value.
    /// Both are taken only as far as they depend on its parameters and on captured variables that never change; a
    /// precondition that depends on more can't be a Spec.Pre, so it is reported (CSV1029). A method group made one
    /// gives its method's contract the same way.</item>
    /// <item>A delegate handed to a library (Task.Run, List.ForEach, a query) may be called with anything, so it must
    /// be total (CSV1029).</item>
    /// <item>A lambda knows the preconditions of the method it is in that are of what never changes (Spec.Total of a
    /// parameter never assigned): they held when it was made and still do.</item>
    /// </list>
    /// </summary>
    internal sealed partial class MethodVerifier
    {
        /// <summary>A delegate type whose calls have no contract of their own: Spec.Pre and Spec.Post speak of them.</summary>
        private bool IsPlainDelegate(ITypeSymbol t) =>
            t is INamedTypeSymbol { TypeKind: TypeKind.Delegate } d && d.DelegateInvokeMethod != null && !_engine.HasDelegateContract(d);

        private (Term[] args, Term result) DelegateSignature(INamedTypeSymbol type, IReadOnlyList<Term> args, Term result)
        {
            var invoke = type.DelegateInvokeMethod;
            var a = invoke.Parameters.Select((p, i) => T.Coerce(args[i], SortOf(p.Type))).ToArray();
            var r = invoke.ReturnsVoid || result == null ? null : T.Coerce(result, SortOf(invoke.ReturnType));
            return (a, r);
        }

        // ---- Spec.Pre, Spec.Post, Spec.Total and what they read, in a state
        //
        // Each is a function of the delegate, a state and the arguments. A steady delegate's are the same in every
        // state (what Canon stands for) and it reads nothing; one with a reads frame keeps them from one state to another
        // where the two agree on what it reads (Dafny's frame axiom).

        /// <summary>Any state: what a steady delegate's Spec.Pre and Spec.Post are in all of them.</summary>
        private static readonly Term Canon = T.Int(-1);

        private Term[] Sig(INamedTypeSymbol type, out Sort? result)
        {
            var invoke = type.DelegateInvokeMethod;
            result = invoke.ReturnsVoid ? (Sort?)null : SortOf(invoke.ReturnType);
            return invoke.Parameters.Select(p => new Term("", SortOf(p.Type))).ToArray();
        }

        private string SigKey(INamedTypeSymbol type)
        {
            var xs = Sig(type, out var r);
            return string.Join(",", xs.Select(x => x.Sort)) + "->" + (r?.ToString() ?? "void");
        }

        private Term PreAt(INamedTypeSymbol type, Term d, Term sid, IReadOnlyList<Term> args)
        {
            StateAxioms(type);
            var (a, _) = DelegateSignature(type, args, null);
            return _z3.Apply("cv_pre", Sort.Bool, new[] { T.Coerce(d, Sort.Int), sid }.Concat(a).ToArray());
        }

        private Term PostAt(INamedTypeSymbol type, Term d, Term sid, IReadOnlyList<Term> args, Term result)
        {
            StateAxioms(type);
            var (a, r) = DelegateSignature(type, args, result);
            var all = new[] { T.Coerce(d, Sort.Int), sid }.Concat(a);
            if (r != null) all = all.Append(r);
            return _z3.Apply("cv_post", Sort.Bool, all.ToArray());
        }

        private Term ReadsAt(INamedTypeSymbol type, Term d, Term sid, IReadOnlyList<Term> args)
        {
            StateAxioms(type);
            var (a, _) = DelegateSignature(type, args, null);
            return _z3.Apply("cv_dreads", Sort.Row, new[] { T.Coerce(d, Sort.Int), sid }.Concat(a).ToArray());
        }

        private Term TotalAt(INamedTypeSymbol type, Term d, Term sid)
        {
            StateAxioms(type);
            return _z3.Apply("cv_total" + type.DelegateInvokeMethod.Parameters.Length, Sort.Bool, new[] { T.Coerce(d, Sort.Int), sid });
        }

        private Term Steady(Term d) => _z3.Apply("cv_steady", Sort.Bool, new[] { T.Coerce(d, Sort.Int) });

        // the delegates known here to be steady: their Spec.Pre and Spec.Post are taken in "any state" at once, so that
        // one under a quantifier (a precondition's Spec.Forall) is the very term a call asks for
        private readonly HashSet<string> _steadyTerms = new HashSet<string>(System.StringComparer.Ordinal);

        private void AssumeSteady(Term d)
        {
            _z3.Assume(Steady(d));
            _steadyTerms.Add(T.Coerce(d, Sort.Int).S);
        }

        private Term StateFor(Term d, Frame state) => _steadyTerms.Contains(T.Coerce(d, Sort.Int).S) ? Canon : SidOf(state);

        private Term PreOf(INamedTypeSymbol type, Term d, IReadOnlyList<Term> args, Frame state) => PreAt(type, d, StateFor(d, state), args);
        private Term PostOf(INamedTypeSymbol type, Term d, IReadOnlyList<Term> args, Term result, Frame state) => PostAt(type, d, StateFor(d, state), args, result);
        private Term TotalOf(INamedTypeSymbol type, Term d, Frame state) => TotalAt(type, d, StateFor(d, state));

        /// <summary>For a signature: Spec.Total from Spec.Pre and back, and a steady delegate's being the same in every state.</summary>
        private void StateAxioms(INamedTypeSymbol type)
        {
            var key = SigKey(type);
            if (_signatures.TryAdd(key, type) && _readsFrames) foreach (var s in LiveSnapshots()) PairAxioms(s);
            _z3.AssumeOnce("delegate-states:" + key, () =>
            {
                var sorts = Sig(type, out var rs).Select(x => x.Sort).ToArray();
                var dv = new Term(_z3.FreshName("d"), Sort.Int);
                var sid = new Term(_z3.FreshName("s"), Sort.Int);
                var xs = sorts.Select(x => new Term(_z3.FreshName("x"), x)).ToArray();
                var r = rs is Sort rsort ? new Term(_z3.FreshName("r"), rsort) : null;
                Term Pre(Term state) => _z3.Apply("cv_pre", Sort.Bool, new[] { dv, state }.Concat(xs).ToArray());
                Term Post(Term state) => _z3.Apply("cv_post", Sort.Bool, (r == null ? new[] { dv, state }.Concat(xs) : new[] { dv, state }.Concat(xs).Append(r)).ToArray());
                Term Reads(Term state) => _z3.Apply("cv_dreads", Sort.Row, new[] { dv, state }.Concat(xs).ToArray());
                Term Total(Term state) => _z3.Apply("cv_total" + sorts.Length, Sort.Bool, new[] { dv, state });
                var steady = Steady(dv);
                var facts = new List<Term>
                {
                    Forall(new[] { dv, sid }.Concat(xs).ToArray(), T.Implies(Total(sid), Pre(sid)), Pre(sid)),
                    Forall(new[] { dv, sid }.Concat(xs).ToArray(), T.Implies(steady, T.Eq(Pre(sid), Pre(Canon))), Pre(sid)),
                    Forall(new[] { dv, sid }.Concat(xs).ToArray(), T.Implies(steady, T.Eq(Reads(sid), T.ZeroRow())), Reads(sid)),
                    Forall(new[] { dv, sid }, T.Implies(steady, T.Eq(Total(sid), Total(Canon))), Total(sid)),
                    Forall((r == null ? new[] { dv, sid }.Concat(xs) : new[] { dv, sid }.Concat(xs).Append(r)).ToArray(), T.Implies(steady, T.Eq(Post(sid), Post(Canon))), Post(sid)),
                };
                // and back: Spec.Pre at a witness the function picks (if it holds there, it holds everywhere)
                var witness = sorts.Select((x, i) => _z3.Apply("cv_witness" + sorts.Length + "_" + i, x, new[] { dv, sid })).ToArray();
                facts.Add(Forall(new[] { dv, sid }, T.Implies(_z3.Apply("cv_pre", Sort.Bool, new[] { dv, sid }.Concat(witness).ToArray()), Total(sid)), Total(sid)));
                return T.And(facts.ToArray());
            });
        }

        // ---- states: one number for each different state Spec.Pre and Spec.Post are taken in

        private sealed class Snapshot
        {
            public Term Sid;
            public Frame State;
            public string Key;
            public (int, long) Mark;
        }

        private readonly List<Snapshot> _snapshots = new List<Snapshot>();
        private readonly Dictionary<string, INamedTypeSymbol> _signatures = new Dictionary<string, INamedTypeSymbol>();
        private bool _readsFrames; // (some delegate here reads state: the frame axioms between states are needed)

        private IEnumerable<Snapshot> LiveSnapshots() => _snapshots.Where(x => _z3.Alive(x.Mark));

        private static string StateKey(Frame f) =>
            (f.Heap?.S ?? "") + "#" + f.FieldEpoch + "#" + string.Join(";", f.Fields.Select(kv => kv.Key.ToDisplayString() + "=" + kv.Value.S).OrderBy(x => x, System.StringComparer.Ordinal));

        /// <summary>The number of this state (the same for states that are the same).</summary>
        private Term SidOf(Frame f)
        {
            if (f == null) return Canon;
            var key = StateKey(f);
            var known = LiveSnapshots().FirstOrDefault(x => x.Key == key);
            if (known == null)
            {
                var state = f.Clone();
                foreach (var field in _engine.Fields.AllFields()) FieldMap(state, field); // (its maps now, while they are in scope)
                known = new Snapshot { Sid = _z3.Apply("cv_sid", Sort.Int, new[] { T.Int(_snapshots.Count) }), State = state, Key = key, Mark = _z3.Mark };
                _z3.Assume(T.Not(T.Eq(known.Sid, Canon)));
                _snapshots.Add(known);
            }
            if (_readsFrames) PairAxioms(known);
            return known.Sid;
        }

        /// <summary>Between this state and each other one: what a delegate reads the same in both, it accepts and gives the same.</summary>
        private void PairAxioms(Snapshot s1)
        {
            foreach (var s0 in LiveSnapshots())
            {
                if (s0 == s1) continue;
                foreach (var type in _signatures.Values)
                {
                    var key = "frame:" + s0.Sid.S + "," + s1.Sid.S + ":" + SigKey(type);
                    _z3.AssumeOnce(key, () => T.And(FrameAxiom(type, s0, s1), FrameAxiom(type, s1, s0)));
                }
            }
        }

        private Term FrameAxiom(INamedTypeSymbol type, Snapshot s0, Snapshot s1)
        {
            var sorts = Sig(type, out var rs).Select(x => x.Sort).ToArray();
            var dv = new Term(_z3.FreshName("d"), Sort.Int);
            var xs = sorts.Select(x => new Term(_z3.FreshName("x"), x)).ToArray();
            var reads0 = _z3.Apply("cv_dreads", Sort.Row, new[] { dv, s0.Sid }.Concat(xs).ToArray());
            var agree = Agree(s0.State, s1.State, reads0);
            Term Pre(Term sid) => _z3.Apply("cv_pre", Sort.Bool, new[] { dv, sid }.Concat(xs).ToArray());
            Term Reads(Term sid) => _z3.Apply("cv_dreads", Sort.Row, new[] { dv, sid }.Concat(xs).ToArray());
            var vars = new[] { dv }.Concat(xs).ToArray();
            var same = T.Implies(agree, T.And(T.Eq(Pre(s0.Sid), Pre(s1.Sid)), T.Eq(Reads(s0.Sid), Reads(s1.Sid))));
            var pre = new Term($"(forall ({string.Join(" ", vars.Select(v => $"({v.S} {T.SortName(v.Sort)})"))}) (! {same.S} :pattern ({Pre(s1.Sid).S}) :pattern ({Reads(s1.Sid).S})))", Sort.Bool);
            if (!(rs is Sort rsort)) return pre;
            var r = new Term(_z3.FreshName("r"), rsort);
            Term Post(Term sid) => _z3.Apply("cv_post", Sort.Bool, new[] { dv, sid }.Concat(xs).Append(r).ToArray());
            var all = vars.Append(r).ToArray();
            var post = Forall(all, T.Implies(agree, T.Eq(Post(s0.Sid), Post(s1.Sid))), Post(s1.Sid));
            return T.And(pre, post);
        }

        /// <summary>The two states have the same arrays and fields at the objects in <paramref name="reads"/>, and the same statics.</summary>
        private Term Agree(Frame a, Frame b, Term reads)
        {
            var parts = new List<Term>();
            var o = new Term(_z3.FreshName("o"), Sort.Int);
            var inReads = new Term($"(distinct (select {reads.S} {o.S}) 0)", Sort.Bool);
            if (a.Heap != null && b.Heap != null && a.Heap.S != b.Heap.S)
                parts.Add(T.Quant("forall", o.S, T.Implies(inReads, T.Eq(T.Select(a.Heap, o, Sort.Row), T.Select(b.Heap, o, Sort.Row)))));
            foreach (var field in _engine.Fields.AllFields())
            {
                var ma = FieldMap(a, field);
                var mb = FieldMap(b, field);
                if (ma.S == mb.S) continue;
                var sort = ValueSort(field);
                if (FieldEffects.IsStaticField(field)) parts.Add(T.Eq(T.Select(ma, T.Int(0), sort), T.Select(mb, T.Int(0), sort)));
                else parts.Add(T.Quant("forall", o.S, T.Implies(inReads, T.Eq(T.Select(ma, o, sort), T.Select(mb, o, sort)))));
            }
            return T.And(parts.ToArray());
        }

        // ---- what a delegate may change: a frame of its arguments (Spec.Changes, Spec.ChangesNothing)

        /// <summary>The objects and arrays a call of d with these arguments may change (besides what it makes).</summary>
        private Term FrameOf(INamedTypeSymbol type, Term d, IReadOnlyList<Term> args)
        {
            var (a, _) = DelegateSignature(type, args, null);
            return _z3.Apply("cv_dframe", Sort.Row, new[] { T.Coerce(d, Sort.Int) }.Concat(a).ToArray());
        }

        /// <summary>d changes nothing: its frame is empty for every argument.</summary>
        private Term NoChange(INamedTypeSymbol type, Term d)
        {
            var sorts = type.DelegateInvokeMethod.Parameters.Select(p => SortOf(p.Type)).ToArray();
            _z3.AssumeOnce("nochange:" + string.Join(",", sorts), () =>
            {
                var dv = new Term(_z3.FreshName("d"), Sort.Int);
                var xs = sorts.Select(x => new Term(_z3.FreshName("x"), x)).ToArray();
                var frame = _z3.Apply("cv_dframe", Sort.Row, new[] { dv }.Concat(xs).ToArray());
                var none = _z3.Apply("cv_nochange", Sort.Bool, new[] { dv });
                var all = new[] { dv }.Concat(xs).ToArray();
                // (without arguments, an empty frame is changing nothing, and back)
                var body = xs.Length == 0 ? T.Eq(none, T.Eq(frame, T.ZeroRow())) : T.Implies(none, T.Eq(frame, T.ZeroRow()));
                return Forall(all, body, frame);
            });
            return _z3.Apply("cv_nochange", Sort.Bool, new[] { T.Coerce(d, Sort.Int) });
        }

        /// <summary>Every call of d changes only what <paramref name="within"/> gives for its arguments.</summary>
        private Term ChangesWithin(INamedTypeSymbol type, Term d, IReadOnlyList<Term> xs, Term within)
        {
            var frame = FrameOf(type, d, xs);
            return Forall(xs, new Term($"(cv_subset {frame.S} {T.Coerce(within, Sort.Row).S})", Sort.Bool), frame);
        }

        private bool Entailed(Term t) => _z3.Check(T.Not(t)) == "unsat";

        /// <summary>Spec.ChangesNothing(f), Spec.Changes(f, x => frame), Spec.Reads(f, x => frame) in a specification.</summary>
        private Term FrameSpec(IInvocationOperation inv, Frame f, SpecEnv spec)
        {
            var first = Unconverted(inv.Arguments[0].Value);
            var type = (inv.TargetMethod.Name == "ChangesNothing" ? first.Type : inv.TargetMethod.Parameters[0].Type) as INamedTypeSymbol;
            if (type?.DelegateInvokeMethod == null) { Unsupported(inv); return _z3.Fresh("frame", Sort.Bool); }
            var d = Eval(inv.Arguments[0].Value, f, spec);
            if (inv.TargetMethod.Name == "ChangesNothing") return NoChange(type, d);
            bool reads = inv.TargetMethod.Name == "Reads";
            if (reads) _readsFrames = true;
            var sid = reads ? SidOf(f) : null;
            Term Within(IReadOnlyList<Term> xs, Term set) => reads
                ? Forall(xs, new Term($"(cv_subset {ReadsAt(type, d, sid, xs).S} {T.Coerce(set, Sort.Row).S})", Sort.Bool), ReadsAt(type, d, sid, xs))
                : ChangesWithin(type, d, xs, set);
            var given = inv.Arguments[1].Value;
            if (!(Unconverted(given) is IDelegateCreationOperation dc && DelegateTarget(dc.Target) is IMethodSymbol fn && fn.MethodKind == MethodKind.AnonymousFunction))
                return Within(new Term[0], Eval(given, f, spec)); // (no arguments: the frame itself)
            var body = ValueOf(fn);
            if (body == null) { Unsupported(inv); return _z3.Fresh("frame", Sort.Bool); }
            var xs = Bound(fn.Parameters);
            var within = Closed(fn.Parameters, xs, f, inner => EvalSpec(body, inner, spec));
            return Within(xs, within);
        }

        /// <summary>At a call of a delegate: what it may change, or null if nothing (null too if it isn't one with a frame).</summary>
        private (bool known, Term frame) DelegateFrameAt(IInvocationOperation inv, Term receiver, Term[] args, Frame f)
        {
            if (!(inv.TargetMethod.ContainingType is INamedTypeSymbol type) || inv.TargetMethod.MethodKind != MethodKind.DelegateInvoke || !IsPlainDelegate(type) || receiver == null)
                return (false, null);
            if (Entailed(NoChange(type, receiver))) return (true, null);
            var frame = FrameOf(type, receiver, args);
            return (true, f.Alloc != null ? new Term($"(cv_mod {frame.S} {f.Alloc.S})", Sort.Row) : frame);
        }

        private static Term Forall(IReadOnlyList<Term> vars, Term body, Term pattern) =>
            vars.Count == 0 ? body
            : new Term($"(forall ({string.Join(" ", vars.Select(v => $"({v.S} {T.SortName(v.Sort)})"))}) (! {body.S} :pattern ({pattern.S})))", Sort.Bool);

        /// <summary>The precondition a lambda or method group made a delegate has (its own, for a lambda).</summary>
        private IReadOnlyList<IOperation> DelegateRequires(IOperation target) => target switch
        {
            IAnonymousFunctionOperation fn => _engine.ContractOf(fn.Symbol).OwnRequires,
            IFlowAnonymousFunctionOperation ffn => _engine.ContractOf(ffn.Symbol).OwnRequires,
            IMethodReferenceOperation mr => _engine.ContractOf(mr.Method).Requires,
            _ => new IOperation[0],
        };

        private static IMethodSymbol DelegateTarget(IOperation target) => target switch
        {
            IAnonymousFunctionOperation fn => fn.Symbol,
            IFlowAnonymousFunctionOperation ffn => ffn.Symbol,
            IMethodReferenceOperation mr => mr.Method,
            _ => null,
        };

        // ---- the hook: every delegate value the method computes

        private void DelegateValue(IOperation op, Term t, Frame f)
        {
            // (in a callee's contract, its parameters are the arguments: what they are is the caller's to say)
            if (_foreignSpec > 0 || !(op is IDelegateCreationOperation dc) || !(op.Type is INamedTypeSymbol type) || !IsPlainDelegate(type)) return;
            DelegateMade(dc, type, t, f);
        }

        /// <summary>
        /// A delegate handed to a library: the library's call of it must be allowed. What the library passes it is
        /// known for some members, and then only that must be accepted; otherwise it may pass anything, so the delegate
        /// must be total (proved, not just a lambda without a precondition: one whose precondition always holds is too).
        /// <list type="bullet">
        /// <item>A stub that says what it needs of the delegate (its Spec.Requires name it in Spec.Pre or Spec.Total)
        /// has that proved where it is called, as all its preconditions are.</item>
        /// <item>The members that call it on the elements of a list or an array, and on nothing else, before they return
        /// (List.ForEach, Exists, Find..., Array.ForEach..., and the LINQ members that aren't lazy: Any, All, Count,
        /// First, Sum...): Spec.Pre for each element, when the delegate is a lambda or method group that changes
        /// neither the list nor any array (so the elements it is given are those there now).</item>
        /// <item>Parallel.For(from, to, body): Spec.Pre(body, i) for each i in [from, to).</item>
        /// </list>
        /// </summary>
        private void HandedToLibrary(IMethodSymbol m, IEnumerable<IArgumentOperation> args, Frame f, SpecEnv spec, IOperation instance = null)
        {
            if (!_codeMode || _foreignSpec > 0 || m.DeclaringSyntaxReferences.Length > 0 || m.MethodKind == MethodKind.DelegateInvoke) return;
            var callee = _engine.ContractOf(m);
            var argList = args.ToList();
            foreach (var a in argList)
            {
                if (!(a.Parameter?.Type is INamedTypeSymbol type) || !IsPlainDelegate(type)) continue;
                if (callee.IsStub && StubSpeaksOf(callee, a.Parameter.Name)) continue;
                var value = Unconverted(a.Value);
                bool made = value is IDelegateCreationOperation;
                if (made && DelegateRequires(((IDelegateCreationOperation)value).Target).Count == 0) continue; // (total: its body is proved for anything)
                var known = made || value is ILocalReferenceOperation || value is IParameterReferenceOperation || value is IFieldReferenceOperation;
                if (!known)
                {
                    Prove(T.False, "CSV1029", a.Syntax, $"'{m.Name}' may call '{a.Value.Syntax}' with any arguments, but it isn't known to accept them all: keep it in a local said to be Spec.Total");
                    continue;
                }
                var d = Eval(a.Value, f, spec);
                // Parallel.For(from, to, body): body(i) for each i from 'from' up to 'to', whatever body does
                if (m.ContainingType?.ToDisplayString() == "System.Threading.Tasks.Parallel" && m.Name == "For" && a.Parameter.Ordinal == 2 &&
                    type.DelegateInvokeMethod.Parameters.Length == 1 && type.DelegateInvokeMethod.Parameters[0].Type.SpecialType == SpecialType.System_Int32 &&
                    argList.FirstOrDefault(x => x.Parameter?.Ordinal == 0) is IArgumentOperation fromArg && argList.FirstOrDefault(x => x.Parameter?.Ordinal == 1) is IArgumentOperation toArg)
                {
                    var lo = T.Coerce(Eval(fromArg.Value, f, spec), Sort.Int);
                    var hi = T.Coerce(Eval(toArg.Value, f, spec), Sort.Int);
                    var k = new Term(_z3.FreshName("i"), Sort.Int);
                    Prove(T.Quant("forall", k.S, T.Implies(T.And(T.Le(lo, k), T.Lt(k, hi)), PreOf(type, d, new[] { k }, f))), "CSV1001", a.Syntax,
                        $"'{m.Name}' calls this with each index from {fromArg.Value.Syntax} up to {toArg.Value.Syntax}, but it might not accept them all");
                    continue;
                }
                if (made && EachElement(m, a, argList, instance, f, spec) is (Term length, System.Func<Term, Term> element, Term listKnown))
                {
                    var i = new Term(_z3.FreshName("i"), Sort.Int);
                    // (facts of the element, its range, are of the bound index: hypotheses inside, not facts outside)
                    _quantDepth++;
                    _quantFacts.Push(new List<Term>());
                    Term pre;
                    List<Term> facts;
                    try { pre = PreOf(type, d, new[] { element(i) }, f); }
                    finally { facts = _quantFacts.Pop(); _quantDepth--; }
                    foreach (var plain in facts.Where(x => !x.S.Contains(i.S))) AssumeSide(plain);
                    var each = T.Quant("forall", i.S, T.Implies(T.And(new[] { listKnown, T.Le(T.Int(0), i), T.Lt(i, length) }.Concat(facts.Where(x => x.S.Contains(i.S))).ToArray()), pre));
                    Prove(each, "CSV1001", a.Syntax, $"'{m.Name}' calls this with each element, but it might not accept them all (its Spec.Requires)");
                    continue;
                }
                Prove(TotalOf(type, d, f), "CSV1029", a.Syntax, made
                    ? $"'{m.Name}' may call this with any arguments, but its precondition might not hold for them all"
                    : $"'{m.Name}' may call '{a.Value.Syntax}' with any arguments, but it isn't known to accept them all: say so with Spec.Requires(Spec.Total({a.Value.Syntax}))");
            }
        }

        // ---- library members that change nothing they are given: a call changes only what the code it runs does

        private static readonly HashSet<string> ReadOnlyCollectionMembers = new HashSet<string>
        {
            "Exists", "TrueForAll", "Find", "FindIndex", "FindLast", "FindLastIndex", "FindAll", "ConvertAll", "ForEach",
            "Contains", "IndexOf", "LastIndexOf",
        };

        /// <summary>
        /// A library member that writes nothing it is given, nor any state of the program's: every LINQ member (they
        /// read their sources, and make what they return), and the List and Array members that only look. What a call
        /// of one changes is what the program code it runs changes, its delegates' included.
        /// </summary>
        private static bool ReadsOnly(IMethodSymbol m)
        {
            var owner = (m.ReducedFrom ?? m).ContainingType?.OriginalDefinition.ToDisplayString();
            return owner == "System.Linq.Enumerable"
                || owner == "System.Collections.Generic.List<T>" && !m.IsStatic && ReadOnlyCollectionMembers.Contains(m.Name)
                || owner == "System.Array" && m.IsStatic && ReadOnlyCollectionMembers.Contains(m.Name);
        }

        /// <summary>A delegate argument whose code is in sight (a lambda, a method group) and writes no arrays.</summary>
        private bool WritesNoArrays(IOperation value) =>
            Unconverted(value) is IDelegateCreationOperation dc && DelegateTarget(dc.Target) is IMethodSymbol fn ? !_engine.MayWriteHeap(fn) : SaidToChangeNothing(value);

        /// <summary>A delegate argument whose code is in sight and writes no field nor model state.</summary>
        private bool WritesNoFields(IOperation value) =>
            Unconverted(value) is IDelegateCreationOperation dc && DelegateTarget(dc.Target) is IMethodSymbol fn ? WritesNoFields(fn) : SaidToChangeNothing(value);

        /// <summary>A delegate in a variable that its specifications say changes nothing.</summary>
        private bool SaidToChangeNothing(IOperation value)
        {
            var u = Unconverted(value);
            if (!(u is ILocalReferenceOperation || u is IParameterReferenceOperation || u is IFieldReferenceOperation) || !(u.Type is INamedTypeSymbol type) || !IsPlainDelegate(type)) return false;
            return Entailed(NoChange(type, Eval(u, _handOffState, null)));
        }

        private Frame _handOffState; // (the state at the call being looked at, for SaidToChangeNothing)

        /// <summary>Its code writes no array, field or model state.</summary>
        private bool WritesNothing(IMethodSymbol fn) => !_engine.MayWriteHeap(fn) && WritesNoFields(fn);

        private bool WritesNoFields(IMethodSymbol fn)
        {
            if (fn.MethodKind != MethodKind.AnonymousFunction)
            {
                var (fields, all) = _engine.Fields.WritesOf(fn);
                return !all && fields.Count == 0;
            }
            // a lambda: its own code, looked at here (its effects are counted with its method's, not on their own)
            var syntax = fn.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax();
            var model = syntax == null ? null : _engine.Compilation.GetSemanticModel(syntax.SyntaxTree);
            var body = model?.GetOperation(syntax);
            if (body == null) return false;
            foreach (var op in body.DescendantsAndSelf())
            {
                if (SpecSymbols.EnclosingSpecCall(op.Syntax, model) != null) continue;
                switch (op)
                {
                    case IAssignmentOperation a when !(a.Target is ILocalReferenceOperation || a.Target is IParameterReferenceOperation && ((IParameterReferenceOperation)a.Target).Parameter.RefKind == RefKind.None):
                    case IIncrementOrDecrementOperation inc when !(inc.Target is ILocalReferenceOperation || inc.Target is IParameterReferenceOperation):
                    case IDeconstructionAssignmentOperation _:
                    case IObjectCreationOperation _:
                        return false;
                    case IArgumentOperation arg when arg.Parameter?.RefKind != RefKind.None && arg.Parameter?.RefKind != RefKind.In:
                        return false;
                    case IInvocationOperation inv when !(SpecSymbols.IsSpecClass(inv.TargetMethod.ContainingType) || _engine.ContractOf(inv.TargetMethod).IsPure ||
                                                         inv.TargetMethod.DeclaringSyntaxReferences.Length > 0 && inv.TargetMethod.MethodKind != MethodKind.AnonymousFunction &&
                                                         inv.TargetMethod.MethodKind != MethodKind.LocalFunction && _engine.Fields.WritesOf(inv.TargetMethod) is var w && !w.all && w.fields.Count == 0):
                        return false;
                }
            }
            return true;
        }

        /// <summary>Does this call of a library member keep the arrays as they are: it reads only, and runs nothing that writes one?</summary>
        private bool KeepsArrays(IInvocationOperation inv, Frame f) { _handOffState = f; return ReadsOnly(inv.TargetMethod) && !_engine.Fields.RunsOtherCodeAt(inv, WritesNoArrays); }

        /// <summary>And the fields and model state (a list's elements)?</summary>
        private bool KeepsFields(IInvocationOperation inv, Frame f) { _handOffState = f; return ReadsOnly(inv.TargetMethod) && !_engine.Fields.RunsOtherCodeAt(inv, WritesNoFields); }

        /// <summary>Does the stub's precondition say what the delegate parameter must accept?</summary>
        private static bool StubSpeaksOf(Contract stub, string parameter) =>
            stub.Requires.Any(r => r.DescendantsAndSelf().OfType<IInvocationOperation>().Any(i =>
                SpecSymbols.IsSpecClass(i.TargetMethod.ContainingType) && (i.TargetMethod.Name == "Pre" || i.TargetMethod.Name == "Total") &&
                i.Arguments.Length > 0 && Unconverted(i.Arguments[0].Value) is IParameterReferenceOperation p && p.Parameter.Name == parameter));

        private static readonly HashSet<string> EagerEnumerable = new HashSet<string>
        {
            "Any", "All", "Count", "LongCount", "First", "FirstOrDefault", "Last", "LastOrDefault", "Single", "SingleOrDefault",
            "Sum", "Min", "Max", "Average", "ToDictionary",
        };

        private static readonly HashSet<string> ElementwiseCollection = new HashSet<string>
        {
            "ForEach", "Exists", "TrueForAll", "Find", "FindIndex", "FindLast", "FindLastIndex", "FindAll", "RemoveAll", "ConvertAll",
        };

        /// <summary>
        /// If the library calls this delegate with the elements of a list or array, and nothing else, before it returns:
        /// that sequence (its length, its element at an index, when that is what it is).
        /// </summary>
        private (Term, System.Func<Term, Term>, Term)? EachElement(IMethodSymbol m, IArgumentOperation a, List<IArgumentOperation> args, IOperation instance, Frame f, SpecEnv spec)
        {
            var type = (INamedTypeSymbol)a.Parameter.Type;
            if (type.DelegateInvokeMethod.Parameters.Length != 1) return null;
            var owner = m.ContainingType?.OriginalDefinition.ToDisplayString();
            IOperation source;
            if (owner == "System.Linq.Enumerable" && EagerEnumerable.Contains(m.Name) && a.Parameter.Ordinal == 1)
                source = args.FirstOrDefault(x => x.Parameter?.Ordinal == 0)?.Value;
            else if (owner == "System.Array" && ElementwiseCollection.Contains(m.Name) && m.IsStatic)
                source = args.FirstOrDefault(x => x.Parameter?.Ordinal == 0)?.Value;
            else if (owner == "System.Collections.Generic.List<T>" && ElementwiseCollection.Contains(m.Name) && !m.IsStatic)
                source = instance;
            else return null;
            source = Unconverted(source);
            // (read again here: only what reading twice can't change)
            if (!(source is ILocalReferenceOperation || source is IParameterReferenceOperation || source is IFieldReferenceOperation)) return null;
            var sourceType = source.Type;
            bool array = sourceType is IArrayTypeSymbol, list = IsListType(sourceType);
            if (!array && !list) return null;
            if (!SymbolEqualityComparer.Default.Equals(ElementOf(sourceType), type.DelegateInvokeMethod.Parameters[0].Type)) return null;
            // (it changes neither the list nor an array: the elements it is called with are those there now)
            var fn = DelegateTarget(((IDelegateCreationOperation)Unconverted(a.Value)).Target);
            if (fn == null || _engine.MayTouchArrays(fn) && array) return null;
            if (list && !WritesNoFields(a.Value)) return null; // (nor the list's model state)
            var seq = ListSequence(T.Coerce(Eval(source, f, spec), Sort.Int), sourceType, f);
            return (seq.Length, seq.Element, seq.Known);
        }

        // ---- steady by default: a method relying on a delegate's Spec.Pre or Spec.Post takes it to be steady

        /// <summary>
        /// The delegate parameters whose Spec.Pre, Spec.Post or Spec.Total this method's specifications speak of, and
        /// that no Spec.Reads(p, ...) says may depend on state: it takes them to be steady, and its callers prove it.
        /// </summary>
        private HashSet<IParameterSymbol> SteadyParams(IMethodSymbol m)
        {
            var c = _engine.ContractOf(m);
            var named = new HashSet<IParameterSymbol>(SymbolEqualityComparer.Default);
            var reading = new HashSet<IParameterSymbol>(SymbolEqualityComparer.Default);
            foreach (var op in c.Requires.Concat(c.Ensures.Select(e => e.Expr)).Where(x => x != null).SelectMany(x => x.DescendantsAndSelf()).OfType<IInvocationOperation>())
            {
                if (!SpecSymbols.IsSpecClass(op.TargetMethod.ContainingType) || op.Arguments.Length == 0 ||
                    !(Unconverted(op.Arguments[0].Value) is IParameterReferenceOperation pr)) continue;
                var p = pr.Parameter.Ordinal < m.Parameters.Length ? m.Parameters[pr.Parameter.Ordinal] : pr.Parameter;
                switch (op.TargetMethod.Name)
                {
                    case "Pre": case "Post": case "Total": named.Add(p.OriginalDefinition); break;
                    case "Reads" when op.Arguments.Length == 2: reading.Add(p.OriginalDefinition); break;
                }
            }
            named.ExceptWith(reading);
            return named;
        }

        /// <summary>On entry: the parameters this method takes to be steady are.</summary>
        private void SteadyOnEntry(Frame f)
        {
            if (_method.MethodKind == MethodKind.AnonymousFunction || _method.MethodKind == MethodKind.LocalFunction) return;
            foreach (var p in SteadyParams(_method))
                if (f.Vars.TryGetValue(p, out var v) || f.Vars.TryGetValue(p.OriginalDefinition, out v)) AssumeSteady(v);
        }

        /// <summary>At a call: what the callee takes to be steady must be.</summary>
        private void SteadyArguments(IInvocationOperation inv, Contract callee, Term[] args)
        {
            if (!_codeMode || callee.Method == null || callee.Method.MethodKind == MethodKind.AnonymousFunction) return;
            foreach (var p in SteadyParams(callee.Method))
                if (p.Ordinal < args.Length && args[p.Ordinal] != null)
                    Require(Steady(args[p.Ordinal]), "CSV1001", inv.Syntax,
                        $"'{callee.Method.Name}' takes what '{p.Name}' accepts and gives to be the same in every state, but this might depend on state: " +
                        $"say what it reads with Spec.Requires(Spec.Reads({p.Name}, ...)) in '{callee.Method.Name}'");
        }

        /// <summary>A lambda knows what the method it is in requires of what never changes: Spec.Total(g) of a parameter g never assigned.</summary>
        private void EnclosingFacts(Frame f, SpecEnv spec)
        {
            if (_method.MethodKind != MethodKind.AnonymousFunction && _method.MethodKind != MethodKind.LocalFunction) return;
            var outer = _contract.Declaration?.Ancestors().OfType<BaseMethodDeclarationSyntax>().FirstOrDefault();
            if (outer == null || !(_model.GetDeclaredSymbol(outer) is IMethodSymbol enclosing)) return;
            var none = new HashSet<ISymbol>(SymbolEqualityComparer.Default);
            foreach (var p in SteadyParams(enclosing))
                if (NeverWritten(p)) AssumeSteady(Read(f, p));
            foreach (var req in _engine.ContractOf(enclosing).Requires)
                if (req.DescendantsAndSelf().OfType<IInvocationOperation>().Any(i => SpecSymbols.IsSpecClass(i.TargetMethod.ContainingType) && (i.TargetMethod.Name == "Pre" || i.TargetMethod.Name == "Total")) &&
                    Steady(req, none, _method))
                    _z3.Assume(AsBool(EvalSpec(req, f, spec)));
        }

        // ---- a lambda or method group made a delegate: its Spec.Pre and Spec.Post

        private void DelegateMade(IDelegateCreationOperation dc, INamedTypeSymbol type, Term d, Frame f)
        {
            var fn = DelegateTarget(dc.Target);
            if (fn == null) return;
            var c = _engine.ContractOf(fn);
            var requires = DelegateRequires(dc.Target);
            var ps = type.DelegateInvokeMethod.Parameters.Length == fn.Parameters.Length ? fn.Parameters : default;
            if (ps.IsDefault) return;
            var own = new HashSet<ISymbol>(ps, SymbolEqualityComparer.Default);
            // steady: its precondition is of its parameters and of what never changes, the same in every state.
            // Otherwise it must say what it reads (its own Spec.Reads), and is taken in the state it is made in, for as
            // long as what it reads stays as it is.
            Term sid;
            if (requires.All(r => Steady(r, own, fn)))
            {
                sid = Canon;
                AssumeSide(Steady(d));
                if (_quantFacts.Count == 0) _steadyTerms.Add(T.Coerce(d, Sort.Int).S);
                if (requires.Count == 0) AssumeSide(TotalAt(type, d, Canon)); // (its body is proved for any arguments)
                else
                {
                    var xs = Bound(ps);
                    var pre = PreAt(type, d, Canon, xs);
                    var given = Closed(ps, xs, f, inner => T.And(requires.Select(r => AsBool(EvalForeignSpec(r, inner, new SpecEnv { Old = inner }))).ToArray()));
                    AssumeSide(Forall(xs, T.Eq(pre, given), pre));
                }
            }
            else if (c.Reads != null && Steady(c.Reads, own, fn) && fn.MethodKind == MethodKind.AnonymousFunction &&
                     requires.All(r => StateRead(r, own, fn, new List<IOperation>())))
            {
                _readsFrames = true;
                sid = SidOf(f);
                var xs = Bound(ps);
                var pre = PreAt(type, d, sid, xs);
                var given = Closed(ps, xs, f, inner => T.And(requires.Select(r => AsBool(EvalForeignSpec(r, inner, new SpecEnv { Old = inner }))).ToArray()));
                AssumeSide(Forall(xs, T.Eq(pre, given), pre));
                var reads = ReadsAt(type, d, sid, xs);
                var frame = Closed(ps, xs, f, inner => T.Coerce(EvalForeignSpec(c.Reads, inner, new SpecEnv { Old = inner }), Sort.Row));
                AssumeSide(Forall(xs, new Term($"(cv_subset {reads.S} {frame.S})", Sort.Bool), reads));
                // what the precondition reads must be in the frame
                if (_codeMode && _foreignSpec == 0)
                {
                    var objects = new List<IOperation>();
                    foreach (var r in requires) StateRead(r, own, fn, objects);
                    foreach (var o in objects)
                    {
                        var ys = Bound(ps);
                        var inFrame = Closed(ps, ys, f, inner =>
                            new Term($"(distinct (select {T.Coerce(EvalForeignSpec(c.Reads, inner, new SpecEnv { Old = inner }), Sort.Row).S} {T.Coerce(EvalForeignSpec(o, inner, new SpecEnv { Old = inner }), Sort.Int).S}) 0)", Sort.Bool));
                        var goal = ys.Length == 0 ? inFrame : new Term($"(forall ({string.Join(" ", ys.Select(v => $"({v.S} {T.SortName(v.Sort)})"))}) {inFrame.S})", Sort.Bool);
                        Prove(goal, "CSV1029", o.Syntax, $"the precondition reads '{o.Syntax}', which isn't in its Spec.Reads", assume: false);
                    }
                }
            }
            else
            {
                if (_codeMode && _foreignSpec == 0)
                    Report("CSV1029", dc.Syntax, $"the precondition of what is made a '{type.Name}' here depends on state that may change: " +
                                                 "say what it reads with Spec.Reads(...) in the lambda (fields and array cells of the objects it names), or use a delegate type with a contract", isError: true);
                return;
            }

            // what it may change: its own Spec.Modifies, or nothing if it writes nothing
            if (c.Modifies != null && Steady(c.Modifies, own, fn))
            {
                var xs = Bound(ps);
                var within = Closed(ps, xs, f, inner => EvalForeignSpec(c.Modifies, inner, new SpecEnv { Old = inner }));
                AssumeSide(ChangesWithin(type, d, xs, within));
            }
            else if (WritesNothing(fn)) AssumeSide(NoChange(type, d));

            // what it gives: its postconditions, and an expression's value
            var invoke = type.DelegateInvokeMethod;
            var facts = new List<(IReadOnlyList<Term> xs, Term r, Term fact)>();
            foreach (var post in c.Ensures)
            {
                var ownR = new HashSet<ISymbol>(own, SymbolEqualityComparer.Default);
                if (post.ResultParameter != null) ownR.Add(post.ResultParameter);
                if (post.Guard != null || !Steady(post.Expr, ownR, fn)) continue;
                var xs = Bound(ps);
                var r = invoke.ReturnsVoid ? null : new Term(_z3.FreshName("r"), SortOf(invoke.ReturnType));
                var fact = Closed(ps, xs, f, inner => AsBool(EvalForeignSpec(post.Expr, inner, new SpecEnv { Old = inner, Result = r, ResultParameter = post.ResultParameter })));
                facts.Add((xs, r, fact));
            }
            if (!invoke.ReturnsVoid && ValueOf(fn) is IOperation body && Steady(body, own, fn))
            {
                var xs = Bound(ps);
                var r = new Term(_z3.FreshName("r"), SortOf(invoke.ReturnType));
                var value = Closed(ps, xs, f, inner => EvalSpec(body, inner, null));
                facts.Add((xs, r, T.Eq(r, T.Coerce(value, r.Sort))));
            }
            foreach (var (xs, r, fact) in facts)
            {
                var post = PostAt(type, d, sid, xs, r);
                var vars = r == null ? xs.ToArray() : xs.Append(r).ToArray();
                AssumeSide(Forall(vars, T.Implies(T.And(post, PreAt(type, d, sid, xs)), fact), post));
            }
        }

        private Term[] Bound(IReadOnlyList<IParameterSymbol> ps) => ps.Select(p => new Term(_z3.FreshName(p.Name), SortOf(p.Type))).ToArray();

        /// <summary>Evaluates a condition of the parameters, bound to <paramref name="xs"/>, with the captured variables as they are now.</summary>
        private Term Closed(IReadOnlyList<IParameterSymbol> ps, IReadOnlyList<Term> xs, Frame f, System.Func<Frame, Term> eval)
        {
            var inner = f.Clone();
            for (int i = 0; i < ps.Count; i++) inner.Vars[ps[i]] = xs[i];
            _quantDepth++;
            _quantFacts.Push(new List<Term>());
            _obligations.Push(new List<Obligation>()); // (well-definedness is the lambda's own to prove)
            try
            {
                var t = eval(inner);
                var collected = _quantFacts.Pop();
                return T.And(collected.Append(t).ToArray());
            }
            finally { _obligations.Pop(); _quantDepth--; }
        }

        /// <summary>A lambda's value as one expression (<c>x => x + 1</c>, or a block that only returns one), if it is one.</summary>
        private IOperation ValueOf(IMethodSymbol fn)
        {
            if (fn.MethodKind != MethodKind.AnonymousFunction || !(fn.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() is AnonymousFunctionExpressionSyntax syntax)) return null;
            var model = _engine.ContractOf(fn).Model;
            if (model == null) return null;
            if (syntax.ExpressionBody != null) return model.GetOperation(syntax.ExpressionBody);
            var rest = syntax.Block?.Statements.Where(s => !(s is ExpressionStatementSyntax es && es.Expression is InvocationExpressionSyntax inv &&
                                                             model.GetSymbolInfo(inv).Symbol is IMethodSymbol m && SpecSymbols.IsSpecClass(m.ContainingType))).ToList();
            return rest?.Count == 1 && rest[0] is ReturnStatementSyntax ret && ret.Expression != null ? model.GetOperation(ret.Expression) : null;
        }

        /// <summary>
        /// Does this depend only on <paramref name="own"/> parameters, constants, and captured variables that are never
        /// written after they're declared, through arithmetic, comparisons, Spec.Pre/Post and static [Pure] functions of values?
        /// </summary>
        private bool Steady(IOperation op, ISet<ISymbol> own, IMethodSymbol fn)
        {
            if (op == null) return false;
            if (op.ConstantValue.HasValue) return true;
            switch (op)
            {
                case IParameterReferenceOperation p:
                    return own.Contains(p.Parameter) || !SymbolEqualityComparer.Default.Equals(p.Parameter.ContainingSymbol, fn) && p.Parameter.RefKind == RefKind.None && NeverWritten(p.Parameter);
                case ILocalReferenceOperation l:
                    return !SymbolEqualityComparer.Default.Equals(l.Local.ContainingSymbol, fn) && l.Local.RefKind == RefKind.None && NeverWritten(l.Local);
                case IBinaryOperation _:
                case IUnaryOperation _:
                case IConversionOperation _:
                case IParenthesizedOperation _:
                case IConditionalOperation _:
                    return op.ChildOperations.All(ch => Steady(ch, own, fn));
                case IPropertyReferenceOperation len when len.Property.Name == "Length" && len.Instance?.Type is IArrayTypeSymbol:
                    return Steady(len.Instance, own, fn); // (an array's length never changes)
                case IInvocationOperation inv when SpecSymbols.IsSpecClass(inv.TargetMethod.ContainingType) && (inv.TargetMethod.Name == "Pre" || inv.TargetMethod.Name == "Post" || inv.TargetMethod.Name == "Total"):
                    return inv.Arguments.All(a => Steady(a.Value, own, fn));
                case IInvocationOperation inv when SpecSymbols.IsObjSet(inv.TargetMethod.ContainingType):
                    return (inv.Instance == null || Steady(inv.Instance, own, fn)) && inv.Arguments.All(a => Steady(a.Value, own, fn));
                case IPropertyReferenceOperation pr when SpecSymbols.IsObjSet(pr.Property.ContainingType) && pr.Instance == null:
                    return true;
                case IInvocationOperation inv when inv.Instance == null && _engine.ContractOf(inv.TargetMethod).IsPure &&
                                                   inv.TargetMethod.Parameters.All(p => p.Type.IsValueType) && inv.TargetMethod.ReturnType.IsValueType:
                    return inv.Arguments.All(a => Steady(a.Value, own, fn));
                default:
                    return false;
            }
        }

        /// <summary>
        /// Like <see cref="Steady"/>, but it may also read fields and array cells (and statics): the objects whose fields
        /// or cells it reads are added to <paramref name="objects"/>, for its Spec.Reads to have.
        /// </summary>
        private bool StateRead(IOperation op, ISet<ISymbol> own, IMethodSymbol fn, List<IOperation> objects)
        {
            if (op == null) return false;
            if (op.ConstantValue.HasValue) return true;
            switch (op)
            {
                case IFieldReferenceOperation fr when FieldEffects.IsHeapField(fr.Field):
                    if (fr.Field.IsStatic) return true;
                    objects.Add(fr.Instance);
                    return StateRead(fr.Instance, own, fn, objects);
                case IPropertyReferenceOperation pr when FieldEffects.IsHeapField(pr.Property) && pr.Instance != null:
                    objects.Add(pr.Instance);
                    return StateRead(pr.Instance, own, fn, objects);
                case IArrayElementReferenceOperation ae:
                    objects.Add(ae.ArrayReference);
                    return StateRead(ae.ArrayReference, own, fn, objects) && ae.Indices.All(i => StateRead(i, own, fn, objects));
                case IPropertyReferenceOperation len when len.Property.Name == "Length" && len.Instance?.Type is IArrayTypeSymbol:
                    return StateRead(len.Instance, own, fn, objects); // (an array's length never changes)
                case IInstanceReferenceOperation _:
                    return true;
                case IBinaryOperation _:
                case IUnaryOperation _:
                case IConversionOperation _:
                case IParenthesizedOperation _:
                case IConditionalOperation _:
                    return op.ChildOperations.All(ch => StateRead(ch, own, fn, objects));
                default:
                    return Steady(op, own, fn);
            }
        }

        /// <summary>A local or parameter assigned nowhere after its declaration (nor passed by ref or out).</summary>
        private bool NeverWritten(ISymbol s)
        {
            var owner = s.ContainingSymbol?.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax();
            if (owner == null) return false;
            var model = _engine.Compilation.GetSemanticModel(owner.SyntaxTree);
            foreach (var id in owner.DescendantNodes().OfType<IdentifierNameSyntax>())
            {
                if (id.Identifier.Text != s.Name || !SymbolEqualityComparer.Default.Equals(model.GetSymbolInfo(id).Symbol, s)) continue;
                SyntaxNode e = id;
                while (e.Parent is ParenthesizedExpressionSyntax) e = e.Parent;
                if (e.Parent is AssignmentExpressionSyntax a && a.Left == e) return false;
                if (e.Parent is PrefixUnaryExpressionSyntax || e.Parent is PostfixUnaryExpressionSyntax pu && !pu.IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.SuppressNullableWarningExpression)) return false;
                if (e.Parent is ArgumentSyntax arg && !arg.RefKindKeyword.IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.None)) return false;
            }
            return true;
        }

        // ---- a call of a delegate

        private void DelegateCalled(IInvocationOperation inv, Term receiver, Term[] args, Frame state)
        {
            if (!(inv.TargetMethod.ContainingType is INamedTypeSymbol type) || inv.TargetMethod.MethodKind != MethodKind.DelegateInvoke || !IsPlainDelegate(type) || receiver == null) return;
            Require(PreOf(type, receiver, args, state), "CSV1001", inv.Syntax,
                $"'{inv.Instance?.Syntax}' might not accept these arguments: say what it accepts with Spec.Requires(Spec.Pre({inv.Instance?.Syntax}, ...))");
        }

        private void DelegateGave(IInvocationOperation inv, Term receiver, Term[] args, Term result, Frame before)
        {
            if (before == null) return;
            if (!(inv.TargetMethod.ContainingType is INamedTypeSymbol type) || inv.TargetMethod.MethodKind != MethodKind.DelegateInvoke || !IsPlainDelegate(type) || receiver == null) return;
            _z3.Assume(PostOf(type, receiver, args, inv.TargetMethod.ReturnsVoid ? null : result, before));
        }
    }
}
