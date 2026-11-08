using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// async and await, for code that runs one piece at a time (no two threads in the same state at once):
    /// <list type="bullet">
    /// <item>an async method's contract speaks of what it returns, the T of its Task&lt;T&gt; (Spec.Ensures&lt;T&gt;),
    /// and holds when its task completes;</item>
    /// <item><c>await F(...)</c> of an async method of the program is a call: F's precondition is checked and its
    /// postcondition assumed for the awaited value;</item>
    /// <item>at every <c>await</c> other code may run before the method resumes. Everything it could write is
    /// forgotten: arrays, fields, and locals that lambdas or local functions write. What the method holds stays: the
    /// fields of [Owned] objects whose views or permissions are in hand, array cells its Spec.Acc contract gave it, and
    /// memory cells whose views it holds (whoever else runs cannot hold them too);</item>
    /// <item><c>var t = F(...); ...; await t;</c>, with t a local used only to be awaited (or Task.WhenAll'd, or its
    /// Result read once it has been): a call whose precondition is checked where it starts, and whose postcondition is
    /// known of what it gives, once that is awaited. Until then it may run at any moment, so what the method doesn't
    /// hold is forgotten from each statement to the next. If some path never awaits it, its failure would be lost
    /// (CSV1026). Its Spec.Acc permissions go when it starts, and come back when it is awaited (see FinishLater). Views and predicates, lent to a call until it returns, can't go with it;</item>
    /// <item>any other call of an async method of the program, not awaited at once, would run interleaved with its
    /// caller in ways that can't be followed: that is not supported (CSV1901). Tasks from the library are
    /// values like any other; awaiting one gives an unknown result (non-null as the library declares it).</item>
    /// </list>
    /// </summary>
    internal sealed partial class MethodVerifier
    {
        /// <summary>The call an await is evaluating: its result is the awaited value, not the task.</summary>
        private IInvocationOperation _awaitedCall;

        /// <summary>The T of an async method returning Task&lt;T&gt; or ValueTask&lt;T&gt;; null for Task, ValueTask or void.</summary>
        internal static ITypeSymbol AsyncResultType(IMethodSymbol m) =>
            m.IsAsync && m.ReturnType is INamedTypeSymbol rt && rt.TypeArguments.Length == 1 &&
            (rt.Name == "Task" || rt.Name == "ValueTask") && rt.ContainingNamespace?.ToDisplayString() == "System.Threading.Tasks"
                ? rt.TypeArguments[0] : null;

        /// <summary>The type a call's result has where it is used: an awaited async method's T, otherwise its return type.</summary>
        private ITypeSymbol ResultTypeOf(IInvocationOperation inv) =>
            inv == _awaitedCall && AwaitedType(inv.TargetMethod) is ITypeSymbol t ? t : inv.TargetMethod.ReturnType;

        /// <summary>A call of an async method of the program that is not awaited at once.</summary>
        private bool CheckNotAwaited(IInvocationOperation inv, Contract callee)
        {
            if (!inv.TargetMethod.IsAsync || !callee.HasSource || inv == _awaitedCall || !_codeMode) return false;
            // (() => F(x), handed on: whoever it's handed to has the task. See LambdaGivesTasks.)
            if (IsLambdasResult(inv.Syntax)) return false;
            NotModeled(inv.Syntax, $"'{inv.TargetMethod.Name}' is async and is not awaited at once: it would run interleaved with this method, " +
                                   "each changing what the other relies on (write 'await' at the call)");
            return true;
        }

        private static bool IsLambdasResult(SyntaxNode call)
        {
            var e = call.Parent;
            while (e is ParenthesizedExpressionSyntax) e = e.Parent;
            return e is LambdaExpressionSyntax || e is ReturnStatementSyntax r && r.Ancestors().OfType<MemberDeclarationSyntax>().First().Span.Contains(r.Span) &&
                   r.FirstAncestorOrSelf<AnonymousFunctionExpressionSyntax>() != null && r.Ancestors().TakeWhile(x => !(x is AnonymousFunctionExpressionSyntax)).All(x => !(x is LocalFunctionStatementSyntax));
        }

        /// <summary>
        /// ids.Select(id => F(id)): tasks are going from here on, however many and until whenever, as far as this method can
        /// tell, for it isn't followed where they go. So it forgets what it doesn't hold from here to its end.
        /// </summary>
        private void LambdaGivesTasks(IInvocationOperation inv, Frame f)
        {
            if (!_codeMode || IsTaskRun(inv.TargetMethod) || inv.TargetMethod.DeclaringSyntaxReferences.Length > 0) return;
            foreach (var a in inv.Arguments)
                if (a.Value.Syntax is LambdaExpressionSyntax l && l.ExpressionBody != null && _model.GetTypeInfo(l.ExpressionBody).Type is ITypeSymbol r && IsTaskLike(r) &&
                    !IsAwaitedHere(l.ExpressionBody))
                {
                    var effects = EffectsOf(l, f, capturing: true);
                    var key = _z3.Fresh("tasks", Sort.Int);
                    WarnIfTheyMayRace(inv.Syntax, effects, f);
                    f.Started[key.S] = new StartedTask(T.True, false, inv.TargetMethod, inv.Syntax, effects, true);
                }
        }

        private static bool IsTaskLike(ITypeSymbol t) =>
            t is INamedTypeSymbol n && (n.Name == "Task" || n.Name == "ValueTask") && n.ContainingNamespace?.ToDisplayString() == "System.Threading.Tasks";

        /// <summary>A direct argument of an awaited Task.WhenAll: started and finished there.</summary>
        private bool IsInAwaitedWhenAll(SyntaxNode call) =>
            call.Parent is ArgumentSyntax arg && arg.Parent?.Parent is InvocationExpressionSyntax all && IsWhenAll(_model.GetSymbolInfo(all).Symbol as IMethodSymbol) && IsAwaitedHere(all);

        // ================================================================================== tasks awaited later

        /// <summary>The local a call's task is put in, if all that happens to the local is that it is awaited.</summary>
        private ILocalSymbol TaskLocal(IInvocationOperation inv)
        {
            if (!(inv.Syntax.Parent is EqualsValueClauseSyntax eq) || !(eq.Parent is VariableDeclaratorSyntax d) ||
                !(_model.GetDeclaredSymbol(d) is ILocalSymbol local)) return null;
            foreach (var id in _contract.Declaration.DescendantNodes().OfType<IdentifierNameSyntax>())
            {
                if (!SymbolEqualityComparer.Default.Equals(_model.GetSymbolInfo(id).Symbol, local)) continue;
                if (id.Ancestors().TakeWhile(a => a != _contract.Declaration).Any(a => a is AnonymousFunctionExpressionSyntax || a is LocalFunctionStatementSyntax)) return null;
                if (!IsTaskUse(id)) return null;
            }
            return local;
        }

        /// <summary><c>await t</c>, <c>await t.ConfigureAwait(b)</c>, <c>await Task.WhenAll(..., t, ...)</c> or <c>t.Result</c>.</summary>
        private bool IsTaskUse(IdentifierNameSyntax id)
        {
            if (id.Parent is AwaitExpressionSyntax) return true;
            if (id.Parent is MemberAccessExpressionSyntax ma && ma.Expression == id)
                return ma.Name.Identifier.Text == "Result" ||
                       ma.Name.Identifier.Text == "ConfigureAwait" && ma.Parent is InvocationExpressionSyntax c && c.Parent is AwaitExpressionSyntax;
            return id.Parent is ArgumentSyntax arg && arg.RefKindKeyword.IsKind(SyntaxKind.None) && arg.Parent?.Parent is InvocationExpressionSyntax inv &&
                   IsWhenAll(_model.GetSymbolInfo(inv).Symbol as IMethodSymbol) && inv.Parent is AwaitExpressionSyntax;
        }

        private static bool IsWhenAll(IMethodSymbol m) =>
            m != null && m.Name == "WhenAll" && m.ContainingType?.ToDisplayString() == "System.Threading.Tasks.Task";

        /// <summary>A call of an async method of the program whose task a local holds for later (null for any other call).</summary>
        private IInvocationOperation _startedCall;

        private Term StartTask(IInvocationOperation inv, Contract callee, Frame f, SpecEnv spec)
        {
            var m = inv.TargetMethod;
            if (!_codeMode || !m.IsAsync || !callee.HasSource || inv == _awaitedCall || TaskLocal(inv) == null && !IsInAwaitedWhenAll(inv.Syntax)) return null;
            if (!CanStart(inv, callee)) return null;
            // (it would run on what its caller holds the lock for, while its caller does too)
            if (_engine.Locks.GuardOf(m) is IFieldSymbol held && _engine.Locks.IsSemaphore(held))
                Report("CSV1023", inv.Syntax, $"'{m.Name}' relies on holding '{held.Name}', but its task isn't awaited here: it would run alongside this code", isError: true);
            var effects = EffectsOfCall(inv, f);
            var outer = _awaitedCall;
            _awaitedCall = inv;
            _startedCall = inv;
            _finishStarted = null;
            Term result;
            try { result = EvalInvocationCore(inv, f, spec); }
            finally { _awaitedCall = outer; _startedCall = null; }
            // (after it has taken what it takes: what's then known to be apart from what others have)
            WarnIfTheyMayRace(inv.Syntax, effects, f);
            var task = _z3.Fresh("task", Sort.Int);
            _z3.Assume(NotNull(task));
            f.Started[task.S] = new StartedTask(AwaitedType(m) == null ? T.True : result, false, m, inv.Syntax, effects, false, _finishStarted != null, _finishStarted);
            // (what its contract said of the state is of the state when it completes, whenever that is: not of this one)
            Interleave(f);
            return task;
        }

        // ================================================================================== permissions of tasks

        /// <summary>What finishing the task being started will do, if it took permissions (set by the call).</summary>
        private System.Action<Frame> _finishStarted;

        /// <summary>The code of a delegate hasn't begun when Task.Run returns, so nothing of the state then can be said of its start, but what it was given.</summary>
        private bool _startsLater;

        /// <summary>
        /// Can a call's task go on alongside this code? Views are lent by what is passed, and given back by returning, which
        /// it hasn't: not followed. Nor are the instances of predicates, or a class's own view, which goes with its receiver.
        /// </summary>
        private bool CanStart(IInvocationOperation inv, Contract callee)
        {
            if (inv.Arguments.Any(a => SpecSymbols.IsLinear(a.Parameter?.Type) || a.Parameter?.RefKind != RefKind.None)) return false;
            if (!inv.TargetMethod.IsStatic && SpecSymbols.IsOwned(inv.TargetMethod.ContainingType)) return false;
            return !callee.Requires.Concat(callee.Ensures.Select(e => e.Expr)).Any(e => e != null && e.DescendantsAndSelf().Any(o => IsPredicateCall(o, out _)));
        }

        /// <summary>
        /// A started task's permissions went when it started. It gives back what its postcondition names when it finishes, and
        /// nobody has that until then. The rest of what its postcondition says is of the state when it finished, which by the
        /// time it is awaited may have gone: so all of it is said of a state of its own, in which only what comes back is known
        /// to be as it is now.
        /// </summary>
        private System.Action<Frame> FinishLater(Contract callee, Frame pre, Term result)
        {
            // (a delegate starts when it starts: of the state then, only what it was given is as it is now)
            CheckFinishFramed(callee, pre, result);
            var old = pre;
            if (_startsLater)
            {
                old = DetachedFrom(pre);
                Keep(old, pre, AtomsOf(callee.Requires, pre, new SpecEnv { Old = pre }), reads: true);
            }
            return f =>
            {
                var ended = DetachedFrom(pre);
                SpecEnv Env(Postcondition e) => new SpecEnv { Old = old, Result = result, ResultParameter = e.ResultParameter };
                var atoms = new List<Atom>();
                foreach (var ens in callee.Ensures.Where(e => HasPermissions(e.Expr)))
                    atoms.AddRange(AtomsOf(new[] { ens.Expr }, ended, Env(ens)));
                // what it only read, nobody has written
                foreach (var a in atoms.Where(a => a.Read))
                    _z3.Assume(new Term($"(forall ((x Int) (i Int)) (! (=> {InCells(a, "x", "i")} (= (select (select {ended.Heap} x) i) (select (select {f.Heap} x) i))) :pattern ((select (select {ended.Heap} x) i))))", Sort.Bool));
                Keep(f, ended, atoms, reads: false);
                foreach (var ens in callee.Ensures) Inhale(ens.Expr, ended, Env(ens), f);
                foreach (var ens in callee.Ensures)
                    _z3.Assume(GuardedBy(ens, pre, AsBool(EvalForeignSpec(ens.Expr, ended, Env(ens)))));
            };
        }

        /// <summary>The start of a task whose postcondition is being checked to read only what it gives back, or null.</summary>
        private SyntaxNode _framingTask;

        /// <summary>
        /// A started task's postcondition is of the state when it ends, and by the await others may have changed what it
        /// doesn't give back. So it may read only what never changes and what it gives back, to its left (self-framed, as a
        /// predicate's body is): anything else would be lost, and is reported, not silently forgotten (CSV1016).
        /// <c>Spec.Old</c> is of the start, which is known.
        /// </summary>
        private void CheckFinishFramed(Contract callee, Frame pre, Term result)
        {
            var at = _startedCall?.Syntax;
            if (at == null) return;
            var obligations = new List<Obligation>();
            _z3.Push();
            _obligations.Push(obligations);
            try
            {
                var ended = DetachedFrom(pre);
                ended.Perm = new Term("((as const (Array Int Real)) 0.0)", Sort.Perm);
                ended.FPerm = new Term("((as const (Array Int (Array Int Real))) ((as const (Array Int Real)) 0.0))", Sort.PermHeap);
                ended.ArrPerm = ended.FPerm;
                var old = pre.Clone();
                old.Perm = null;
                old.ArrPerm = null;
                _framingCheck = true;
                _framingTask = at;
                foreach (var ens in callee.Ensures)
                    Walk(ens.Expr, ended, new SpecEnv { Old = old, Result = result, ResultParameter = ens.ResultParameter }, T.True, own: false,
                        atom: a =>
                        {
                            if (a.Obj != null) _z3.Assume(T.Implies(a.Guard, NotNull(a.Obj)));
                            if (a.Arr != null) ChangeCells(ended, a, "+");
                            else if (a.Field != null) ChangeField(ended, a.Obj, FieldId(a.Field), a.Guard, "+");
                            else if (a.Obj != null) ended.Perm = Change(ended.Perm, a.Obj, a.Guard, "+");
                        }, fact: null);
                // (proved here, within the state just built, each closed over the quantifiers it was in)
                foreach (var ob in obligations) Prove(ob.Condition, ob.Id, ob.At, ob.Message, assume: false);
            }
            finally { _framingCheck = false; _framingTask = null; _obligations.Pop(); _z3.Pop(); }
        }

        /// <summary>What a started task's postcondition reads, that it doesn't give back: CSV1016 at the start.</summary>
        private void NotGivenBack(Term held, SyntaxNode read) => Emit(new Obligation
        {
            Condition = T.Implies(T.And(_guards.ToArray()), held),
            Id = "CSV1016",
            At = _framingTask,
            Message = $"the postcondition of the task started here reads '{read}', which it doesn't give back (no Spec.Acc for it to its left): by the time it is awaited, others may have changed it. Give it back, or await the call at once",
        });

        private List<Atom> AtomsOf(IEnumerable<IOperation> assertions, Frame f, SpecEnv env)
        {
            var atoms = new List<Atom>();
            foreach (var e in assertions.Where(HasPermissions))
                Walk(e, f, env, T.True, own: false, atom: a => atoms.Add(a), fact: null);
            return atoms;
        }

        /// <summary>A state like <paramref name="f"/>, its parameters and all, of which nothing that can change is known.</summary>
        private Frame DetachedFrom(Frame f)
        {
            var d = f.Clone();
            d.Perm = null;
            d.ArrPerm = null;
            d.HeldGates = new List<(IFieldSymbol, Term)>();
            Interleave(d);
            return d;
        }

        /// <summary>In <paramref name="target"/>, what the permissions in hand cover is as in <paramref name="source"/>.</summary>
        private void Keep(Frame target, Frame source, IReadOnlyCollection<Atom> atoms, bool reads)
        {
            var cells = atoms.Where(a => a.Arr != null && (reads || !a.Read)).Select(a => InCells(a, "x", "i")).ToList();
            if (cells.Count > 0)
                target.Heap = CellwiseHeap($"(ite (or {string.Join(" ", cells)}) (select (select {source.Heap} x) i) (select (select {target.Heap} x) i))");
            var objects = atoms.Where(a => a.Obj != null && a.Arr == null).ToList();
            if (objects.Count == 0) return;
            foreach (var field in _engine.Fields.OwnedFields())
            {
                var theirs = objects.Where(a => a.Field == null || SymbolEqualityComparer.Default.Equals(FieldEffects.Key(a.Field), field))
                    .Select(a => a.Field == null && source.Root != null
                        ? $"(and {a.Guard} (or (= y {a.Obj}) (= (select {source.Root} y) {a.Obj})))"
                        : $"(and {a.Guard} (= y {a.Obj}))").ToList();
                if (theirs.Count > 0)
                    target.Fields[field] = Pointwise(field.Name, MapSort(field), $"(ite (or {string.Join(" ", theirs)}) (select {FieldMap(source, field)} y) (select {FieldMap(target, field)} y))");
            }
        }

        // ================================================================================== what's shared

        /// <summary>Is this code running alongside other code here? Then all it uses must be held: that makes it free of races, as the logic promises.</summary>
        private bool AmongOthers(Frame f, SyntaxNode at)
        {
            if (!_codeMode || _foreignSpec > 0 || SpecSymbols.IsInGhostContext(at, _model)) return false;
            return _engine.StartedDelegates.RunsAlongside(_method) || f.Started.Values.Any(t => !t.Awaited);
        }

        /// <summary>
        /// What runs concurrently says so: where this code starts a method of the program without awaiting it, hands one to a
        /// thread, or calls one from code that runs concurrently, that method must be [RunsConcurrently] (CSV1028), so that it
        /// is checked as such. Each site is reported once, by whichever method's code holds it.
        /// </summary>
        private void CheckConcurrentMarks()
        {
            if (SpecSymbols.HasAttribute(_method, "TrustedAttribute")) return;
            foreach (var (at, callee, why) in _engine.StartedDelegates.UnmarkedIn(_contract.Declaration))
                if (_engine.StartedDelegates.Claim(at))
                    Report("CSV1028", at, callee.MethodKind == MethodKind.DelegateInvoke
                        ? $"a '{callee.ContainingType.Name}' runs concurrently ({why}), but the delegate type isn't marked so: say [RunsConcurrently] on it, and every lambda made one is checked as such"
                        : $"'{callee.Name}' runs concurrently ({why}), but isn't marked so: say [RunsConcurrently] on it or its class, and it is checked as such", isError: true);
        }

        /// <summary>Proved, or reported; either way nothing follows from it, so what comes after is still looked at.</summary>
        private void Reported(Term goal, string id, SyntaxNode at, string message) =>
            Prove(T.Implies(T.And(_guards.ToArray()), goal), id, at, message, assume: false);

        /// <summary>The object is new here, and only a local has it.</summary>
        private Term IsConfined(Term o, Frame f) => T.Or(ConfinedValues(f, null).Select(v => T.Eq(T.Coerce(o, Sort.Int), v)).ToArray());

        private static bool NeverChanges(ISymbol field) =>
            field is IFieldSymbol x ? x.IsReadOnly || x.IsConst
            : field is IPropertySymbol p && (p.SetMethod == null || p.SetMethod.IsInitOnly);

        /// <summary>
        /// A field used by code that runs alongside other code: it never changes, or a lock guards it (for which CheckLocking
        /// has its say), or it's in hand: a permission to its object, a new object only a local has, or the object a constructor
        /// is building. Otherwise another could be writing it.
        /// </summary>
        private void CheckFieldHeld(ISymbol field, Term o, SyntaxNode at, Frame f)
        {
            if (!AmongOthers(f, at) || NeverChanges(field) || IsAtomic(field) || _engine.Locks.GuardOf(field) != null) return;
            if (at.Parent is AssignmentExpressionSyntax a && a.Left == at && a.Parent is InitializerExpressionSyntax) return;
            string fix = "guard it with a lock, hold a Spec.Acc for it (the class must be [Owned]), or make it [Atomic]";
            if (o == null)
            {
                Report("CSV1027", at, $"'{at}' is static, with no lock, and this runs alongside other code: {fix}", isError: true);
                return;
            }
            if (_method.MethodKind == MethodKind.Constructor && f.This != null && o.S == f.This.S) return;
            var held = new List<Term> { IsConfined(o, f) };
            if (IsOwnedField(field) && f.Perm != null)
            {
                var i = T.Coerce(o, Sort.Int);
                held.Add(new Term($"(> (select {f.Perm} {i}) 0.0)", Sort.Bool));
                if (f.Root != null) held.Add(new Term($"(> (select {f.Perm} (select {f.Root} {i})) 0.0)", Sort.Bool));
                if (f.FPerm != null) held.Add(new Term($"(> {FieldAmount(f, o, FieldId(field))} 0.0)", Sort.Bool));
            }
            Reported(T.Or(held.ToArray()), "CSV1027", at, $"'{at}' has no lock and no permission here, and this runs alongside other code that could be using it: {fix}");
        }

        /// <summary>An array cell, likewise: under permissions, as they say; without them, only of a new array only a local has.</summary>
        private void CheckCellRead(Term arr, Term i, Frame f, SyntaxNode at)
        {
            if (!AmongOthers(f, at)) return;
            if (_arrayMode && f.ArrPerm != null)
                Require(new Term($"(> {CellPerm(f, arr, i)} 0.0)", Sort.Bool), "CSV1016", at, $"'{at}' reads a cell this code has no Spec.Acc or Spec.AccRead for, and it runs alongside other code that could be writing it");
            else
                Reported(IsConfined(arr, f), "CSV1027", at, $"'{at}' reads an array this code has no Spec.Acc or Spec.AccRead for, and it runs alongside other code that could be writing it");
        }

        private void CheckCellWriteShared(Term arr, Term i, Frame f, SyntaxNode at)
        {
            if (AmongOthers(f, at) && !(_arrayMode && f.ArrPerm != null))
                Reported(IsConfined(arr, f), "CSV1027", at, $"'{at}' writes an array this code has no Spec.Acc for, and it runs alongside other code that could be using it");
        }

        /// <summary>
        /// What some code may use, to tell if it can race with other code: which fields and arrays, and of which object where
        /// that can be told (null where it can't: any). Under a lock doesn't count. Only a warning comes of it, not a proof.
        /// </summary>
        private sealed class TaskEffects
        {
            public string Name;
            public readonly List<(ISymbol field, Term on)> Writes = new List<(ISymbol, Term)>();
            public readonly List<(ISymbol field, Term on)> Reads = new List<(ISymbol, Term)>();
            public readonly List<Term> WrittenArrays = new List<Term>();
            public readonly List<Term> UsedArrays = new List<Term>();
            /// <summary>It has permissions for all it does to arrays, as is proved: so it stays out of what others hold.</summary>
            public bool Covered;
        }

        /// <summary>What's known of the objects some code works on: its parameters and locals, and "this".</summary>
        private sealed class EffectScope
        {
            public System.Func<ISymbol, Term> Of = _ => null;
            public Term This;
        }

        /// <summary>The objects in this method's variables now, those that stay the same. A variable of a loop's body is another object next round, which only what has captured it doesn't see.</summary>
        private EffectScope ScopeHere(Frame f, bool capturing)
        {
            return new EffectScope
            {
                This = f?.This == null ? null : T.Coerce(f.This, Sort.Int),
                Of = s => f != null && f.Vars.TryGetValue(s, out var v) && v.Sort == Sort.Int && StartedDelegates.StaysTheSame(s, _contract.Declaration, _model) && (capturing || !DeclaredInALoop(s)) ? v : null,
            };
        }

        private static bool DeclaredInALoop(ISymbol s) =>
            s.DeclaringSyntaxReferences.Any(r => r.GetSyntax().AncestorsAndSelf().TakeWhile(a => !(a is MemberDeclarationSyntax)).Any(a => a is ForStatementSyntax || a is WhileStatementSyntax || a is DoStatementSyntax || a is CommonForEachStatementSyntax));

        private TaskEffects EffectsOf(IMethodSymbol m)
        {
            var e = new TaskEffects { Name = m.Name };
            AddEffects(m, e, new HashSet<string>(), new EffectScope());
            return e;
        }

        /// <summary>What a call does, on the objects it's given.</summary>
        private TaskEffects EffectsOfCall(IInvocationOperation call, Frame f, bool capturing = false)
        {
            var e = new TaskEffects { Name = call.TargetMethod.Name };
            var seen = new HashSet<string>();
            if (call.Syntax is InvocationExpressionSyntax syntax) AddCallEffects(call.TargetMethod, syntax, _model, ScopeHere(f, capturing), e, seen);
            else AddEffects(call.TargetMethod, e, seen, new EffectScope());
            return e;
        }

        private void AddEffects(IMethodSymbol m, TaskEffects e, HashSet<string> seen, EffectScope scope)
        {
            if (m.OriginalDefinition.DeclaringSyntaxReferences.Length > 0 && _engine.ContractOf(m.OriginalDefinition) is Contract c && c.HasSource && MentionsCells(c)) e.Covered = true;
            if (!seen.Add(m.OriginalDefinition.ToDisplayString() + "/" + (scope.This?.S ?? "") + "/" + string.Join(",", m.OriginalDefinition.Parameters.Select(p => scope.Of(p)?.S ?? "")))) return;
            var refs = m.OriginalDefinition.DeclaringSyntaxReferences;
            if (refs.Length == 0)
            {
                // the library's: what a contract says it does, and for the rest there's nothing to go on
                if (IsTaskRun(m) || !_engine.ContractOf(m).IsStub) return;
                e.Writes.AddRange(_engine.Fields.WritesOf(m).Item1.Select(x => (x, (Term)null)));
                e.Reads.AddRange(_engine.Fields.ReadsOf(m).Select(x => (x, (Term)null)));
                if (_engine.MayWriteHeap(m)) e.WrittenArrays.Add(null);
                if (_engine.MayTouchArrays(m)) e.UsedArrays.Add(null);
                return;
            }
            foreach (var r in refs) AddEffects(r.GetSyntax(), _engine.ModelOf(r.SyntaxTree), e, seen, null, scope);
        }

        /// <summary>The object an expression is, where it can be told.</summary>
        private static Term ObjectOf(ExpressionSyntax x, SemanticModel model, EffectScope scope)
        {
            while (x is ParenthesizedExpressionSyntax p) x = p.Expression;
            if (x == null || x is ThisExpressionSyntax) return scope.This;
            return x is IdentifierNameSyntax && (model.GetSymbolInfo(x).Symbol is ILocalSymbol || model.GetSymbolInfo(x).Symbol is IParameterSymbol) ? scope.Of(model.GetSymbolInfo(x).Symbol) : null;
        }

        private void AddCallEffects(IMethodSymbol callee, InvocationExpressionSyntax call, SemanticModel model, EffectScope scope, TaskEffects e, HashSet<string> seen)
        {
            var given = new Dictionary<ISymbol, Term>(SymbolEqualityComparer.Default);
            var definition = callee.OriginalDefinition;
            var operation = model.GetOperation(call) as IInvocationOperation;
            if (operation != null)
                foreach (var a in operation.Arguments)
                    if (a.Parameter != null && a.Syntax is ArgumentSyntax arg && a.Parameter.RefKind == RefKind.None &&
                        definition.Parameters.ElementAtOrDefault(a.Parameter.Ordinal) is IParameterSymbol p && ObjectOf(arg.Expression, model, scope) is Term t &&
                        p.DeclaringSyntaxReferences.Select(r => r.SyntaxTree).FirstOrDefault() is SyntaxTree tree && definition.DeclaringSyntaxReferences.All(r => StartedDelegates.StaysTheSame(p, r.GetSyntax(), _engine.ModelOf(tree))))
                        given[p] = t;
            var receiver = definition.IsStatic ? null : call.Expression is MemberAccessExpressionSyntax ma ? ObjectOf(ma.Expression, model, scope) : scope.This;
            AddEffects(callee, e, seen, new EffectScope { This = receiver, Of = s => given.TryGetValue(s, out var t) ? t : null });
        }

        /// <summary>What's done under a lock doesn't count, even to what isn't a field (a dictionary's contents): that is what a lock is for.</summary>
        private void AddEffects(SyntaxNode code, SemanticModel model, TaskEffects e, HashSet<string> seen, SyntaxNode except, EffectScope scope)
        {
            bool Enter(SyntaxNode x) => x != except && !(x is LockStatementSyntax) && !(x is TryStatementSyntax t && _engine.Locks.GateOfTry(t, model) != null) && !(x is UsingStatementSyntax u && _engine.Locks.GateOfUsing(u, model) != null) && !(x is StatementSyntax st && st.Parent is BlockSyntax b && _engine.Locks.UsingsBefore(st, b, model).Any());
            if (code == except) return;
            var inside = code.DescendantNodes(Enter);
            foreach (var n in inside)
                switch (n)
                {
                    case InvocationExpressionSyntax call when model.GetSymbolInfo(call).Symbol is IMethodSymbol callee:
                        AddCallEffects(callee, call, model, scope, e, seen);
                        break;
                    case SimpleNameSyntax name when !(name.Parent is NameColonSyntax) && !(name.Parent is NameEqualsSyntax):
                        var symbol = model.GetSymbolInfo(name).Symbol;
                        if (symbol is IPropertySymbol stubbed && stubbed.DeclaringSyntaxReferences.Length == 0) symbol = LockGuards.IsWriteTarget(name) ? stubbed.SetMethod : stubbed.GetMethod;
                        if (symbol is IMethodSymbol accessed) { if (!(name.Parent is InvocationExpressionSyntax) && !(name.Parent is MemberAccessExpressionSyntax m0 && m0.Name == name && m0.Parent is InvocationExpressionSyntax)) AddEffects(accessed, e, seen, new EffectScope()); }
                        else if (symbol != null && FieldEffects.IsHeapField(symbol))
                        {
                            ExpressionSyntax whole = name.Parent is MemberAccessExpressionSyntax ma && ma.Name == name ? ma : name;
                            var on = symbol.IsStatic ? null : whole is MemberAccessExpressionSyntax owner ? ObjectOf(owner.Expression, model, scope) : scope.This;
                            (LockGuards.IsWriteTarget(whole) ? e.Writes : e.Reads).Add((FieldEffects.Key(symbol), on));
                        }
                        break;
                    case ElementAccessExpressionSyntax ea when model.GetTypeInfo(ea.Expression).Type is IArrayTypeSymbol:
                        var array = ObjectOf(ea.Expression, model, scope);
                        e.UsedArrays.Add(array);
                        if (LockGuards.IsWriteTarget(ea)) e.WrittenArrays.Add(array);
                        break;
                    case ElementAccessExpressionSyntax ea when model.GetSymbolInfo(ea).Symbol is IPropertySymbol ix:
                        // (d[k] = v: a library's indexer)
                        if ((LockGuards.IsWriteTarget(ea) ? ix.SetMethod : ix.GetMethod) is IMethodSymbol accessor) AddEffects(accessor, e, seen, new EffectScope());
                        break;
                }
        }

        /// <summary>What a piece of this method's source uses, itself and through its calls.</summary>
        private TaskEffects EffectsOf(SyntaxNode code, Frame f, bool capturing, SyntaxNode except = null)
        {
            var e = new TaskEffects { Name = "this method" };
            AddEffects(code, _model, e, new HashSet<string>(), except, ScopeHere(f, capturing));
            return e;
        }

        /// <summary>What a delegate handed to a thread may use. Null if it can't be told which code it is.</summary>
        private TaskEffects EffectsOfDelegate(IOperation d, Frame f)
        {
            d = Unconverted(d);
            if (d is IDelegateCreationOperation dc) d = Unconverted(dc.Target);
            if (d is IAnonymousFunctionOperation af) { var e = EffectsOf(af.Syntax, f, capturing: true); e.Name = "the delegate"; return e; }
            if (d is IMethodReferenceOperation mr && mr.Method.DeclaringSyntaxReferences.Length > 0) return EffectsOf(mr.Method);
            return null;
        }

        /// <summary>What this method does while a task it started goes on: from there to where it is awaited or joined, as far as can be told.</summary>
        private TaskEffects EffectsAlongside(SyntaxNode start, string task, Frame f, SyntaxNode except, bool covered)
        {
            var e = new TaskEffects { Name = "this method", Covered = covered };
            var seen = new HashSet<string>();
            var scope = ScopeHere(f, capturing: false);
            foreach (var code in CodeAlongside(start, task))
            {
                AddEffects(code, _model, e, seen, except, scope);
            }
            return e;
        }

        private IEnumerable<SyntaxNode> CodeAlongside(SyntaxNode start, string task) => StartedDelegates.CodeAlongside(start, task, _contract.Declaration, _model);

        /// <summary>Two objects that can be told apart here.</summary>
        private bool Apart(Term x, Term y) => x != null && y != null && x.S != y.S && _z3.Check(T.Eq(x, y)) == "unsat";

        /// <summary>A field or array one writes and the other uses, that no lock guards, on what may be the same object.</summary>
        private void WarnIfMayRace(SyntaxNode at, TaskEffects a, TaskEffects b)
        {
            if (a == null || b == null) return;
            if (FieldRace(a, b) is ISymbol shared || FieldRace(b, a) is ISymbol other && (shared = other) != null)
                Warn(at, $"'{a.Name}' and '{b.Name}' run at once, and '{shared.Name}' is written by one and used by the other: on one object, that could race, and each is proved as if alone");
            else if (!(a.Covered && b.Covered) && (ArrayRace(a, b) || ArrayRace(b, a)))
                Warn(at, $"'{a.Name}' and '{b.Name}' run at once, and one writes arrays the other may use: on one array, that could race, and each is proved as if alone");
        }

        private ISymbol FieldRace(TaskEffects writer, TaskEffects other)
        {
            foreach (var (field, on) in writer.Writes)
                if (_engine.Locks.GuardOf(field) == null && !IsAtomic(field) && !_engine.Locks.IsFlag(field) && other.Writes.Concat(other.Reads).Any(x => SymbolEqualityComparer.Default.Equals(x.field, field) && !Apart(on, x.on)))
                    return field;
            return null;
        }

        private bool ArrayRace(TaskEffects writer, TaskEffects other) =>
            writer.WrittenArrays.Any(w => other.UsedArrays.Any(u => !Apart(w, u)));

        /// <summary>Two tasks running at once, where one writes what the other uses, each proved as if alone.</summary>
        private void WarnIfTheyMayRace(SyntaxNode at, TaskEffects mine, Frame f)
        {
            foreach (var other in f.Started.Values.Where(t => !t.Awaited))
                WarnIfMayRace(at, mine, other.Effects as TaskEffects);
        }

        // ================================================================================== Task.Run and threads

        private static bool IsAwaitedHere(SyntaxNode call) => StartedDelegates.IsAwaitedHere(call);

        private static bool IsTaskRun(IMethodSymbol m) =>
            m.Name == "Run" && m.ContainingType?.ToDisplayString() == "System.Threading.Tasks.Task" ||
            m.Name == "StartNew" && m.ContainingType?.ToDisplayString().StartsWith("System.Threading.Tasks.TaskFactory") == true;

        private static bool IsThread(ITypeSymbol t) => t?.ToDisplayString() == "System.Threading.Thread";

        /// <summary>
        /// Task.Run(...): the library's call, and then a task of what it runs is going, as for a task awaited later. Null for
        /// any other call, and for one awaited at once, which runs alongside nothing (unless a WhenAll has others next to it).
        /// </summary>
        private Term StartRun(IInvocationOperation inv, Frame f, SpecEnv spec)
        {
            if (!_codeMode || inv == _startedCall) return null;
            if (DelegateCallOf(inv) is IInvocationOperation given) return StartDelegateCall(inv, given, f, spec);
            if (IsAwaitedHere(inv.Syntax) || IsLambdasResult(inv.Syntax)) return null;
            if (!IsTaskRun(inv.TargetMethod)) return StartOther(inv, f, spec);
            var effects = EffectsOfDelegate(RunDelegate(inv), f);
            // await Task.WhenAll(Task.Run(a), Task.Run(b)): alongside each other, and then all done
            if (inv.Syntax.Parent is ArgumentSyntax sibling && sibling.Parent?.Parent is InvocationExpressionSyntax all && IsWhenAll(_model.GetSymbolInfo(all).Symbol as IMethodSymbol) && IsAwaitedHere(all))
            {
                foreach (var earlier in ((ArgumentListSyntax)sibling.Parent).Arguments.TakeWhile(x => x != sibling))
                    if (_model.GetOperation(earlier.Expression) is IInvocationOperation other && IsTaskRun(other.TargetMethod))
                        WarnIfMayRace(inv.Syntax, effects, EffectsOfDelegate(RunDelegate(other), f));
                return null;
            }
            WarnIfTheyMayRace(inv.Syntax, effects, f);
            WarnIfMayRace(inv.Syntax, effects, EffectsAlongside(inv.Syntax, TaskLocal(inv)?.Name, f, inv.Arguments.First(a => a.Parameter?.Ordinal == 0).Value.Syntax, false));
            _startedCall = inv;
            Term task;
            try { task = EvalInvocationCore(inv, f, spec); }
            finally { _startedCall = null; }
            _z3.Assume(NotNull(task));
            var kept = TaskLocal(inv) != null;
            // (a task stored, returned or dropped goes on running, and nothing here can tell about what)
            if (!kept) Detached(inv.Syntax, effects);
            // the statement itself, with its task dropped: a failure in it would be lost
            if (!kept && inv.Syntax.Parent is ExpressionStatementSyntax)
                Report("CSV1026", inv.Syntax, "the task of 'Run' is never awaited: a failure in it would be lost (keep it and await it, or write '_ = ' if that is meant)", isError: true);
            f.Started[task.S] = new StartedTask(TaskRunResult(inv), false, inv.TargetMethod, inv.Syntax, effects, !kept);
            Interleave(f);
            return task;
        }

        /// <summary>The one call a Task.Run's delegate is, if it has permissions to be given it there. (See StartedDelegates.)</summary>
        private IInvocationOperation DelegateCallOf(IInvocationOperation run)
        {
            if (!IsTaskRun(run.TargetMethod) || run.TargetMethod.Name != "Run") return null;
            return run.Arguments.FirstOrDefault(a => a.Parameter?.Ordinal == 0)?.Value.Syntax is AnonymousFunctionExpressionSyntax l && _engine.StartedDelegates.CallOf(l) is InvocationExpressionSyntax c
                ? _model.GetOperation(c) as IInvocationOperation : null;
        }

        /// <summary>
        /// A delegate that is one call, with values fixed by now: the call is checked here, and gets what its precondition
        /// names, and its permissions and postcondition come back when it is awaited or joined.
        /// </summary>
        private Term StartDelegateCall(IInvocationOperation run, IInvocationOperation call, Frame f, SpecEnv spec)
        {
            var m = call.TargetMethod;
            var callee = _engine.ContractOf(m);
            if (!CanStart(call, callee))
            {
                NotModeled(run.Syntax, $"what '{m.Name}' holds can't be given to it here: a delegate can be given array cells and objects by Spec.Acc, but not views or predicates");
                return null;
            }
            var effects = EffectsOfCall(call, f, capturing: true);
            var result = StartCallOfDelegate(call, f, spec, out var finish);
            WarnIfTheyMayRace(run.Syntax, effects, f);
            WarnIfMayRace(run.Syntax, effects, EffectsAlongside(run.Syntax, TaskLocal(run)?.Name, f, null, effects.Covered));
            var task = _z3.Fresh("task", Sort.Int);
            _z3.Assume(NotNull(task));
            bool kept = TaskLocal(run) != null || IsAwaitedHere(run.Syntax) || InAwaitedWhenAllOfRuns(run.Syntax);
            if (!kept) Detached(run.Syntax, effects);
            if (!kept && run.Syntax.Parent is ExpressionStatementSyntax)
                Report("CSV1026", run.Syntax, "the task of 'Run' is never awaited: a failure in it would be lost (keep it and await it, or write '_ = ' if that is meant)", isError: true);
            f.Started[task.S] = new StartedTask(result, false, m, run.Syntax, effects, !kept, true, finish);
            Interleave(f);
            return task;
        }

        private Term StartCallOfDelegate(IInvocationOperation call, Frame f, SpecEnv spec, out System.Action<Frame> finish)
        {
            var outer = _awaitedCall;
            _awaitedCall = call;
            _startedCall = call;
            _startsLater = true;
            _finishStarted = null;
            try { return EvalInvocationCore(call, f, spec); }
            finally
            {
                finish = _finishStarted;
                _awaitedCall = outer;
                _startedCall = null;
                _startsLater = false;
            }
        }

        private bool InAwaitedWhenAllOfRuns(SyntaxNode run) =>
            run.Parent is ArgumentSyntax arg && arg.Parent?.Parent is InvocationExpressionSyntax all && IsWhenAll(_model.GetSymbolInfo(all).Symbol as IMethodSymbol) && IsAwaitedHere(all);

        // (from the syntax: in a flow graph, a lambda isn't one any more)
        private IOperation RunDelegate(IInvocationOperation inv) =>
            _model.GetOperation(inv.Arguments.First(a => a.Parameter?.Ordinal == 0).Value.Syntax);

        /// <summary>
        /// A task from code that isn't an async method here: an interface's, a delegate's, or a method that returns one. It too
        /// runs the program's code alongside what follows, for all that can be told. (A library's own, like Task.Delay's, doesn't.)
        /// </summary>
        private Term StartOther(IInvocationOperation inv, Frame f, SpecEnv spec)
        {
            var m = inv.TargetMethod;
            if (!IsTaskLike(m.ReturnType) || m.IsAsync || !(m.DeclaringSyntaxReferences.Length > 0 || m.MethodKind == MethodKind.DelegateInvoke)) return null;
            if (m.Name == "Yield" || inv.Arguments.Any(a => SpecSymbols.IsLinear(a.Parameter?.Type) || a.Parameter?.RefKind != RefKind.None)) return null;
            var effects = m.DeclaringSyntaxReferences.Length > 0 && !m.IsAbstract ? EffectsOfCall(inv, f) : null;
            WarnIfTheyMayRace(inv.Syntax, effects, f);
            _startedCall = inv;
            Term task;
            try { task = EvalInvocationCore(inv, f, spec); }
            finally { _startedCall = null; }
            var kept = TaskLocal(inv) != null;
            if (!kept && inv.Syntax.Parent is ExpressionStatementSyntax)
                Report("CSV1026", inv.Syntax, $"the task of '{m.Name}' is never awaited: a failure in it would be lost (keep it and await it, or write '_ = ' if that is meant)", isError: true);
            f.Started[task.S] = new StartedTask(TaskRunResult(inv), false, m, inv.Syntax, effects, !kept);
            Interleave(f);
            return task;
        }

        /// <summary>What awaiting a Task.Run's task gives: nothing known, but not null if the code it runs doesn't return that.</summary>
        private Term TaskRunResult(IInvocationOperation inv)
        {
            if (!(_model.GetTypeInfo(inv.Syntax).Type is INamedTypeSymbol { TypeArguments: { Length: 1 } } task)) return T.True;
            var r = Unknown(task.TypeArguments[0], "task");
            if (IsNonNullableType(task.TypeArguments[0])) _z3.Assume(NotNull(r));
            return r;
        }

        private void Detached(SyntaxNode at, TaskEffects effects)
        {
            if (effects == null)
                Warn(at, "this runs a delegate that can't be told, and keeps running after this method: what it does to state no lock guards isn't looked at");
            else if (effects.Writes.Select(x => x.field).FirstOrDefault(x => _engine.Locks.GuardOf(x) == null && !IsAtomic(x) && !_engine.Locks.IsFlag(x)) is ISymbol unguarded)
                Warn(at, $"this keeps running after this method, and writes '{unguarded.Name}', which no lock guards: it could race with whatever uses it, and every method is proved as if nothing did");
            else if (effects.WrittenArrays.Count > 0 && !effects.Covered)
                Warn(at, "this keeps running after this method, and writes arrays: it could race with whatever uses them, and every method is proved as if nothing did");
        }

        /// <summary>th.Start() of a local made by new Thread(d), and th.Join(): the same, with nothing to lose if it isn't joined.</summary>
        private void ThreadEvent(IInvocationOperation inv, Frame f, SpecEnv spec)
        {
            if (!_codeMode || !IsThread(inv.Instance?.Type) || inv.Arguments.Length != 0) return;
            if (inv.TargetMethod.Name == "Join")
            {
                var t = Eval(inv.Instance, f, spec);
                if (f.Started.TryGetValue(t.S, out var started))
                {
                    f.Started[t.S] = started.AsAwaited();
                    if (!started.Awaited && started.Finish != null) { Interleave(f); started.Finish(f); }
                }
                return;
            }
            if (inv.TargetMethod.Name != "Start") return;
            if (ThreadDelegateSyntax(inv.Instance) is AnonymousFunctionExpressionSyntax lambda && _engine.StartedDelegates.CallOf(lambda) is InvocationExpressionSyntax cs && _model.GetOperation(cs) is IInvocationOperation given)
            {
                if (!CanStart(given, _engine.ContractOf(given.TargetMethod))) { NotModeled(inv.Syntax, $"what '{given.TargetMethod.Name}' holds can't be given to it here: a delegate can be given array cells and objects by Spec.Acc, but not views or predicates"); return; }
                var mine = EffectsOfCall(given, f, capturing: true);
                Eval(inv.Instance, f, spec);
                StartCallOfDelegate(given, f, spec, out var finish);
                WarnIfTheyMayRace(inv.Syntax, mine, f);
                WarnIfMayRace(inv.Syntax, mine, EffectsAlongside(inv.Syntax, (inv.Instance as ILocalReferenceOperation)?.Local.Name, f, null, mine.Covered));
                f.Started[Eval(inv.Instance, f, spec).S] = new StartedTask(T.True, false, inv.TargetMethod, inv.Syntax, mine, true, true, finish);
                Interleave(f);
                return;
            }
            var effects = ThreadDelegate(inv.Instance, f);
            WarnIfTheyMayRace(inv.Syntax, effects, f);
            if (effects != null) WarnIfMayRace(inv.Syntax, effects, EffectsAlongside(inv.Syntax, (inv.Instance as ILocalReferenceOperation)?.Local.Name, f, ThreadDelegateSyntax(inv.Instance), false));
            // (one that is joined somewhere is warned of by what runs alongside it, up to there)
            bool joined = inv.Instance is ILocalReferenceOperation th && _contract.Declaration.DescendantNodes().OfType<InvocationExpressionSyntax>().Any(j =>
                j.Expression is MemberAccessExpressionSyntax jm && jm.Name.Identifier.Text == "Join" && SymbolEqualityComparer.Default.Equals(_model.GetSymbolInfo(jm.Expression).Symbol, th.Local));
            if (!joined) Detached(inv.Syntax, effects);
            f.Started[Eval(inv.Instance, f, spec).S] = new StartedTask(T.True, false, inv.TargetMethod, inv.Syntax, effects, true);
        }

        private SyntaxNode ThreadDelegateSyntax(IOperation thread) =>
            thread is ILocalReferenceOperation l && l.Local.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() is VariableDeclaratorSyntax d &&
            d.Initializer?.Value is BaseObjectCreationExpressionSyntax c && c.ArgumentList?.Arguments.Count > 0 ? c.ArgumentList.Arguments[0].Expression : null;

        private TaskEffects ThreadDelegate(IOperation thread, Frame f) =>
            ThreadDelegateSyntax(thread) is SyntaxNode d && _model.GetOperation(d) is IOperation op ? EffectsOfDelegate(op, f) : null;

        /// <summary>At the end of the method: every task it started has been awaited, or a failure in it would be lost.</summary>
        private void CheckAllAwaited(Frame f)
        {
            if (!_codeMode) return;
            foreach (var t in f.Started.Values.Where(t => !t.Awaited && !t.Detached))
                Report("CSV1026", t.At, $"the task of '{t.Method.Name}' might not be awaited on every path: a failure in it would be lost", isError: true);
        }

        /// <summary>A task started in a loop's body and not awaited by its end: the next round's local is another one, so nothing could await it.</summary>
        private void CheckAwaitedInLoop(Loop loop, Frame f)
        {
            if (!_codeMode || loop.Syntax == null) return;
            foreach (var t in f.Started.Values.Where(t => !t.Awaited && !t.Detached && loop.Syntax.Span.Contains(t.At.Span)))
                Report("CSV1026", t.At, $"the task of '{t.Method.Name}' might not be awaited on every path: a failure in it would be lost", isError: true);
        }

        /// <summary><c>await t</c> or <c>await Task.WhenAll(...)</c> of tasks this method holds; null for anything else.</summary>
        private Term AwaitStarted(IOperation operand, IAwaitOperation aw, Frame f, SpecEnv spec)
        {
            if (Unconverted(operand) is ILocalReferenceOperation)
            {
                var t = Eval(Unconverted(operand), f, spec);
                if (!f.Started.TryGetValue(t.S, out var started)) return null;
                f.Started[t.S] = started.AsAwaited();
                if (!started.Awaited) { MayRaise(T.True, f, null); Interleave(f); started.Finish?.Invoke(f); }
                return started.Result;
            }
            // (await Task.Run(() => F(x)), with permissions for it)
            if (operand is IInvocationOperation run && DelegateCallOf(run) != null)
            {
                var t = Eval(run, f, spec);
                var running = f.Started[t.S];
                f.Started[t.S] = running.AsAwaited();
                MayRaise(T.True, f, null);
                Interleave(f);
                running.Finish?.Invoke(f);
                return running.Result;
            }
            if (!(operand is IInvocationOperation all) || !IsWhenAll(all.TargetMethod)) return null;
            // (from the syntax: whether a list of them is an array or a span depends on the framework)
            var elements = ((InvocationExpressionSyntax)all.Syntax).ArgumentList.Arguments.Select(a => Unconverted(_model.GetOperation(a.Expression))).ToList();
            // (only a list of them as written: an array built elsewhere isn't followed; each is a task held, or a call of an async method here)
            // (await Task.WhenAll(ts), with ts made by ids.Select(id => F(id)): those are over, whatever they did)
            if (elements.Count == 1 && elements[0] is ILocalReferenceOperation many && many.Local.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() is VariableDeclaratorSyntax { Initializer: { } made })
                foreach (var kv in f.Started.ToList())
                    if (kv.Value.Detached && !kv.Value.Awaited && made.Span.Contains(kv.Value.At.Span))
                        f.Started[kv.Key] = kv.Value.AsAwaited();
            if (elements.Count == 0 || elements.Any(e => !(e is ILocalReferenceOperation l && f.Started.ContainsKey(Eval(l, f, spec).S) ||
                                                           e is IInvocationOperation c && (c.TargetMethod.IsAsync && _engine.ContractOf(c.TargetMethod).HasSource || DelegateCallOf(c) != null)))) return null;
            var results = new List<Term>();
            var finishing = new List<System.Action<Frame>>();
            foreach (var e in elements)
            {
                var t = Eval(e, f, spec);
                results.Add(f.Started[t.S].Result);
                if (!f.Started[t.S].Awaited && f.Started[t.S].Finish != null) finishing.Add(f.Started[t.S].Finish);
                f.Started[t.S] = f.Started[t.S].AsAwaited();
            }
            MayRaise(T.True, f, null);
            Interleave(f);
            foreach (var finish in finishing) finish(f);
            if (aw.Type == null || aw.Type.SpecialType == SpecialType.System_Void || !(aw.Type is IArrayTypeSymbol)) return T.True;
            // Task<T>: an array of what they gave, in order, of its own
            var arr = Unknown(aw.Type, "whenAll");
            _z3.Assume(NotNull(arr));
            _z3.Assume(T.Eq(Len(arr), T.Int(results.Count)));
            NewArrayIsDistinct(arr, f);
            var row = T.ZeroRow();
            for (int i = 0; i < results.Count; i++) row = T.Store(row, T.Int(i), T.Coerce(results[i], Sort.Int));
            f.Heap = T.Store(f.Heap, arr, row);
            return arr;
        }

        /// <summary><c>t.Result</c>, of a task this method holds: what it gave, once awaited. Before that, it would block.</summary>
        private Term TaskResult(IPropertyReferenceOperation pr, Frame f, SpecEnv spec)
        {
            if (pr.Property.Name != "Result" || !(pr.Instance is ILocalReferenceOperation l) || f.Started.Count == 0) return null;
            var t = Eval(l, f, spec);
            if (!f.Started.TryGetValue(t.S, out var started)) return null;
            if (!started.Awaited && _codeMode)
                Report("CSV1026", pr.Syntax, $"the task of '{started.Method.Name}' might not have finished: reading Result blocks until it does, and that can deadlock (await it first)", isError: true);
            return T.Coerce(started.Result, SortOf(pr.Type));
        }

        private Term EvalAwait(IAwaitOperation aw, Frame f, SpecEnv spec)
        {
            var operand = aw.Operation;
            // (x.ConfigureAwait(b) awaits x)
            while (operand is IInvocationOperation ca && ca.TargetMethod.Name == "ConfigureAwait" && ca.Instance != null && ca.TargetMethod.DeclaringSyntaxReferences.Length == 0)
                operand = ca.Instance;
            if (AwaitStarted(operand, aw, f, spec) is Term given) return given;
            Term result;
            if (operand is IInvocationOperation call && (call.TargetMethod.IsAsync && _engine.ContractOf(call.TargetMethod).HasSource || IsAsyncStubbed(call.TargetMethod)))
            {
                // an async method of the program, or a library one with an async stub: a call whose postcondition
                // holds when its task completes
                var outer = _awaitedCall;
                _awaitedCall = call;
                try { result = Eval(call, f, spec); }
                finally { _awaitedCall = outer; }
                for (var w = aw.Operation; w != call; w = ((IInvocationOperation)w).Instance)
                    foreach (var a in ((IInvocationOperation)w).Arguments) Eval(a.Value, f, spec); // (ConfigureAwait's argument)
                if (AwaitedType(call.TargetMethod) == null) result = T.True;
            }
            else
            {
                Eval(aw.Operation, f, spec);
                result = aw.Type == null || aw.Type.SpecialType == SpecialType.System_Void ? T.True : Unknown(aw.Type, "awaited");
                // a library task's result is as the library declares it; a faulted task throws here
                if (operand is IInvocationOperation li && li.TargetMethod.OriginalDefinition.ReturnType is INamedTypeSymbol lt &&
                    lt.TypeArguments.Length == 1 && result.Sort == Sort.Int &&
                    (IsNonNullableType(lt.TypeArguments[0]) || lt.TypeArguments[0] is ITypeParameterSymbol && lt.TypeArgumentNullableAnnotations[0] == NullableAnnotation.NotAnnotated &&
                        (IsNonNullableType(aw.Type) || IsTaskRun(li.TargetMethod) && _model.GetTypeInfo(aw.Syntax).Nullability.FlowState == NullableFlowState.NotNull)))
                    _z3.Assume(NotNull(result));
                MayRaise(T.True, f, null);
            }
            Interleave(f);
            // (await g.WaitAsync(): past here it's ours)
            if (operand is IInvocationOperation taking && (GateOf(taking, "WaitAsync", f) ?? GateOfWrapperCall(taking, true, f)) is { } got)
            {
                ProveOrderAt(taking.Syntax, f, spec);
                GateTaken(got, f);
                if (result.Sort == Sort.Int) _z3.Assume(NotNull(result)); // (what it gives is there to give it back)
            }
            return result;
        }

        /// <summary>
        /// Other code ran: everything this method does not hold may have changed. (It cannot hold what this method
        /// holds: views are linear, and permissions add up to one.)
        /// </summary>
        private void Interleave(Frame f)
        {
            var guarded = GuardedByHeldGates(f);
            var confined = ConfinedValues(f, null);
            var before = f.Heap;
            var fresh = _z3.Fresh("heap", Sort.Heap);
            f.Heap = _arrayMode && f.ArrPerm != null
                ? CellwiseHeap($"(ite (> (select (select {f.ArrPerm} x) i) 0.0) (select (select {before} x) i) (select (select {fresh} x) i))")
                : fresh;
            f.Heap = KeepHeldMemory(f.Heap, before, f.ArrPerm);

            f.Heap = KeepConfinedArrays(f.Heap, before, confined);

            var owned = f.Perm != null ? _engine.Fields.OwnedFields().ToDictionary(x => x, x => FieldMap(f, x), SymbolEqualityComparer.Default) : null;
            var rootBefore = f.Root;
            HavocAllFieldsKeeping(f, confined);
            if (owned != null)
            {
                // an object is in hand when its view (or its tree's root's) is
                var held = rootBefore != null
                    ? $"(or (>= (select {f.Perm} y) 1.0) (>= (select {f.Perm} (select {rootBefore} y)) 1.0))"
                    : $"(>= (select {f.Perm} y) 1.0)";
                foreach (var kv in owned)
                    f.Fields[kv.Key] = Pointwise(kv.Key.Name, MapSort(kv.Key), $"(ite {held} (select {kv.Value} y) (select {FreshMap(kv.Key)} y))");
                if (rootBefore != null)
                    f.Root = Pointwise("root", Sort.Row, $"(ite {held} (select {rootBefore} y) (select {_z3.Fresh("root", Sort.Row)} y))");
            }
            else if (f.Root != null) f.Root = _z3.Fresh("root", Sort.Row);
            KeepGuarded(guarded, f);
            AllocAfterCall(f);
            HavocClosureLocals(f);
        }

        // ================================================================================== closures

        private HashSet<ISymbol> _closureWritten;

        /// <summary>
        /// The method's locals and parameters that a lambda or local function in it writes: any call may run one of
        /// those (it was handed the delegate, or the local function is called), and so may other code at an await.
        /// </summary>
        private HashSet<ISymbol> ClosureWritten()
        {
            if (_closureWritten != null) return _closureWritten;
            _closureWritten = new HashSet<ISymbol>(SymbolEqualityComparer.Default);
            foreach (var fn in _contract.Declaration.DescendantNodes().Where(n => n is AnonymousFunctionExpressionSyntax || n is LocalFunctionStatementSyntax))
            {
                var flow = _model.AnalyzeDataFlow(fn);
                if (flow == null || !flow.Succeeded) continue;
                foreach (var s in flow.WrittenInside)
                    if ((s is ILocalSymbol || s is IParameterSymbol) && !s.DeclaringSyntaxReferences.Any(r => fn.Span.Contains(r.Span)) &&
                        SymbolEqualityComparer.Default.Equals(s.ContainingSymbol, _method))
                        _closureWritten.Add(s);
            }
            return _closureWritten;
        }

        /// <summary>After a call (or an await): what lambdas and local functions may have written is unknown.</summary>
        private void HavocClosureLocals(Frame f)
        {
            foreach (var s in ClosureWritten())
            {
                f.Vars[s] = FreshOf(TypeOf(s), s.Name);
                if (IsNonNullVariable(s)) _z3.Assume(NotNull(f.Vars[s]));
            }
        }

        // ================================================================================== confined locals

        private HashSet<ILocalSymbol> _confined;

        /// <summary>
        /// The objects in the method's confined locals (except those in <paramref name="except"/>): no other code can
        /// reach them, so an await leaves their fields and cells as they were.
        /// </summary>
        private IReadOnlyList<Term> ConfinedValues(Frame f, ICollection<ISymbol> except) =>
            Confined().Where(l => f.Vars.ContainsKey(l) && (except == null || !except.Contains(l)))
                .Select(l => f.Vars[l]).Where(v => v.Sort == Sort.Int).ToList();

        /// <summary>A heap equal to <paramref name="before"/> at the arrays <paramref name="objs"/>.</summary>
        private Term KeepConfinedArrays(Term heap, Term before, IReadOnlyList<Term> objs)
        {
            if (objs == null) return heap;
            foreach (var o in objs)
                _z3.Assume(T.Implies(NotNull(o), T.Eq(T.Select(heap, o, Sort.Row), T.Select(before, o, Sort.Row))));
            return heap;
        }

        /// <summary>
        /// The locals of an async method that confine their objects: each holds only objects the method made itself
        /// (<c>new</c>, whose constructor does not hand out <c>this</c>), and is used only in ways that cannot hand its
        /// object to other code: reading and writing its fields and elements, comparing it with null, calling members
        /// of the base class library that do not keep their receiver (any result that may be the object is used the same
        /// way), <c>foreach</c> and <c>using</c> over it, and passing it to pure functions and specifications. It is
        /// not captured by a lambda or local function. Such an object is reachable only through the local, so no code
        /// that runs at an await can read or write it.
        /// </summary>
        private HashSet<ILocalSymbol> Confined()
        {
            if (_confined != null) return _confined;
            _confined = new HashSet<ILocalSymbol>(SymbolEqualityComparer.Default);
            if (_contract.Declaration == null) return _confined;
            var body = _contract.Declaration;
            var ok = new Dictionary<ILocalSymbol, bool>(SymbolEqualityComparer.Default);
            foreach (var d in body.DescendantNodes().OfType<VariableDeclaratorSyntax>())
                if (_model.GetDeclaredSymbol(d) is ILocalSymbol l && l.RefKind == RefKind.None && l.Type.IsReferenceType &&
                    l.Type.SpecialType != SpecialType.System_String && SymbolEqualityComparer.Default.Equals(l.ContainingSymbol, _method))
                    // (a using declaration disposes it: only the library's Dispose is known not to hand it out)
                    ok[l] = (d.Initializer == null || FreshObject(d.Initializer.Value)) &&
                            (!(d.Parent?.Parent is LocalDeclarationStatementSyntax ld) || ld.UsingKeyword.IsKind(SyntaxKind.None) || IsLibrary(l.Type));
            foreach (var id in body.DescendantNodes().OfType<IdentifierNameSyntax>())
                if (_model.GetSymbolInfo(id).Symbol is ILocalSymbol l && ok.TryGetValue(l, out var good) && good && !ConfinedUse(id))
                    ok[l] = false;
            foreach (var kv in ok) if (kv.Value) _confined.Add(kv.Key);
            return _confined;
        }

        private static ExpressionSyntax Unparenthesized(ExpressionSyntax e)
        {
            while (e is ParenthesizedExpressionSyntax p) e = p.Expression;
            return e;
        }

        private static SyntaxNode Outer(SyntaxNode e)
        {
            while (e.Parent is ParenthesizedExpressionSyntax) e = e.Parent;
            return e;
        }

        /// <summary>A new object no other code has: an array, or an object whose constructor keeps <c>this</c> to itself.</summary>
        private bool FreshObject(ExpressionSyntax value)
        {
            switch (Unparenthesized(value))
            {
                case LiteralExpressionSyntax lit: return lit.IsKind(SyntaxKind.NullLiteralExpression) || lit.IsKind(SyntaxKind.DefaultLiteralExpression);
                case DefaultExpressionSyntax _:
                case ArrayCreationExpressionSyntax _:
                case ImplicitArrayCreationExpressionSyntax _:
                case InitializerExpressionSyntax _:
                    return true;
                case BaseObjectCreationExpressionSyntax oc:
                    if (!(_model.GetSymbolInfo(oc).Symbol is IMethodSymbol ctor) || !CtorKeepsThis(ctor, 0)) return false;
                    if (oc.Initializer == null || oc.Initializer.IsKind(SyntaxKind.CollectionInitializerExpression)) return oc.Initializer == null || IsLibrary(ctor.ContainingType);
                    // an object initializer sets fields and plain properties
                    return oc.Initializer.Expressions.All(x => x is AssignmentExpressionSyntax a && a.Left is IdentifierNameSyntax n &&
                                                               PlainMember(_model.GetSymbolInfo(n).Symbol));
                default: return false;
            }
        }

        /// <summary>A member of the base class library (outside threading, which may hand objects to other threads).</summary>
        private static bool IsLibrary(ISymbol s)
        {
            var type = s as INamedTypeSymbol ?? s.ContainingType;
            if (type == null || type.DeclaringSyntaxReferences.Length > 0) return false;
            var ns = type.ContainingNamespace?.ToDisplayString() ?? "";
            return (ns == "System" || ns.StartsWith("System.")) && !ns.StartsWith("System.Threading") && !ns.StartsWith("System.Runtime") &&
                   !ns.StartsWith("System.Reflection");
        }

        /// <summary>A field, or a property whose accessors are the compiler's (an auto-property, a record's positional one), or the library's.</summary>
        private static bool PlainMember(ISymbol s)
        {
            switch (s)
            {
                case IFieldSymbol _: return true;
                case IPropertySymbol p:
                    if (IsLibrary(p)) return true;
                    if (p.IsIndexer) return false;
                    return p.DeclaringSyntaxReferences.Select(r => r.GetSyntax()).All(d =>
                        d is ParameterSyntax ||
                        d is PropertyDeclarationSyntax pd && pd.ExpressionBody == null && pd.AccessorList != null &&
                        pd.AccessorList.Accessors.All(a => a.Body == null && a.ExpressionBody == null));
                default: return false;
            }
        }

        private bool IsPureMember(IMethodSymbol m) =>
            m != null && (SpecSymbols.IsPureCallee(m) || SpecSymbols.IsPure(m.OriginalDefinition) || _engine.ContractOf(m.OriginalDefinition).IsPure);

        /// <summary>A constructor that does not hand out the object it builds (nor do the constructors it chains to).</summary>
        private bool CtorKeepsThis(IMethodSymbol ctor, int depth)
        {
            if (depth > 16) return false;
            var type = ctor.ContainingType;
            if (type.DeclaringSyntaxReferences.Length == 0) return IsLibrary(type);
            if (type.TypeKind != TypeKind.Class) return false;
            var decl = ctor.DeclaringSyntaxReferences.Select(r => r.GetSyntax()).OfType<ConstructorDeclarationSyntax>().FirstOrDefault();
            if (decl == null) return BaseKeepsThis(type, depth);
            var model = _engine.ModelOf(decl.SyntaxTree);
            if (Leaks(decl, model)) return false;
            if (decl.Initializer != null && decl.Initializer.IsKind(SyntaxKind.ThisConstructorInitializer))
                return model.GetSymbolInfo(decl.Initializer).Symbol is IMethodSymbol target && CtorKeepsThis(target, depth + 1);
            if (decl.Initializer != null)
                return model.GetSymbolInfo(decl.Initializer).Symbol is IMethodSymbol baseCtor && CtorKeepsThis(baseCtor, depth + 1);
            return BaseKeepsThis(type, depth);
        }

        private bool BaseKeepsThis(INamedTypeSymbol type, int depth)
        {
            var b = type.BaseType;
            if (b == null || b.SpecialType == SpecialType.System_Object) return true;
            // (a library base may call the class's overrides, which may hand out this)
            if (b.DeclaringSyntaxReferences.Length == 0) return false;
            var ctor = b.InstanceConstructors.FirstOrDefault(c => c.Parameters.Length == 0);
            return ctor != null && CtorKeepsThis(ctor, depth + 1);
        }

        /// <summary>Code in a constructor that may hand out <c>this</c>: using it as a value, or calling its methods or accessors that are not plain.</summary>
        private bool Leaks(SyntaxNode code, SemanticModel model)
        {
            foreach (var n in code.DescendantNodes())
            {
                switch (n)
                {
                    case AnonymousFunctionExpressionSyntax _:
                    case LocalFunctionStatementSyntax _:
                        return true;
                    case ThisExpressionSyntax _:
                    case BaseExpressionSyntax _:
                        if (!(Outer(n).Parent is MemberAccessExpressionSyntax ma && ma.Expression == Outer(n) && ThisMemberOk(ma, model))) return true;
                        break;
                    case IdentifierNameSyntax id when !(id.Parent is MemberAccessExpressionSyntax pm && pm.Name == id && !(pm.Expression is ThisExpressionSyntax)):
                        var s = model.GetSymbolInfo(id).Symbol;
                        if (s != null && !s.IsStatic && (s is IMethodSymbol m && !IsPureMember(m) || s is IEventSymbol ||
                                                         s is IPropertySymbol && !PlainMember(s)) &&
                            s.ContainingType != null && !(s is IMethodSymbol lm && lm.MethodKind == MethodKind.LocalFunction))
                            return true;
                        break;
                }
            }
            return false;
        }

        private bool ThisMemberOk(MemberAccessExpressionSyntax ma, SemanticModel model)
        {
            var s = model.GetSymbolInfo(ma).Symbol;
            return s is IMethodSymbol m ? IsPureMember(m) : PlainMember(s);
        }

        /// <summary>A use of a candidate confined local (or of a result that may be its object) that keeps it confined.</summary>
        private bool ConfinedUse(SyntaxNode node)
        {
            if (SpecSymbols.IsInGhostContext(node, _model)) return true;
            for (var a = node.Parent; a != null && a != _contract.Declaration; a = a.Parent)
                if (a is AnonymousFunctionExpressionSyntax || a is LocalFunctionStatementSyntax) return false;
            var e = Outer(node);
            switch (e.Parent)
            {
                case ExpressionStatementSyntax _:
                case ReturnStatementSyntax _:
                    return true;
                case MemberAccessExpressionSyntax ma when ma.Expression == e:
                    return ConfinedMember(ma);
                case ElementAccessExpressionSyntax ea when ea.Expression == e:
                    if (_model.GetTypeInfo(ea.Expression).Type is IArrayTypeSymbol) return true;
                    return _model.GetSymbolInfo(ea).Symbol is IPropertySymbol ix && (IsLibrary(ix) || ix.GetMethod != null && IsPureMember(ix.GetMethod) && !IsWriteTarget(ea));
                case AssignmentExpressionSyntax asg when asg.Left == e:
                    return node is IdentifierNameSyntax && asg.IsKind(SyntaxKind.SimpleAssignmentExpression) && FreshObject(asg.Right) &&
                           Outer(asg).Parent is ExpressionStatementSyntax;
                case BinaryExpressionSyntax b when b.IsKind(SyntaxKind.EqualsExpression) || b.IsKind(SyntaxKind.NotEqualsExpression):
                    return Unparenthesized(b.Left == e ? b.Right : b.Left).IsKind(SyntaxKind.NullLiteralExpression);
                case IsPatternExpressionSyntax ip when ip.Expression == e:
                    return ip.Pattern is ConstantPatternSyntax || ip.Pattern is UnaryPatternSyntax u && u.Pattern is ConstantPatternSyntax;
                case ForEachStatementSyntax fe when fe.Expression == e:
                    return _model.GetTypeInfo(fe.Expression).Type is IArrayTypeSymbol ||
                           _model.GetForEachStatementInfo(fe).GetEnumeratorMethod is IMethodSymbol ge && IsLibrary(ge);
                case UsingStatementSyntax us when us.Expression == e:
                    return _model.GetTypeInfo(us.Expression).Type is ITypeSymbol ut && IsLibrary(ut);
                case ArgumentSyntax arg when arg.RefKindKeyword.IsKind(SyntaxKind.None) && arg.Parent?.Parent is InvocationExpressionSyntax inv:
                    if (inv.Expression is IdentifierNameSyntax nm && nm.Identifier.Text == "nameof") return true;
                    if (!(_model.GetSymbolInfo(inv).Symbol is IMethodSymbol callee)) return false;
                    if (SpecSymbols.IsGhostMethod(callee) || IsPureMember(callee)) return true;
                    // a static library method that cannot keep it (its result holds no reference to it)
                    return callee.IsStatic && IsLibrary(callee) && callee.MethodKind != MethodKind.ReducedExtension && HoldsNoObject(callee.ReturnsVoid ? null : callee.ReturnType);
                default:
                    return false;
            }
        }

        private bool IsWriteTarget(ExpressionSyntax e) =>
            Outer(e).Parent is AssignmentExpressionSyntax a && a.Left == Outer(e) ||
            Outer(e).Parent is PrefixUnaryExpressionSyntax || Outer(e).Parent is PostfixUnaryExpressionSyntax;

        /// <summary>A value that cannot refer to an object: none, a primitive, an enum, a string, or a ref struct (which cannot outlive an await).</summary>
        private static bool HoldsNoObject(ITypeSymbol t) =>
            t == null || t.SpecialType == SpecialType.System_Void || t.TypeKind == TypeKind.Enum || t.SpecialType != SpecialType.None && t.SpecialType != SpecialType.System_Object ||
            t.IsRefLikeType;

        private static bool IsTaskType(ITypeSymbol t) =>
            t is INamedTypeSymbol n && (n.Name == "Task" || n.Name == "ValueTask") && n.ContainingNamespace?.ToDisplayString() == "System.Threading.Tasks";

        /// <summary>A result that stands for work still running (an IAsyncResult, or anything awaitable that is not a task).</summary>
        private static bool IsPendingWork(ITypeSymbol t) =>
            t.Name == "IAsyncResult" || t.AllInterfaces.Any(i => i.Name == "IAsyncResult") ||
            t.GetMembers("GetAwaiter").Any() || t.Name.EndsWith("Awaitable");

        /// <summary><c>x.M</c> on a confined local's object: a plain member, or a call that keeps it, with its result used so too.</summary>
        private bool ConfinedMember(MemberAccessExpressionSyntax ma)
        {
            var s = _model.GetSymbolInfo(ma).Symbol;
            if (s is IFieldSymbol) return true;
            if (s is IPropertySymbol p)
            {
                if (PlainMember(p)) return IsLibrary(p) ? ConfinedResult(ma, p.Type, p.OriginalDefinition.Type) : true;
                return p.GetMethod != null && IsPureMember(p.GetMethod) && !IsWriteTarget(ma);
            }
            if (!(s is IMethodSymbol m) || !(Outer(ma).Parent is InvocationExpressionSyntax inv) || inv.Expression != Outer(ma)) return false;
            if (IsPureMember(m)) return true;
            if (!IsLibrary(m)) return false;
            if (m.MethodKind == MethodKind.ReducedExtension && !(m.Name == "AsSpan" && m.ContainingType.Name == "MemoryExtensions")) return false;
            return ConfinedResult(inv, m.ReturnsVoid ? null : m.ReturnType, m.OriginalDefinition.ReturnType);
        }

        /// <summary>
        /// The result of a library member of a confined object: nothing that can refer to it, an element (of a type
        /// parameter), or, if it may be the object or hold it, used as the object may be. A task must be awaited at once.
        /// </summary>
        private bool ConfinedResult(ExpressionSyntax at, ITypeSymbol type, ITypeSymbol declared)
        {
            if (type == null || declared is ITypeParameterSymbol) return true;
            if (IsTaskType(type))
            {
                SyntaxNode e = Outer(at);
                while (e.Parent is MemberAccessExpressionSyntax ca && ca.Name.Identifier.Text == "ConfigureAwait" && Outer(ca).Parent is InvocationExpressionSyntax ci)
                    e = Outer(ci);
                if (!(e.Parent is AwaitExpressionSyntax aw)) return false;
                var awaited = ((INamedTypeSymbol)type).TypeArguments.FirstOrDefault();
                var declaredAwaited = (declared as INamedTypeSymbol)?.TypeArguments.FirstOrDefault();
                return awaited == null || declaredAwaited is ITypeParameterSymbol || HoldsNoObject(awaited) || ConfinedUse(aw);
            }
            if (IsPendingWork(type)) return false;
            if (type.TypeKind == TypeKind.Enum || type.SpecialType != SpecialType.None && type.SpecialType != SpecialType.System_Object || type.IsRefLikeType) return true;
            return ConfinedUse(at);
        }

        private bool RunsCode(IMethodSymbol m)
        {
            var c = _engine.ContractOf(m);
            return !c.IsPure && !c.IsLemma && !SpecSymbols.IsSpecClass(m.ContainingType) && !SpecSymbols.IsGhostOf(m);
        }
    }
}
