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
    /// (CSV1026). What is lent to a call isn't back until it returns, so it can't lend permissions to one like this;</item>
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
                    var effects = EffectsOf(l);
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
            // (what is lent to it isn't back until it returns, and returning is what this doesn't follow)
            if (inv.Arguments.Any(a => SpecSymbols.IsLinear(a.Parameter?.Type) || a.Parameter?.RefKind != RefKind.None) || MentionsCells(callee))
                return null;
            // (it would run on what its caller holds the lock for, while its caller does too)
            if (_engine.Locks.GuardOf(m) is IFieldSymbol held && LockGuards.IsSemaphore(held))
                Report("CSV1023", inv.Syntax, $"'{m.Name}' relies on holding '{held.Name}', but its task isn't awaited here: it would run alongside this code", isError: true);
            var effects = EffectsOf(m);
            WarnIfTheyMayRace(inv.Syntax, effects, f);
            var outer = _awaitedCall;
            _awaitedCall = inv;
            _startedCall = inv;
            Term result;
            try { result = EvalInvocationCore(inv, f, spec); }
            finally { _awaitedCall = outer; _startedCall = null; }
            var task = _z3.Fresh("task", Sort.Int);
            _z3.Assume(NotNull(task));
            f.Started[task.S] = new StartedTask(AwaitedType(m) == null ? T.True : result, false, m, inv.Syntax, effects);
            // (what its contract said of the state is of the state when it completes, whenever that is: not of this one)
            Interleave(f);
            return task;
        }

        /// <summary>What some code may use, to tell if it can race with other code.</summary>
        private sealed class TaskEffects
        {
            public string Name;
            public readonly HashSet<ISymbol> Writes = new HashSet<ISymbol>(SymbolEqualityComparer.Default);
            public readonly HashSet<ISymbol> Reads = new HashSet<ISymbol>(SymbolEqualityComparer.Default);
            public bool WritesArrays, UsesArrays;

            public void Add(TaskEffects o)
            {
                Writes.UnionWith(o.Writes);
                Reads.UnionWith(o.Reads);
                WritesArrays |= o.WritesArrays;
                UsesArrays |= o.UsesArrays;
            }
        }

        private TaskEffects EffectsOf(IMethodSymbol m)
        {
            var e = new TaskEffects { Name = m.Name };
            AddEffects(m, e, new HashSet<IMethodSymbol>(SymbolEqualityComparer.Default));
            return e;
        }

        private void AddEffects(IMethodSymbol m, TaskEffects e, HashSet<IMethodSymbol> seen)
        {
            if (!seen.Add(m.OriginalDefinition)) return;
            var refs = m.OriginalDefinition.DeclaringSyntaxReferences;
            if (refs.Length == 0)
            {
                // the library's: what a contract says it does, and for the rest there's nothing to go on
                if (IsTaskRun(m) || !_engine.ContractOf(m).IsStub) return;
                e.Writes.UnionWith(_engine.Fields.WritesOf(m).Item1);
                e.Reads.UnionWith(_engine.Fields.ReadsOf(m));
                e.WritesArrays |= _engine.MayWriteHeap(m);
                e.UsesArrays |= _engine.MayTouchArrays(m);
                return;
            }
            foreach (var r in refs) AddEffects(r.GetSyntax(), _engine.ModelOf(r.SyntaxTree), e, seen, null);
        }

        /// <summary>What's done under a lock doesn't count, even to what isn't a field (a dictionary's contents): that is what a lock is for.</summary>
        private void AddEffects(SyntaxNode code, SemanticModel model, TaskEffects e, HashSet<IMethodSymbol> seen, SyntaxNode except)
        {
            bool Enter(SyntaxNode x) => x != except && !(x is LockStatementSyntax) && !(x is TryStatementSyntax t && LockGuards.GateOfTry(t, model) != null);
            var inside = code.DescendantNodes(Enter);
            foreach (var n in inside)
                switch (n)
                {
                    case SimpleNameSyntax name when !(name.Parent is NameColonSyntax) && !(name.Parent is NameEqualsSyntax):
                        var symbol = model.GetSymbolInfo(name).Symbol;
                        if (symbol is IPropertySymbol stubbed && stubbed.DeclaringSyntaxReferences.Length == 0) symbol = LockGuards.IsWriteTarget(name) ? stubbed.SetMethod : stubbed.GetMethod;
                        if (symbol is IMethodSymbol callee) AddEffects(callee, e, seen);
                        else if (symbol != null && FieldEffects.IsHeapField(symbol))
                        {
                            ExpressionSyntax whole = name.Parent is MemberAccessExpressionSyntax ma && ma.Name == name ? ma : name;
                            if (LockGuards.IsWriteTarget(whole)) e.Writes.Add(FieldEffects.Key(symbol)); else e.Reads.Add(FieldEffects.Key(symbol));
                        }
                        break;
                    case ElementAccessExpressionSyntax ea when model.GetTypeInfo(ea.Expression).Type is IArrayTypeSymbol:
                        e.UsesArrays = true;
                        if (LockGuards.IsWriteTarget(ea)) e.WritesArrays = true;
                        break;
                    case ElementAccessExpressionSyntax ea when model.GetSymbolInfo(ea).Symbol is IPropertySymbol ix:
                        // (d[k] = v: a library's indexer)
                        if ((LockGuards.IsWriteTarget(ea) ? ix.SetMethod : ix.GetMethod) is IMethodSymbol accessor) AddEffects(accessor, e, seen);
                        break;
                }
        }

        /// <summary>What a piece of this method's source uses, itself and through its calls.</summary>
        private TaskEffects EffectsOf(SyntaxNode code, SyntaxNode except = null)
        {
            var e = new TaskEffects { Name = "this method" };
            AddEffects(code, _model, e, new HashSet<IMethodSymbol>(SymbolEqualityComparer.Default), except);
            return e;
        }

        /// <summary>What a delegate handed to a thread may use. Null if it can't be told which code it is.</summary>
        private TaskEffects EffectsOfDelegate(IOperation d)
        {
            d = Unconverted(d);
            if (d is IDelegateCreationOperation dc) d = Unconverted(dc.Target);
            if (d is IAnonymousFunctionOperation af) { var e = EffectsOf(af.Syntax); e.Name = "the delegate"; return e; }
            if (d is IMethodReferenceOperation mr && mr.Method.DeclaringSyntaxReferences.Length > 0) return EffectsOf(mr.Method);
            return null;
        }

        /// <summary>A field or array one writes and the other uses, that no lock guards.</summary>
        private void WarnIfMayRace(SyntaxNode at, TaskEffects a, TaskEffects b)
        {
            if (a == null || b == null) return;
            bool Unguarded(ISymbol x) => _engine.Locks.GuardOf(x) == null;
            var shared = a.Writes.Where(x => Unguarded(x) && (b.Writes.Contains(x) || b.Reads.Contains(x))).Concat(b.Writes.Where(x => Unguarded(x) && a.Reads.Contains(x))).FirstOrDefault();
            if (shared != null)
                Warn(at, $"'{a.Name}' and '{b.Name}' run at once, and '{shared.Name}' is written by one and used by the other: on one object, that could race, and each is proved as if alone");
            else if (a.WritesArrays && b.UsesArrays || b.WritesArrays && a.UsesArrays)
                Warn(at, $"'{a.Name}' and '{b.Name}' run at once, and one writes arrays the other may use: on one array, that could race, and each is proved as if alone");
        }

        /// <summary>Two tasks running at once, where one writes what the other uses, each proved as if alone.</summary>
        private void WarnIfTheyMayRace(SyntaxNode at, TaskEffects mine, Frame f)
        {
            foreach (var other in f.Started.Values.Where(t => !t.Awaited))
                WarnIfMayRace(at, mine, other.Effects as TaskEffects);
        }

        // ================================================================================== Task.Run and threads

        /// <summary><c>await X</c> or <c>await X.ConfigureAwait(b)</c>: X doesn't run alongside what comes after.</summary>
        private static bool IsAwaitedHere(SyntaxNode call)
        {
            var e = call.Parent;
            while (e is ParenthesizedExpressionSyntax) e = e.Parent;
            if (e is MemberAccessExpressionSyntax ma && ma.Name.Identifier.Text == "ConfigureAwait" && ma.Parent is InvocationExpressionSyntax c) e = c.Parent;
            return e is AwaitExpressionSyntax;
        }

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
            if (!_codeMode || inv == _startedCall || IsAwaitedHere(inv.Syntax) || IsLambdasResult(inv.Syntax)) return null;
            if (!IsTaskRun(inv.TargetMethod)) return StartOther(inv, f, spec);
            var effects = EffectsOfDelegate(RunDelegate(inv));
            // await Task.WhenAll(Task.Run(a), Task.Run(b)): alongside each other, and then all done
            if (inv.Syntax.Parent is ArgumentSyntax sibling && sibling.Parent?.Parent is InvocationExpressionSyntax all && IsWhenAll(_model.GetSymbolInfo(all).Symbol as IMethodSymbol) && IsAwaitedHere(all))
            {
                foreach (var earlier in ((ArgumentListSyntax)sibling.Parent).Arguments.TakeWhile(x => x != sibling))
                    if (_model.GetOperation(earlier.Expression) is IInvocationOperation other && IsTaskRun(other.TargetMethod))
                        WarnIfMayRace(inv.Syntax, effects, EffectsOfDelegate(RunDelegate(other)));
                return null;
            }
            WarnIfTheyMayRace(inv.Syntax, effects, f);
            WarnIfMayRace(inv.Syntax, effects, EffectsOf(_contract.Declaration, inv.Arguments.First(a => a.Parameter?.Ordinal == 0).Value.Syntax));
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
            var effects = m.DeclaringSyntaxReferences.Length > 0 && !m.IsAbstract ? EffectsOf(m) : null;
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
            else if (effects.Writes.FirstOrDefault(x => _engine.Locks.GuardOf(x) == null) is ISymbol unguarded)
                Warn(at, $"this keeps running after this method, and writes '{unguarded.Name}', which no lock guards: it could race with whatever uses it, and every method is proved as if nothing did");
            else if (effects.WritesArrays)
                Warn(at, "this keeps running after this method, and writes arrays: it could race with whatever uses them, and every method is proved as if nothing did");
        }

        /// <summary>th.Start() of a local made by new Thread(d), and th.Join(): the same, with nothing to lose if it isn't joined.</summary>
        private void ThreadEvent(IInvocationOperation inv, Frame f, SpecEnv spec)
        {
            if (!_codeMode || !IsThread(inv.Instance?.Type) || inv.Arguments.Length != 0) return;
            if (inv.TargetMethod.Name == "Join")
            {
                var t = Eval(inv.Instance, f, spec);
                if (f.Started.TryGetValue(t.S, out var started)) f.Started[t.S] = started.AsAwaited();
                return;
            }
            if (inv.TargetMethod.Name != "Start") return;
            var effects = ThreadDelegate(inv.Instance);
            WarnIfTheyMayRace(inv.Syntax, effects, f);
            if (effects != null) WarnIfMayRace(inv.Syntax, effects, EffectsOf(_contract.Declaration, ThreadDelegateSyntax(inv.Instance)));
            Detached(inv.Syntax, effects);
            f.Started[Eval(inv.Instance, f, spec).S] = new StartedTask(T.True, false, inv.TargetMethod, inv.Syntax, effects, true);
        }

        private SyntaxNode ThreadDelegateSyntax(IOperation thread) =>
            thread is ILocalReferenceOperation l && l.Local.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() is VariableDeclaratorSyntax d &&
            d.Initializer?.Value is BaseObjectCreationExpressionSyntax c && c.ArgumentList?.Arguments.Count > 0 ? c.ArgumentList.Arguments[0].Expression : null;

        private TaskEffects ThreadDelegate(IOperation thread) =>
            ThreadDelegateSyntax(thread) is SyntaxNode d && _model.GetOperation(d) is IOperation op ? EffectsOfDelegate(op) : null;

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
                if (!started.Awaited) { MayRaise(T.True, f, null); Interleave(f); }
                return started.Result;
            }
            if (!(operand is IInvocationOperation all) || !IsWhenAll(all.TargetMethod)) return null;
            // (from the syntax: whether a list of them is an array or a span depends on the framework)
            var elements = ((InvocationExpressionSyntax)all.Syntax).ArgumentList.Arguments.Select(a => Unconverted(_model.GetOperation(a.Expression))).ToList();
            // (only a list of them as written: an array built elsewhere isn't followed; each is a task held, or a call of an async method here)
            if (elements.Count == 0 || elements.Any(e => !(e is ILocalReferenceOperation l && f.Started.ContainsKey(Eval(l, f, spec).S) ||
                                                           e is IInvocationOperation c && c.TargetMethod.IsAsync && _engine.ContractOf(c.TargetMethod).HasSource))) return null;
            var results = new List<Term>();
            foreach (var e in elements)
            {
                var t = Eval(e, f, spec);
                results.Add(f.Started[t.S].Result);
                f.Started[t.S] = f.Started[t.S].AsAwaited();
            }
            MayRaise(T.True, f, null);
            Interleave(f);
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
            if (operand is IInvocationOperation taking && GateOf(taking, "WaitAsync", f) is { } got) GateTaken(got, f);
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
                ? CellwiseHeap($"(ite (>= (select (select {f.ArrPerm} x) i) 1.0) (select (select {before} x) i) (select (select {fresh} x) i))")
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
            if (!_method.IsAsync || _contract.Declaration == null) return _confined;
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
