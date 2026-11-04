using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
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
    /// <item>an async method of the program called without being awaited at once would run interleaved with its
    /// caller, each changing what the other relies on: that is not supported (CSV1901). Tasks from the library are
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
            inv == _awaitedCall && AsyncResultType(inv.TargetMethod) is ITypeSymbol t ? t : inv.TargetMethod.ReturnType;

        /// <summary>A call of an async method of the program that is not awaited at once.</summary>
        private bool CheckNotAwaited(IInvocationOperation inv, Contract callee)
        {
            if (!inv.TargetMethod.IsAsync || !callee.HasSource || inv == _awaitedCall || !_codeMode) return false;
            NotModeled(inv.Syntax, $"'{inv.TargetMethod.Name}' is async and is not awaited at once: it would run interleaved with this method, " +
                                   "each changing what the other relies on (write 'await' at the call)");
            return true;
        }

        private Term EvalAwait(IAwaitOperation aw, Frame f, SpecEnv spec)
        {
            var operand = aw.Operation;
            // (x.ConfigureAwait(b) awaits x)
            while (operand is IInvocationOperation ca && ca.TargetMethod.Name == "ConfigureAwait" && ca.Instance != null && ca.TargetMethod.DeclaringSyntaxReferences.Length == 0)
                operand = ca.Instance;
            Term result;
            if (operand is IInvocationOperation call && call.TargetMethod.IsAsync && _engine.ContractOf(call.TargetMethod).HasSource)
            {
                // an async method of the program: a call whose postcondition holds when its task completes
                var outer = _awaitedCall;
                _awaitedCall = call;
                try { result = Eval(call, f, spec); }
                finally { _awaitedCall = outer; }
                for (var w = aw.Operation; w != call; w = ((IInvocationOperation)w).Instance)
                    foreach (var a in ((IInvocationOperation)w).Arguments) Eval(a.Value, f, spec); // (ConfigureAwait's argument)
                if (AsyncResultType(call.TargetMethod) == null) result = T.True;
            }
            else
            {
                Eval(aw.Operation, f, spec);
                result = aw.Type == null || aw.Type.SpecialType == SpecialType.System_Void ? T.True : Unknown(aw.Type, "awaited");
                // a library task's result is as the library declares it; a faulted task throws here
                if (operand is IInvocationOperation li && li.TargetMethod.OriginalDefinition.ReturnType is INamedTypeSymbol lt &&
                    lt.TypeArguments.Length == 1 && IsNonNullableType(lt.TypeArguments[0]) && result.Sort == Sort.Int)
                    _z3.Assume(NotNull(result));
                MayRaise(T.True, f, null);
            }
            Interleave(f);
            return result;
        }

        /// <summary>
        /// Other code ran: everything this method does not hold may have changed. (It cannot hold what this method
        /// holds: views are linear, and permissions add up to one.)
        /// </summary>
        private void Interleave(Frame f)
        {
            var before = f.Heap;
            var fresh = _z3.Fresh("heap", Sort.Heap);
            f.Heap = _arrayMode && f.ArrPerm != null
                ? CellwiseHeap($"(ite (>= (select (select {f.ArrPerm} x) i) 1.0) (select (select {before} x) i) (select (select {fresh} x) i))")
                : fresh;
            f.Heap = KeepHeldMemory(f.Heap, before, f.ArrPerm);

            var owned = f.Perm != null ? _engine.Fields.OwnedFields().ToDictionary(x => x, x => FieldMap(f, x), SymbolEqualityComparer.Default) : null;
            var rootBefore = f.Root;
            HavocAllFields(f);
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

        private bool RunsCode(IMethodSymbol m)
        {
            var c = _engine.ContractOf(m);
            return !c.IsPure && !c.IsLemma && !SpecSymbols.IsSpecClass(m.ContainingType) && !SpecSymbols.IsGhostOf(m);
        }
    }
}
