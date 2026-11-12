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
    internal sealed partial class StaticChecks
    {

        /// <summary>The T of an async method returning Task&lt;T&gt; or ValueTask&lt;T&gt;; null for Task, ValueTask or void.</summary>
        internal static ITypeSymbol AsyncResultType(IMethodSymbol m) =>
            m.IsAsync && m.ReturnType is INamedTypeSymbol rt && rt.TypeArguments.Length == 1 &&
            (rt.Name == "Task" || rt.Name == "ValueTask") && rt.ContainingNamespace?.ToDisplayString() == "System.Threading.Tasks"
                ? rt.TypeArguments[0] : null;

        private static bool IsTaskLike(ITypeSymbol t) =>
            t is INamedTypeSymbol n && (n.Name == "Task" || n.Name == "ValueTask") && n.ContainingNamespace?.ToDisplayString() == "System.Threading.Tasks";

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
    }
}
