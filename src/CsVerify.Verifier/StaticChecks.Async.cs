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
    /// async and concurrency marks, as the static checks read them: what an async method's task gives, and that what
    /// runs concurrently says so ([RunsConcurrently], CSV1028). Awaits, tasks and threads themselves are the Boogie
    /// engine's (docs/boogie.md).
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
