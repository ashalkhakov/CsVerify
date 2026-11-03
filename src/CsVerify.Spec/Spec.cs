using System;
using System.Diagnostics;

namespace CsVerify
{
    /// <summary>
    /// Specification statements. Every method is <c>[Conditional("CSVERIFY_SPEC")]</c>: in a normal build the
    /// compiler removes the call <em>and the evaluation of its arguments</em>, so specifications cost nothing at
    /// run time. The CsVerify verifier compiles with <c>CSVERIFY_SPEC</c> defined and reads them as proof obligations.
    /// </summary>
    public static class Spec
    {
        public const string Symbol = "CSVERIFY_SPEC";

        /// <summary>Precondition. A top-level statement of a method body (contracts are read from there).</summary>
        [Conditional(Symbol)] public static void Requires(bool condition) { }

        /// <summary>Postcondition over the return value, bound to the lambda's parameter.</summary>
        [Conditional(Symbol)] public static void Ensures<R>(Func<R, bool> condition) { }

        /// <summary>
        /// Postcondition evaluated in the final state. Use <see cref="Result{T}"/> for the return value and
        /// <see cref="Old{T}"/> for entry values (needed for <c>ref</c> parameters, which lambdas cannot capture).
        /// </summary>
        [Conditional(Symbol)] public static void Ensures(bool condition) { }

        /// <summary>Loop invariant: the leading statements of a loop body; holds every time the loop condition is tested.</summary>
        [Conditional(Symbol)] public static void Invariant(bool condition) { }

        /// <summary>Termination measure: leading statement of a loop body or of a recursive method's body.</summary>
        [Conditional(Symbol)] public static void Decreases(int measure) { }

        /// <summary>Lexicographic termination measure (ATS's <c>.&lt;m, n&gt;.</c>): the first component that changes must go down.</summary>
        [Conditional(Symbol)] public static void Decreases(int measure1, int measure2) { }

        /// <summary>Lexicographic termination measure with three components.</summary>
        [Conditional(Symbol)] public static void Decreases(int measure1, int measure2, int measure3) { }

        /// <summary>
        /// Structural termination measure: <paramref name="structure"/>, a value of a data type (a closed positional
        /// record hierarchy), is smaller at every recursive call, as when recursing on a sub-term (ATS's datatype metrics).
        /// </summary>
        [Conditional(Symbol)] public static void Decreases<T>(T structure) where T : class { }

        /// <summary>Proof obligation at this point.</summary>
        [Conditional(Symbol)] public static void Assert(bool condition) { }

        /// <summary>Unchecked assumption at this point (the specification analogue of <c>$UNSAFE</c>).</summary>
        [Conditional(Symbol)] public static void Assume(bool condition) { }

        /// <summary>The method's return value; only meaningful inside <see cref="Ensures(bool)"/>.</summary>
        public static T Result<T>() => throw GhostException.Instance;

        /// <summary>Bounded universal quantifier: <paramref name="body"/> holds for every i with from &lt;= i &lt; to.</summary>
        public static bool Forall(int from, int to, Func<int, bool> body) => throw GhostException.Instance;

        /// <summary>Bounded existential quantifier: <paramref name="body"/> holds for some i with from &lt;= i &lt; to.</summary>
        public static bool Exists(int from, int to, Func<int, bool> body) => throw GhostException.Instance;

        /// <summary>The value an expression had on method entry; only meaningful inside <see cref="Ensures(bool)"/>.</summary>
        public static T Old<T>(T value) => throw GhostException.Instance;
    }

    /// <summary>Thrown when ghost-only code is reached at run time; the analyzers make this unreachable.</summary>
    public sealed class GhostException : InvalidOperationException
    {
        internal static readonly GhostException Instance = new GhostException();
        private GhostException() : base("Ghost code is only meaningful inside CsVerify specifications.") { }
    }
}
