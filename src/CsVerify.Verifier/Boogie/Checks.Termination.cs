using System;
using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using static CsVerify.Verifier.Boogie.KernelTypes;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>Termination: a recursive call's measure decreases, lexicographically.</summary>
    internal sealed partial class Checks
    {
        /// <summary>
        /// A call back into its own recursion group: the callee's measure, at the arguments, below the caller's,
        /// lexicographically (CSV1008). A [Pure] function or lemma that recurses without one doesn't terminate
        /// (CSV1011); an ordinary method needn't (partial correctness).
        /// </summary>
        private void Termination(KCall c, MExpr receiver, MExpr[] args, List<MExpr> mine)
        {
            if (!_program.Recursive(_p.Method, c.Callee)) return;
            var theirs = _program.ContractOf(c.Callee);
            bool self = SymbolEqualityComparer.Default.Equals(c.Callee.OriginalDefinition, _p.Method.OriginalDefinition);
            // (without measures on both, a proof doesn't terminate, other code isn't checked to;
            // measures of different shapes can't be compared)
            if ((mine == null || theirs?.Decreases == null) && (_p.Contract.IsPure || _p.Contract.IsLemma || _p.Ghost))
            {
                Assert(new MLit("false"), At("CSV1011", c.At, self ? $"recursive lemma or [Pure] function '{_p.Method.Name}' needs Spec.Decreases"
                                                                   : $"mutually recursive call from '{_p.Method.Name}' to '{c.Callee.Name}' needs Spec.Decreases on both"));
                return;
            }
            if (mine == null || theirs?.Decreases == null)
            {
                if (c.At != null)
                    _p.Warnings.Add(new VerificationDiagnostic("CSV1900", false, self
                        ? $"recursive call without Spec.Decreases in '{_p.Method.Name}'; termination is not checked"
                        : $"mutually recursive call from '{_p.Method.Name}' to '{c.Callee.Name}' without Spec.Decreases on both; termination is not checked", c.At.GetLocation().GetLineSpan()));
                return;
            }
            if (theirs.Decreases.Count != mine.Count)
            {
                Assert(new MLit("false"), At("CSV1008", c.At, $"cannot prove termination: '{c.Callee.Name}' and '{_p.Method.Name}' call each other but their measures have different numbers of components"));
                return;
            }
            {
                var sig = _program.Signature(c.Callee);
                var given = Given(c.Callee, receiver, args);
                var next = sig.Decreases.Select(d => Subst(Spec(d, out _), given)).ToList();
                Assert(Lexicographic(next, mine), At("CSV1008", c.At,
                    $"cannot prove termination: measure '{string.Join(", ", theirs.Decreases.Select(d => d.Syntax))}' of '{c.Callee.Name}' might not decrease or might be negative"));
            }
        }

        private Dictionary<string, MExpr> Given(IMethodSymbol callee, MExpr receiver, MExpr[] args)
        {
            var given = callee.Parameters.Select((p, k) => (p, k)).Where(x => x.k < args.Length).ToDictionary(x => Local(x.p), x => args[x.k]);
            if (receiver != null) given["this"] = receiver;
            // (a local function's captured inputs: after its arguments)
            if (callee.MethodKind == MethodKind.LocalFunction)
            {
                var captured = _program.Signature(callee).Captured;
                for (int k = 0; k < captured.Count && callee.Parameters.Length + k < args.Length; k++) given[captured[k].input] = args[callee.Parameters.Length + k];
            }
            return given;
        }

        internal static bool IsRequired(ISymbol field) =>
            (field is IFieldSymbol f ? f.IsRequired : field is IPropertySymbol p && p.IsRequired) ||
            field.GetAttributes().Any(a => a.AttributeClass?.Name == "JsonRequiredAttribute");

        /// <summary>
        /// next below before, lexicographically, each part bounded below by 0 where it goes down (Dafny's rule: the
        /// part before isn't negative, the next is less, which is well-founded; the next may be negative).
        /// </summary>
        private static MExpr Lexicographic(List<MExpr> next, List<MExpr> before)
        {
            int n = Math.Min(next.Count, before.Count);
            MExpr Below(int k)
            {
                var down = new MOp("&&", new MOp("<=", new MLit("0"), before[k]), new MOp("<", next[k], before[k]));
                return k == n - 1 ? down : new MOp("||", down, new MOp("&&", new MOp("==", next[k], before[k]), Below(k + 1)));
            }
            return n == 0 ? new MLit("false") : Below(0);
        }
    }
}
