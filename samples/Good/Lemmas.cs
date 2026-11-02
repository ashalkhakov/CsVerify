using System.Diagnostics;
using CsVerify;

namespace Samples
{
    public static class Lemmas
    {
        /// <summary>1 + 2 + ... + n, defined recursively.</summary>
        [Pure]
        public static int Tri(int n)
        {
            Spec.Requires(n >= 0);
            Spec.Decreases(n);
            return n == 0 ? 0 : n + Tri(n - 1);
        }

        /// <summary>
        /// prfun tri_formula {n:nat} .&lt;n&gt;. (): [2 * tri(n) == n * (n + 1)]. Proved by induction: the recursive call is
        /// the induction hypothesis, the Decreases clause is the termination metric. Erased from normal builds.
        /// </summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void TriFormula(int n)
        {
            Spec.Requires(n >= 0);
            Spec.Ensures(2 * Tri(n) == n * (n + 1));
            Spec.Decreases(n);
            if (n > 0) TriFormula(n - 1);
        }

        /// <summary>Uses the lemma: without the TriFormula call the assertion cannot be proved.</summary>
        public static int TriFast(int n)
        {
            Spec.Requires(n >= 0 && n <= 1000);
            Spec.Ensures<int>(r => r == Tri(n));
            TriFormula(n);
            return n * (n + 1) / 2;
        }

        /// <summary>Recursion with a termination metric (ATS .&lt;n&gt;.).</summary>
        public static int Power2(int n)
        {
            Spec.Requires(0 <= n && n <= 30);
            Spec.Ensures<int>(r => r >= 1);
            Spec.Decreases(n);
            if (n == 0) return 1;
            return 2 * Power2(n - 1);
        }
    }
}
