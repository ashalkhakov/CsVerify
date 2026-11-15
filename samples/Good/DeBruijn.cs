using System.Diagnostics;
using CsVerify;

namespace Samples
{
    /// <summary>Lambda terms with de Bruijn indices alone (Pierce, TAPL, chapter 6): a variable is the number of binders out to its own.</summary>
    public abstract record Db
    {
        private Db() { }
        public sealed record Var(int Index) : Db;
        public sealed record App(Db Fun, Db Arg) : Db;
        public sealed record Lam(Db Body) : Db;
    }

    /// <summary>Shifting and substitution, and the laws by which they commute, proved by structural induction.</summary>
    public static class DeBruijn
    {
        // ---------------------------------------------------------------- operations

        /// <summary>The d-place shift of t above cutoff c: each index at least c moved by d.</summary>
        [GhostFunction]
        public static Db Shift(Db t, int d, int c)
        {
            Spec.Decreases(t);
            return t switch
            {
                Db.Var v => v.Index < c ? t : new Db.Var(v.Index + d),
                Db.App a => new Db.App(Shift(a.Fun, d, c), Shift(a.Arg, d, c)),
                Db.Lam l => new Db.Lam(Shift(l.Body, d, c + 1)),
            };
        }

        /// <summary>[j -> s] t: index j replaced by s; under a binder, j + 1 by s shifted past it.</summary>
        [GhostFunction]
        public static Db Subst(Db t, int j, Db s)
        {
            Spec.Decreases(t);
            return t switch
            {
                Db.Var v => v.Index == j ? s : t,
                Db.App a => new Db.App(Subst(a.Fun, j, s), Subst(a.Arg, j, s)),
                Db.Lam l => new Db.Lam(Subst(l.Body, j + 1, Shift(s, 1, 0))),
            };
        }

        /// <summary>A beta step's result, (\. t) s: index 0 replaced by s, the binder gone (TAPL's ↑⁻¹([0 -> ↑¹ s] t)).</summary>
        [GhostFunction]
        public static Db Beta(Db t, Db s) => Shift(Subst(t, 0, Shift(s, 1, 0)), -1, 0);

        // ---------------------------------------------------------------- shifting

        /// <summary>Shifting by nothing changes nothing.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void ShiftZero(Db t, int c)
        {
            Spec.Ensures(Shift(t, 0, c) == t);
            Spec.Decreases(t);
            switch (t)
            {
                case Db.App a: ShiftZero(a.Fun, c); ShiftZero(a.Arg, c); break;
                case Db.Lam l: ShiftZero(l.Body, c + 1); break;
            }
        }

        /// <summary>Two shifts at one cutoff are one, by their sum (the first moving no index below the cutoff).</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void ShiftShift(Db t, int d, int e, int c)
        {
            Spec.Requires(d >= 0);
            Spec.Ensures(Shift(Shift(t, d, c), e, c) == Shift(t, d + e, c));
            Spec.Decreases(t);
            switch (t)
            {
                case Db.App a: ShiftShift(a.Fun, d, e, c); ShiftShift(a.Arg, d, e, c); break;
                case Db.Lam l: ShiftShift(l.Body, d, e, c + 1); break;
            }
        }

        /// <summary>Shifts at two cutoffs commute, the higher cutoff moved by the lower shift.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void ShiftCommute(Db t, int d, int c, int e, int c2)
        {
            Spec.Requires(d >= 0 && e >= 0 && c <= c2);
            Spec.Ensures(Shift(Shift(t, d, c), e, c2 + d) == Shift(Shift(t, e, c2), d, c));
            Spec.Decreases(t);
            switch (t)
            {
                case Db.App a: ShiftCommute(a.Fun, d, c, e, c2); ShiftCommute(a.Arg, d, c, e, c2); break;
                case Db.Lam l: ShiftCommute(l.Body, d, c + 1, e, c2 + 1); break;
            }
        }

        /// <summary>Shifting down at a cutoff undoes shifting up at it.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void ShiftUnshift(Db t, int c)
        {
            Spec.Ensures(Shift(Shift(t, 1, c), -1, c) == t);
            Spec.Decreases(t);
            switch (t)
            {
                case Db.App a: ShiftUnshift(a.Fun, c); ShiftUnshift(a.Arg, c); break;
                case Db.Lam l: ShiftUnshift(l.Body, c + 1); break;
            }
        }

        // ---------------------------------------------------------------- substitution

        /// <summary>Shifting distributes through substitution for an index at or above its cutoff.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void ShiftSubst(Db t, int j, Db s, int d, int c)
        {
            Spec.Requires(d >= 0 && 0 <= c && c <= j);
            Spec.Ensures(Shift(Subst(t, j, s), d, c) == Subst(Shift(t, d, c), j + d, Shift(s, d, c)));
            Spec.Decreases(t);
            switch (t)
            {
                case Db.App a: ShiftSubst(a.Fun, j, s, d, c); ShiftSubst(a.Arg, j, s, d, c); break;
                case Db.Lam l:
                    ShiftSubst(l.Body, j + 1, Shift(s, 1, 0), d, c + 1);
                    ShiftCommute(s, 1, 0, d, c);
                    break;
            }
        }

        /// <summary>Substituting for an index a shift left out changes nothing.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void SubstShifted(Db t, int c, Db s)
        {
            Spec.Ensures(Subst(Shift(t, 1, c), c, s) == Shift(t, 1, c));
            Spec.Decreases(t);
            switch (t)
            {
                case Db.App a: SubstShifted(a.Fun, c, s); SubstShifted(a.Arg, c, s); break;
                case Db.Lam l: SubstShifted(l.Body, c + 1, Shift(s, 1, 0)); break;
            }
        }

        /// <summary>A beta step on a body that doesn't use its variable gives the body back, unshifted.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void BetaVacuous(Db t, Db s)
        {
            Spec.Ensures(Beta(Shift(t, 1, 0), s) == t);
            SubstShifted(t, 0, Shift(s, 1, 0));
            ShiftUnshift(t, 0);
        }
    }
}
