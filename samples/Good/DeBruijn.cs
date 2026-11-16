using System.Diagnostics;
using CsVerify;

namespace Samples
{
    /// <summary>Lambda terms with de Bruijn indices alone (Pierce, TAPL, chapter 6): a variable is the number of binders out to its own.</summary>
    public abstract record Db
    {
        private Db() { }
        public sealed record Var(Nat Index) : Db;
        public sealed record App(Db Fun, Db Arg) : Db;
        public sealed record Lam(Db Body) : Db;
    }

    /// <summary>Shifting and substitution, and the laws by which they commute, proved by structural induction.</summary>
    public static class DeBruijn
    {
        // ---------------------------------------------------------------- operations

        /// <summary>The d-place shift of t above cutoff c: each index at least c moved up by d.</summary>
        [GhostFunction]
        public static Db Shift(Db t, Nat d, Nat c)
        {
            Spec.Decreases(t);
            return t switch
            {
                Db.Var v => Naturals.Lt(v.Index, c) ? t : new Db.Var(Naturals.Add(v.Index, d)),
                Db.App a => new Db.App(Shift(a.Fun, d, c), Shift(a.Arg, d, c)),
                Db.Lam l => new Db.Lam(Shift(l.Body, d, new Nat.S(c))),
            };
        }

        /// <summary>The shift down by one above cutoff c (where c's own index isn't used: a beta step's binder gone).</summary>
        [GhostFunction]
        public static Db Unshift(Db t, Nat c)
        {
            Spec.Decreases(t);
            return t switch
            {
                Db.Var v => !Naturals.Lt(v.Index, c) && v.Index is Nat.S p ? new Db.Var(p.Pred) : t,
                Db.App a => new Db.App(Unshift(a.Fun, c), Unshift(a.Arg, c)),
                Db.Lam l => new Db.Lam(Unshift(l.Body, new Nat.S(c))),
            };
        }

        /// <summary>[j -> s] t: index j replaced by s; under a binder, j + 1 by s shifted past it.</summary>
        [GhostFunction]
        public static Db Subst(Db t, Nat j, Db s)
        {
            Spec.Decreases(t);
            return t switch
            {
                Db.Var v => v.Index == j ? s : t,
                Db.App a => new Db.App(Subst(a.Fun, j, s), Subst(a.Arg, j, s)),
                Db.Lam l => new Db.Lam(Subst(l.Body, new Nat.S(j), Shift(s, Naturals.One(), new Nat.Z()))),
            };
        }

        /// <summary>A beta step's result, (\. t) s: index 0 replaced by s, the binder gone (TAPL's ↑⁻¹([0 -> ↑¹ s] t)).</summary>
        [GhostFunction]
        public static Db Beta(Db t, Db s) => Unshift(Subst(t, new Nat.Z(), Shift(s, Naturals.One(), new Nat.Z())), new Nat.Z());

        // ---------------------------------------------------------------- shifting

        /// <summary>Shifting by nothing changes nothing.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void ShiftZero(Db t, Nat c)
        {
            Spec.Ensures(Shift(t, new Nat.Z(), c) == t);
            Spec.Decreases(t);
            switch (t)
            {
                case Db.Var v: Naturals.AddZero(v.Index); break;
                case Db.App a: ShiftZero(a.Fun, c); ShiftZero(a.Arg, c); break;
                case Db.Lam l: ShiftZero(l.Body, new Nat.S(c)); break;
            }
        }

        /// <summary>Two shifts at one cutoff are one, by their sum.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void ShiftShift(Db t, Nat d, Nat e, Nat c)
        {
            Spec.Ensures(Shift(Shift(t, d, c), e, c) == Shift(t, Naturals.Add(d, e), c));
            Spec.Decreases(t);
            switch (t)
            {
                case Db.Var v:
                    var i = v.Index;
                    Naturals.ValueLt(i, c);
                    Naturals.ValueLt(Naturals.Add(i, d), c);
                    Naturals.ValueAdd(i, d);
                    Naturals.ValueAdd(Naturals.Add(i, d), e);
                    Naturals.ValueAdd(d, e);
                    Naturals.ValueAdd(i, Naturals.Add(d, e));
                    Naturals.ValueInjective(Naturals.Add(Naturals.Add(i, d), e), Naturals.Add(i, Naturals.Add(d, e)));
                    break;
                case Db.App a: ShiftShift(a.Fun, d, e, c); ShiftShift(a.Arg, d, e, c); break;
                case Db.Lam l: ShiftShift(l.Body, d, e, new Nat.S(c)); break;
            }
        }

        /// <summary>Shifts at two cutoffs commute, the higher cutoff moved by the lower shift.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void ShiftCommute(Db t, Nat d, Nat c, Nat e, Nat c2)
        {
            Spec.Requires(!Naturals.Lt(c2, c));
            Spec.Ensures(Shift(Shift(t, d, c), e, Naturals.Add(c2, d)) == Shift(Shift(t, e, c2), d, c));
            Spec.Decreases(t);
            switch (t)
            {
                case Db.Var v:
                    var i = v.Index;
                    var id = Naturals.Add(i, d);
                    var ie = Naturals.Add(i, e);
                    Naturals.ValueAdd(i, d);
                    Naturals.ValueAdd(i, e);
                    Naturals.ValueAdd(c2, d);
                    Naturals.ValueAdd(id, e);
                    Naturals.ValueAdd(ie, d);
                    Naturals.ValueLt(i, c);
                    Naturals.ValueLt(i, c2);
                    Naturals.ValueLt(c2, c);
                    Naturals.ValueLt(id, Naturals.Add(c2, d));
                    Naturals.ValueLt(ie, c);
                    Naturals.ValueLt(i, Naturals.Add(c2, d));
                    Naturals.ValueInjective(Naturals.Add(id, e), Naturals.Add(ie, d));
                    break;
                case Db.App a: ShiftCommute(a.Fun, d, c, e, c2); ShiftCommute(a.Arg, d, c, e, c2); break;
                case Db.Lam l: ShiftCommute(l.Body, d, new Nat.S(c), e, new Nat.S(c2)); break;
            }
        }

        /// <summary>Shifting down at a cutoff undoes shifting up by one at it.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void ShiftUnshift(Db t, Nat c)
        {
            Spec.Ensures(Unshift(Shift(t, Naturals.One(), c), c) == t);
            Spec.Decreases(t);
            switch (t)
            {
                case Db.Var v:
                    Naturals.AddOne(v.Index);
                    Naturals.ValueLt(v.Index, c);
                    Naturals.ValueLt(new Nat.S(v.Index), c);
                    break;
                case Db.App a: ShiftUnshift(a.Fun, c); ShiftUnshift(a.Arg, c); break;
                case Db.Lam l: ShiftUnshift(l.Body, new Nat.S(c)); break;
            }
        }

        // ---------------------------------------------------------------- substitution

        /// <summary>Shifting distributes through substitution for an index at or above its cutoff.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void ShiftSubst(Db t, Nat j, Db s, Nat d, Nat c)
        {
            Spec.Requires(!Naturals.Lt(j, c));
            Spec.Ensures(Shift(Subst(t, j, s), d, c) == Subst(Shift(t, d, c), Naturals.Add(j, d), Shift(s, d, c)));
            Spec.Decreases(t);
            switch (t)
            {
                case Db.Var v:
                    var i = v.Index;
                    Naturals.ValueLt(i, c);
                    Naturals.ValueLt(j, c);
                    Naturals.ValueAdd(i, d);
                    Naturals.ValueAdd(j, d);
                    Naturals.ValueInjective(i, Naturals.Add(j, d));
                    Naturals.ValueInjective(Naturals.Add(i, d), Naturals.Add(j, d));
                    Naturals.ValueInjective(i, j);
                    break;
                case Db.App a: ShiftSubst(a.Fun, j, s, d, c); ShiftSubst(a.Arg, j, s, d, c); break;
                case Db.Lam l:
                    ShiftSubst(l.Body, new Nat.S(j), Shift(s, Naturals.One(), new Nat.Z()), d, new Nat.S(c));
                    ShiftCommute(s, Naturals.One(), new Nat.Z(), d, c);
                    Naturals.AddOne(c);
                    break;
            }
        }

        /// <summary>Substituting for an index a shift left out changes nothing.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void SubstShifted(Db t, Nat c, Db s)
        {
            Spec.Ensures(Subst(Shift(t, Naturals.One(), c), c, s) == Shift(t, Naturals.One(), c));
            Spec.Decreases(t);
            switch (t)
            {
                case Db.Var v:
                    Naturals.AddOne(v.Index);
                    Naturals.LtIrreflexive(c);
                    Naturals.ValueLt(v.Index, c);
                    Naturals.ValueInjective(new Nat.S(v.Index), c);
                    break;
                case Db.App a: SubstShifted(a.Fun, c, s); SubstShifted(a.Arg, c, s); break;
                case Db.Lam l: SubstShifted(l.Body, new Nat.S(c), Shift(s, Naturals.One(), new Nat.Z())); break;
            }
        }

        /// <summary>A beta step on a body that doesn't use its variable gives the body back.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void BetaVacuous(Db t, Db s)
        {
            Spec.Ensures(Beta(Shift(t, Naturals.One(), new Nat.Z()), s) == t);
            SubstShifted(t, new Nat.Z(), Shift(s, Naturals.One(), new Nat.Z()));
            ShiftUnshift(t, new Nat.Z());
        }

        // ---------------------------------------------------------------- examples

        /// <summary>(\. 0 0) (\. 0): a beta step gives (\. 0) (\. 0).</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void Examples()
        {
            var zero = new Nat.Z();
            var v0 = new Db.Var(zero);
            var id = new Db.Lam(v0);
            // (the argument shifted past the binder: its index 0 is its own binder's, below the cutoff 1)
            Spec.Assert(Naturals.Lt(zero, new Nat.S(zero)));
            Spec.Assert(Shift(v0, Naturals.One(), new Nat.S(zero)) == v0);
            Spec.Assert(Shift(id, Naturals.One(), zero) == id);
            Spec.Assert(Subst(v0, zero, id) == id);
            Spec.Assert(Subst(new Db.App(v0, v0), zero, id) == new Db.App(id, id));
            Spec.Assert(Unshift(v0, new Nat.S(zero)) == v0 && Unshift(id, zero) == id);
            Spec.Assert(Unshift(new Db.App(id, id), zero) == new Db.App(id, id));
            Spec.Assert(Beta(new Db.App(v0, v0), id) == new Db.App(id, id));
        }
    }
}
