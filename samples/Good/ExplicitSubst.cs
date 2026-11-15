using System.Diagnostics;
using CsVerify;

namespace Samples
{
    /// <summary>
    /// A substitution as data, after the λσ-calculus (Abadi, Cardelli, Curien and Lévy, "Explicit Substitutions", 1991):
    /// what each index of a de Bruijn term (Db) becomes.
    /// </summary>
    public abstract record Sub
    {
        private Sub() { }
        /// <summary>id: each index itself.</summary>
        public sealed record Id() : Sub;
        /// <summary>↑ⁿ: index i to i + n.</summary>
        public sealed record Up(int N) : Sub;
        /// <summary>t · σ: index 0 to t, i + 1 to what σ gives i.</summary>
        public sealed record Cons(Db Head, Sub Tail) : Sub;
        /// <summary>⇑σ, σ under a binder: index 0 to itself, i + 1 to what σ gives i, shifted past the binder.</summary>
        public sealed record Lift(Sub Under) : Sub;
    }

    /// <summary>Explicit substitutions applied to de Bruijn terms, proved to agree with DeBruijn.Subst.</summary>
    public static class ExplicitSubst
    {
        // ---------------------------------------------------------------- operations

        /// <summary>What σ gives index i.</summary>
        [GhostFunction]
        public static Db Lookup(Sub s, int i)
        {
            Spec.Decreases(s);
            return s switch
            {
                Sub.Id => new Db.Var(i),
                Sub.Up u => new Db.Var(i + u.N),
                Sub.Cons c => i == 0 ? c.Head : Lookup(c.Tail, i - 1),
                Sub.Lift l => i <= 0 ? new Db.Var(i) : DeBruijn.Shift(Lookup(l.Under, i - 1), 1, 0),
            };
        }

        /// <summary>t[σ]: each index replaced by what σ gives it; under a binder, by what ⇑σ does.</summary>
        [GhostFunction]
        public static Db Apply(Db t, Sub s)
        {
            Spec.Decreases(t);
            return t switch
            {
                Db.Var v => Lookup(s, v.Index),
                Db.App a => new Db.App(Apply(a.Fun, s), Apply(a.Arg, s)),
                Db.Lam l => new Db.Lam(Apply(l.Body, new Sub.Lift(s))),
            };
        }

        /// <summary>σ under k binders: ⇑ᵏσ.</summary>
        [GhostFunction]
        public static Sub Lifts(int k, Sub s)
        {
            Spec.Requires(k >= 0);
            Spec.Decreases(k);
            return k == 0 ? s : new Sub.Lift(Lifts(k - 1, s));
        }

        /// <summary>s shifted past k binders: ↑ᵏ s, one place at a time.</summary>
        [GhostFunction]
        public static Db ShiftN(Db s, int k)
        {
            Spec.Requires(k >= 0);
            Spec.Decreases(k);
            return k == 0 ? s : DeBruijn.Shift(ShiftN(s, k - 1), 1, 0);
        }

        // ---------------------------------------------------------------- the identity

        /// <summary>id under binders gives each index itself.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void LookupId(int k, int i)
        {
            Spec.Requires(k >= 0);
            Spec.Ensures(Lookup(Lifts(k, new Sub.Id()), i) == new Db.Var(i));
            Spec.Decreases(k);
            if (k > 0 && i > 0)
            {
                LookupId(k - 1, i - 1);
            }
        }

        /// <summary>t[⇑ᵏ id] = t.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void ApplyId(Db t, int k)
        {
            Spec.Requires(k >= 0);
            Spec.Ensures(Apply(t, Lifts(k, new Sub.Id())) == t);
            Spec.Decreases(t);
            switch (t)
            {
                case Db.Var v: LookupId(k, v.Index); break;
                case Db.App a: ApplyId(a.Fun, k); ApplyId(a.Arg, k); break;
                case Db.Lam l: ApplyId(l.Body, k + 1); break;
            }
        }

        // ---------------------------------------------------------------- agreement with DeBruijn.Subst

        /// <summary>(s · ↑) under j binders gives index j the term s shifted past them, and every other index itself.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void LookupSubst(int j, Db s, int i)
        {
            Spec.Requires(j >= 0);
            Spec.Ensures(Lookup(Lifts(j, new Sub.Cons(s, new Sub.Up(1))), i) == (i == j ? ShiftN(s, j) : new Db.Var(i)));
            Spec.Decreases(j);
            var top = new Sub.Cons(s, new Sub.Up(1));
            if (j == 0)
            {
                Spec.Assert(i == 0 || Lookup(top, i) == Lookup(new Sub.Up(1), i - 1));
            }
            else if (i > 0)
            {
                // (one level of each definition at a time: ⇑ᵏ, ⇑'s lookup, the shift of what's under it)
                var under = Lifts(j - 1, top);
                Spec.Assert(Lifts(j, top) == new Sub.Lift(under));
                LookupSubst(j - 1, s, i - 1);
                Spec.Assert(Lookup(new Sub.Lift(under), i) == DeBruijn.Shift(Lookup(under, i - 1), 1, 0));
                Spec.Assert(i == j || DeBruijn.Shift(new Db.Var(i - 1), 1, 0) == new Db.Var(i));
                Spec.Assert(i != j || ShiftN(s, j) == DeBruijn.Shift(ShiftN(s, j - 1), 1, 0));
            }
            else
            {
                Spec.Assert(Lifts(j, top) == new Sub.Lift(Lifts(j - 1, top)));
            }
        }

        /// <summary>The explicit substitution (s · ↑), under j binders, is DeBruijn.Subst at j.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void ApplyIsSubst(Db t, int j, Db s)
        {
            Spec.Requires(j >= 0);
            Spec.Ensures(Apply(t, Lifts(j, new Sub.Cons(s, new Sub.Up(1)))) == DeBruijn.Subst(t, j, ShiftN(s, j)));
            Spec.Decreases(t);
            switch (t)
            {
                case Db.Var v: LookupSubst(j, s, v.Index); break;
                case Db.App a: ApplyIsSubst(a.Fun, j, s); ApplyIsSubst(a.Arg, j, s); break;
                case Db.Lam l: ApplyIsSubst(l.Body, j + 1, s); break;
            }
        }

        /// <summary>At the top: t[s · ↑] = [0 -> s] t.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void ConsIsSubst(Db t, Db s)
        {
            Spec.Ensures(Apply(t, new Sub.Cons(s, new Sub.Up(1))) == DeBruijn.Subst(t, 0, s));
            ApplyIsSubst(t, 0, s);
        }
    }
}
