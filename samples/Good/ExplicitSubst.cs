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
        public sealed record Up(Nat N) : Sub;
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
        public static Db Lookup(Sub s, Nat i)
        {
            Spec.Decreases(s);
            return s switch
            {
                Sub.Id => new Db.Var(i),
                Sub.Up u => new Db.Var(Naturals.Add(i, u.N)),
                Sub.Cons c => i is Nat.S p ? Lookup(c.Tail, p.Pred) : c.Head,
                Sub.Lift l => i is Nat.S p ? DeBruijn.Shift(Lookup(l.Under, p.Pred), Naturals.One(), new Nat.Z()) : new Db.Var(i),
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
        public static Sub Lifts(Nat k, Sub s)
        {
            Spec.Decreases(k);
            return k is Nat.S p ? new Sub.Lift(Lifts(p.Pred, s)) : s;
        }

        /// <summary>s shifted past k binders: ↑ᵏ s, one place at a time.</summary>
        [GhostFunction]
        public static Db ShiftN(Db s, Nat k)
        {
            Spec.Decreases(k);
            return k is Nat.S p ? DeBruijn.Shift(ShiftN(s, p.Pred), Naturals.One(), new Nat.Z()) : s;
        }

        // ---------------------------------------------------------------- the identity

        /// <summary>id under binders gives each index itself.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void LookupId(Nat k, Nat i)
        {
            Spec.Ensures(Lookup(Lifts(k, new Sub.Id()), i) == new Db.Var(i));
            Spec.Decreases(k);
            if (k is Nat.S p && i is Nat.S q)
            {
                LookupId(p.Pred, q.Pred);
                Naturals.AddOne(q.Pred);
            }
        }

        /// <summary>t[⇑ᵏ id] = t.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void ApplyId(Db t, Nat k)
        {
            Spec.Ensures(Apply(t, Lifts(k, new Sub.Id())) == t);
            Spec.Decreases(t);
            switch (t)
            {
                case Db.Var v: LookupId(k, v.Index); break;
                case Db.App a: ApplyId(a.Fun, k); ApplyId(a.Arg, k); break;
                case Db.Lam l: ApplyId(l.Body, new Nat.S(k)); break;
            }
        }

        // ---------------------------------------------------------------- agreement with DeBruijn.Subst

        /// <summary>(s · ↑) under j binders gives index j the term s shifted past them, and every other index itself.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void LookupSubst(Nat j, Db s, Nat i)
        {
            Spec.Ensures(Lookup(Lifts(j, new Sub.Cons(s, new Sub.Up(Naturals.One()))), i) == (i == j ? ShiftN(s, j) : new Db.Var(i)));
            Spec.Decreases(j);
            var top = new Sub.Cons(s, new Sub.Up(Naturals.One()));
            if (i is Nat.S q)
            {
                Naturals.AddOne(q.Pred);
                if (j is Nat.S p)
                {
                    // (one level of each definition at a time: ⇑ʲ, ⇑'s lookup, the shift of what's under it)
                    var under = Lifts(p.Pred, top);
                    Spec.Assert(Lifts(j, top) == new Sub.Lift(under));
                    LookupSubst(p.Pred, s, q.Pred);
                    Spec.Assert(Lookup(new Sub.Lift(under), i) == DeBruijn.Shift(Lookup(under, q.Pred), Naturals.One(), new Nat.Z()));
                    Spec.Assert(i == j || DeBruijn.Shift(new Db.Var(q.Pred), Naturals.One(), new Nat.Z()) == new Db.Var(i));
                    Spec.Assert(i != j || ShiftN(s, j) == DeBruijn.Shift(ShiftN(s, p.Pred), Naturals.One(), new Nat.Z()));
                }
                else
                {
                    Spec.Assert(Lookup(top, i) == Lookup(new Sub.Up(Naturals.One()), q.Pred));
                }
            }
        }

        /// <summary>The explicit substitution (s · ↑), under j binders, is DeBruijn.Subst at j.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void ApplyIsSubst(Db t, Nat j, Db s)
        {
            Spec.Ensures(Apply(t, Lifts(j, new Sub.Cons(s, new Sub.Up(Naturals.One())))) == DeBruijn.Subst(t, j, ShiftN(s, j)));
            Spec.Decreases(t);
            switch (t)
            {
                case Db.Var v: LookupSubst(j, s, v.Index); break;
                case Db.App a: ApplyIsSubst(a.Fun, j, s); ApplyIsSubst(a.Arg, j, s); break;
                case Db.Lam l: ApplyIsSubst(l.Body, new Nat.S(j), s); break;
            }
        }

        /// <summary>At the top: t[s · ↑] = [0 -> s] t.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void ConsIsSubst(Db t, Db s)
        {
            Spec.Ensures(Apply(t, new Sub.Cons(s, new Sub.Up(Naturals.One()))) == DeBruijn.Subst(t, new Nat.Z(), s));
            ApplyIsSubst(t, new Nat.Z(), s);
        }

        // ---------------------------------------------------------------- examples

        /// <summary>(0 1)[s · ↑] is (s 1): index 0 is s, index 1 is shifted to itself; and so is [0 -> s] (0 1).</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void Examples()
        {
            var zero = new Nat.Z();
            var one = Naturals.One();
            var s = new Db.Lam(new Db.Var(zero));
            var sigma = new Sub.Cons(s, new Sub.Up(one));
            var t = new Db.App(new Db.Var(zero), new Db.Var(one));
            Spec.Assert(Lookup(sigma, zero) == s);
            Spec.Assert(Naturals.Add(zero, one) == one);
            Spec.Assert(Lookup(new Sub.Up(one), zero) == new Db.Var(one));
            Spec.Assert(Lookup(sigma, one) == new Db.Var(one));
            Spec.Assert(Apply(new Db.Var(zero), sigma) == s && Apply(new Db.Var(one), sigma) == new Db.Var(one));
            Spec.Assert(Apply(t, sigma) == new Db.App(s, new Db.Var(one)));
            ConsIsSubst(t, s);
            Spec.Assert(DeBruijn.Subst(t, zero, s) == new Db.App(s, new Db.Var(one)));
        }
    }
}
