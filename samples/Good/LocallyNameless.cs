using System.Diagnostics;
using CsVerify;

namespace Samples
{
    /// <summary>
    /// Lambda terms in the locally nameless representation (Charguéraud, "The Locally Nameless Representation", 2012),
    /// as the verifier's own terms are (KBound, KVar; Nameless.Open, Close, Substitute): a bound variable is a de Bruijn
    /// index, a free one a name.
    /// </summary>
    public abstract record Term
    {
        private Term() { }
        public sealed record Bound(Nat Index) : Term;
        public sealed record Free(int Name) : Term;
        public sealed record App(Term Fun, Term Arg) : Term;
        public sealed record Lam(Term Body) : Term;
    }

    /// <summary>Opening, closing and substitution, and their laws, proved by structural induction.</summary>
    public static class LocallyNameless
    {
        // ---------------------------------------------------------------- operations

        /// <summary>{k -> u} t: index k replaced by u (one more under each binder).</summary>
        [GhostFunction]
        public static Term Open(Term t, Nat k, Term u)
        {
            Spec.Decreases(t);
            return t switch
            {
                Term.Bound b => b.Index == k ? u : t,
                Term.Free => t,
                Term.App a => new Term.App(Open(a.Fun, k, u), Open(a.Arg, k, u)),
                Term.Lam l => new Term.Lam(Open(l.Body, new Nat.S(k), u)),
            };
        }

        /// <summary>{k &lt;- x} t: the name x made index k (one more under each binder).</summary>
        [GhostFunction]
        public static Term Close(Term t, Nat k, int x)
        {
            Spec.Decreases(t);
            return t switch
            {
                Term.Bound => t,
                Term.Free f => f.Name == x ? new Term.Bound(k) : t,
                Term.App a => new Term.App(Close(a.Fun, k, x), Close(a.Arg, k, x)),
                Term.Lam l => new Term.Lam(Close(l.Body, new Nat.S(k), x)),
            };
        }

        /// <summary>[x -> u] t: the name x replaced by u. No index moves: u is to be locally closed.</summary>
        [GhostFunction]
        public static Term Subst(Term t, int x, Term u)
        {
            Spec.Decreases(t);
            return t switch
            {
                Term.Bound => t,
                Term.Free f => f.Name == x ? u : t,
                Term.App a => new Term.App(Subst(a.Fun, x, u), Subst(a.Arg, x, u)),
                Term.Lam l => new Term.Lam(Subst(l.Body, x, u)),
            };
        }

        /// <summary>x is not free in t.</summary>
        [GhostFunction]
        public static bool Fresh(Term t, int x)
        {
            Spec.Decreases(t);
            return t switch
            {
                Term.Bound => true,
                Term.Free f => f.Name != x,
                Term.App a => Fresh(a.Fun, x) && Fresh(a.Arg, x),
                Term.Lam l => Fresh(l.Body, x),
            };
        }

        /// <summary>Every index in t is bound, under k binders more than t's own: locally closed at level k.</summary>
        [GhostFunction]
        public static bool Closed(Term t, Nat k)
        {
            Spec.Decreases(t);
            return t switch
            {
                Term.Bound b => Naturals.Lt(b.Index, k),
                Term.Free => true,
                Term.App a => Closed(a.Fun, k) && Closed(a.Arg, k),
                Term.Lam l => Closed(l.Body, new Nat.S(k)),
            };
        }

        // ---------------------------------------------------------------- local closure

        /// <summary>Locally closed at a level, it is at every higher one.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void ClosedUp(Term t, Nat j, Nat k)
        {
            Spec.Requires((j == k || Naturals.Lt(j, k)) && Closed(t, j));
            Spec.Ensures(Closed(t, k));
            Spec.Decreases(t);
            switch (t)
            {
                case Term.Bound b: if (j != k) Naturals.LtTrans(b.Index, j, k); break;
                case Term.App a: ClosedUp(a.Fun, j, k); ClosedUp(a.Arg, j, k); break;
                case Term.Lam l: ClosedUp(l.Body, new Nat.S(j), new Nat.S(k)); break;
            }
        }

        /// <summary>Opening a term locally closed at k, at k, changes nothing: it has no index k to replace.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void OpenClosed(Term t, Nat k, Term u)
        {
            Spec.Requires(Closed(t, k));
            Spec.Ensures(Open(t, k, u) == t);
            Spec.Decreases(t);
            switch (t)
            {
                case Term.Bound: Naturals.LtIrreflexive(k); break;
                case Term.App a: OpenClosed(a.Fun, k, u); OpenClosed(a.Arg, k, u); break;
                case Term.Lam l: OpenClosed(l.Body, new Nat.S(k), u); break;
            }
        }

        // ---------------------------------------------------------------- opening and closing

        /// <summary>Closing over a fresh name what was opened at it gives back the term.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void CloseOpen(Term t, Nat k, int x)
        {
            Spec.Requires(Fresh(t, x));
            Spec.Ensures(Close(Open(t, k, new Term.Free(x)), k, x) == t);
            Spec.Decreases(t);
            switch (t)
            {
                case Term.App a: CloseOpen(a.Fun, k, x); CloseOpen(a.Arg, k, x); break;
                case Term.Lam l: CloseOpen(l.Body, new Nat.S(k), x); break;
            }
        }

        /// <summary>Opening at a name what was closed over it gives back the term, if it had no index k of its own.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void OpenClose(Term t, Nat k, int x)
        {
            Spec.Requires(Closed(t, k));
            Spec.Ensures(Open(Close(t, k, x), k, new Term.Free(x)) == t);
            Spec.Decreases(t);
            switch (t)
            {
                case Term.Bound: Naturals.LtIrreflexive(k); break;
                case Term.App a: OpenClose(a.Fun, k, x); OpenClose(a.Arg, k, x); break;
                case Term.Lam l: OpenClose(l.Body, new Nat.S(k), x); break;
            }
        }

        // ---------------------------------------------------------------- substitution

        /// <summary>Substituting for a name the term doesn't have changes nothing.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void SubstFresh(Term t, int x, Term u)
        {
            Spec.Requires(Fresh(t, x));
            Spec.Ensures(Subst(t, x, u) == t);
            Spec.Decreases(t);
            switch (t)
            {
                case Term.App a: SubstFresh(a.Fun, x, u); SubstFresh(a.Arg, x, u); break;
                case Term.Lam l: SubstFresh(l.Body, x, u); break;
            }
        }

        /// <summary>
        /// The substitution lemma: substitution commutes with opening, the opened-at term substituted too, where u is
        /// locally closed (no index of it is captured under a binder).
        /// </summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void SubstOpen(Term t, Nat k, Term v, int x, Term u)
        {
            Spec.Requires(Closed(u, new Nat.Z()));
            Spec.Ensures(Subst(Open(t, k, v), x, u) == Open(Subst(t, x, u), k, Subst(v, x, u)));
            Spec.Decreases(t);
            switch (t)
            {
                case Term.Free f:
                    if (f.Name == x)
                    {
                        ClosedUp(u, new Nat.Z(), k);
                        OpenClosed(u, k, Subst(v, x, u));
                    }
                    break;
                case Term.App a: SubstOpen(a.Fun, k, v, x, u); SubstOpen(a.Arg, k, v, x, u); break;
                case Term.Lam l: SubstOpen(l.Body, new Nat.S(k), v, x, u); break;
            }
        }

        /// <summary>
        /// Opening at a term is opening at a fresh name, then substituting the term for it: how a binder's body, opened
        /// at a name, is instantiated.
        /// </summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void SubstIntro(Term t, Nat k, int x, Term u)
        {
            Spec.Requires(Fresh(t, x) && Closed(u, new Nat.Z()));
            Spec.Ensures(Open(t, k, u) == Subst(Open(t, k, new Term.Free(x)), x, u));
            SubstOpen(t, k, new Term.Free(x), x, u);
            SubstFresh(t, x, u);
        }

        // ---------------------------------------------------------------- examples

        /// <summary>\. (1 0), its index 1 bound outside: opened at x it is \. (x 0), and closing over x gives it back.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void Examples()
        {
            var zero = new Nat.Z();
            var one = new Nat.S(zero);
            var body = new Term.App(new Term.Bound(one), new Term.Bound(zero));
            var t = new Term.Lam(body);
            var x = new Term.Free(7);
            var opened = new Term.App(x, new Term.Bound(zero));
            Spec.Assert(Open(new Term.Bound(one), one, x) == x && Open(new Term.Bound(zero), one, x) == new Term.Bound(zero));
            Spec.Assert(Open(body, one, x) == opened);
            Spec.Assert(Open(t, zero, x) == new Term.Lam(opened));
            Spec.Assert(Close(x, one, 7) == new Term.Bound(one) && Close(new Term.Bound(zero), one, 7) == new Term.Bound(zero));
            Spec.Assert(Close(opened, one, 7) == body);
            Spec.Assert(Close(new Term.Lam(opened), zero, 7) == t);
        }
    }
}
