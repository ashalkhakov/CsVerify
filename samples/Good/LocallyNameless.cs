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
        public sealed record Bound(int Index) : Term;
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
        public static Term Open(Term t, int k, Term u)
        {
            Spec.Decreases(t);
            return t switch
            {
                Term.Bound b => b.Index == k ? u : t,
                Term.Free => t,
                Term.App a => new Term.App(Open(a.Fun, k, u), Open(a.Arg, k, u)),
                Term.Lam l => new Term.Lam(Open(l.Body, k + 1, u)),
            };
        }

        /// <summary>{k &lt;- x} t: the name x made index k (one more under each binder).</summary>
        [GhostFunction]
        public static Term Close(Term t, int k, int x)
        {
            Spec.Decreases(t);
            return t switch
            {
                Term.Bound => t,
                Term.Free f => f.Name == x ? new Term.Bound(k) : t,
                Term.App a => new Term.App(Close(a.Fun, k, x), Close(a.Arg, k, x)),
                Term.Lam l => new Term.Lam(Close(l.Body, k + 1, x)),
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
        public static bool Closed(Term t, int k)
        {
            Spec.Decreases(t);
            return t switch
            {
                Term.Bound b => 0 <= b.Index && b.Index < k,
                Term.Free => true,
                Term.App a => Closed(a.Fun, k) && Closed(a.Arg, k),
                Term.Lam l => Closed(l.Body, k + 1),
            };
        }

        // ---------------------------------------------------------------- local closure

        /// <summary>Locally closed at a level, it is at every higher one.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void ClosedUp(Term t, int j, int k)
        {
            Spec.Requires(j <= k && Closed(t, j));
            Spec.Ensures(Closed(t, k));
            Spec.Decreases(t);
            switch (t)
            {
                case Term.App a: ClosedUp(a.Fun, j, k); ClosedUp(a.Arg, j, k); break;
                case Term.Lam l: ClosedUp(l.Body, j + 1, k + 1); break;
            }
        }

        /// <summary>Opening a term locally closed at k, at k, changes nothing: it has no index k to replace.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void OpenClosed(Term t, int k, Term u)
        {
            Spec.Requires(Closed(t, k));
            Spec.Ensures(Open(t, k, u) == t);
            Spec.Decreases(t);
            switch (t)
            {
                case Term.App a: OpenClosed(a.Fun, k, u); OpenClosed(a.Arg, k, u); break;
                case Term.Lam l: OpenClosed(l.Body, k + 1, u); break;
            }
        }

        // ---------------------------------------------------------------- opening and closing

        /// <summary>Closing over a fresh name what was opened at it gives back the term.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void CloseOpen(Term t, int k, int x)
        {
            Spec.Requires(Fresh(t, x));
            Spec.Ensures(Close(Open(t, k, new Term.Free(x)), k, x) == t);
            Spec.Decreases(t);
            switch (t)
            {
                case Term.App a: CloseOpen(a.Fun, k, x); CloseOpen(a.Arg, k, x); break;
                case Term.Lam l: CloseOpen(l.Body, k + 1, x); break;
            }
        }

        /// <summary>Opening at a name what was closed over it gives back the term, if it had no index k of its own.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void OpenClose(Term t, int k, int x)
        {
            Spec.Requires(Closed(t, k));
            Spec.Ensures(Open(Close(t, k, x), k, new Term.Free(x)) == t);
            Spec.Decreases(t);
            switch (t)
            {
                case Term.App a: OpenClose(a.Fun, k, x); OpenClose(a.Arg, k, x); break;
                case Term.Lam l: OpenClose(l.Body, k + 1, x); break;
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
        public static void SubstOpen(Term t, int k, Term v, int x, Term u)
        {
            Spec.Requires(0 <= k && Closed(u, 0));
            Spec.Ensures(Subst(Open(t, k, v), x, u) == Open(Subst(t, x, u), k, Subst(v, x, u)));
            Spec.Decreases(t);
            switch (t)
            {
                case Term.Free f:
                    if (f.Name == x)
                    {
                        ClosedUp(u, 0, k);
                        OpenClosed(u, k, Subst(v, x, u));
                    }
                    break;
                case Term.App a: SubstOpen(a.Fun, k, v, x, u); SubstOpen(a.Arg, k, v, x, u); break;
                case Term.Lam l: SubstOpen(l.Body, k + 1, v, x, u); break;
            }
        }

        /// <summary>
        /// Opening at a term is opening at a fresh name, then substituting the term for it: how a binder's body, opened
        /// at a name, is instantiated.
        /// </summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void SubstIntro(Term t, int k, int x, Term u)
        {
            Spec.Requires(0 <= k && Fresh(t, x) && Closed(u, 0));
            Spec.Ensures(Open(t, k, u) == Subst(Open(t, k, new Term.Free(x)), x, u));
            SubstOpen(t, k, new Term.Free(x), x, u);
            SubstFresh(t, x, u);
        }
    }
}
