using System.Diagnostics;
using CsVerify;

#nullable enable

namespace Samples
{
    /// <summary>The simply typed lambda calculus's types: a base type and functions.</summary>
    public abstract record Ty
    {
        private Ty() { }
        public sealed record Base() : Ty;
        public sealed record Arrow(Ty From, Ty To) : Ty;
    }

    /// <summary>A typing context: index 0's type first.</summary>
    public abstract record Ctx
    {
        private Ctx() { }
        public sealed record Empty() : Ctx;
        public sealed record Bind(Ty Head, Ctx Rest) : Ctx;
    }

    /// <summary>Terms with de Bruijn indices, each binder giving its variable's type (Church style).</summary>
    public abstract record Tm
    {
        private Tm() { }
        public sealed record Var(int Index) : Tm;
        public sealed record App(Tm Fun, Tm Arg) : Tm;
        public sealed record Lam(Ty Param, Tm Body) : Tm;
    }

    /// <summary>
    /// Typing, as a function (each binder gives its type), and its metatheory after TAPL (chapters 6 and 9): weakening,
    /// and the substitution lemma, proved by structural induction.
    /// </summary>
    public static class Stlc
    {
        // ---------------------------------------------------------------- contexts

        [GhostFunction]
        public static int Length(Ctx g)
        {
            Spec.Decreases(g);
            Spec.Ensures((int r) => r >= 0);
            return g is Ctx.Bind b ? 1 + Length(b.Rest) : 0;
        }

        /// <summary>Index i's type in g; null where g has no index i.</summary>
        [GhostFunction]
        public static Ty? At(Ctx g, int i)
        {
            Spec.Decreases(g);
            return g is Ctx.Bind b && i >= 0 ? (i == 0 ? b.Head : At(b.Rest, i - 1)) : null;
        }

        /// <summary>g with a binding of type x inserted at position c: the indices from c on moved up one.</summary>
        [GhostFunction]
        public static Ctx Insert(Ctx g, int c, Ty x)
        {
            Spec.Decreases(g);
            return c > 0 && g is Ctx.Bind b ? new Ctx.Bind(b.Head, Insert(b.Rest, c - 1, x)) : new Ctx.Bind(x, g);
        }

        // ---------------------------------------------------------------- typing

        /// <summary>t's type in g; null where t is ill-typed.</summary>
        [GhostFunction]
        public static Ty? TypeOf(Ctx g, Tm t)
        {
            Spec.Decreases(t);
            return t switch
            {
                Tm.Var v => At(g, v.Index),
                Tm.App a => TypeOf(g, a.Fun) is Ty.Arrow f && TypeOf(g, a.Arg) is Ty x && f.From == x ? f.To : null,
                Tm.Lam l => TypeOf(new Ctx.Bind(l.Param, g), l.Body) is Ty r ? new Ty.Arrow(l.Param, r) : null,
            };
        }

        // ---------------------------------------------------------------- shifting and substitution

        /// <summary>The d-place shift of t above cutoff c.</summary>
        [GhostFunction]
        public static Tm Shift(Tm t, int d, int c)
        {
            Spec.Decreases(t);
            return t switch
            {
                Tm.Var v => v.Index < c ? t : new Tm.Var(v.Index + d),
                Tm.App a => new Tm.App(Shift(a.Fun, d, c), Shift(a.Arg, d, c)),
                Tm.Lam l => new Tm.Lam(l.Param, Shift(l.Body, d, c + 1)),
            };
        }

        /// <summary>[j -> s] t: index j replaced by s; under a binder, j + 1 by s shifted past it.</summary>
        [GhostFunction]
        public static Tm Subst(Tm t, int j, Tm s)
        {
            Spec.Decreases(t);
            return t switch
            {
                Tm.Var v => v.Index == j ? s : t,
                Tm.App a => new Tm.App(Subst(a.Fun, j, s), Subst(a.Arg, j, s)),
                Tm.Lam l => new Tm.Lam(l.Param, Subst(l.Body, j + 1, Shift(s, 1, 0))),
            };
        }

        // ---------------------------------------------------------------- weakening

        /// <summary>With a binding inserted at c, index i's type is i's below c and i - 1's above, and c's is the new one.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void AtInsert(Ctx g, int c, Ty x, int i)
        {
            Spec.Requires(0 <= c && c <= Length(g));
            Spec.Ensures(At(Insert(g, c, x), i) == (i < c ? At(g, i) : i == c ? x : At(g, i - 1)));
            Spec.Decreases(g);
            if (c > 0 && g is Ctx.Bind b && i > 0)
            {
                AtInsert(b.Rest, c - 1, x, i - 1);
            }
        }

        /// <summary>Weakening: t shifted at c has, in g with a binding inserted at c, the type t has in g.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void Weaken(Ctx g, Tm t, int c, Ty x)
        {
            Spec.Requires(0 <= c && c <= Length(g));
            Spec.Ensures(TypeOf(Insert(g, c, x), Shift(t, 1, c)) == TypeOf(g, t));
            Spec.Decreases(t);
            switch (t)
            {
                case Tm.Var v:
                    AtInsert(g, c, x, v.Index);
                    AtInsert(g, c, x, v.Index + 1);
                    break;
                case Tm.App a: Weaken(g, a.Fun, c, x); Weaken(g, a.Arg, c, x); break;
                case Tm.Lam l:
                    var under = new Ctx.Bind(l.Param, g);
                    Spec.Assert(Insert(under, c + 1, x) == new Ctx.Bind(l.Param, Insert(g, c, x)));
                    Weaken(under, l.Body, c + 1, x);
                    break;
            }
        }

        // ---------------------------------------------------------------- substitution

        /// <summary>
        /// The substitution lemma: where s has index j's type, substituting s for j keeps t's type (and an ill-typed t
        /// ill-typed). Under a binder, s shifted past it has it by weakening.
        /// </summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void SubstTyped(Ctx g, Tm t, int j, Tm s)
        {
            Spec.Requires(0 <= j && TypeOf(g, s) == At(g, j));
            Spec.Ensures(TypeOf(g, Subst(t, j, s)) == TypeOf(g, t));
            Spec.Decreases(t);
            switch (t)
            {
                case Tm.App a: SubstTyped(g, a.Fun, j, s); SubstTyped(g, a.Arg, j, s); break;
                case Tm.Lam l:
                    var under = new Ctx.Bind(l.Param, g);
                    Weaken(g, s, 0, l.Param);
                    Spec.Assert(Insert(g, 0, l.Param) == under);
                    Spec.Assert(At(under, j + 1) == At(g, j));
                    SubstTyped(under, l.Body, j + 1, Shift(s, 1, 0));
                    break;
            }
        }

        // ---------------------------------------------------------------- strengthening

        /// <summary>Index c occurs in t.</summary>
        [GhostFunction]
        public static bool Uses(Tm t, int c)
        {
            Spec.Decreases(t);
            return t switch
            {
                Tm.Var v => v.Index == c,
                Tm.App a => Uses(a.Fun, c) || Uses(a.Arg, c),
                Tm.Lam l => Uses(l.Body, c + 1),
            };
        }

        /// <summary>A shift at a cutoff up to c leaves out index c + 1, if t didn't use c.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void ShiftUnused(Tm t, int c0, int c)
        {
            Spec.Requires(c0 <= c && !Uses(t, c));
            Spec.Ensures(!Uses(Shift(t, 1, c0), c + 1));
            Spec.Decreases(t);
            switch (t)
            {
                case Tm.App a: ShiftUnused(a.Fun, c0, c); ShiftUnused(a.Arg, c0, c); break;
                case Tm.Lam l: ShiftUnused(l.Body, c0 + 1, c + 1); break;
            }
        }

        /// <summary>A shift at c leaves out index c.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void ShiftLeavesOut(Tm t, int c)
        {
            Spec.Ensures(!Uses(Shift(t, 1, c), c));
            Spec.Decreases(t);
            switch (t)
            {
                case Tm.App a: ShiftLeavesOut(a.Fun, c); ShiftLeavesOut(a.Arg, c); break;
                case Tm.Lam l: ShiftLeavesOut(l.Body, c + 1); break;
            }
        }

        /// <summary>Substituting for c a term that doesn't use c leaves c out.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void SubstLeavesOut(Tm t, int c, Tm s)
        {
            Spec.Requires(0 <= c && !Uses(s, c));
            Spec.Ensures(!Uses(Subst(t, c, s), c));
            Spec.Decreases(t);
            switch (t)
            {
                case Tm.App a: SubstLeavesOut(a.Fun, c, s); SubstLeavesOut(a.Arg, c, s); break;
                case Tm.Lam l:
                    ShiftUnused(s, 0, c);
                    SubstLeavesOut(l.Body, c + 1, Shift(s, 1, 0));
                    break;
            }
        }

        /// <summary>Strengthening: t, not using c, shifted down at c, has in g the type it has in g with a binding inserted at c.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void Strengthen(Ctx g, Tm t, int c, Ty x)
        {
            Spec.Requires(0 <= c && c <= Length(g) && !Uses(t, c));
            Spec.Ensures(TypeOf(g, Shift(t, -1, c)) == TypeOf(Insert(g, c, x), t));
            Spec.Decreases(t);
            switch (t)
            {
                case Tm.Var v:
                    AtInsert(g, c, x, v.Index);
                    AtInsert(g, c, x, v.Index - 1);
                    break;
                case Tm.App a: Strengthen(g, a.Fun, c, x); Strengthen(g, a.Arg, c, x); break;
                case Tm.Lam l:
                    var under = new Ctx.Bind(l.Param, g);
                    Spec.Assert(Insert(under, c + 1, x) == new Ctx.Bind(l.Param, Insert(g, c, x)));
                    Strengthen(under, l.Body, c + 1, x);
                    break;
            }
        }

        // ---------------------------------------------------------------- preservation

        /// <summary>A beta step's result, (\:p. b) s: index 0 replaced by s, the binder gone (TAPL's ↑⁻¹([0 -> ↑¹ s] b)).</summary>
        [GhostFunction]
        public static Tm Beta(Tm b, Tm s) => Shift(Subst(b, 0, Shift(s, 1, 0)), -1, 0);

        /// <summary>Preservation for beta: a well-typed redex steps to a term of its type.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void BetaPreserves(Ctx g, Ty p, Tm b, Tm s)
        {
            Spec.Requires(TypeOf(g, new Tm.App(new Tm.Lam(p, b), s)) != null);
            Spec.Ensures(TypeOf(g, Beta(b, s)) == TypeOf(g, new Tm.App(new Tm.Lam(p, b), s)));
            var under = new Ctx.Bind(p, g);
            var up = Shift(s, 1, 0);
            // (the redex typed: the body has some type r under p, and the argument has type p)
            var r = TypeOf(under, b);
            Spec.Assert(r != null && TypeOf(g, new Tm.Lam(p, b)) == new Ty.Arrow(p, r!));
            Spec.Assert(TypeOf(g, s) == p && TypeOf(g, new Tm.App(new Tm.Lam(p, b), s)) == r);
            Spec.Assert(At(under, 0) == p);
            Weaken(g, s, 0, p);
            Spec.Assert(Insert(g, 0, p) == under);
            SubstTyped(under, b, 0, up);
            ShiftLeavesOut(s, 0);
            SubstLeavesOut(b, 0, up);
            Strengthen(g, Subst(b, 0, up), 0, p);
        }
    }
}
