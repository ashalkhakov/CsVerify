using System.Diagnostics;
using CsVerify;

#nullable enable

namespace Samples
{
    /// <summary>The simply typed lambda calculus's types: booleans, integers and functions.</summary>
    public abstract record Ty
    {
        private Ty() { }
        public sealed record Bool() : Ty;
        public sealed record Int() : Ty;
        public sealed record Arrow(Ty From, Ty To) : Ty;
    }

    /// <summary>A typing context: index 0's type first.</summary>
    public abstract record Ctx
    {
        private Ctx() { }
        public sealed record Empty() : Ctx;
        public sealed record Bind(Ty Head, Ctx Rest) : Ctx;
    }

    /// <summary>Terms with de Bruijn indices, each binder giving its variable's type (Church style), and booleans and integers.</summary>
    public abstract record Tm
    {
        private Tm() { }
        public sealed record Var(Nat Index) : Tm;
        public sealed record App(Tm Fun, Tm Arg) : Tm;
        public sealed record Lam(Ty Param, Tm Body) : Tm;
        public sealed record BoolLit(bool Value) : Tm;
        public sealed record IntLit(int Value) : Tm;
        public sealed record If(Tm Cond, Tm Then, Tm Else) : Tm;
        public sealed record Add(Tm Left, Tm Right) : Tm;
        public sealed record Less(Tm Left, Tm Right) : Tm;
    }

    /// <summary>
    /// Typing, as a function (each binder gives its type), call-by-value reduction, and their metatheory after TAPL
    /// (chapters 6, 8 and 9): weakening, the substitution lemma, strengthening, preservation and progress, proved by
    /// structural induction.
    /// </summary>
    public static class Stlc
    {
        // ---------------------------------------------------------------- contexts

        /// <summary>Index i's type in g; null where g has no index i.</summary>
        [GhostFunction]
        public static Ty? At(Ctx g, Nat i)
        {
            Spec.Decreases(g);
            return g is Ctx.Bind b ? (i is Nat.S p ? At(b.Rest, p.Pred) : b.Head) : null;
        }

        /// <summary>g has at least c bindings: a binding can be inserted at c.</summary>
        [GhostFunction]
        public static bool Fits(Ctx g, Nat c)
        {
            Spec.Decreases(c);
            return c is Nat.S p ? g is Ctx.Bind b && Fits(b.Rest, p.Pred) : true;
        }

        /// <summary>g with a binding of type x inserted at position c: the indices from c on moved up one.</summary>
        [GhostFunction]
        public static Ctx Insert(Ctx g, Nat c, Ty x)
        {
            Spec.Decreases(g);
            return c is Nat.S p && g is Ctx.Bind b ? new Ctx.Bind(b.Head, Insert(b.Rest, p.Pred, x)) : new Ctx.Bind(x, g);
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
                Tm.BoolLit => new Ty.Bool(),
                Tm.IntLit => new Ty.Int(),
                Tm.If i => TypeOf(g, i.Cond) is Ty.Bool && TypeOf(g, i.Then) is Ty y && TypeOf(g, i.Else) == y ? y : null,
                Tm.Add a => TypeOf(g, a.Left) is Ty.Int && TypeOf(g, a.Right) is Ty.Int ? new Ty.Int() : null,
                Tm.Less l => TypeOf(g, l.Left) is Ty.Int && TypeOf(g, l.Right) is Ty.Int ? new Ty.Bool() : null,
            };
        }

        // ---------------------------------------------------------------- shifting and substitution

        /// <summary>The shift of t up by one above cutoff c.</summary>
        [GhostFunction]
        public static Tm Shift(Tm t, Nat c)
        {
            Spec.Decreases(t);
            return t switch
            {
                Tm.Var v => Naturals.Lt(v.Index, c) ? t : new Tm.Var(new Nat.S(v.Index)),
                Tm.App a => new Tm.App(Shift(a.Fun, c), Shift(a.Arg, c)),
                Tm.Lam l => new Tm.Lam(l.Param, Shift(l.Body, new Nat.S(c))),
                Tm.BoolLit or Tm.IntLit => t,
                Tm.If i => new Tm.If(Shift(i.Cond, c), Shift(i.Then, c), Shift(i.Else, c)),
                Tm.Add a => new Tm.Add(Shift(a.Left, c), Shift(a.Right, c)),
                Tm.Less l => new Tm.Less(Shift(l.Left, c), Shift(l.Right, c)),
            };
        }

        /// <summary>The shift of t down by one above cutoff c (where c's own index isn't used: a beta step's binder gone).</summary>
        [GhostFunction]
        public static Tm Unshift(Tm t, Nat c)
        {
            Spec.Decreases(t);
            return t switch
            {
                Tm.Var v => !Naturals.Lt(v.Index, c) && v.Index is Nat.S p ? new Tm.Var(p.Pred) : t,
                Tm.App a => new Tm.App(Unshift(a.Fun, c), Unshift(a.Arg, c)),
                Tm.Lam l => new Tm.Lam(l.Param, Unshift(l.Body, new Nat.S(c))),
                Tm.BoolLit or Tm.IntLit => t,
                Tm.If i => new Tm.If(Unshift(i.Cond, c), Unshift(i.Then, c), Unshift(i.Else, c)),
                Tm.Add a => new Tm.Add(Unshift(a.Left, c), Unshift(a.Right, c)),
                Tm.Less l => new Tm.Less(Unshift(l.Left, c), Unshift(l.Right, c)),
            };
        }

        /// <summary>[j -> s] t: index j replaced by s; under a binder, j + 1 by s shifted past it.</summary>
        [GhostFunction]
        public static Tm Subst(Tm t, Nat j, Tm s)
        {
            Spec.Decreases(t);
            return t switch
            {
                Tm.Var v => v.Index == j ? s : t,
                Tm.App a => new Tm.App(Subst(a.Fun, j, s), Subst(a.Arg, j, s)),
                Tm.Lam l => new Tm.Lam(l.Param, Subst(l.Body, new Nat.S(j), Shift(s, new Nat.Z()))),
                Tm.BoolLit or Tm.IntLit => t,
                Tm.If i => new Tm.If(Subst(i.Cond, j, s), Subst(i.Then, j, s), Subst(i.Else, j, s)),
                Tm.Add a => new Tm.Add(Subst(a.Left, j, s), Subst(a.Right, j, s)),
                Tm.Less l => new Tm.Less(Subst(l.Left, j, s), Subst(l.Right, j, s)),
            };
        }

        // ---------------------------------------------------------------- weakening

        /// <summary>With a binding inserted at c, index i's type is i's below c, the new one at c, and i - 1's above.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void AtInsert(Ctx g, Nat c, Ty x, Nat i)
        {
            Spec.Requires(Fits(g, c));
            Spec.Ensures(At(Insert(g, c, x), i) == (Naturals.Lt(i, c) ? At(g, i) : i == c ? x : i is Nat.S p ? At(g, p.Pred) : null));
            Spec.Decreases(g);
            if (c is Nat.S cp && g is Ctx.Bind b && i is Nat.S q)
            {
                AtInsert(b.Rest, cp.Pred, x, q.Pred);
            }
        }

        /// <summary>Above a cutoff, an index's successor is above it too, and isn't it.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void Above(Nat i, Nat c)
        {
            Spec.Ensures(Naturals.Lt(i, c) || !Naturals.Lt(new Nat.S(i), c) && new Nat.S(i) != c);
            Naturals.ValueLt(i, c);
            Naturals.ValueLt(new Nat.S(i), c);
            Naturals.ValueInjective(new Nat.S(i), c);
        }

        /// <summary>Weakening: t shifted at c has, in g with a binding inserted at c, the type t has in g.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void Weaken(Ctx g, Tm t, Nat c, Ty x)
        {
            Spec.Requires(Fits(g, c));
            Spec.Ensures(TypeOf(Insert(g, c, x), Shift(t, c)) == TypeOf(g, t));
            Spec.Decreases(t);
            switch (t)
            {
                case Tm.Var v:
                    AtInsert(g, c, x, v.Index);
                    AtInsert(g, c, x, new Nat.S(v.Index));
                    Above(v.Index, c);
                    break;
                case Tm.App a: Weaken(g, a.Fun, c, x); Weaken(g, a.Arg, c, x); break;
                case Tm.Lam l:
                    var under = new Ctx.Bind(l.Param, g);
                    Spec.Assert(Insert(under, new Nat.S(c), x) == new Ctx.Bind(l.Param, Insert(g, c, x)));
                    Weaken(under, l.Body, new Nat.S(c), x);
                    break;
                case Tm.If i: Weaken(g, i.Cond, c, x); Weaken(g, i.Then, c, x); Weaken(g, i.Else, c, x); break;
                case Tm.Add a: Weaken(g, a.Left, c, x); Weaken(g, a.Right, c, x); break;
                case Tm.Less l: Weaken(g, l.Left, c, x); Weaken(g, l.Right, c, x); break;
            }
        }

        // ---------------------------------------------------------------- substitution

        /// <summary>
        /// The substitution lemma: where s has index j's type, substituting s for j keeps t's type (and an ill-typed t
        /// ill-typed). Under a binder, s shifted past it has it by weakening.
        /// </summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void SubstTyped(Ctx g, Tm t, Nat j, Tm s)
        {
            Spec.Requires(TypeOf(g, s) == At(g, j));
            Spec.Ensures(TypeOf(g, Subst(t, j, s)) == TypeOf(g, t));
            Spec.Decreases(t);
            switch (t)
            {
                case Tm.App a: SubstTyped(g, a.Fun, j, s); SubstTyped(g, a.Arg, j, s); break;
                case Tm.Lam l:
                    var under = new Ctx.Bind(l.Param, g);
                    Weaken(g, s, new Nat.Z(), l.Param);
                    Spec.Assert(Insert(g, new Nat.Z(), l.Param) == under);
                    Spec.Assert(At(under, new Nat.S(j)) == At(g, j));
                    SubstTyped(under, l.Body, new Nat.S(j), Shift(s, new Nat.Z()));
                    break;
                case Tm.If i: SubstTyped(g, i.Cond, j, s); SubstTyped(g, i.Then, j, s); SubstTyped(g, i.Else, j, s); break;
                case Tm.Add a: SubstTyped(g, a.Left, j, s); SubstTyped(g, a.Right, j, s); break;
                case Tm.Less l: SubstTyped(g, l.Left, j, s); SubstTyped(g, l.Right, j, s); break;
            }
        }

        // ---------------------------------------------------------------- strengthening

        /// <summary>Index c occurs in t.</summary>
        [GhostFunction]
        public static bool Uses(Tm t, Nat c)
        {
            Spec.Decreases(t);
            return t switch
            {
                Tm.Var v => v.Index == c,
                Tm.App a => Uses(a.Fun, c) || Uses(a.Arg, c),
                Tm.Lam l => Uses(l.Body, new Nat.S(c)),
                Tm.BoolLit or Tm.IntLit => false,
                Tm.If i => Uses(i.Cond, c) || Uses(i.Then, c) || Uses(i.Else, c),
                Tm.Add a => Uses(a.Left, c) || Uses(a.Right, c),
                Tm.Less l => Uses(l.Left, c) || Uses(l.Right, c),
            };
        }

        /// <summary>A shift at a cutoff up to c leaves out index c + 1, if t didn't use c.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void ShiftUnused(Tm t, Nat c0, Nat c)
        {
            Spec.Requires(!Naturals.Lt(c, c0) && !Uses(t, c));
            Spec.Ensures(!Uses(Shift(t, c0), new Nat.S(c)));
            Spec.Decreases(t);
            switch (t)
            {
                case Tm.Var v:
                    Naturals.ValueLt(v.Index, c0);
                    Naturals.ValueLt(c, c0);
                    Naturals.ValueInjective(v.Index, new Nat.S(c));
                    break;
                case Tm.App a: ShiftUnused(a.Fun, c0, c); ShiftUnused(a.Arg, c0, c); break;
                case Tm.Lam l: ShiftUnused(l.Body, new Nat.S(c0), new Nat.S(c)); break;
                case Tm.If i: ShiftUnused(i.Cond, c0, c); ShiftUnused(i.Then, c0, c); ShiftUnused(i.Else, c0, c); break;
                case Tm.Add a: ShiftUnused(a.Left, c0, c); ShiftUnused(a.Right, c0, c); break;
                case Tm.Less l: ShiftUnused(l.Left, c0, c); ShiftUnused(l.Right, c0, c); break;
            }
        }

        /// <summary>A shift at c leaves out index c.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void ShiftLeavesOut(Tm t, Nat c)
        {
            Spec.Ensures(!Uses(Shift(t, c), c));
            Spec.Decreases(t);
            switch (t)
            {
                case Tm.Var v: Naturals.LtIrreflexive(c); Above(v.Index, c); break;
                case Tm.App a: ShiftLeavesOut(a.Fun, c); ShiftLeavesOut(a.Arg, c); break;
                case Tm.Lam l: ShiftLeavesOut(l.Body, new Nat.S(c)); break;
                case Tm.If i: ShiftLeavesOut(i.Cond, c); ShiftLeavesOut(i.Then, c); ShiftLeavesOut(i.Else, c); break;
                case Tm.Add a: ShiftLeavesOut(a.Left, c); ShiftLeavesOut(a.Right, c); break;
                case Tm.Less l: ShiftLeavesOut(l.Left, c); ShiftLeavesOut(l.Right, c); break;
            }
        }

        /// <summary>Substituting for c a term that doesn't use c leaves c out.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void SubstLeavesOut(Tm t, Nat c, Tm s)
        {
            Spec.Requires(!Uses(s, c));
            Spec.Ensures(!Uses(Subst(t, c, s), c));
            Spec.Decreases(t);
            switch (t)
            {
                case Tm.App a: SubstLeavesOut(a.Fun, c, s); SubstLeavesOut(a.Arg, c, s); break;
                case Tm.Lam l:
                    ShiftUnused(s, new Nat.Z(), c);
                    SubstLeavesOut(l.Body, new Nat.S(c), Shift(s, new Nat.Z()));
                    break;
                case Tm.If i: SubstLeavesOut(i.Cond, c, s); SubstLeavesOut(i.Then, c, s); SubstLeavesOut(i.Else, c, s); break;
                case Tm.Add a: SubstLeavesOut(a.Left, c, s); SubstLeavesOut(a.Right, c, s); break;
                case Tm.Less l: SubstLeavesOut(l.Left, c, s); SubstLeavesOut(l.Right, c, s); break;
            }
        }

        /// <summary>Strengthening: t, not using c, shifted down at c, has in g the type it has in g with a binding inserted at c.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void Strengthen(Ctx g, Tm t, Nat c, Ty x)
        {
            Spec.Requires(Fits(g, c) && !Uses(t, c));
            Spec.Ensures(TypeOf(g, Unshift(t, c)) == TypeOf(Insert(g, c, x), t));
            Spec.Decreases(t);
            switch (t)
            {
                case Tm.Var v:
                    AtInsert(g, c, x, v.Index);
                    Naturals.ValueLt(v.Index, c);
                    Naturals.ValueInjective(v.Index, c);
                    break;
                case Tm.App a: Strengthen(g, a.Fun, c, x); Strengthen(g, a.Arg, c, x); break;
                case Tm.Lam l:
                    var under = new Ctx.Bind(l.Param, g);
                    Spec.Assert(Insert(under, new Nat.S(c), x) == new Ctx.Bind(l.Param, Insert(g, c, x)));
                    Strengthen(under, l.Body, new Nat.S(c), x);
                    break;
                case Tm.If i: Strengthen(g, i.Cond, c, x); Strengthen(g, i.Then, c, x); Strengthen(g, i.Else, c, x); break;
                case Tm.Add a: Strengthen(g, a.Left, c, x); Strengthen(g, a.Right, c, x); break;
                case Tm.Less l: Strengthen(g, l.Left, c, x); Strengthen(g, l.Right, c, x); break;
            }
        }

        // ---------------------------------------------------------------- reduction

        /// <summary>A value: a literal or an abstraction.</summary>
        [GhostFunction]
        public static bool IsValue(Tm t) => t is Tm.BoolLit or Tm.IntLit or Tm.Lam;

        /// <summary>A beta step's result, (\:p. b) s: index 0 replaced by s, the binder gone (TAPL's ↑⁻¹([0 -> ↑¹ s] b)).</summary>
        [GhostFunction]
        public static Tm Beta(Tm b, Tm s) => Unshift(Subst(b, new Nat.Z(), Shift(s, new Nat.Z())), new Nat.Z());

        /// <summary>x + y as C#'s unchecked int addition: wrapped around into int's range.</summary>
        [GhostFunction]
        public static int Plus(int x, int y)
        {
            Spec.Ensures((int r) => int.MinValue <= r && r <= int.MaxValue);
            long s = (long)x + y;
            return s > int.MaxValue ? (int)(s - 4294967296L) : s < int.MinValue ? (int)(s + 4294967296L) : (int)s;
        }

        /// <summary>The call-by-value step t takes; null where it takes none (a value, or stuck).</summary>
        [GhostFunction]
        public static Tm? Step(Tm t)
        {
            Spec.Decreases(t);
            return t switch
            {
                Tm.App a => a.Fun is Tm.Lam l && IsValue(a.Arg) ? Beta(l.Body, a.Arg)
                          : Step(a.Fun) is Tm f ? new Tm.App(f, a.Arg)
                          : IsValue(a.Fun) && Step(a.Arg) is Tm x ? new Tm.App(a.Fun, x) : null,
                Tm.If i => i.Cond is Tm.BoolLit b ? (b.Value ? i.Then : i.Else)
                         : Step(i.Cond) is Tm c ? new Tm.If(c, i.Then, i.Else) : null,
                Tm.Add a => a.Left is Tm.IntLit x && a.Right is Tm.IntLit y ? new Tm.IntLit(Plus(x.Value, y.Value))
                           : Step(a.Left) is Tm l ? new Tm.Add(l, a.Right)
                           : IsValue(a.Left) && Step(a.Right) is Tm r ? new Tm.Add(a.Left, r) : null,
                Tm.Less l => l.Left is Tm.IntLit x && l.Right is Tm.IntLit y ? new Tm.BoolLit(x.Value < y.Value)
                           : Step(l.Left) is Tm m ? new Tm.Less(m, l.Right)
                           : IsValue(l.Left) && Step(l.Right) is Tm r ? new Tm.Less(l.Left, r) : null,
                _ => null,
            };
        }

        // ---------------------------------------------------------------- preservation

        /// <summary>Preservation for beta: a well-typed redex steps to a term of its type.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void BetaPreserves(Ctx g, Ty p, Tm b, Tm s)
        {
            Spec.Requires(TypeOf(g, new Tm.App(new Tm.Lam(p, b), s)) != null);
            Spec.Ensures(TypeOf(g, Beta(b, s)) == TypeOf(g, new Tm.App(new Tm.Lam(p, b), s)));
            var under = new Ctx.Bind(p, g);
            var z = new Nat.Z();
            var up = Shift(s, z);
            // (the redex typed: the body has some type r under p, and the argument has type p)
            var lam = new Tm.Lam(p, b);
            var r = TypeOf(under, b);
            Spec.Assert(TypeOf(g, lam) is Ty.Arrow && TypeOf(g, s) != null);
            Spec.Assert(r != null);
            Spec.Assert(TypeOf(g, lam) == new Ty.Arrow(p, r!));
            Spec.Assert(TypeOf(g, s) == p && TypeOf(g, new Tm.App(lam, s)) == r);
            Spec.Assert(At(under, z) == p);
            Weaken(g, s, z, p);
            Spec.Assert(Insert(g, z, p) == under);
            SubstTyped(under, b, z, up);
            ShiftLeavesOut(s, z);
            SubstLeavesOut(b, z, up);
            Strengthen(g, Subst(b, z, up), z, p);
        }

        /// <summary>Preservation: a well-typed term that steps steps to a term of its type.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void Preserves(Ctx g, Tm t)
        {
            Spec.Requires(TypeOf(g, t) != null && Step(t) != null);
            Spec.Ensures(TypeOf(g, Step(t)!) == TypeOf(g, t));
            Spec.Decreases(t);
            switch (t)
            {
                case Tm.App a:
                    if (a.Fun is Tm.Lam lam && IsValue(a.Arg))
                    {
                        BetaPreserves(g, lam.Param, lam.Body, a.Arg);
                    }
                    else if (Step(a.Fun) != null)
                    {
                        Preserves(g, a.Fun);
                    }
                    else
                    {
                        Preserves(g, a.Arg);
                    }
                    break;
                case Tm.If i:
                    if (!(i.Cond is Tm.BoolLit))
                    {
                        Preserves(g, i.Cond);
                    }
                    break;
                case Tm.Add a:
                    if (!(a.Left is Tm.IntLit && a.Right is Tm.IntLit))
                    {
                        if (Step(a.Left) != null)
                        {
                            Preserves(g, a.Left);
                        }
                        else
                        {
                            Preserves(g, a.Right);
                        }
                    }
                    break;
                case Tm.Less l:
                    if (!(l.Left is Tm.IntLit && l.Right is Tm.IntLit))
                    {
                        if (Step(l.Left) != null)
                        {
                            Preserves(g, l.Left);
                        }
                        else
                        {
                            Preserves(g, l.Right);
                        }
                    }
                    break;
            }
        }

        // ---------------------------------------------------------------- progress

        /// <summary>Canonical forms: a value of a type is of that type's form.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void Canonical(Ctx g, Tm v)
        {
            Spec.Requires(IsValue(v) && TypeOf(g, v) != null);
            Spec.Ensures(TypeOf(g, v) is Ty.Bool ? v is Tm.BoolLit : TypeOf(g, v) is Ty.Int ? v is Tm.IntLit : v is Tm.Lam);
        }

        /// <summary>Progress: a closed well-typed term is a value, or it steps.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void Progress(Tm t)
        {
            Spec.Requires(TypeOf(new Ctx.Empty(), t) != null);
            Spec.Ensures(IsValue(t) || Step(t) != null);
            Spec.Decreases(t);
            var empty = new Ctx.Empty();
            switch (t)
            {
                case Tm.App a:
                    Progress(a.Fun); Progress(a.Arg);
                    if (IsValue(a.Fun)) Canonical(empty, a.Fun);
                    break;
                case Tm.If i:
                    Progress(i.Cond);
                    if (IsValue(i.Cond)) Canonical(empty, i.Cond);
                    break;
                case Tm.Add a:
                    Progress(a.Left); Progress(a.Right);
                    if (IsValue(a.Left)) Canonical(empty, a.Left);
                    if (IsValue(a.Right)) Canonical(empty, a.Right);
                    break;
                case Tm.Less l:
                    Progress(l.Left); Progress(l.Right);
                    if (IsValue(l.Left)) Canonical(empty, l.Left);
                    if (IsValue(l.Right)) Canonical(empty, l.Right);
                    break;
            }
        }

        // ---------------------------------------------------------------- examples

        /// <summary>(\x:Int. x + 1) 41 is an Int, and steps to 41 + 1, then to 42; if 1 &lt; 2 then true else false steps to true.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void Examples()
        {
            var empty = new Ctx.Empty();
            var zero = new Nat.Z();
            var x = new Tm.Var(zero);
            var body = new Tm.Add(x, new Tm.IntLit(1));
            var inc = new Tm.Lam(new Ty.Int(), body);
            var t = new Tm.App(inc, new Tm.IntLit(41));
            // its type: the body is an Int where x is
            Spec.Assert(TypeOf(new Ctx.Bind(new Ty.Int(), empty), x) == new Ty.Int());
            Spec.Assert(TypeOf(new Ctx.Bind(new Ty.Int(), empty), new Tm.IntLit(1)) == new Ty.Int() && TypeOf(empty, new Tm.IntLit(41)) == new Ty.Int());
            Spec.Assert(TypeOf(new Ctx.Bind(new Ty.Int(), empty), body) == new Ty.Int());
            Spec.Assert(TypeOf(empty, inc) == new Ty.Arrow(new Ty.Int(), new Ty.Int()));
            Spec.Assert(TypeOf(empty, t) == new Ty.Int());
            // a beta step: 41 for x, shifted past the binder and back
            Spec.Assert(IsValue(new Tm.IntLit(41)) && Shift(new Tm.IntLit(41), zero) == new Tm.IntLit(41));
            Spec.Assert(Subst(x, zero, new Tm.IntLit(41)) == new Tm.IntLit(41) && Subst(new Tm.IntLit(1), zero, new Tm.IntLit(41)) == new Tm.IntLit(1));
            Spec.Assert(Subst(body, zero, new Tm.IntLit(41)) == new Tm.Add(new Tm.IntLit(41), new Tm.IntLit(1)));
            Spec.Assert(Unshift(new Tm.IntLit(41), zero) == new Tm.IntLit(41) && Unshift(new Tm.IntLit(1), zero) == new Tm.IntLit(1));
            Spec.Assert(Unshift(new Tm.Add(new Tm.IntLit(41), new Tm.IntLit(1)), zero) == new Tm.Add(new Tm.IntLit(41), new Tm.IntLit(1)));
            Spec.Assert(Step(t) == new Tm.Add(new Tm.IntLit(41), new Tm.IntLit(1)));
            // and the addition
            Spec.Assert(Plus(41, 1) == 42);
            Spec.Assert(Step(new Tm.Add(new Tm.IntLit(41), new Tm.IntLit(1))) == new Tm.IntLit(42));
            // a condition
            var c = new Tm.If(new Tm.Less(new Tm.IntLit(1), new Tm.IntLit(2)), new Tm.BoolLit(true), new Tm.BoolLit(false));
            Spec.Assert(TypeOf(empty, new Tm.IntLit(1)) == new Ty.Int() && TypeOf(empty, new Tm.IntLit(2)) == new Ty.Int());
            Spec.Assert(TypeOf(empty, new Tm.Less(new Tm.IntLit(1), new Tm.IntLit(2))) == new Ty.Bool());
            Spec.Assert(TypeOf(empty, new Tm.BoolLit(true)) == new Ty.Bool() && TypeOf(empty, new Tm.BoolLit(false)) == new Ty.Bool());
            Spec.Assert(TypeOf(empty, c) == new Ty.Bool());
            Spec.Assert(Step(new Tm.Less(new Tm.IntLit(1), new Tm.IntLit(2))) == new Tm.BoolLit(true));
            Spec.Assert(Step(c) == new Tm.If(new Tm.BoolLit(true), new Tm.BoolLit(true), new Tm.BoolLit(false)));
            Spec.Assert(Step(new Tm.If(new Tm.BoolLit(true), new Tm.BoolLit(true), new Tm.BoolLit(false))) == new Tm.BoolLit(true));
        }
    }
}
