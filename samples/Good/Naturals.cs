using System.Diagnostics;
using CsVerify;

namespace Samples
{
    /// <summary>A natural number, Peano's: zero, or one more than a natural. No overflow: the term samples' indices and depths.</summary>
    public abstract record Nat
    {
        private Nat() { }
        public sealed record Z() : Nat;
        public sealed record S(Nat Pred) : Nat;
    }

    /// <summary>
    /// Order and addition on the naturals. Their laws come from their values as integers (Value): addition is the
    /// integers', so is order, and a value is one natural's; a proof about indices is then the solver's linear arithmetic.
    /// </summary>
    public static class Naturals
    {
        [GhostFunction]
        public static Nat One() => new Nat.S(new Nat.Z());

        /// <summary>a &lt; b.</summary>
        [GhostFunction]
        public static bool Lt(Nat a, Nat b)
        {
            Spec.Decreases(b);
            return b is Nat.S sb && (a is Nat.Z || a is Nat.S sa && Lt(sa.Pred, sb.Pred));
        }

        /// <summary>a + b.</summary>
        [GhostFunction]
        public static Nat Add(Nat a, Nat b)
        {
            Spec.Decreases(a);
            return a is Nat.S s ? new Nat.S(Add(s.Pred, b)) : b;
        }

        /// <summary>n as an integer.</summary>
        [GhostFunction]
        public static int Value(Nat n)
        {
            Spec.Decreases(n);
            Spec.Ensures((int r) => r >= 0);
            return n is Nat.S s ? Value(s.Pred) + 1 : 0;
        }

        // ---------------------------------------------------------------- values

        [Lemma, Conditional(Spec.Symbol)]
        public static void ValueAdd(Nat a, Nat b)
        {
            Spec.Ensures(Value(Add(a, b)) == Value(a) + Value(b));
            Spec.Decreases(a);
            if (a is Nat.S s)
            {
                ValueAdd(s.Pred, b);
            }
        }

        [Lemma, Conditional(Spec.Symbol)]
        public static void ValueLt(Nat a, Nat b)
        {
            Spec.Ensures(Lt(a, b) == (Value(a) < Value(b)));
            Spec.Decreases(b);
            if (a is Nat.S sa && b is Nat.S sb)
            {
                ValueLt(sa.Pred, sb.Pred);
            }
        }

        /// <summary>Two naturals of one value are one.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void ValueInjective(Nat a, Nat b)
        {
            Spec.Ensures((Value(a) == Value(b)) == (a == b));
            Spec.Decreases(a);
            if (a is Nat.S sa && b is Nat.S sb)
            {
                ValueInjective(sa.Pred, sb.Pred);
            }
        }

        // ---------------------------------------------------------------- the laws the samples use

        /// <summary>Nothing is less than itself.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void LtIrreflexive(Nat a)
        {
            Spec.Ensures(!Lt(a, a));
            ValueLt(a, a);
        }

        /// <summary>a &lt; b &lt; c gives a &lt; c.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void LtTrans(Nat a, Nat b, Nat c)
        {
            Spec.Requires(Lt(a, b) && Lt(b, c));
            Spec.Ensures(Lt(a, c));
            ValueLt(a, b);
            ValueLt(b, c);
            ValueLt(a, c);
        }

        [Lemma, Conditional(Spec.Symbol)]
        public static void AddZero(Nat a)
        {
            Spec.Ensures(Add(a, new Nat.Z()) == a);
            ValueAdd(a, new Nat.Z());
            ValueInjective(Add(a, new Nat.Z()), a);
        }

        [Lemma, Conditional(Spec.Symbol)]
        public static void AddOne(Nat a)
        {
            Spec.Ensures(Add(a, One()) == new Nat.S(a));
            Spec.Assert(Value(new Nat.Z()) == 0 && Value(One()) == 1 && Value(new Nat.S(a)) == Value(a) + 1);
            ValueAdd(a, One());
            ValueInjective(Add(a, One()), new Nat.S(a));
        }
    }
}
