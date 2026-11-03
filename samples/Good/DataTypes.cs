using System.Diagnostics;
using CsVerify;

namespace Samples
{
    /// <summary>
    /// A list as an algebraic data type (ATS <c>datatype list</c>, Dafny <c>datatype List</c>): a closed record
    /// hierarchy. The private constructor and nested sealed cases mean Nil and Cons are the only cases. It is generic:
    /// one data type for every element type, so <c>Length&lt;T&gt;</c> takes apart the <c>List&lt;int&gt;</c> a caller built.
    /// </summary>
    public abstract record List<T>
    {
        private List() { }
        public sealed record Nil() : List<T>;
        public sealed record Cons(T Head, List<T> Tail) : List<T>;
    }

    /// <summary>
    /// Arithmetic expressions and their meaning, from Dafny's tutorial: constant folding preserves evaluation.
    /// </summary>
    public abstract record Exp
    {
        private Exp() { }
        public sealed record Num(int Value) : Exp;
        public sealed record Add(Exp Left, Exp Right) : Exp;
        public sealed record Mul(Exp Left, Exp Right) : Exp;
    }

    /// <summary>
    /// ATS's dataprop FACT (INT2PROGINATS): <c>FACTbas() : FACT(0, 1) | {n:nat}{r:int} FACTind(n+1, (n+1)*r) of FACT(n, r)</c>.
    /// A proof is a value of this closed hierarchy; runtime code carries it as <c>Ghost&lt;Fact&gt;</c>, so the erased
    /// program never builds one.
    /// </summary>
    internal abstract record Fact(int N, int R)
    {
        /// <summary>The index is a natural number (ATS's <c>{n:nat}</c>): true of FACTbas, and kept by FACTind.</summary>
        [Invariant, Pure] public bool Natural() => N >= 0;

        public sealed record Bas() : Fact(0, 1);
        public sealed record Ind(Fact Prev) : Fact(Prev.N + 1, (Prev.N + 1) * Prev.R);
    }

    /// <summary>An interval: an immutable object with an invariant, proved where one is built, assumed everywhere else.</summary>
    public sealed record Interval(int Lo, int Hi)
    {
        [Invariant, Pure] public bool Valid() => Lo <= Hi;

        [Pure]
        public int Width()
        {
            Spec.Ensures((int r) => r >= 0);
            return Hi - Lo;
        }
    }

    public static class DataTypes
    {
        // ---------------------------------------------------------------- lists

        [Pure]
        public static int Length<T>(List<T> xs)
        {
            Spec.Decreases(xs);
            Spec.Ensures((int r) => r >= 0);
            return xs switch { List<T>.Nil => 0, List<T>.Cons c => 1 + Length(c.Tail) };
        }

        [Pure]
        public static List<T> Append<T>(List<T> xs, List<T> ys)
        {
            Spec.Decreases(xs);
            return xs switch { List<T>.Nil => ys, List<T>.Cons c => new List<T>.Cons(c.Head, Append(c.Tail, ys)) };
        }

        [Pure]
        public static List<T> Reverse<T>(List<T> xs)
        {
            Spec.Decreases(xs);
            return xs switch { List<T>.Nil => xs, List<T>.Cons c => Append(Reverse(c.Tail), new List<T>.Cons(c.Head, new List<T>.Nil())) };
        }

        /// <summary>|xs ++ ys| = |xs| + |ys|, by induction on xs.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void AppendLength<T>(List<T> xs, List<T> ys)
        {
            Spec.Decreases(xs);
            Spec.Ensures(Length(Append(xs, ys)) == Length(xs) + Length(ys));
            if (xs is List<T>.Cons c) AppendLength(c.Tail, ys);
        }

        /// <summary>|reverse xs| = |xs|, using the append lemma at each step.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void ReverseLength<T>(List<T> xs)
        {
            Spec.Decreases(xs);
            Spec.Ensures(Length(Reverse(xs)) == Length(xs));
            if (xs is List<T>.Cons c)
            {
                ReverseLength(c.Tail);
                var one = new List<T>.Cons(c.Head, new List<T>.Nil());
                AppendLength(Reverse(c.Tail), one);
                Spec.Assert(Length(one.Tail) == 0);
            }
        }

        /// <summary>Builds [n-1, ..., 1, 0] at run time; its length is proved, not tested.</summary>
        public static List<int> Countdown(int n)
        {
            Spec.Requires(n >= 0);
            Spec.Ensures((List<int> r) => Length(r) == n);
            List<int> xs = new List<int>.Nil();
            Spec.Assert(Length(xs) == 0);
            for (int i = 0; i < n; i++)
            {
                Spec.Invariant(0 <= i && i <= n && xs != null && Length(xs) == i); // a reassigned local is only what the invariant says
                var next = new List<int>.Cons(i, xs);
                Spec.Assert(Length(next) == Length(next.Tail) + 1);
                xs = next;
            }
            return xs;
        }

        /// <summary>Reversing what Countdown built keeps its length: the generic lemma used at List&lt;int&gt;.</summary>
        public static int ReversedCount(int n)
        {
            Spec.Requires(n >= 0);
            Spec.Ensures((int r) => r == n);
            var xs = Countdown(n);
            ReverseLength(xs);
            return Length(Reverse(xs));
        }

        // ---------------------------------------------------------------- expressions

        [Pure]
        public static int Eval(Exp e)
        {
            Spec.Decreases(e);
            return e switch
            {
                Exp.Num n => n.Value,
                Exp.Add a => Eval(a.Left) + Eval(a.Right),
                Exp.Mul m => Eval(m.Left) * Eval(m.Right),
            };
        }

        /// <summary>One step of constant folding: 0 + e = e, 0 * e = 0, 1 * e = e.</summary>
        [Pure]
        public static Exp Fold(Exp e) => e switch
        {
            Exp.Add(Exp.Num(0), var r) => r,
            Exp.Mul(Exp.Num(0), _) => new Exp.Num(0),
            Exp.Mul(Exp.Num(1), var r) => r,
            _ => e,
        };

        [Lemma, Conditional(Spec.Symbol)]
        public static void FoldPreservesEval(Exp e)
        {
            Spec.Ensures(Eval(Fold(e)) == Eval(e));
            if (e is Exp.Add a && a.Left is Exp.Num) Spec.Assert(Eval(a.Left) == ((Exp.Num)a.Left).Value);
            if (e is Exp.Mul m && m.Left is Exp.Num) Spec.Assert(Eval(m.Left) == ((Exp.Num)m.Left).Value);
        }

        // ---------------------------------------------------------------- a dataprop

        /// <summary>FACT is a function: two proofs about the same n agree on r (ATS's <c>fact_isfun</c>).</summary>
        [Lemma, Conditional(Spec.Symbol)]
        internal static void FactIsFunctional(Fact p, Fact q)
        {
            Spec.Requires(p.N == q.N);
            Spec.Decreases(p);
            Spec.Ensures(p.R == q.R);
            if (p is Fact.Ind pi && q is Fact.Ind qi) FactIsFunctional(pi.Prev, qi.Prev);
        }

        /// <summary>n! by a loop, returning the FACT(n, r) proof that justifies r (INT2PROGINATS's <c>fact</c> with a proof).</summary>
        internal static int Factorial(int n, out Ghost<Fact> proof)
        {
            Spec.Requires(n >= 0);
            Spec.Ensures(proof.Value.N == n && proof.Value.R == Spec.Result<int>());
            int r = 1;
            var pf = Ghost.Of<Fact>(new Fact.Bas());
            for (int i = 0; i < n; i++)
            {
                Spec.Invariant(0 <= i && i <= n && pf.Value != null && pf.Value.N == i && pf.Value.R == r);
                pf = Ghost.Of<Fact>(new Fact.Ind(pf.Value));
                r = (i + 1) * r;
            }
            proof = pf;
            return r;
        }

        // ---------------------------------------------------------------- an invariant

        public static Interval Widen(Interval v, int by)
        {
            Spec.Requires(by >= 0);
            Spec.Ensures((Interval r) => r.Width() == v.Width() + 2 * by);
            return new Interval(v.Lo - by, v.Hi + by);
        }

        public static int Demo()
        {
            int known = ReversedCount(3) + Widen(new Interval(0, 2), 1).Width();
            Spec.Assert(known == 3 + 4);
            var e = new Exp.Mul(new Exp.Num(1), new Exp.Add(new Exp.Num(3), new Exp.Num(4)));
            FoldPreservesEval(e);
            return known + Eval(Fold(e)) + Factorial(3, out _);
        }
    }
}
