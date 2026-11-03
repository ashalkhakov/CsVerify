using System.Diagnostics;
using CsVerify;

namespace Samples.Buggy
{
    public abstract record Tree
    {
        private Tree() { }
        public sealed record Leaf() : Tree;
        public sealed record Node(Tree Left, int Key, Tree Right) : Tree;
    }

    public abstract record Exp
    {
        private Exp() { }
        public sealed record Num(int Value) : Exp;
        public sealed record Mul(Exp Left, Exp Right) : Exp;
    }

    internal abstract record Fact(int N, int R)
    {
        [Invariant, Pure] public bool Natural() => N >= 0;
        public sealed record Bas() : Fact(0, 1);
        public sealed record Ind(Fact Prev) : Fact(Prev.N + 1, (Prev.N + 1) * Prev.R);
    }

    public sealed record Interval(int Lo, int Hi)
    {
        [Invariant, Pure] public bool Valid() => Lo <= Hi;
    }

    public sealed class Gauge { public int Level; }

    // BUG: the invariant reads a mutable gauge, which anyone holding it can change after the reading is built (CSV1015)
    public sealed record Reading(Gauge G)
    {
        [Invariant, Pure] public bool Positive() => G.Level > 0;
    }

    public static class DataBugs
    {
        // BUG: forgets the Leaf case, so the definition throws on it (CSV1011)
        [Pure]
        public static int Key(Tree t) => t switch { Tree.Node n => n.Key };

        // BUG: recurses on the same tree, not a subtree (CSV1008)
        [Pure]
        public static int Size(Tree t)
        {
            Spec.Decreases(t);
            return t is Tree.Node n ? 1 + Size(n.Left) + Size(t) : 0;
        }

        [Pure]
        public static int Eval(Exp e)
        {
            Spec.Decreases(e);
            return e switch { Exp.Num n => n.Value, Exp.Mul m => Eval(m.Left) * Eval(m.Right) };
        }

        // BUG: 1 * e folds to 1 instead of e
        [Pure]
        public static Exp Fold(Exp e) => e switch { Exp.Mul(Exp.Num(1), var r) => new Exp.Num(1), _ => e };

        // so constant folding no longer preserves the meaning (CSV1002)
        [Lemma, Conditional(Spec.Symbol)]
        public static void FoldPreservesEval(Exp e)
        {
            Spec.Ensures(Eval(Fold(e)) == Eval(e));
            if (e is Exp.Mul m && m.Left is Exp.Num) Spec.Assert(Eval(m.Left) == ((Exp.Num)m.Left).Value);
        }

        // BUG: the proof step is FACTind but the computation multiplies by i, not i + 1 (CSV1006)
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
                r = i * r;
            }
            proof = pf;
            return r;
        }

        // BUG: an empty interval the wrong way round (CSV1015)
        public static Interval Backwards(int x) => new Interval(x + 1, x);

        // BUG: two equal values are still two objects; reference identity is not what record == means (CSV1004)
        public static void SameObject()
        {
            object a = new Tree.Leaf();
            object b = new Tree.Leaf();
            Spec.Assert(a == b);
        }
    }
}
