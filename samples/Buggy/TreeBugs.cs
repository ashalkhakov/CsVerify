using System;
using CsVerify;

namespace Samples.Buggy
{
    // The tree types and smart constructors of samples/Good/Trees.cs (this project does not reference that one).
    public abstract record Avl
    {
        private Avl() { }
        public sealed record E() : Avl;
        public sealed record N(int H, Avl L, int K, Avl R) : Avl
        {
            [Invariant, Pure] public bool Balanced() =>
                H == 1 + System.Math.Max(AvlTree.Ht(L), AvlTree.Ht(R)) && System.Math.Abs(AvlTree.Ht(L) - AvlTree.Ht(R)) <= 1;
        }
    }

    public static class AvlTree
    {
        [Pure] public static int Ht(Avl t) => t switch { Avl.N n => n.H, _ => 0 };

        public static Avl Node(Avl l, int k, Avl r)
        {
            Spec.Requires(System.Math.Abs(Ht(l) - Ht(r)) <= 1);
            Spec.Ensures((Avl t) => Ht(t) == 1 + System.Math.Max(Ht(l), Ht(r)));
            return new Avl.N(1 + System.Math.Max(Ht(l), Ht(r)), l, k, r);
        }
    }

    public abstract record Rb
    {
        private Rb() { }
        public sealed record E() : Rb;
        public sealed record T(bool Red, Rb L, int K, Rb R) : Rb
        {
            [Invariant, Pure] public bool Valid() =>
                RbTree.Bh(L) == RbTree.Bh(R) && (!Red || !RbTree.IsRed(L) && !RbTree.IsRed(R));
        }
    }

    public abstract record Ins
    {
        private Ins() { }
        public sealed record Fine(Rb Tree) : Ins;
        public sealed record Viol(Rb L, int K, Rb R) : Ins
        {
            [Invariant, Pure] public bool SameHeight() => RbTree.Bh(L) == RbTree.Bh(R);
        }
    }

    public static class RbTree
    {
        [Pure] public static int Bh(Rb t)
        {
            Spec.Decreases(t);
            return t switch { Rb.T n => n.Red ? Bh(n.L) : Bh(n.L) + 1, _ => 0 };
        }
        [Pure] public static bool IsRed(Rb t) => t is Rb.T n && n.Red;
        [Pure] public static int BhI(Ins i) => i switch { Ins.Fine f => Bh(f.Tree), Ins.Viol v => Bh(v.L), _ => 0 };

        public static Rb Black(Rb l, int k, Rb r)
        {
            Spec.Requires(Bh(l) == Bh(r));
            Spec.Ensures((Rb t) => Bh(t) == Bh(l) + 1 && !IsRed(t));
            return new Rb.T(false, l, k, r);
        }

        public static Rb Red(Rb l, int k, Rb r)
        {
            Spec.Requires(Bh(l) == Bh(r) && !IsRed(l) && !IsRed(r));
            Spec.Ensures((Rb t) => Bh(t) == Bh(l) && IsRed(t));
            return new Rb.T(true, l, k, r);
        }
    }

    public static class TreeBugs
    {
        // BUG: an AVL insert that never rebalances: a node two levels out of balance (CSV1001, Node's precondition)
        public static Avl InsertNoRotation(Avl t, int k)
        {
            Spec.Decreases(t);
            Spec.Ensures((Avl r) => AvlTree.Ht(r) == AvlTree.Ht(t) || AvlTree.Ht(r) == AvlTree.Ht(t) + 1);
            if (t is not Avl.N n) return AvlTree.Node(t, k, t);
            if (k < n.K) return AvlTree.Node(InsertNoRotation(n.L, k), n.K, n.R);
            if (k > n.K) return AvlTree.Node(n.L, n.K, InsertNoRotation(n.R, k));
            return t;
        }

        // BUG: a single rotation where the double one is needed: the node built is unbalanced (CSV1015)
        public static Avl RotRSingleOnly(Avl l, int k, Avl r)
        {
            Spec.Requires(AvlTree.Ht(l) == AvlTree.Ht(r) + 2);
            if (l is not Avl.N n) return l;
            var right = AvlTree.Node(n.R, k, r);
            return new Avl.N(1 + System.Math.Max(AvlTree.Ht(n.L), AvlTree.Ht(right)), n.L, n.K, right);
        }

        // BUG: recolors the new subtree's root red over a red child (CSV1001, Red's precondition)
        public static Rb BalanceLRecolorWrong(Ins l, int z, Rb d)
        {
            Spec.Requires(RbTree.BhI(l) == RbTree.Bh(d));
            switch (l)
            {
                case Ins.Viol(Rb.T { Red: true } a, var y, var c):
                    Spec.Assert(RbTree.Bh(a) == RbTree.Bh(a.L));
                    return RbTree.Red(a, y, RbTree.Black(c, z, d));
                default:
                    return d;
            }
        }
    }
}
