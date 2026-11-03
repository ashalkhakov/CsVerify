using System;
using System.Diagnostics;
using CsVerify;

namespace Samples
{
    // Balanced search trees after ATS's verified AVL and red-black trees (rewritten in C#, not copied). In ATS the
    // tree type is indexed (avltree(h); rbtree(color, bh, violation)) so an unbalanced tree does not type-check.
    // Here the same facts are object invariants of immutable data records: every node is proved balanced where it
    // is built, so no unbalanced value can exist. The red-black insertion's intermediate "infrared" tree (a red
    // node that may have a red child: ATS's violation index) is a type of its own, Ins.
    /// <summary>An AVL tree: each node stores its height, and its subtrees differ in height by at most one.</summary>
    public abstract record Avl
    {
        private Avl() { }
        public sealed record E() : Avl;
        public sealed record N(int H, Avl L, int K, Avl R) : Avl
        {
            [Invariant, GhostFunction] public bool Balanced() =>
                H == 1 + Math.Max(AvlTree.Ht(L), AvlTree.Ht(R)) && Math.Abs(AvlTree.Ht(L) - AvlTree.Ht(R)) <= 1;
        }
    }
    public static class AvlTree
    {
        [Pure] public static int Ht(Avl t) => t switch { Avl.N n => n.H, _ => 0 };

        public static Avl Node(Avl l, int k, Avl r)
        {
            Spec.Requires(Math.Abs(Ht(l) - Ht(r)) <= 1);
            Spec.Ensures((Avl t) => Ht(t) == 1 + Math.Max(Ht(l), Ht(r)));
            return new Avl.N(checked(1 + Math.Max(Ht(l), Ht(r))), l, k, r);
        }

        public static Avl RotR(Avl l, int k, Avl r)
        {
            Spec.Requires(Ht(l) == Ht(r) + 2);
            Spec.Ensures((Avl t) => Ht(t) == Ht(r) + 2 || Ht(t) == Ht(r) + 3);
            if (l is not Avl.N n) return l;
            if (Ht(n.L) >= Ht(n.R)) return Node(n.L, n.K, Node(n.R, k, r));
            if (n.R is not Avl.N m) return l;
            return Node(Node(n.L, n.K, m.L), m.K, Node(m.R, k, r));
        }

        public static Avl RotL(Avl l, int k, Avl r)
        {
            Spec.Requires(Ht(r) == Ht(l) + 2);
            Spec.Ensures((Avl t) => Ht(t) == Ht(l) + 2 || Ht(t) == Ht(l) + 3);
            if (r is not Avl.N n) return r;
            if (Ht(n.R) >= Ht(n.L)) return Node(Node(l, k, n.L), n.K, n.R);
            if (n.L is not Avl.N m) return r;
            return Node(Node(l, k, m.L), m.K, Node(m.R, n.K, n.R));
        }

        public static Avl Insert(Avl t, int k)
        {
            Spec.Decreases(t);
            Spec.Ensures((Avl r) => Ht(r) == Ht(t) || Ht(r) == Ht(t) + 1);
            if (t is not Avl.N n) return Node(t, k, t);
            if (k < n.K)
            {
                var l = Insert(n.L, k);
                return Ht(l) - Ht(n.R) == 2 ? RotR(l, n.K, n.R) : Node(l, n.K, n.R);
            }
            if (k > n.K)
            {
                var r = Insert(n.R, k);
                return Ht(r) - Ht(n.L) == 2 ? RotL(n.L, n.K, r) : Node(n.L, n.K, r);
            }
            return t;
        }
    }

    /// <summary>A red-black tree: equal black height on both sides of every node, and no red node with a red child.</summary>
    public abstract record Rb
    {
        private Rb() { }
        public sealed record E() : Rb;
        public sealed record T(bool Red, Rb L, int K, Rb R) : Rb
        {
            [Invariant, GhostFunction] public bool Valid() =>
                RbTree.Bh(L) == RbTree.Bh(R) && (!Red || !RbTree.IsRed(L) && !RbTree.IsRed(R));
        }
    }
    /// <summary>What insertion returns: a valid tree, or a red node whose child may be red (to be fixed by the parent).</summary>
    public abstract record Ins
    {
        private Ins() { }
        public sealed record Fine(Rb Tree) : Ins;
        public sealed record Viol(Rb L, int K, Rb R) : Ins
        {
            [Invariant, GhostFunction] public bool SameHeight() => RbTree.Bh(L) == RbTree.Bh(R);
        }
    }
    public static class RbTree
    {
        [GhostFunction] public static int Bh(Rb t)
        {
            Spec.Decreases(t);
            return t switch { Rb.T n => n.Red ? Bh(n.L) : Bh(n.L) + 1, _ => 0 };
        }
        /// <summary>The black height at run time, along the leftmost path, proved equal to Bh.</summary>
        public static int BlackHeight(Rb t)
        {
            Spec.Decreases(t);
            Spec.Ensures((int r) => r == Bh(t));
            if (t is not Rb.T n) return 0;
            int below = BlackHeight(n.L);
            return n.Red ? below : checked(below + 1);
        }

        [Pure] public static bool IsRed(Rb t) => t is Rb.T n && n.Red;
        [GhostFunction] public static int BhI(Ins i) => i switch { Ins.Fine f => Bh(f.Tree), Ins.Viol v => Bh(v.L), _ => 0 };

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

        /// <summary>A black node over a possibly infrared left child: Okasaki's balance, left cases.</summary>
        public static Rb BalanceL(Ins l, int z, Rb d)
        {
            Spec.Requires(BhI(l) == Bh(d));
            Spec.Ensures((Rb t) => Bh(t) == Bh(d) + 1);
            switch (l)
            {
                case Ins.Viol(Rb.T { Red: true } a, var y, var c):
                    Spec.Assert(Bh(a) == Bh(a.L)); // a red node is as black-high as its children
                    return Red(Black(a.L, a.K, a.R), y, Black(c, z, d));
                case Ins.Viol(var a, var x, Rb.T { Red: true } b):
                    Spec.Assert(Bh(b) == Bh(b.L));
                    return Red(Black(a, x, b.L), b.K, Black(b.R, z, d));
                case Ins.Viol v:
                    return Black(Red(v.L, v.K, v.R), z, d);
                case Ins.Fine f:
                    return Black(f.Tree, z, d);
                default:
                    Spec.Assert(false); // Fine and Viol are the only cases
                    return d;
            }
        }

        public static Rb BalanceR(Rb a, int x, Ins r)
        {
            Spec.Requires(BhI(r) == Bh(a));
            Spec.Ensures((Rb t) => Bh(t) == Bh(a) + 1);
            switch (r)
            {
                case Ins.Viol(Rb.T { Red: true } b, var z, var d):
                    Spec.Assert(Bh(b) == Bh(b.L));
                    return Red(Black(a, x, b.L), b.K, Black(b.R, z, d));
                case Ins.Viol(var b, var y, Rb.T { Red: true } c):
                    Spec.Assert(Bh(c) == Bh(c.L));
                    return Red(Black(a, x, b), y, Black(c.L, c.K, c.R));
                case Ins.Viol v:
                    return Black(a, x, Red(v.L, v.K, v.R));
                case Ins.Fine f:
                    return Black(a, x, f.Tree);
                default:
                    Spec.Assert(false);
                    return a;
            }
        }

        /// <summary>Okasaki's ins: below a black node the result is a valid tree; below a red one, at worst infrared.</summary>
        public static Ins Ins(Rb t, int k)
        {
            Spec.Decreases(t);
            Spec.Ensures((Ins i) => BhI(i) == Bh(t) && (IsRed(t) || i is Ins.Fine));
            if (t is not Rb.T n) return new Ins.Fine(Red(t, k, t));
            Spec.Assert(Bh(t) == (n.Red ? Bh(n.L) : Bh(n.L) + 1));
            if (k < n.K)
            {
                var l = Ins(n.L, k);
                if (!n.Red) return new Ins.Fine(BalanceL(l, n.K, n.R));
                if (l is Ins.Fine f) return new Ins.Viol(f.Tree, n.K, n.R);
                Spec.Assert(false); // a red node's children are black, so below it ins never leaves a violation
                return new Ins.Fine(t);
            }
            if (k > n.K)
            {
                var r = Ins(n.R, k);
                if (!n.Red) return new Ins.Fine(BalanceR(n.L, n.K, r));
                if (r is Ins.Fine f) return new Ins.Viol(n.L, n.K, f.Tree);
                Spec.Assert(false);
                return new Ins.Fine(t);
            }
            return new Ins.Fine(t);
        }

        /// <summary>Insertion: the root is blackened, so the black height grows by at most one.</summary>
        public static Rb Insert(Rb t, int k)
        {
            Spec.Ensures((Rb r) => Bh(r) == Bh(t) || Bh(r) == Bh(t) + 1);
            var i = Ins(t, k);
            switch (i)
            {
                case Ins.Viol v: return Black(v.L, v.K, v.R);
                case Ins.Fine { Tree: Rb.T n }:
                    Spec.Assert(Bh(n) == (n.Red ? Bh(n.L) : Bh(n.L) + 1));
                    return Black(n.L, n.K, n.R);
                case Ins.Fine f: return f.Tree;
                default: Spec.Assert(false); return t;
            }
        }
    }

    public static class Trees
    {
        /// <summary>Inserts 1..7 into both trees: the run-time result of the verified code.</summary>
        public static int Demo()
        {
            Avl a = new Avl.E();
            Rb r = new Rb.E();
            for (int i = 1; i <= 7; i++)
            {
                Spec.Invariant(a != null && r != null);
                a = AvlTree.Insert(a, i);
                r = RbTree.Insert(r, i);
            }
            return checked(10 * AvlTree.Ht(a) + RbTree.BlackHeight(r));
        }
    }
}
