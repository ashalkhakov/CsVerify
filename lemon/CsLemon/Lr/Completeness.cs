// The completeness validator (lemon/Lr/DESIGN.md, after Jourdan, Pottier and Leroy, ESOP 2012, section 3.3): if it
// accepts an automaton with its items, the interpreter accepts every sentence, with the very parse tree given.
using System.Diagnostics;
using CsVerify;

namespace CsLemon.Lr
{
    /// <summary>
    /// What the completeness validator is given: each state's LR(1) items, as rule, dot and lookahead set (Rule[σ][k],
    /// Dot[σ][k], La[σ][k], a set of terminals), and each nonterminal's first set and nullability (indexed by symbol
    /// minus NTerm).
    /// </summary>
    public sealed class Items
    {
        public readonly int[][] Rule, Dot;
        public readonly bool[][][] La;
        public readonly bool[][] First;
        public readonly bool[] Nullable;

        public Items(int[][] rule, int[][] dot, bool[][][] la, bool[][] first, bool[] nullable)
        {
            Rule = rule; Dot = dot; La = la; First = first; Nullable = nullable;
        }
    }

    public static class Completeness
    {
        // ------------------------------------------------------------------------------------------ items

        /// <summary>The items' tables have their sizes (per state, per item; first sets per nonterminal, of NTerm terminals).</summary>
        [GhostFunction]
        public static bool ItemShape(Grammar g, Automaton a, Items it) =>
            it.Rule.Length == a.NState && it.Dot.Length == a.NState && it.La.Length == a.NState &&
            0 < g.NTerm && g.NTerm <= g.NSym && it.First.Length == g.NSym - g.NTerm && it.Nullable.Length == g.NSym - g.NTerm &&
            Spec.Forall(0, a.NState, σ => it.Rule[σ] != null && it.Dot[σ] != null && it.La[σ] != null &&
                                          it.Dot[σ].Length == it.Rule[σ].Length && it.La[σ].Length == it.Rule[σ].Length) &&
            Spec.Forall(0, g.NSym - g.NTerm, x => it.First[x] != null && it.First[x].Length == g.NTerm);

        /// <summary>The first item of σ from the k-th on that is (r, d); -1 if none.</summary>
        [Pure]
        public static int FindItem(Grammar g, Automaton a, Items it, int σ, int r, int d, int k)
        {
            Spec.Requires(ItemShape(g, a, it) && 0 <= σ && σ < a.NState && 0 <= k);
            Spec.Decreases(it.Rule[σ].Length - k);
            Spec.Ensures((int j) => -1 <= j && j < it.Rule[σ].Length && (j < 0 || it.Rule[σ][j] == r && it.Dot[σ][j] == d));
            if (k >= it.Rule[σ].Length) return -1;
            if (it.Rule[σ][k] == r && it.Dot[σ][k] == d) return k;
            return FindItem(g, a, it, σ, r, d, k + 1);
        }

        /// <summary>σ has the item (r, d) with c among its lookaheads.</summary>
        [GhostFunction]
        public static bool Has(Grammar g, Automaton a, Items it, int σ, int r, int d, int c)
        {
            Spec.Requires(ItemShape(g, a, it) && 0 <= σ && σ < a.NState);
            return FindItem(g, a, it, σ, r, d, 0) >= 0 && it.La[σ][FindItem(g, a, it, σ, r, d, 0)] != null &&
                   Safety.In(it.La[σ][FindItem(g, a, it, σ, r, d, 0)], c);
        }

        // ------------------------------------------------------------------------------------------ first sets

        /// <summary>c can begin what symbol x derives: x is c (or a multiterminal of it), or a nonterminal with c in its first set.</summary>
        [GhostFunction]
        public static bool FirstOf(Grammar g, Items it, int x, int c)
        {
            Spec.Requires(it.First.Length == g.NSym - g.NTerm && 0 <= g.NTerm);
            return g.NTerm <= x && x < g.NSym ? it.First[x - g.NTerm] != null && Safety.In(it.First[x - g.NTerm], c) : Interpreter.Matches(g, x, c);
        }

        /// <summary>x derives the empty word, by the given nullability.</summary>
        [GhostFunction]
        public static bool NullableOf(Grammar g, Items it, int x)
        {
            Spec.Requires(it.Nullable.Length == g.NSym - g.NTerm && 0 <= g.NTerm);
            return g.NTerm <= x && x < g.NSym && it.Nullable[x - g.NTerm];
        }

        /// <summary>c can begin what rhs[i..] derives (not empty).</summary>
        [GhostFunction]
        public static bool FirstSeq(Grammar g, Items it, int[] rhs, int i, int c)
        {
            Spec.Requires(it.First.Length == g.NSym - g.NTerm && it.Nullable.Length == g.NSym - g.NTerm && 0 <= g.NTerm && 0 <= i);
            Spec.Decreases(rhs.Length - i);
            return i < rhs.Length && (FirstOf(g, it, rhs[i], c) || NullableOf(g, it, rhs[i]) && FirstSeq(g, it, rhs, i + 1, c));
        }

        /// <summary>rhs[i..] derives the empty word.</summary>
        [GhostFunction]
        public static bool AllNullable(Grammar g, Items it, int[] rhs, int i)
        {
            Spec.Requires(it.Nullable.Length == g.NSym - g.NTerm && 0 <= g.NTerm && 0 <= i);
            Spec.Decreases(rhs.Length - i);
            return i >= rhs.Length || NullableOf(g, it, rhs[i]) && AllNullable(g, it, rhs, i + 1);
        }

        /// <summary>The first sets and nullability are closed under the rules (a fixed point would be the least such).</summary>
        [GhostFunction]
        public static bool FirstOk(Grammar g, Automaton a, Items it)
        {
            Spec.Requires(ItemShape(g, a, it));
            return Spec.Forall(0, g.Lhs.Length, r => RuleFirstOk(g, a, it, r));
        }

        [GhostFunction]
        public static bool RuleFirstOk(Grammar g, Automaton a, Items it, int r)
        {
            Spec.Requires(ItemShape(g, a, it) && 0 <= r && r < g.Lhs.Length);
            return r < g.Rhs.Length && g.Rhs[r] != null && g.NTerm <= g.Lhs[r] && g.Lhs[r] < g.NSym &&
                   Spec.Forall(0, g.NTerm, c => !FirstSeq(g, it, g.Rhs[r], 0, c) || it.First[g.Lhs[r] - g.NTerm][c]) &&
                   (!AllNullable(g, it, g.Rhs[r], 0) || it.Nullable[g.Lhs[r] - g.NTerm]);
        }

        /// <summary>What can begin a sequence is a terminal.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void FirstSeqRange(Grammar g, Automaton a, Items it, int[] rhs, int i, int c)
        {
            Spec.Requires(ItemShape(g, a, it) && 0 <= i && FirstSeq(g, it, rhs, i, c));
            Spec.Decreases(rhs.Length - i);
            Spec.Ensures(0 <= c && c < g.NTerm);
            int x = rhs[i];
            Spec.Assert(FirstOf(g, it, x, c) || NullableOf(g, it, x) && FirstSeq(g, it, rhs, i + 1, c));
            if (FirstOf(g, it, x, c))
            {
                if (g.NTerm <= x && x < g.NSym)
                {
                    Spec.Assert(Safety.In(it.First[x - g.NTerm]!, c));
                    Spec.Assert(c < it.First[x - g.NTerm]!.Length);
                    Spec.Assert(it.First[x - g.NTerm]!.Length == g.NTerm);
                }
                else Spec.Assert(Interpreter.Matches(g, x, c));
            }
            else FirstSeqRange(g, a, it, rhs, i + 1, c);
        }

        // ------------------------------------------------------------------------------------------ trees, input

        [GhostFunction]
        public static int Len(Word v)
        {
            Spec.Decreases(v);
            Spec.Ensures((int n) => 0 <= n);
            return v is Word.Cons c ? 1 + Len(c.Tail) : 0;
        }

        /// <summary>The input at pos begins with v.</summary>
        [GhostFunction]
        public static bool WordAt(int[] w, int pos, Word v)
        {
            Spec.Decreases(v);
            return v is Word.Cons c ? 0 <= pos && pos < w.Length && w[pos] == c.Head && WordAt(w, pos + 1, c.Tail) : 0 <= pos && pos <= w.Length;
        }

        /// <summary>The lookahead at p: the terminal there, or 0 (the end of input) past the input.</summary>
        [GhostFunction]
        public static int La(int[] w, int p) => 0 <= p && p < w.Length ? w[p] : 0;

        [Lemma, Conditional(Spec.Symbol)]
        public static void WordAtAppend(int[] w, int pos, Word x, Word y)
        {
            Spec.Requires(WordAt(w, pos, Interpreter.Append(x, y)));
            Spec.Decreases(x);
            Spec.Ensures(WordAt(w, pos, x) && WordAt(w, pos + Len(x), y) && Len(Interpreter.Append(x, y)) == Len(x) + Len(y));
            if (x is Word.Cons c) WordAtAppend(w, pos + 1, c.Tail, y);
        }

        /// <summary>A parse tree's first terminal can begin its symbol; a tree with no leaves is of a nullable symbol.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void FirstSound(Grammar g, Automaton a, Items it, Tree t, int x)
        {
            Spec.Requires(ItemShape(g, a, it) && FirstOk(g, a, it) && Interpreter.Valid(g, t, x));
            Spec.Decreases(t);
            Spec.Ensures(Interpreter.Fringe(t) is Word.Cons c ? FirstOf(g, it, x, c.Head) : NullableOf(g, it, x));
            if (t is Tree.Node n)
            {
                Spec.Assert(RuleFirstOk(g, a, it, n.Rule));
                KidsFirst(g, a, it, n.Kids, g.Rhs[n.Rule]!, 0);
                Spec.Assert(Interpreter.Fringe(t) == Interpreter.Fringes(n.Kids));
                Spec.Assert(x == g.Lhs[n.Rule] && g.NTerm <= x && x < g.NSym);
                if (Interpreter.Fringes(n.Kids) is Word.Cons head)
                {
                    FirstSeqRange(g, a, it, g.Rhs[n.Rule]!, 0, head.Head);
                    Spec.Assert(it.First[x - g.NTerm]![head.Head]);
                    Spec.Assert(it.First[x - g.NTerm]!.Length == g.NTerm);
                    Spec.Assert(it.First[x - g.NTerm] != null && Safety.In(it.First[x - g.NTerm]!, head.Head));
                    Spec.Assert(FirstOf(g, it, x, head.Head));
                }
                else Spec.Assert(it.Nullable[x - g.NTerm]);
            }
            else if (t is Tree.Leaf l)
            {
                Spec.Assert(Interpreter.Fringe(t) == new Word.Cons(l.Term, new Word.Nil()));
                Spec.Assert(Interpreter.Matches(g, x, l.Term));
                Spec.Assert(!(g.NTerm <= x && x < g.NSym));
            }
        }

        /// <summary>The same for the children of a node, of rhs[i..].</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void KidsFirst(Grammar g, Automaton a, Items it, Forest ts, int[] rhs, int i)
        {
            Spec.Requires(ItemShape(g, a, it) && FirstOk(g, a, it) && 0 <= i && Interpreter.Kids(g, ts, rhs, i));
            Spec.Decreases(ts);
            Spec.Ensures(Interpreter.Fringes(ts) is Word.Cons c ? FirstSeq(g, it, rhs, i, c.Head) : AllNullable(g, it, rhs, i));
            if (ts is Forest.Cons k)
            {
                FirstSound(g, a, it, k.Head, rhs[i]);
                KidsFirst(g, a, it, k.Tail, rhs, i + 1);
                Spec.Assert(Interpreter.Fringes(ts) == Interpreter.Append(Interpreter.Fringe(k.Head), Interpreter.Fringes(k.Tail)));
            }
        }
    }
}
