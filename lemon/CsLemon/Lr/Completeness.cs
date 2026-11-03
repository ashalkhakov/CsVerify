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

        // ------------------------------------------------------------------------------------------ the conditions

        /// <summary>The automaton's tables and the items have their sizes.</summary>
        [GhostFunction]
        public static bool Wf(Grammar g, Automaton a, Items it) =>
            ItemShape(g, a, it) && a.NState == a.Incoming.Length && a.Kind.Length == a.NState && a.Arg.Length == a.NState &&
            a.Goto.Length == a.NState && 0 < a.NState && g.Lhs.Length == g.Rhs.Length &&
            Spec.Forall(0, a.NState, σ => a.Kind[σ] != null && a.Arg[σ] != null && a.Goto[σ] != null &&
                                          a.Kind[σ].Length == g.NTerm && a.Arg[σ].Length == g.NTerm && a.Goto[σ].Length == g.NSym - g.NTerm);

        /// <summary>State σ2 has the item (r, d) with every lookahead in L.</summary>
        [GhostFunction]
        public static bool HasAll(Grammar g, Automaton a, Items it, int σ2, int r, int d, bool[] L)
        {
            Spec.Requires(Wf(g, a, it) && 0 <= σ2 && σ2 < a.NState);
            return FindItem(g, a, it, σ2, r, d, 0) >= 0 && it.La[σ2][FindItem(g, a, it, σ2, r, d, 0)] != null &&
                   Safety.Sub(L, it.La[σ2][FindItem(g, a, it, σ2, r, d, 0)]);
        }

        /// <summary>c can begin rhs[i..] followed by one of L.</summary>
        [GhostFunction]
        public static bool FirstSeqIn(Grammar g, Items it, int[] rhs, int i, bool[] L, int c)
        {
            Spec.Requires(it.First.Length == g.NSym - g.NTerm && it.Nullable.Length == g.NSym - g.NTerm && 0 <= g.NTerm && 0 <= i);
            return FirstSeq(g, it, rhs, i, c) || AllNullable(g, it, rhs, i) && Safety.In(L, c);
        }

        /// <summary>
        /// The k-th item of σ, (r, d, L): if d is past its first symbol, σ was entered on the symbol before the dot; at
        /// the end, σ reduces r on L; before a nonterminal, σ has a goto on it to a state with (r, d+1, L), and every
        /// rule of the nonterminal at dot 0, with what can begin the rest; before a terminal (or multiterminal), σ
        /// shifts each of its terminals to a state with (r, d+1, L).
        /// </summary>
        [GhostFunction]
        public static bool ItemOk(Grammar g, Automaton a, Items it, int σ, int k)
        {
            Spec.Requires(Wf(g, a, it) && ItemShape(g, a, it) && 0 <= σ && σ < a.NState && 0 <= k && k < it.Rule[σ].Length);
            return 0 <= it.Rule[σ][k] && it.Rule[σ][k] < g.Lhs.Length && g.Rhs[it.Rule[σ][k]] != null &&
                   0 <= it.Dot[σ][k] && it.Dot[σ][k] <= g.Rhs[it.Rule[σ][k]].Length &&
                   it.La[σ][k] != null && it.La[σ][k].Length == g.NTerm &&
                   (it.Dot[σ][k] == 0 || a.Incoming[σ] == g.Rhs[it.Rule[σ][k]][it.Dot[σ][k] - 1]) &&
                   ItemActsOk(g, a, it, σ, it.Rule[σ][k], it.Dot[σ][k], it.La[σ][k]);
        }

        [GhostFunction]
        public static bool ItemActsOk(Grammar g, Automaton a, Items it, int σ, int r, int d, bool[] L)
        {
            Spec.Requires(Wf(g, a, it) && 0 <= σ && σ < a.NState && 0 <= r && r < g.Lhs.Length && g.Rhs[r] != null &&
                          0 <= d && d <= g.Rhs[r].Length);
            return d == g.Rhs[r].Length
                ? Spec.Forall(0, g.NTerm, c => !Safety.In(L, c) || a.Kind[σ][c] == Automaton.Reduce && a.Arg[σ][c] == r)
                : g.NTerm <= g.Rhs[r][d] && g.Rhs[r][d] < g.NSym
                    ? 0 <= a.Goto[σ][g.Rhs[r][d] - g.NTerm] && a.Goto[σ][g.Rhs[r][d] - g.NTerm] < a.NState &&
                      HasAll(g, a, it, a.Goto[σ][g.Rhs[r][d] - g.NTerm], r, d + 1, L) &&
                      Spec.Forall(0, g.Lhs.Length, r2 => g.Lhs[r2] != g.Rhs[r][d] || ClosureOk(g, a, it, σ, r, d, L, r2))
                    : Spec.Forall(0, g.NTerm, c => !Interpreter.Matches(g, g.Rhs[r][d], c) ||
                                                   a.Kind[σ][c] == Automaton.Shift && 0 <= a.Arg[σ][c] && a.Arg[σ][c] < a.NState &&
                                                   HasAll(g, a, it, a.Arg[σ][c], r, d + 1, L));
        }

        /// <summary>Closure: σ has rule r2 at dot 0 with every terminal that can begin rhs[d+1..] L.</summary>
        [GhostFunction]
        public static bool ClosureOk(Grammar g, Automaton a, Items it, int σ, int r, int d, bool[] L, int r2)
        {
            Spec.Requires(Wf(g, a, it) && 0 <= σ && σ < a.NState && 0 <= r && r < g.Lhs.Length && g.Rhs[r] != null &&
                          0 <= d && d < g.Rhs[r].Length);
            return FindItem(g, a, it, σ, r2, 0, 0) >= 0 && it.La[σ][FindItem(g, a, it, σ, r2, 0, 0)] != null &&
                   Spec.Forall(0, g.NTerm, c => !FirstSeqIn(g, it, g.Rhs[r], d + 1, L, c) || Safety.In(it.La[σ][FindItem(g, a, it, σ, r2, 0, 0)], c));
        }

        /// <summary>
        /// The start: state 0 has every rule of the start symbol at dot 0 with the end of input as lookahead; its goto on
        /// the start symbol is a state entered on it that accepts at the end of input.
        /// </summary>
        [GhostFunction]
        public static bool RootOk(Grammar g, Automaton a, Items it)
        {
            Spec.Requires(Wf(g, a, it) && ItemShape(g, a, it));
            return g.NTerm <= g.Start && g.Start < g.NSym &&
                   0 < a.Goto[0][g.Start - g.NTerm] && a.Goto[0][g.Start - g.NTerm] < a.NState &&
                   a.Incoming[a.Goto[0][g.Start - g.NTerm]] == g.Start && a.Kind[a.Goto[0][g.Start - g.NTerm]][0] == Automaton.Accept &&
                   Spec.Forall(0, g.Lhs.Length, r => g.Lhs[r] != g.Start || Has(g, a, it, 0, r, 0, 0));
        }

        /// <summary>What the completeness validator checks.</summary>
        [GhostFunction]
        public static bool CompleteOk(Grammar g, Automaton a, Items it) =>
            Wf(g, a, it) && ItemShape(g, a, it) && FirstOk(g, a, it) && RootOk(g, a, it) &&
            Spec.Forall(0, a.NState, σ => Spec.Forall(0, it.Rule[σ].Length, k => ItemOk(g, a, it, σ, k)));

        // ------------------------------------------------------------------------------------------ steps

        /// <summary>The steps a tree takes: a shift per leaf, a reduce per node.</summary>
        [GhostFunction]
        public static int Size(Tree t)
        {
            Spec.Decreases(t);
            Spec.Ensures((int n) => n >= 1);
            return t is Tree.Node n ? 1 + SizeF(n.Kids) : 1;
        }

        [GhostFunction]
        public static int SizeF(Forest ts)
        {
            Spec.Decreases(ts);
            Spec.Ensures((int n) => n >= 0);
            return ts is Forest.Cons c ? Size(c.Head) + SizeF(c.Tail) : 0;
        }

        [Lemma, Conditional(Spec.Symbol)]
        public static void StepsStopped(Grammar g, Automaton a, int[] w, int m, Run r)
        {
            Spec.Requires(r is Run.Stopped);
            Spec.Ensures(Interpreter.Steps(g, a, w, m, r) == r);
        }

        /// <summary>n steps and then m are n + m steps.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void StepsAdd(Grammar g, Automaton a, int[] w, int n, int m, Run r)
        {
            Spec.Requires(0 <= n && 0 <= m);
            Spec.Decreases(n);
            Spec.Ensures(Interpreter.Steps(g, a, w, n + m, r) == Interpreter.Steps(g, a, w, m, Interpreter.Steps(g, a, w, n, r)));
            if (n == 0)
            {
                Spec.Assert(Interpreter.Steps(g, a, w, 0, r) == r);
            }
            else if (r is Run.Going go && 0 <= go.Pos && go.Pos <= w.Length)
            {
                var next = Interpreter.Step(g, a, w, go.S, go.Pos);
                Spec.Assert(Interpreter.Steps(g, a, w, n + m, r) == Interpreter.Steps(g, a, w, n + m - 1, next));
                Spec.Assert(Interpreter.Steps(g, a, w, n, r) == Interpreter.Steps(g, a, w, n - 1, next));
                StepsAdd(g, a, w, n - 1, m, next);
            }
            else if (r is Run.Going)
            {
                var err = new Run.Stopped(new Result.InternalError());
                Spec.Assert(Interpreter.Steps(g, a, w, n + m, r) == err && Interpreter.Steps(g, a, w, n, r) == err);
                StepsStopped(g, a, w, m, err);
            }
            else
            {
                Spec.Assert(Interpreter.Steps(g, a, w, n + m, r) == r && Interpreter.Steps(g, a, w, n, r) == r);
                StepsStopped(g, a, w, m, r);
            }
        }

        /// <summary>One step is Step.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void StepsOne(Grammar g, Automaton a, int[] w, Stack s, int pos)
        {
            Spec.Requires(0 <= pos && pos <= w.Length);
            Spec.Ensures(Interpreter.Steps(g, a, w, 1, new Run.Going(s, pos)) == Interpreter.Step(g, a, w, s, pos));
            Spec.Assert(Interpreter.Steps(g, a, w, 1, new Run.Going(s, pos)) == Interpreter.Steps(g, a, w, 0, Interpreter.Step(g, a, w, s, pos)));
        }

        /// <summary>The lookahead before some children is what can begin their symbols, followed by the lookahead after them.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void LaFirst(Grammar g, Automaton a, Items it, int[] w, Forest ts, int[] rhs, int i, int p, int b)
        {
            Spec.Requires(ItemShape(g, a, it) && FirstOk(g, a, it) && 0 <= i && Interpreter.Kids(g, ts, rhs, i) &&
                          WordAt(w, p, Interpreter.Fringes(ts)) && La(w, p + Len(Interpreter.Fringes(ts))) == b);
            Spec.Ensures(FirstSeq(g, it, rhs, i, La(w, p)) || AllNullable(g, it, rhs, i) && La(w, p) == b);
            KidsFirst(g, a, it, ts, rhs, i);
            if (Interpreter.Fringes(ts) is Word.Cons h)
                Spec.Assert(La(w, p) == h.Head);
            else
                Spec.Assert(Len(Interpreter.Fringes(ts)) == 0);
        }

        // ------------------------------------------------------------------------------------------ the walk

        [Lemma, Conditional(Spec.Symbol)]
        public static void SubIn(bool[] A, bool[] B, int x)
        {
            Spec.Requires(Safety.Sub(A, B) && Safety.In(A, x));
            Spec.Ensures(Safety.In(B, x));
            Spec.Assert(!A[x] || x < B.Length && B[x]);
        }

        /// <summary>A word at pos ends within the input.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void WordAtEnd(int[] w, int pos, Word v)
        {
            Spec.Requires(WordAt(w, pos, v));
            Spec.Decreases(v);
            Spec.Ensures(0 <= pos && pos + Len(v) <= w.Length);
            if (v is Word.Cons c) WordAtEnd(w, pos + 1, c.Tail);
        }

        /// <summary>From HasAll and one lookahead in L, the item with that lookahead.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void HasOne(Grammar g, Automaton a, Items it, int σ2, int r, int d, bool[] L, int b)
        {
            Spec.Requires(Wf(g, a, it) && ItemShape(g, a, it) && 0 <= σ2 && σ2 < a.NState && HasAll(g, a, it, σ2, r, d, L) && Safety.In(L, b));
            Spec.Ensures(Has(g, a, it, σ2, r, d, b));
            int j = FindItem(g, a, it, σ2, r, d, 0);
            SubIn(L, it.La[σ2]![j]!, b);
        }

        /// <summary>An item of a state, by its index: what ItemOk says of it.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void AtItem(Grammar g, Automaton a, Items it, int σ, int r, int d)
        {
            Spec.Requires(CompleteOk(g, a, it) && ItemShape(g, a, it) && 0 <= σ && σ < a.NState && FindItem(g, a, it, σ, r, d, 0) >= 0);
            Spec.Ensures(Wf(g, a, it) && ItemShape(g, a, it) && ItemOk(g, a, it, σ, FindItem(g, a, it, σ, r, d, 0)) &&
                         it.Rule[σ][FindItem(g, a, it, σ, r, d, 0)] == r && it.Dot[σ][FindItem(g, a, it, σ, r, d, 0)] == d);
            Spec.Assert(Spec.Forall(0, it.Rule[σ].Length, k => ItemOk(g, a, it, σ, k)));
        }

        /// <summary>
        /// The parser walks a parse tree: if t is a tree for the symbol after the dot of an item (r, d) of the top state
        /// with lookahead b, the input at pos begins with t's leaves, and the terminal after them can begin
        /// rhs[d+1..] b, then Size(t) steps push exactly t, in a state with the item (r, d+1) and lookahead b.
        /// </summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void Walk(Grammar g, Automaton a, Items it, int[] w, Tree t, Stack s, int pos, int r, int d, int b)
        {
            Spec.Requires(CompleteOk(g, a, it) && Wf(g, a, it) && ItemShape(g, a, it) && 0 <= r && r < g.Rhs.Length && g.Rhs[r] != null &&
                          0 <= d && d < g.Rhs[r].Length && Interpreter.Valid(g, t, g.Rhs[r][d]) &&
                          0 <= Interpreter.Top(s) && Interpreter.Top(s) < a.NState && Has(g, a, it, Interpreter.Top(s), r, d, b) &&
                          0 <= pos && WordAt(w, pos, Interpreter.Fringe(t)) &&
                          (FirstSeq(g, it, g.Rhs[r], d + 1, La(w, pos + Len(Interpreter.Fringe(t)))) ||
                           AllNullable(g, it, g.Rhs[r], d + 1) && La(w, pos + Len(Interpreter.Fringe(t))) == b));
            Spec.Decreases(t);
            Spec.Ensures(Interpreter.Steps(g, a, w, Size(t), new Run.Going(s, pos)) is Run.Going go &&
                         go.Pos == pos + Len(Interpreter.Fringe(t)) && go.S is Stack.Cell c && c.T == t && c.Below == s &&
                         0 <= c.State && c.State < a.NState && Has(g, a, it, c.State, r, d + 1, b));
            int σ = Interpreter.Top(s);
            int x = g.Rhs[r]![d];
            AtItem(g, a, it, σ, r, d);
            int k = FindItem(g, a, it, σ, r, d, 0);
            bool[] L = it.La[σ]![k]!;
            Spec.Assert(Safety.In(L, b));
            WordAtEnd(w, pos, Interpreter.Fringe(t));
            if (t is Tree.Leaf leaf)
            {
                int c0 = leaf.Term;
                Spec.Assert(Interpreter.Matches(g, x, c0) && !(g.NTerm <= x && x < g.NSym) && 0 <= c0 && c0 < g.NTerm);
                var one = new Word.Cons(c0, new Word.Nil());
                Spec.Assert(Interpreter.Fringe(t) == one);
                Spec.Assert(Len(one.Tail) == 0 && Len(one) == 1);
                Spec.Assert(pos < w.Length && w[pos] == c0);
                Spec.Assert(ItemActsOk(g, a, it, σ, r, d, L));
                int σ2 = a.Arg[σ]![c0];
                Spec.Assert(a.Kind[σ]![c0] == Automaton.Shift && 0 <= σ2 && σ2 < a.NState && HasAll(g, a, it, σ2, r, d + 1, L));
                HasOne(g, a, it, σ2, r, d + 1, L, b);
                AtItem(g, a, it, σ2, r, d + 1);
                Spec.Assert(a.Incoming[σ2] == x);
                Spec.Assert(Interpreter.Match(g, a.Incoming[σ2], c0));
                StepsOne(g, a, w, s, pos);
                Spec.Assert(Interpreter.Step(g, a, w, s, pos) == new Run.Going(new Stack.Cell(σ2, t, s), pos + 1));
            }
            else if (t is Tree.Node node)
            {
                int r2 = node.Rule;
                int[] rhs2 = g.Rhs[r2]!;
                int la = La(w, pos + Len(Interpreter.Fringe(t)));
                Spec.Assert(0 <= r2 && r2 < g.Lhs.Length && g.Lhs[r2] == x && Interpreter.Kids(g, node.Kids, rhs2, 0));
                Spec.Assert(FirstOk(g, a, it) && RuleFirstOk(g, a, it, r2));
                Spec.Assert(g.NTerm <= x && x < g.NSym);
                Spec.Assert(Interpreter.Fringe(t) == Interpreter.Fringes(node.Kids));
                Spec.Assert(ItemActsOk(g, a, it, σ, r, d, L));
                /* closure: the node's rule is in σ at dot 0, with the lookahead after the node */
                Spec.Assert(ClosureOk(g, a, it, σ, r, d, L, r2));
                Spec.Assert(FirstSeqIn(g, it, g.Rhs[r]!, d + 1, L, la));
                if (FirstSeq(g, it, g.Rhs[r]!, d + 1, la)) FirstSeqRange(g, a, it, g.Rhs[r]!, d + 1, la);
                Spec.Assert(0 <= la && la < g.NTerm);
                Spec.Assert(Safety.In(it.La[σ]![FindItem(g, a, it, σ, r2, 0, 0)]!, la));
                Spec.Assert(Has(g, a, it, σ, r2, 0, la));
                WalkKids(g, a, it, w, node.Kids, r2, 0, s, pos, la);
                var mid = (Run.Going)Interpreter.Steps(g, a, w, SizeF(node.Kids), new Run.Going(s, pos));
                int σ1 = Interpreter.Top(mid.S);
                /* the reduce */
                AtItem(g, a, it, σ1, r2, rhs2.Length);
                int k1 = FindItem(g, a, it, σ1, r2, rhs2.Length, 0);
                Spec.Assert(ItemActsOk(g, a, it, σ1, r2, rhs2.Length, it.La[σ1]![k1]!));
                Spec.Assert(Safety.In(it.La[σ1]![k1]!, la) && 0 <= la && la < g.NTerm);
                Spec.Assert(a.Kind[σ1]![la] == Automaton.Reduce && a.Arg[σ1]![la] == r2);
                /* the goto */
                int σ2 = a.Goto[σ]![x - g.NTerm];
                Spec.Assert(0 <= σ2 && σ2 < a.NState && HasAll(g, a, it, σ2, r, d + 1, L));
                HasOne(g, a, it, σ2, r, d + 1, L, b);
                AtItem(g, a, it, σ2, r, d + 1);
                Spec.Assert(a.Incoming[σ2] == x);
                WordAtEnd(w, pos, Interpreter.Fringes(node.Kids));
                Spec.Assert(Interpreter.Top(mid.S) == σ1 && 0 <= mid.Pos && mid.Pos <= w.Length);
                Interpreter.ReduceShape(g, a, mid.S, r2);
                Spec.Assert(Interpreter.Pop(a, mid.S, rhs2, 0, rhs2.Length, new Forest.Nil()) == new Popped.Ok(s, node.Kids));
                Spec.Assert(Interpreter.Reduce(g, a, mid.S, r2) == new Stack.Cell(σ2, t, s));
                Spec.Assert(mid.Pos == pos + Len(Interpreter.Fringe(t)) && la == La(w, mid.Pos));
                Spec.Assert(Interpreter.Step(g, a, w, mid.S, mid.Pos) == new Run.Going(new Stack.Cell(σ2, t, s), mid.Pos));
                StepsOne(g, a, w, mid.S, mid.Pos);
                StepsAdd(g, a, w, SizeF(node.Kids), 1, new Run.Going(s, pos));
                Spec.Assert(Size(t) == SizeF(node.Kids) + 1);
            }
        }

        /// <summary>
        /// The children rhs[i..] of a node of rule r, walked one after the other from a state with the item (r, i) and
        /// the lookahead after the node: they are pushed, the top state then has (r, |rhs|), and popping them gives
        /// them back over the stack they started on.
        /// </summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void WalkKids(Grammar g, Automaton a, Items it, int[] w, Forest ts, int r, int i, Stack s, int pos, int la)
        {
            Spec.Requires(CompleteOk(g, a, it) && Wf(g, a, it) && ItemShape(g, a, it) && 0 <= r && r < g.Rhs.Length && g.Rhs[r] != null &&
                          0 <= i && i <= g.Rhs[r].Length && Interpreter.Kids(g, ts, g.Rhs[r], i) &&
                          0 <= Interpreter.Top(s) && Interpreter.Top(s) < a.NState && Has(g, a, it, Interpreter.Top(s), r, i, la) &&
                          0 <= pos && WordAt(w, pos, Interpreter.Fringes(ts)) && La(w, pos + Len(Interpreter.Fringes(ts))) == la);
            Spec.Decreases(ts);
            Spec.Ensures(Interpreter.Steps(g, a, w, SizeF(ts), new Run.Going(s, pos)) is Run.Going go &&
                         go.Pos == pos + Len(Interpreter.Fringes(ts)) &&
                         0 <= Interpreter.Top(go.S) && Interpreter.Top(go.S) < a.NState && Has(g, a, it, Interpreter.Top(go.S), r, g.Rhs[r].Length, la) &&
                         Interpreter.Pop(a, go.S, g.Rhs[r], i, g.Rhs[r].Length, new Forest.Nil()) == new Popped.Ok(s, ts));
            int[] rhs = g.Rhs[r]!;
            if (ts is Forest.Cons c)
            {
                Tree t0 = c.Head;
                Spec.Assert(i < rhs.Length && Interpreter.Valid(g, t0, rhs[i]) && Interpreter.Kids(g, c.Tail, rhs, i + 1));
                Spec.Assert(Interpreter.Fringes(ts) == Interpreter.Append(Interpreter.Fringe(t0), Interpreter.Fringes(c.Tail)));
                WordAtAppend(w, pos, Interpreter.Fringe(t0), Interpreter.Fringes(c.Tail));
                int pos1 = pos + Len(Interpreter.Fringe(t0));
                LaFirst(g, a, it, w, c.Tail, rhs, i + 1, pos1, la);
                Walk(g, a, it, w, t0, s, pos, r, i, la);
                var mid = (Run.Going)Interpreter.Steps(g, a, w, Size(t0), new Run.Going(s, pos));
                var cell = (Stack.Cell)mid.S;
                WalkKids(g, a, it, w, c.Tail, r, i + 1, mid.S, pos1, la);
                StepsAdd(g, a, w, Size(t0), SizeF(c.Tail), new Run.Going(s, pos));
                Spec.Assert(SizeF(ts) == Size(t0) + SizeF(c.Tail));
                var end = (Run.Going)Interpreter.Steps(g, a, w, SizeF(c.Tail), mid);
                /* popping the first child too: its state was entered on its symbol */
                AtItem(g, a, it, cell.State, r, i + 1);
                Spec.Assert(a.Incoming[cell.State] == rhs[i]);
                Interpreter.PopSplit(a, end.S, rhs, i, i + 1, rhs.Length, new Forest.Nil());
                Spec.Assert(Interpreter.Pop(a, mid.S, rhs, i, i + 1, c.Tail) == Interpreter.Pop(a, s, rhs, i, i, new Forest.Cons(t0, c.Tail)));
                Spec.Assert(Interpreter.Pop(a, s, rhs, i, i, ts) == new Popped.Ok(s, ts));
            }
            else
            {
                Spec.Assert(i == rhs.Length && Interpreter.Fringes(ts) == new Word.Nil());
                Spec.Assert(Interpreter.Steps(g, a, w, 0, new Run.Going(s, pos)) == new Run.Going(s, pos));
                Spec.Assert(Interpreter.Pop(a, s, rhs, i, i, new Forest.Nil()) == new Popped.Ok(s, new Forest.Nil()));
            }
        }

        // ------------------------------------------------------------------------------------------ completeness

        /// <summary>
        /// Completeness (the paper's Theorem 3): with items that pass the completeness validator, for a parse tree t of
        /// the start symbol whose leaves are the input w, Size(t) + 1 steps from the start accept t itself.
        /// </summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void Accepts(Grammar g, Automaton a, Items it, int[] w, Tree t)
        {
            Spec.Requires(CompleteOk(g, a, it) && Wf(g, a, it) && ItemShape(g, a, it) && Interpreter.Valid(g, t, g.Start) &&
                          WordAt(w, 0, Interpreter.Fringe(t)) && Len(Interpreter.Fringe(t)) == w.Length);
            Spec.Ensures(Interpreter.Steps(g, a, w, Size(t) + 1, Interpreter.Start()) == new Run.Stopped(new Result.Accepted(t, w.Length)));
            Spec.Assert(RootOk(g, a, it));
            int acc = a.Goto[0]![g.Start - g.NTerm];
            Spec.Assert(0 < acc && acc < a.NState && a.Incoming[acc] == g.Start && a.Kind[acc]![0] == Automaton.Accept);
            if (t is Tree.Leaf l0)
                Spec.Assert(Interpreter.Matches(g, g.Start, l0.Term) && l0.Term < g.NTerm && g.NTerm <= g.Start && g.Start < g.NSym);
            Spec.Assert(!(t is Tree.Leaf));
            var node = (Tree.Node)t;
            int r = node.Rule;
            int[] rhs = g.Rhs[r]!;
            Spec.Assert(0 <= r && r < g.Lhs.Length && g.Lhs[r] == g.Start && Interpreter.Kids(g, node.Kids, rhs, 0));
            Spec.Assert(Has(g, a, it, 0, r, 0, 0));
            Spec.Assert(Interpreter.Fringe(t) == Interpreter.Fringes(node.Kids));
            Spec.Assert(La(w, w.Length) == 0);
            var empty = new Stack.Empty();
            Spec.Assert(Interpreter.Top(empty) == 0 && Interpreter.Start() == new Run.Going(empty, 0));
            WalkKids(g, a, it, w, node.Kids, r, 0, empty, 0, 0);
            var mid = (Run.Going)Interpreter.Steps(g, a, w, SizeF(node.Kids), Interpreter.Start());
            int σ1 = Interpreter.Top(mid.S);
            Spec.Assert(mid.Pos == w.Length);
            /* the reduce of the root's rule, at the end of input */
            AtItem(g, a, it, σ1, r, rhs.Length);
            int k1 = FindItem(g, a, it, σ1, r, rhs.Length, 0);
            Spec.Assert(ItemActsOk(g, a, it, σ1, r, rhs.Length, it.La[σ1]![k1]!));
            Spec.Assert(Safety.In(it.La[σ1]![k1]!, 0));
            Spec.Assert(a.Kind[σ1]![0] == Automaton.Reduce && a.Arg[σ1]![0] == r);
            Interpreter.ReduceShape(g, a, mid.S, r);
            Spec.Assert(Interpreter.Pop(a, mid.S, rhs, 0, rhs.Length, new Forest.Nil()) == new Popped.Ok(empty, node.Kids));
            var top = new Stack.Cell(acc, t, empty);
            Spec.Assert(Interpreter.Reduce(g, a, mid.S, r) == top);
            Spec.Assert(Interpreter.Step(g, a, w, mid.S, mid.Pos) == new Run.Going(top, w.Length));
            /* the accept */
            Spec.Assert(Interpreter.Top(top) == acc);
            Spec.Assert(Interpreter.Step(g, a, w, top, w.Length) == new Run.Stopped(new Result.Accepted(t, w.Length)));
            StepsOne(g, a, w, mid.S, mid.Pos);
            StepsOne(g, a, w, top, w.Length);
            StepsAdd(g, a, w, 1, 1, mid);
            StepsAdd(g, a, w, SizeF(node.Kids), 2, Interpreter.Start());
            Spec.Assert(Size(t) + 1 == SizeF(node.Kids) + 2);
        }

        /// <summary>
        /// Completeness for Parse: with more fuel than the tree's size, Steps(fuel) accepts t, so (Parse's
        /// postcondition) Parse returns Accepted(t, |w|): a validated grammar is unambiguous, and every sentence is
        /// parsed, into its one parse tree.
        /// </summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void ParseAccepts(Grammar g, Automaton a, Items it, int[] w, Tree t, int fuel)
        {
            Spec.Requires(CompleteOk(g, a, it) && Wf(g, a, it) && ItemShape(g, a, it) && Interpreter.Valid(g, t, g.Start) &&
                          WordAt(w, 0, Interpreter.Fringe(t)) && Len(Interpreter.Fringe(t)) == w.Length && fuel > Size(t));
            Spec.Ensures(Interpreter.Steps(g, a, w, fuel, Interpreter.Start()) == new Run.Stopped(new Result.Accepted(t, w.Length)));
            Accepts(g, a, it, w, t);
            Interpreter.StepsRest(g, a, w, Size(t) + 1, fuel, Interpreter.Start());
        }
    }
}
