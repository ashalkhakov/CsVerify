// An LR(1) interpreter, proved sound: whatever it accepts, the grammar derives (see lemon/Lr/DESIGN.md, after
// Jourdan, Pottier and Leroy, "Validating LR(1) Parsers", ESOP 2012).
using System.Diagnostics;
using CsVerify;

namespace CsLemon.Lr
{
    /// <summary>A sequence of terminals.</summary>
    public abstract record Word
    {
        private Word() { }
        public sealed record Nil() : Word;
        public sealed record Cons(int Head, Word Tail) : Word;
    }

    /// <summary>A parse tree: a terminal, or a rule over one tree per symbol of its right-hand side.</summary>
    public abstract record Tree
    {
        private Tree() { }
        public sealed record Leaf(int Term) : Tree;
        public sealed record Node(int Rule, Forest Kids) : Tree;
    }

    /// <summary>A sequence of parse trees.</summary>
    public abstract record Forest
    {
        private Forest() { }
        public sealed record Nil() : Forest;
        public sealed record Cons(Tree Head, Forest Tail) : Forest;
    }

    /// <summary>The interpreter's stack: cells of a state and the tree of the symbol that led to it, the top first.</summary>
    public abstract record Stack
    {
        private Stack() { }
        public sealed record Empty() : Stack;
        public sealed record Cell(int State, Tree T, Stack Below) : Stack;
    }

    /// <summary>What a run of the interpreter comes to.</summary>
    public abstract record Result
    {
        private Result() { }
        /// <summary>The first <c>Consumed</c> terminals of the input are a sentence; T is its parse tree.</summary>
        public sealed record Accepted(Tree T, int Consumed) : Result;
        /// <summary>
        /// The input is not a sentence: no action at the terminal At. S is the stack then: its trees are the
        /// reductions made so far (a parser that runs actions as it reduces has run theirs).
        /// </summary>
        public sealed record Rejected(int At, Stack S) : Result;
        public sealed record OutOfFuel() : Result;
        /// <summary>The automaton does not fit the grammar (a validated one never gets here).</summary>
        public sealed record InternalError() : Result;
    }

    /// <summary>Between steps: running, with a stack and an input position, or stopped with a result.</summary>
    public abstract record Run
    {
        private Run() { }
        public sealed record Going(Stack S, int Pos) : Run;
        public sealed record Stopped(Result R) : Run;
    }

    /// <summary>What popping a rule's cells gives: the stack left and the popped trees, or a failed check.</summary>
    public abstract record Popped
    {
        private Popped() { }
        public sealed record Fail() : Popped;
        public sealed record Ok(Stack Rest, Forest Kids) : Popped;
    }

    /// <summary>
    /// A grammar: terminals 0 .. NTerm-1 (0 is the end of input), nonterminals NTerm .. NSym-1, and rules r with a
    /// left-hand side Lhs[r] and a right-hand side Rhs[r]. Symbols from NSym on are Lemon's multiterminals (A|B): the
    /// terminals Multi[x - NSym] each match x.
    /// </summary>
    public sealed class Grammar
    {
        public readonly int NTerm, NSym, Start;
        public readonly int[] Lhs;
        public readonly int[][] Rhs;
        public readonly int[][] Multi;

        public Grammar(int nterm, int nsym, int start, int[] lhs, int[][] rhs, int[][] multi)
        {
            NTerm = nterm; NSym = nsym; Start = start; Lhs = lhs; Rhs = rhs; Multi = multi;
        }
    }

    /// <summary>
    /// An LR automaton: states 0 .. NState-1, 0 the initial one; each other state's incoming symbol; the action table
    /// [state][terminal] (Kind, and Arg: the state of a shift, the rule of a reduce); the goto table
    /// [state][nonterminal - NTerm] (a state, or -1).
    /// </summary>
    public sealed class Automaton
    {
        public const int Reject = 0, Shift = 1, Reduce = 2, Accept = 3;

        public readonly int NState;
        public readonly int[] Incoming;
        public readonly int[][] Kind, Arg, Goto;

        public Automaton(int nstate, int[] incoming, int[][] kind, int[][] arg, int[][] @goto)
        {
            NState = nstate; Incoming = incoming; Kind = kind; Arg = arg; Goto = @goto;
        }
    }

    public static class Interpreter
    {
        // ------------------------------------------------------------------------------------------ meaning

        [Pure]
        public static Word Append(Word xs, Word ys)
        {
            Spec.Decreases(xs);
            return xs switch { Word.Cons c => new Word.Cons(c.Head, Append(c.Tail, ys)), _ => ys };
        }

        [Lemma, Conditional(Spec.Symbol)]
        public static void AppendAssoc(Word xs, Word ys, Word zs)
        {
            Spec.Decreases(xs);
            Spec.Ensures(Append(Append(xs, ys), zs) == Append(xs, Append(ys, zs)));
            if (xs is Word.Cons c) AppendAssoc(c.Tail, ys, zs);
        }

        [Lemma, Conditional(Spec.Symbol)]
        public static void AppendNil(Word xs)
        {
            Spec.Decreases(xs);
            Spec.Ensures(Append(xs, new Word.Nil()) == xs);
            if (xs is Word.Cons c) AppendNil(c.Tail);
        }

        /// <summary>The leaves of a tree, in order.</summary>
        [GhostFunction]
        public static Word Fringe(Tree t)
        {
            Spec.Decreases(t);
            return t switch { Tree.Node n => Fringes(n.Kids), Tree.Leaf l => new Word.Cons(l.Term, new Word.Nil()) };
        }

        [GhostFunction]
        public static Word Fringes(Forest ts)
        {
            Spec.Decreases(ts);
            return ts switch { Forest.Cons c => Append(Fringe(c.Head), Fringes(c.Tail)), _ => new Word.Nil() };
        }

        /// <summary>
        /// t is a parse tree for symbol x: a leaf x (a terminal), or a node of a rule whose left-hand side is x and
        /// whose children are parse trees for its right-hand side.
        /// </summary>
        [GhostFunction]
        public static bool Valid(Grammar g, Tree t, int x)
        {
            Spec.Decreases(t);
            return t switch
            {
                Tree.Node n => 0 <= n.Rule && n.Rule < g.Lhs.Length && n.Rule < g.Rhs.Length && g.Lhs[n.Rule] == x &&
                               g.Rhs[n.Rule] != null && Kids(g, n.Kids, g.Rhs[n.Rule], 0),
                Tree.Leaf l => Matches(g, x, l.Term),
            };
        }

        /// <summary>The terminal a matches symbol x: it is x, or one of the multiterminal x's terminals.</summary>
        [GhostFunction]
        public static bool Matches(Grammar g, int x, int a) =>
            0 <= a && a < g.NTerm &&
            (a == x || 0 <= g.NSym && g.NSym <= x && x - g.NSym < g.Multi.Length && g.Multi[x - g.NSym] != null && Spec.Exists(0, g.Multi[x - g.NSym].Length, k => g.Multi[x - g.NSym][k] == a));

        /// <summary>Matches, at run time.</summary>
        [Pure]
        public static bool Match(Grammar g, int x, int a)
        {
            Spec.Ensures((bool r) => r == Matches(g, x, a));
            if (a < 0 || a >= g.NTerm) return false;
            if (a == x) return true;
            if (g.NSym < 0 || x < g.NSym || x - g.NSym >= g.Multi.Length) return false;
            int[]? m = g.Multi[x - g.NSym];
            return m != null && MemberFrom(m, a, 0);
        }

        /// <summary>a is one of m[k..].</summary>
        [Pure]
        public static bool MemberFrom(int[] m, int a, int k)
        {
            Spec.Requires(0 <= k);
            Spec.Decreases(m.Length - k);
            Spec.Ensures((bool r) => r == Spec.Exists(k, m.Length, j => m[j] == a));
            return k < m.Length && (m[k] == a || MemberFrom(m, a, k + 1));
        }

        /// <summary>ts are parse trees for the symbols rhs[i..], one each.</summary>
        [GhostFunction]
        public static bool Kids(Grammar g, Forest ts, int[] rhs, int i)
        {
            Spec.Decreases(ts);
            return ts switch
            {
                Forest.Cons c => 0 <= i && i < rhs.Length && Valid(g, c.Head, rhs[i]) && Kids(g, c.Tail, rhs, i + 1),
                _ => i == rhs.Length,
            };
        }

        /// <summary>The first n terminals of w.</summary>
        [GhostFunction]
        public static Word Prefix(int[] w, int n)
        {
            Spec.Decreases(n);
            return n <= 0 || n > w.Length ? new Word.Nil() : Append(Prefix(w, n - 1), new Word.Cons(w[n - 1], new Word.Nil()));
        }

        // ------------------------------------------------------------------------------------------ the stack

        /// <summary>Every cell's tree is a parse tree for its state's incoming symbol.</summary>
        [GhostFunction]
        public static bool StackOk(Grammar g, Automaton a, Stack s)
        {
            Spec.Decreases(s);
            return s switch
            {
                Stack.Cell c => 0 <= c.State && c.State < a.Incoming.Length && Valid(g, c.T, a.Incoming[c.State]) && StackOk(g, a, c.Below),
                _ => true,
            };
        }

        /// <summary>The leaves of the stack's trees, bottom to top: the input consumed so far.</summary>
        [GhostFunction]
        public static Word StackFringe(Stack s)
        {
            Spec.Decreases(s);
            return s switch { Stack.Cell c => Append(StackFringe(c.Below), Fringe(c.T)), _ => new Word.Nil() };
        }

        // ------------------------------------------------------------------------------------------ the interpreter

        /// <summary>The top state of a stack: its top cell's, or 0 for the empty stack.</summary>
        [Pure]
        public static int Top(Stack s) => s is Stack.Cell c ? c.State : 0;

        /// <summary>
        /// Pops the cells of rhs[lo .. i), checking that each one's incoming symbol is the rule's (rhs[i-1] on top);
        /// kids are the trees popped so far (of rhs[i..]).
        /// </summary>
        [Pure]
        public static Popped Pop(Automaton a, Stack s, int[] rhs, int lo, int i, Forest kids)
        {
            Spec.Requires(0 <= lo && lo <= i && i <= rhs.Length);
            Spec.Decreases(i);
            if (i == lo) return new Popped.Ok(s, kids);
            if (s is Stack.Cell c && 0 <= c.State && c.State < a.Incoming.Length && a.Incoming[c.State] == rhs[i - 1])
                return Pop(a, c.Below, rhs, lo, i - 1, new Forest.Cons(c.T, kids));
            return new Popped.Fail();
        }

        /// <summary>Popping down to lo goes through m: what is left at m pops on down.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void PopSplit(Automaton a, Stack s, int[] rhs, int lo, int m, int i, Forest kids)
        {
            Spec.Requires(0 <= lo && lo <= m && m <= i && i <= rhs.Length);
            Spec.Decreases(i);
            Spec.Ensures(Pop(a, s, rhs, lo, i, kids) ==
                         (Pop(a, s, rhs, m, i, kids) is Popped.Ok ok ? Pop(a, ok.Rest, rhs, lo, m, ok.Kids) : new Popped.Fail()));
            if (i > m && s is Stack.Cell c && 0 <= c.State && c.State < a.Incoming.Length && a.Incoming[c.State] == rhs[i - 1])
            {
                Spec.Assert(Pop(a, s, rhs, lo, i, kids) == Pop(a, c.Below, rhs, lo, i - 1, new Forest.Cons(c.T, kids)));
                Spec.Assert(Pop(a, s, rhs, m, i, kids) == Pop(a, c.Below, rhs, m, i - 1, new Forest.Cons(c.T, kids)));
                PopSplit(a, c.Below, rhs, lo, m, i - 1, new Forest.Cons(c.T, kids));
            }
            else if (i == m) Spec.Assert(Pop(a, s, rhs, m, i, kids) == new Popped.Ok(s, kids));
        }

        /// <summary>Reduces rule r: pops its cells, and pushes the node over their trees with the goto state. Null: an internal error.</summary>
        [Pure]
        public static Stack? Reduce(Grammar g, Automaton a, Stack s, int r)
        {
            if (r < 0 || r >= g.Lhs.Length || r >= g.Rhs.Length || g.NTerm < 0) return null;
            int[]? rhs = g.Rhs[r];
            if (rhs == null) return null;
            Popped p = Pop(a, s, rhs, 0, rhs.Length, new Forest.Nil());
            if (!(p is Popped.Ok ok)) return null;
            int lhs = g.Lhs[r], from = Top(ok.Rest);
            if (lhs < g.NTerm || from < 0 || from >= a.Goto.Length) return null;
            int[]? gotos = a.Goto[from];
            if (gotos == null || lhs - g.NTerm >= gotos.Length) return null;
            int next = gotos[lhs - g.NTerm];
            if (next < 0 || next >= a.Incoming.Length || a.Incoming[next] != lhs) return null;
            return new Stack.Cell(next, new Tree.Node(r, ok.Kids), ok.Rest);
        }

        /// <summary>
        /// One action of the automaton, in the top state on the lookahead (the terminal at pos, or 0 past the end of
        /// the input).
        /// </summary>
        [Pure]
        public static Run Step(Grammar g, Automaton a, int[] w, Stack s, int pos)
        {
            Spec.Requires(0 <= pos && pos <= w.Length);
            int state = Top(s);
            int la = pos < w.Length ? w[pos] : 0;
            if (la < 0 || la >= g.NTerm) return new Run.Stopped(new Result.Rejected(pos, s)); // (not a terminal)
            if (state < 0 || state >= a.Kind.Length || state >= a.Arg.Length) return new Run.Stopped(new Result.InternalError());
            int[]? kinds = a.Kind[state], args = a.Arg[state];
            if (kinds == null || args == null || la >= kinds.Length || la >= args.Length) return new Run.Stopped(new Result.InternalError());
            int kind = kinds[la];
            if (kind == Automaton.Shift)
            {
                int next = args[la];
                if (pos == w.Length || next < 0 || next >= a.Incoming.Length || !Match(g, a.Incoming[next], la))
                    return new Run.Stopped(new Result.InternalError());
                return new Run.Going(new Stack.Cell(next, new Tree.Leaf(la), s), pos + 1);
            }
            if (kind == Automaton.Reduce)
            {
                Stack? red = Reduce(g, a, s, args[la]);
                return red == null ? new Run.Stopped(new Result.InternalError()) : new Run.Going(red, pos);
            }
            if (kind == Automaton.Accept)
            {
                if (s is Stack.Cell c && c.Below is Stack.Empty && 0 <= c.State && c.State < a.Incoming.Length && a.Incoming[c.State] == g.Start)
                    return new Run.Stopped(new Result.Accepted(c.T, pos));
                return new Run.Stopped(new Result.InternalError());
            }
            return new Run.Stopped(new Result.Rejected(pos, s));
        }

        /// <summary>n steps from r (a stopped run stays stopped).</summary>
        [GhostFunction]
        public static Run Steps(Grammar g, Automaton a, int[] w, int n, Run r)
        {
            Spec.Decreases(n);
            if (n <= 0 || !(r is Run.Going go)) return r;
            if (go.Pos < 0 || go.Pos > w.Length) return new Run.Stopped(new Result.InternalError());
            return Steps(g, a, w, n - 1, Step(g, a, w, go.S, go.Pos));
        }

        /// <summary>The start: the empty stack, at the start of the input.</summary>
        [GhostFunction]
        public static Run Start() => new Run.Going(new Stack.Empty(), 0);

        /// <summary>One more step, at the end: Steps(n + 1) is a step after Steps(n), if that is still going.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void StepsLast(Grammar g, Automaton a, int[] w, int n, Run r)
        {
            Spec.Requires(0 <= n);
            Spec.Decreases(n);
            Spec.Ensures(!(Steps(g, a, w, n, r) is Run.Going go) || go.Pos < 0 || go.Pos > w.Length ||
                         Steps(g, a, w, n + 1, r) == Step(g, a, w, go.S, go.Pos));
            Spec.Ensures(!(Steps(g, a, w, n, r) is Run.Stopped) || Steps(g, a, w, n + 1, r) == Steps(g, a, w, n, r));
            if (r is Run.Going r0 && 0 <= r0.Pos && r0.Pos <= w.Length)
            {
                Spec.Assert(Steps(g, a, w, n + 1, r) == Steps(g, a, w, n, Step(g, a, w, r0.S, r0.Pos)));
                if (n > 0)
                {
                    Spec.Assert(Steps(g, a, w, n, r) == Steps(g, a, w, n - 1, Step(g, a, w, r0.S, r0.Pos)));
                    StepsLast(g, a, w, n - 1, Step(g, a, w, r0.S, r0.Pos));
                }
                else
                {
                    Spec.Assert(Steps(g, a, w, 0, r) == r);
                    Spec.Assert(Steps(g, a, w, 0, Step(g, a, w, r0.S, r0.Pos)) == Step(g, a, w, r0.S, r0.Pos));
                }
            }
            else
            {
                Spec.Assert(Steps(g, a, w, n + 1, r) == Steps(g, a, w, n, r) || r is Run.Going);
            }
        }

        /// <summary>What a successful Reduce pushes: the goto state, entered on the left-hand side, over the node of the popped trees.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void ReduceShape(Grammar g, Automaton a, Stack s, int r)
        {
            Spec.Ensures(Reduce(g, a, s, r) == null ||
                         0 <= r && r < g.Lhs.Length && r < g.Rhs.Length && g.Rhs[r] != null &&
                         Pop(a, s, g.Rhs[r], 0, g.Rhs[r].Length, new Forest.Nil()) is Popped.Ok ok &&
                         Reduce(g, a, s, r) is Stack.Cell c && c.T == new Tree.Node(r, ok.Kids) && c.Below == ok.Rest &&
                         0 <= c.State && c.State < a.Incoming.Length && a.Incoming[c.State] == g.Lhs[r] &&
                         g.NTerm <= g.Lhs[r] && 0 <= Top(ok.Rest) && Top(ok.Rest) < a.Goto.Length && a.Goto[Top(ok.Rest)] != null &&
                         g.Lhs[r] - g.NTerm < a.Goto[Top(ok.Rest)].Length && c.State == a.Goto[Top(ok.Rest)][g.Lhs[r] - g.NTerm]);
        }

        // ------------------------------------------------------------------------------------------ soundness

        /// <summary>Popping keeps the invariant: the stack and the trees popped make up the input consumed.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void PopSound(Grammar g, Automaton a, Stack s, int[] rhs, int i, Forest kids, Word consumed)
        {
            Spec.Requires(0 <= i && i <= rhs.Length && StackOk(g, a, s) && Kids(g, kids, rhs, i) &&
                          Append(StackFringe(s), Fringes(kids)) == consumed);
            Spec.Decreases(i);
            Spec.Ensures(!(Pop(a, s, rhs, 0, i, kids) is Popped.Ok ok) ||
                         StackOk(g, a, ok.Rest) && Kids(g, ok.Kids, rhs, 0) && Append(StackFringe(ok.Rest), Fringes(ok.Kids)) == consumed);
            if (i > 0 && s is Stack.Cell c && 0 <= c.State && c.State < a.Incoming.Length && a.Incoming[c.State] == rhs[i - 1])
            {
                var more = new Forest.Cons(c.T, kids);
                Spec.Assert(Kids(g, more, rhs, i - 1));
                Spec.Assert(Fringes(more) == Append(Fringe(c.T), Fringes(kids)));
                Spec.Assert(StackFringe(c) == Append(StackFringe(c.Below), Fringe(c.T)));
                AppendAssoc(StackFringe(c.Below), Fringe(c.T), Fringes(kids));
                Spec.Assert(Pop(a, s, rhs, 0, i, kids) == Pop(a, c.Below, rhs, 0, i - 1, more));
                PopSound(g, a, c.Below, rhs, i - 1, more, consumed);
            }
        }

        /// <summary>A step keeps the invariant, and what it accepts is a parse tree of the start symbol for the input consumed.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void StepSound(Grammar g, Automaton a, int[] w, Stack s, int pos)
        {
            Spec.Requires(0 <= pos && pos <= w.Length && StackOk(g, a, s) && StackFringe(s) == Prefix(w, pos));
            Spec.Ensures(Step(g, a, w, s, pos) is Run.Going go
                ? 0 <= go.Pos && go.Pos <= w.Length && StackOk(g, a, go.S) && StackFringe(go.S) == Prefix(w, go.Pos)
                : !(Step(g, a, w, s, pos) is Run.Stopped st && st.R is Result.Accepted acc) ||
                  0 <= acc.Consumed && acc.Consumed <= w.Length && Valid(g, acc.T, g.Start) && Fringe(acc.T) == Prefix(w, acc.Consumed));
            int state = Top(s);
            int la = pos < w.Length ? w[pos] : 0;
            if (la < 0 || la >= g.NTerm || state < 0 || state >= a.Kind.Length || state >= a.Arg.Length) return;
            int[]? kinds = a.Kind[state], args = a.Arg[state];
            if (kinds == null || args == null || la >= kinds.Length || la >= args.Length) return;
            if (kinds[la] == Automaton.Shift)
            {
                int next = args[la];
                if (pos == w.Length || next < 0 || next >= a.Incoming.Length || !Match(g, a.Incoming[next], la)) return;
                var shifted = new Stack.Cell(next, new Tree.Leaf(la), s);
                Spec.Assert(Valid(g, shifted.T, a.Incoming[next]));
                Spec.Assert(StackOk(g, a, shifted));
                Spec.Assert(Fringe(shifted.T) == new Word.Cons(la, new Word.Nil()));
                Spec.Assert(StackFringe(shifted) == Append(StackFringe(s), Fringe(shifted.T)));
                Spec.Assert(Prefix(w, pos + 1) == Append(Prefix(w, pos), new Word.Cons(w[pos], new Word.Nil())));
            }
            else if (kinds[la] == Automaton.Reduce)
            {
                int r = args[la];
                if (r < 0 || r >= g.Lhs.Length || r >= g.Rhs.Length || g.NTerm < 0) return;
                int[]? rhs = g.Rhs[r];
                if (rhs == null) return;
                Spec.Assert(Fringes(new Forest.Nil()) == new Word.Nil() && Kids(g, new Forest.Nil(), rhs, rhs.Length));
                AppendNil(StackFringe(s));
                PopSound(g, a, s, rhs, rhs.Length, new Forest.Nil(), Prefix(w, pos));
                ReduceShape(g, a, s, r);
                if (Pop(a, s, rhs, 0, rhs.Length, new Forest.Nil()) is Popped.Ok ok && Reduce(g, a, s, r) is Stack.Cell pushed)
                {
                    var node = new Tree.Node(r, ok.Kids);
                    Spec.Assert(Valid(g, node, g.Lhs[r]));
                    Spec.Assert(Fringe(node) == Fringes(ok.Kids));
                    Spec.Assert(StackFringe(pushed) == Append(StackFringe(ok.Rest), Fringe(node)));
                }
            }
            else if (kinds[la] == Automaton.Accept && s is Stack.Cell c && c.Below is Stack.Empty)
            {
                Spec.Assert(StackFringe(c) == Append(StackFringe(c.Below), Fringe(c.T)));
                Spec.Assert(StackFringe(c.Below) == new Word.Nil());
            }
        }

        // ------------------------------------------------------------------------------------------ safety

        /// <summary>
        /// Reducing rule r in σ, i cells still to pop on a safe stack whose top σ's annotation still describes: the
        /// checks pass, and what is left is safe and described by the rest of the annotation.
        /// </summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void PopSafe(Grammar g, Automaton a, Annotations ann, int σ, int r, Stack s, int i, Forest kids)
        {
            Spec.Requires(Safety.SafetyOk(g, a, ann) && Safety.Shape(g, a, ann) && 0 <= σ && σ < a.NState &&
                          Safety.RuleOk(g, a, ann, σ, r) && Safety.Safe(a, ann, s) && 0 <= i && i <= g.Rhs[r].Length &&
                          Safety.SymsOf(a, ann.Syms[σ], ann.Syms[σ].Length - g.Rhs[r].Length + i, s) &&
                          Safety.StatesOf(ann.States[σ], ann.States[σ].Length - g.Rhs[r].Length + i, s));
            Spec.Decreases(i);
            Spec.Ensures(Pop(a, s, g.Rhs[r], 0, i, kids) is Popped.Ok ok && Safety.Safe(a, ann, ok.Rest) &&
                         Safety.StatesOf(ann.States[σ], ann.States[σ].Length - g.Rhs[r].Length, ok.Rest));
            if (i > 0)
            {
                Safety.PopIfSafe(g, a, ann, σ, r, i, s);
                var c = (Stack.Cell)s;
                Spec.Assert(Pop(a, s, g.Rhs[r], 0, i, kids) == Pop(a, c.Below, g.Rhs[r], 0, i - 1, new Forest.Cons(c.T, kids)));
                PopSafe(g, a, ann, σ, r, c.Below, i - 1, new Forest.Cons(c.T, kids));
            }
            else Spec.Assert(Pop(a, s, g.Rhs[r], 0, 0, kids) == new Popped.Ok(s, kids));
        }

        /// <summary>With annotations that pass the safety validator, a step on a safe stack is no internal error, and keeps it safe.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void StepSafe(Grammar g, Automaton a, Annotations ann, int[] w, Stack s, int pos)
        {
            Spec.Requires(0 <= pos && pos <= w.Length);
            Spec.Ensures(!Safety.SafetyOk(g, a, ann) || !Safety.Safe(a, ann, s) ||
                         !(Step(g, a, w, s, pos) is Run.Stopped st && st.R is Result.InternalError) &&
                         (!(Step(g, a, w, s, pos) is Run.Going go) || Safety.Safe(a, ann, go.S)));
            if (!Safety.SafetyOk(g, a, ann) || !Safety.Safe(a, ann, s)) return;
            Safety.AtStateIfSafe(g, a, ann, s);
            int state = Top(s);
            Spec.Assert(state == Safety.TopState(s));
            int la = pos < w.Length ? w[pos] : 0;
            if (la < 0 || la >= g.NTerm) return;
            Spec.Assert(Safety.ShiftOk(g, a, ann, state, la) && Safety.ReduceOk(g, a, ann, state, la) && Safety.AcceptOk(g, a, ann, state, la));
            int[]? kinds = a.Kind[state], args = a.Arg[state];
            if (kinds![la] == Automaton.Shift)
            {
                Safety.PushIfSafe(g, a, ann, s, args![la], new Tree.Leaf(la));
            }
            else if (kinds[la] == Automaton.Reduce)
            {
                int r = args![la];
                Spec.Assert(Safety.RuleOk(g, a, ann, state, r));
                PopSafe(g, a, ann, state, r, s, g.Rhs[r]!.Length, new Forest.Nil());
                var ok = (Popped.Ok)Pop(a, s, g.Rhs[r]!, 0, g.Rhs[r]!.Length, new Forest.Nil());
                Safety.GotoIfSafe(g, a, ann, state, r, ok.Rest);
                Spec.Assert(Top(ok.Rest) == Safety.TopState(ok.Rest));
                Safety.PushIfSafe(g, a, ann, ok.Rest, a.Goto[Top(ok.Rest)]![g.Lhs[r] - g.NTerm], new Tree.Node(r, ok.Kids));
            }
        }

        // ------------------------------------------------------------------------------------------ the interpreter

        /// <summary>
        /// Runs the automaton on the input w (terminals; past its end, the lookahead is 0, the end of input) for at
        /// most fuel steps: the result is what Steps(fuel) comes to (out of fuel if it is still going).
        /// Soundness: an accepted prefix of the input has, as parse tree for the start symbol, the tree returned.
        /// Safety: with annotations that pass the safety validator (ann is ghost: it only names them), there is no
        /// internal error.
        /// </summary>
        public static Result Parse(Grammar g, Automaton a, int[] w, int fuel, Ghost<Annotations> ann)
        {
            Spec.Ensures((Result r) => r is Result.Accepted acc
                ? 0 <= acc.Consumed && acc.Consumed <= w.Length && Valid(g, acc.T, g.Start) && Fringe(acc.T) == Prefix(w, acc.Consumed)
                : true);
            Spec.Ensures((Result r) => !Safety.SafetyOk(g, a, ann.Value) || !(r is Result.InternalError));
            Spec.Ensures((Result r) => Steps(g, a, w, fuel, Start()) is Run.Stopped st ? r == st.R : r is Result.OutOfFuel);
            Stack s = new Stack.Empty();
            int pos = 0;
            Safety.StartIfSafe(g, a, ann.Value);
            Spec.Assert(StackFringe(s) == new Word.Nil() && Prefix(w, 0) == new Word.Nil());
            Spec.Assert(Start() == new Run.Going(s, pos) && Steps(g, a, w, 0, Start()) == Start());
            for (int step = 0; step < fuel; step++)
            {
                Spec.Invariant(0 <= step && 0 <= pos && pos <= w.Length);
                Spec.Invariant(StackOk(g, a, s) && StackFringe(s) == Prefix(w, pos));
                Spec.Invariant(!Safety.SafetyOk(g, a, ann.Value) || Safety.Safe(a, ann.Value, s));
                Spec.Invariant(Steps(g, a, w, step, Start()) == new Run.Going(s, pos));
                StepSound(g, a, w, s, pos);
                StepSafe(g, a, ann.Value, w, s, pos);
                StepsLast(g, a, w, step, Start());
                Run next = Step(g, a, w, s, pos);
                if (next is Run.Stopped stop)
                {
                    StepsRest(g, a, w, step + 1, fuel, Start());
                    return stop.R;
                }
                var go = (Run.Going)next;
                s = go.S;
                pos = go.Pos;
            }
            return new Result.OutOfFuel();
        }

        /// <summary>Once stopped, more steps change nothing.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void StepsRest(Grammar g, Automaton a, int[] w, int n, int m, Run r)
        {
            Spec.Requires(0 <= n && n <= m);
            Spec.Decreases(m - n);
            Spec.Ensures(!(Steps(g, a, w, n, r) is Run.Stopped) || Steps(g, a, w, m, r) == Steps(g, a, w, n, r));
            if (n < m)
            {
                StepsLast(g, a, w, n, r);
                StepsRest(g, a, w, n + 1, m, r);
            }
        }
    }
}
