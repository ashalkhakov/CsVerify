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
        /// <summary>The input is not a sentence: no action at this terminal.</summary>
        public sealed record Rejected(int At) : Result;
        public sealed record OutOfFuel() : Result;
        /// <summary>The automaton does not fit the grammar (a validated one never gets here).</summary>
        public sealed record InternalError() : Result;
    }

    /// <summary>
    /// A grammar: terminals 0 .. NTerm-1 (0 is the end of input), nonterminals NTerm .. NSym-1, and rules r with a
    /// left-hand side Lhs[r] and a right-hand side Rhs[r].
    /// </summary>
    public sealed class Grammar
    {
        public readonly int NTerm, NSym, Start;
        public readonly int[] Lhs;
        public readonly int[][] Rhs;

        public Grammar(int nterm, int nsym, int start, int[] lhs, int[][] rhs)
        {
            NTerm = nterm; NSym = nsym; Start = start; Lhs = lhs; Rhs = rhs;
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
                Tree.Leaf l => l.Term == x && 0 <= x && x < g.NTerm,
            };
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

        /// <summary>
        /// Runs the automaton on the input w (terminals; past its end, the lookahead is 0, the end of input) for at
        /// most fuel steps. Soundness: an accepted prefix of the input has, as parse tree for the start symbol, the
        /// tree returned.
        /// </summary>
        public static Result Parse(Grammar g, Automaton a, int[] w, int fuel)
        {
            Spec.Ensures((Result r) => r is Result.Accepted acc
                ? 0 <= acc.Consumed && acc.Consumed <= w.Length && Valid(g, acc.T, g.Start) && Fringe(acc.T) == Prefix(w, acc.Consumed)
                : true);
            Stack s = new Stack.Empty();
            int pos = 0;
            for (int step = 0; step < fuel; step++)
            {
                Spec.Invariant(0 <= pos && pos <= w.Length);
                Spec.Invariant(StackOk(g, a, s));
                Spec.Invariant(StackFringe(s) == Prefix(w, pos));
                int state = s is Stack.Cell top ? top.State : 0;
                int la = pos < w.Length ? w[pos] : 0;
                if (la < 0 || la >= g.NTerm) return new Result.Rejected(pos); // (not a terminal)
                if (state < 0 || state >= a.Kind.Length || state >= a.Arg.Length) return new Result.InternalError();
                int[]? kinds = a.Kind[state], args = a.Arg[state];
                if (kinds == null || args == null || la >= kinds.Length || la >= args.Length) return new Result.InternalError();
                int kind = kinds[la];
                if (kind == Automaton.Shift)
                {
                    int next = args[la];
                    if (pos == w.Length || next < 0 || next >= a.Incoming.Length || a.Incoming[next] != la) return new Result.InternalError();
                    var shifted = new Stack.Cell(next, new Tree.Leaf(la), s);
                    Spec.Assert(Valid(g, shifted.T, a.Incoming[next]));
                    Spec.Assert(StackOk(g, a, shifted));
                    Spec.Assert(Fringe(shifted.T) == new Word.Cons(la, new Word.Nil()));
                    Spec.Assert(StackFringe(shifted) == Append(StackFringe(s), Fringe(shifted.T)));
                    Spec.Assert(Prefix(w, pos + 1) == Append(Prefix(w, pos), new Word.Cons(w[pos], new Word.Nil())));
                    s = shifted;
                    pos++;
                }
                else if (kind == Automaton.Reduce)
                {
                    var red = ReduceStep(g, a, s, args[la], w, pos);
                    if (red == null) return new Result.InternalError();
                    s = red;
                }
                else if (kind == Automaton.Accept)
                {
                    if (s is Stack.Cell c && c.Below is Stack.Empty && 0 <= c.State && c.State < a.Incoming.Length && a.Incoming[c.State] == g.Start)
                    {
                        Spec.Assert(StackFringe(c) == Append(StackFringe(c.Below), Fringe(c.T)));
                        Spec.Assert(StackFringe(c.Below) == new Word.Nil());
                        return new Result.Accepted(c.T, pos);
                    }
                    return new Result.InternalError();
                }
                else return new Result.Rejected(pos);
            }
            return new Result.OutOfFuel();
        }

        /// <summary>
        /// Reduces rule r: pops one cell per right-hand-side symbol (checking each cell's incoming symbol), and pushes
        /// the node over their trees with the goto state. Null for an internal error.
        /// </summary>
        public static Stack? ReduceStep(Grammar g, Automaton a, Stack s, int r, int[] w, int pos)
        {
            Spec.Requires(0 <= pos && pos <= w.Length && StackOk(g, a, s) && StackFringe(s) == Prefix(w, pos));
            Spec.Ensures((Stack? res) => res == null || StackOk(g, a, res) && StackFringe(res) == Prefix(w, pos));
            if (r < 0 || r >= g.Lhs.Length || r >= g.Rhs.Length) return null;
            int[]? rhs = g.Rhs[r];
            if (rhs == null || g.NTerm < 0) return null;
            Forest kids = new Forest.Nil();
            Spec.Assert(Fringes(kids) == new Word.Nil() && Kids(g, kids, rhs, rhs.Length));
            AppendNil(StackFringe(s));
            for (int i = rhs.Length; i > 0; i--)
            {
                Spec.Invariant(0 <= i && i <= rhs.Length);
                Spec.Invariant(StackOk(g, a, s));
                Spec.Invariant(Kids(g, kids, rhs, i));
                Spec.Invariant(Append(StackFringe(s), Fringes(kids)) == Prefix(w, pos));
                Spec.Invariant(0 <= r && r < g.Lhs.Length && r < g.Rhs.Length && g.Rhs[r] == rhs && g.NTerm >= 0);
                if (!(s is Stack.Cell c) || c.State < 0 || c.State >= a.Incoming.Length || a.Incoming[c.State] != rhs[i - 1]) return null;
                var more = new Forest.Cons(c.T, kids);
                Spec.Assert(Kids(g, more, rhs, i - 1));
                Spec.Assert(Fringes(more) == Append(Fringe(c.T), Fringes(kids)));
                Spec.Assert(StackFringe(c) == Append(StackFringe(c.Below), Fringe(c.T)));
                AppendAssoc(StackFringe(c.Below), Fringe(c.T), Fringes(kids));
                kids = more;
                s = c.Below;
            }
            int lhs = g.Lhs[r];
            int from = s is Stack.Cell top ? top.State : 0;
            if (lhs < g.NTerm || from < 0 || from >= a.Goto.Length) return null;
            int[]? gotos = a.Goto[from];
            if (gotos == null || lhs - g.NTerm >= gotos.Length) return null;
            int next = gotos[lhs - g.NTerm];
            if (next < 0 || next >= a.Incoming.Length || a.Incoming[next] != lhs) return null;
            var node = new Tree.Node(r, kids);
            Spec.Assert(Valid(g, node, lhs));
            Spec.Assert(Fringe(node) == Fringes(kids));
            var pushed = new Stack.Cell(next, node, s);
            Spec.Assert(StackFringe(pushed) == Append(StackFringe(s), Fringe(node)));
            return pushed;
        }
    }
}
