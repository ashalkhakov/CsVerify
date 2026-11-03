// The safety validator (lemon/Lr/DESIGN.md, after Jourdan, Pottier and Leroy, ESOP 2012, section 3.2): if it accepts
// an automaton with its annotations, the interpreter never reaches an internal error.
//
// Unlike the paper's pastSymbols(σ) and pastStates(σ), which describe the cells under σ, each state's annotation here
// describes the top cells of the stack including σ's own: Syms[σ] ends with σ's incoming symbol, States[σ] with a set
// containing σ (for the initial state, no symbols, and one set holding 0 itself, which stands for the empty stack).
using System.Diagnostics;
using CsVerify;

namespace CsLemon.Lr
{
    /// <summary>
    /// What lies on top of the stack in each state σ: the incoming symbols of its top cells, bottom to top
    /// (Syms[σ]), and supersets of their states (States[σ], one more set at the bottom: what is under them, 0 meaning
    /// the bottom of the stack). Sets are indexed by state.
    /// </summary>
    public sealed class Annotations
    {
        public readonly int[][] Syms;
        public readonly bool[][][] States;

        public Annotations(int[][] syms, bool[][][] states) { Syms = syms; States = states; }
    }

    public static class Safety
    {
        // ------------------------------------------------------------------------------------------ the invariant

        [GhostFunction]
        public static bool In(bool[] set, int x) => 0 <= x && x < set.Length && set[x];

        /// <summary>The top n cells of s have the incoming symbols syms[0 .. n), syms[n-1] on top.</summary>
        [GhostFunction]
        public static bool SymsOf(Automaton a, int[] syms, int n, Stack s)
        {
            Spec.Decreases(s);
            return s switch
            {
                Stack.Cell c => n <= 0 || n <= syms.Length && 0 <= c.State && c.State < a.Incoming.Length &&
                                          a.Incoming[c.State] == syms[n - 1] && SymsOf(a, syms, n - 1, c.Below),
                _ => n <= 0,
            };
        }

        /// <summary>
        /// The states of the top n-1 cells of s are in sets[1 .. n), sets[n-1] on top, and the state under them (0 at
        /// the bottom of the stack) is in sets[0].
        /// </summary>
        [GhostFunction]
        public static bool StatesOf(bool[][] sets, int n, Stack s)
        {
            Spec.Decreases(s);
            return s switch
            {
                Stack.Cell c => n <= 0 || n <= sets.Length && sets[n - 1] != null && In(sets[n - 1], c.State) && StatesOf(sets, n - 1, c.Below),
                _ => n <= 0 || n == 1 && sets.Length >= 1 && sets[0] != null && In(sets[0], 0),
            };
        }

        /// <summary>The annotation of state σ describes the top of s.</summary>
        [GhostFunction]
        public static bool Describes(Automaton a, Annotations ann, int σ, Stack s) =>
            0 <= σ && σ < ann.Syms.Length && σ < ann.States.Length && ann.Syms[σ] != null && ann.States[σ] != null &&
            SymsOf(a, ann.Syms[σ], ann.Syms[σ].Length, s) && StatesOf(ann.States[σ], ann.States[σ].Length, s);

        /// <summary>
        /// The safety invariant: the current state's annotation describes the stack, and so on down (each cell's
        /// state's annotation describes the stack it tops); no cell is in the initial state.
        /// </summary>
        [GhostFunction]
        public static bool Safe(Automaton a, Annotations ann, Stack s)
        {
            Spec.Decreases(s);
            return s switch
            {
                Stack.Cell c => c.State != 0 && Describes(a, ann, c.State, s) && Safe(a, ann, c.Below),
                _ => Describes(a, ann, 0, s),
            };
        }

        // ------------------------------------------------------------------------------------------ suffixes

        /// <summary>ys is a suffix of xs, as far as the top m and n elements go.</summary>
        [GhostFunction]
        public static bool SymSuffix(int[] ys, int m, int[] xs, int n) =>
            0 <= m && m <= n && m <= ys.Length && n <= xs.Length && Spec.Forall(0, m, k => ys[k] == xs[k + n - m]);

        /// <summary>A is a subset of B.</summary>
        [GhostFunction]
        public static bool Sub(bool[] A, bool[] B) => Spec.Forall(0, A.Length, x => !A[x] || x < B.Length && B[x]);

        /// <summary>ys is a suffix of xs, by supersets, as far as the top m and n sets go.</summary>
        [GhostFunction]
        public static bool StateSuffix(bool[][] ys, int m, bool[][] xs, int n) =>
            0 <= m && m <= n && m <= ys.Length && n <= xs.Length &&
            Spec.Forall(0, m, k => xs[k + n - m] != null && ys[k] != null && Sub(xs[k + n - m], ys[k]));

        [Lemma, Conditional(Spec.Symbol)]
        public static void SymsSuffix(Automaton a, int[] ys, int m, int[] xs, int n, Stack s)
        {
            Spec.Requires(SymsOf(a, xs, n, s) && SymSuffix(ys, m, xs, n));
            Spec.Ensures(SymsOf(a, ys, m, s));
            Spec.Decreases(s);
            if (m > 0 && s is Stack.Cell c)
            {
                Spec.Assert(ys[m - 1] == xs[m - 1 + n - m]);
                SymsSuffix(a, ys, m - 1, xs, n - 1, c.Below);
            }
        }

        [Lemma, Conditional(Spec.Symbol)]
        public static void StatesSuffix(bool[][] ys, int m, bool[][] xs, int n, Stack s)
        {
            Spec.Requires(StatesOf(xs, n, s) && StateSuffix(ys, m, xs, n));
            Spec.Ensures(StatesOf(ys, m, s));
            Spec.Decreases(s);
            if (m > 0)
            {
                bool[]? top = xs[m - 1 + n - m], mine = ys[m - 1];
                Spec.Assert(top != null && mine != null && Sub(top, mine));
                Spec.Assert(StateSuffix(ys, m - 1, xs, n - 1));
                if (s is Stack.Cell c)
                {
                    Spec.Assert(In(top!, c.State));
                    Spec.Assert(In(mine!, c.State));
                    StatesSuffix(ys, m - 1, xs, n - 1, c.Below);
                }
                else Spec.Assert(In(top!, 0) && In(mine!, 0));
            }
        }

        // ------------------------------------------------------------------------------------------ what is checked

        /// <summary>The top state of a stack: its top cell's, or 0 for the empty stack.</summary>
        [GhostFunction]
        public static int TopState(Stack s) => s is Stack.Cell c ? c.State : 0;

        /// <summary>
        /// A transition (shift or goto) from σ to σ2: σ2 is a state other than the initial one, whose annotation
        /// ends with its own incoming symbol and itself, and whose annotation, below that, is a suffix of σ's.
        /// </summary>
        [GhostFunction]
        public static bool TransOk(Automaton a, Annotations ann, int σ, int σ2) =>
            0 < σ2 && σ2 < a.Incoming.Length && σ2 < ann.Syms.Length && σ2 < ann.States.Length &&
            0 <= σ && σ < ann.Syms.Length && σ < ann.States.Length &&
            ann.Syms[σ] != null && ann.States[σ] != null && ann.Syms[σ2] != null && ann.States[σ2] != null &&
            ann.Syms[σ2].Length >= 1 && ann.States[σ2].Length >= 1 &&
            ann.Syms[σ2][ann.Syms[σ2].Length - 1] == a.Incoming[σ2] &&
            ann.States[σ2][ann.States[σ2].Length - 1] != null && In(ann.States[σ2][ann.States[σ2].Length - 1], σ2) &&
            SymSuffix(ann.Syms[σ2], ann.Syms[σ2].Length - 1, ann.Syms[σ], ann.Syms[σ].Length) &&
            StateSuffix(ann.States[σ2], ann.States[σ2].Length - 1, ann.States[σ], ann.States[σ].Length);

        /// <summary>
        /// Pushing σ2 over a stack that σ's annotation describes (σ its top state): σ2's annotation describes the
        /// result.
        /// </summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void Push(Automaton a, Annotations ann, int σ, Stack s, int σ2, Tree t)
        {
            Spec.Requires(Describes(a, ann, σ, s) && TransOk(a, ann, σ, σ2));
            Spec.Ensures(Describes(a, ann, σ2, new Stack.Cell(σ2, t, s)));
            int[]? ys = ann.Syms[σ2], xs = ann.Syms[σ];
            bool[][]? yt = ann.States[σ2], xt = ann.States[σ];
            var top = new Stack.Cell(σ2, t, s);
            SymsSuffix(a, ys!, ys!.Length - 1, xs!, xs!.Length, s);
            StatesSuffix(yt!, yt!.Length - 1, xt!, xt!.Length, s);
            Spec.Assert(SymsOf(a, ys, ys.Length, top));
            Spec.Assert(StatesOf(yt, yt.Length, top));
        }

        // ------------------------------------------------------------------------------------------ the conditions

        /// <summary>The tables have their sizes; the initial state's annotation is the empty stack's.</summary>
        [GhostFunction]
        public static bool Shape(Grammar g, Automaton a, Annotations ann) =>
            a.NState == a.Incoming.Length && a.Kind.Length == a.NState && a.Arg.Length == a.NState && a.Goto.Length == a.NState &&
            ann.Syms.Length == a.NState && ann.States.Length == a.NState && 0 < a.NState &&
            Spec.Forall(0, a.NState, σ => ann.Syms[σ] != null && ann.States[σ] != null) &&
            0 < g.NTerm && g.NTerm <= g.NSym && g.Lhs.Length == g.Rhs.Length &&
            Spec.Forall(0, a.NState, σ => a.Kind[σ] != null && a.Arg[σ] != null && a.Goto[σ] != null &&
                                          a.Kind[σ].Length == g.NTerm && a.Arg[σ].Length == g.NTerm && a.Goto[σ].Length == g.NSym - g.NTerm) &&
            ann.Syms[0] != null && ann.Syms[0].Length == 0 && ann.States[0] != null && ann.States[0].Length == 1 &&
            ann.States[0][0] != null && In(ann.States[0][0], 0);

        /// <summary>A shift on terminal t from σ: not on the end of input, to a state whose incoming symbol t matches.</summary>
        [GhostFunction]
        public static bool ShiftOk(Grammar g, Automaton a, Annotations ann, int σ, int t)
        {
            Spec.Requires(Shape(g, a, ann) && 0 <= σ && σ < a.NState && 0 <= t && t < g.NTerm);
            return a.Kind[σ][t] != Automaton.Shift ||
            t != 0 && TransOk(a, ann, σ, a.Arg[σ][t]) && Interpreter.Matches(g, a.Incoming[a.Arg[σ][t]], t);
        }

        /// <summary>A goto on nonterminal NTerm + x from σ: none, or to a state whose incoming symbol it is.</summary>
        [GhostFunction]
        public static bool GotoOk(Grammar g, Automaton a, Annotations ann, int σ, int x)
        {
            Spec.Requires(Shape(g, a, ann) && 0 <= σ && σ < a.NState && 0 <= x && x < g.NSym - g.NTerm);
            return a.Goto[σ][x] == -1 || TransOk(a, ann, σ, a.Goto[σ][x]) && a.Incoming[a.Goto[σ][x]] == x + g.NTerm;
        }

        /// <summary>
        /// Reducing rule r in σ: its right-hand side is a suffix of σ's symbols, so the cells to pop are there and
        /// match; and every state that may then be on top (in the set |rhs| below σ's, or any, if that is deeper
        /// than σ's annotation goes) has a goto on its left-hand side.
        /// </summary>
        [GhostFunction]
        public static bool RuleOk(Grammar g, Automaton a, Annotations ann, int σ, int r)
        {
            Spec.Requires(Shape(g, a, ann) && 0 <= σ && σ < a.NState);
            return 0 <= r && r < g.Lhs.Length && r < g.Rhs.Length && g.Rhs[r] != null && g.NTerm <= g.Lhs[r] && g.Lhs[r] < g.NSym &&
            SymSuffix(g.Rhs[r], g.Rhs[r].Length, ann.Syms[σ], ann.Syms[σ].Length) &&
            (g.Rhs[r].Length < ann.States[σ].Length
                ? ann.States[σ][ann.States[σ].Length - 1 - g.Rhs[r].Length] != null &&
                  Spec.Forall(0, a.NState, x => !In(ann.States[σ][ann.States[σ].Length - 1 - g.Rhs[r].Length], x) || a.Goto[x][g.Lhs[r] - g.NTerm] != -1)
                : Spec.Forall(0, a.NState, x => a.Goto[x][g.Lhs[r] - g.NTerm] != -1));
        }

        [GhostFunction]
        public static bool ReduceOk(Grammar g, Automaton a, Annotations ann, int σ, int t)
        {
            Spec.Requires(Shape(g, a, ann) && 0 <= σ && σ < a.NState && 0 <= t && t < g.NTerm);
            return a.Kind[σ][t] != Automaton.Reduce || RuleOk(g, a, ann, σ, a.Arg[σ][t]);
        }

        /// <summary>Accepting in σ: σ was entered on the start symbol, from the initial state at the bottom of the stack.</summary>
        [GhostFunction]
        public static bool AcceptOk(Grammar g, Automaton a, Annotations ann, int σ, int t)
        {
            Spec.Requires(Shape(g, a, ann) && 0 <= σ && σ < a.NState && 0 <= t && t < g.NTerm);
            return a.Kind[σ][t] != Automaton.Accept ||
            σ != 0 && a.Incoming[σ] == g.Start && ann.States[σ].Length == 2 && ann.States[σ][0] != null &&
            Spec.Forall(0, ann.States[σ][0].Length, x => !ann.States[σ][0][x] || x == 0);
        }

        [GhostFunction]
        public static bool StateOk(Grammar g, Automaton a, Annotations ann, int σ)
        {
            Spec.Requires(Shape(g, a, ann) && 0 <= σ && σ < a.NState);
            return Spec.Forall(0, g.NTerm, t => ShiftOk(g, a, ann, σ, t) && ReduceOk(g, a, ann, σ, t) && AcceptOk(g, a, ann, σ, t)) &&
            Spec.Forall(0, g.NSym - g.NTerm, x => GotoOk(g, a, ann, σ, x));
        }

        /// <summary>What the safety validator checks.</summary>
        [GhostFunction]
        public static bool SafetyOk(Grammar g, Automaton a, Annotations ann) =>
            Shape(g, a, ann) && Spec.Forall(0, a.NState, σ => StateOk(g, a, ann, σ));

        // ------------------------------------------------------------------------------------------ for the interpreter

        /// <summary>The empty stack is safe.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void StartIfSafe(Grammar g, Automaton a, Annotations ann)
        {
            Spec.Ensures(!SafetyOk(g, a, ann) || Safe(a, ann, new Stack.Empty()));
            if (SafetyOk(g, a, ann))
            {
                Spec.Assert(Shape(g, a, ann));
                Spec.Assert(SymsOf(a, ann.Syms[0], 0, new Stack.Empty()));
                Spec.Assert(StatesOf(ann.States[0], 1, new Stack.Empty()));
                Spec.Assert(Describes(a, ann, 0, new Stack.Empty()));
            }
        }

        /// <summary>A safe stack: its top state is a state, whose annotation describes it, and which passed the validator.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void AtStateIfSafe(Grammar g, Automaton a, Annotations ann, Stack s)
        {
            Spec.Ensures(!SafetyOk(g, a, ann) || !Safe(a, ann, s) ||
                         Shape(g, a, ann) && 0 <= TopState(s) && TopState(s) < a.NState &&
                         Describes(a, ann, TopState(s), s) && StateOk(g, a, ann, TopState(s)));
            if (SafetyOk(g, a, ann) && Safe(a, ann, s))
            {
                Spec.Assert(Shape(g, a, ann));
                Spec.Assert(Describes(a, ann, TopState(s), s));
                Spec.Assert(StateOk(g, a, ann, TopState(s)));
            }
        }

        /// <summary>A transition from the top state of a safe stack keeps it safe.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void PushIfSafe(Grammar g, Automaton a, Annotations ann, Stack s, int σ2, Tree t)
        {
            Spec.Requires(!SafetyOk(g, a, ann) || Safe(a, ann, s) && Describes(a, ann, TopState(s), s) && TransOk(a, ann, TopState(s), σ2));
            Spec.Ensures(!SafetyOk(g, a, ann) || Safe(a, ann, new Stack.Cell(σ2, t, s)));
            if (SafetyOk(g, a, ann))
            {
                Push(a, ann, TopState(s), s, σ2, t);
                Spec.Assert(Safe(a, ann, new Stack.Cell(σ2, t, s)));
            }
        }

        /// <summary>
        /// Reducing rule r in σ, i cells still to pop: the stack is described by what is left of σ's annotation, so
        /// it has a cell, whose symbol is the rule's i-th, and what is under it is described by the rest.
        /// </summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void PopIfSafe(Grammar g, Automaton a, Annotations ann, int σ, int r, int i, Stack s)
        {
            Spec.Requires(!SafetyOk(g, a, ann) ||
                          Shape(g, a, ann) && 0 <= σ && σ < a.NState && RuleOk(g, a, ann, σ, r) && Safe(a, ann, s) && 0 < i && i <= g.Rhs[r].Length &&
                          SymsOf(a, ann.Syms[σ], ann.Syms[σ].Length - g.Rhs[r].Length + i, s) &&
                          StatesOf(ann.States[σ], ann.States[σ].Length - g.Rhs[r].Length + i, s));
            Spec.Ensures(!SafetyOk(g, a, ann) ||
                         Shape(g, a, ann) && 0 <= σ && σ < a.NState && RuleOk(g, a, ann, σ, r) && 0 < i && i <= g.Rhs[r].Length &&
                         s is Stack.Cell c && 0 <= c.State && c.State < a.Incoming.Length && a.Incoming[c.State] == g.Rhs[r][i - 1] &&
                         Safe(a, ann, c.Below) &&
                         SymsOf(a, ann.Syms[σ], ann.Syms[σ].Length - g.Rhs[r].Length + i - 1, c.Below) &&
                         StatesOf(ann.States[σ], ann.States[σ].Length - g.Rhs[r].Length + i - 1, c.Below));
            if (SafetyOk(g, a, ann))
            {
                Spec.Assert(RuleOk(g, a, ann, σ, r));
                int[]? rhs = g.Rhs[r], syms = ann.Syms[σ];
                Spec.Assert(rhs != null && syms != null && SymSuffix(rhs, rhs.Length, syms, syms.Length));
                Spec.Assert(rhs![i - 1] == syms![i - 1 + syms.Length - rhs.Length]);
                Spec.Assert(s is Stack.Cell);
            }
        }

        /// <summary>
        /// Reducing rule r in σ, all popped: the state now on top is one with a goto on the rule's left-hand side,
        /// to a state entered on it, whose annotation describes the stack with it pushed.
        /// </summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void GotoIfSafe(Grammar g, Automaton a, Annotations ann, int σ, int r, Stack s)
        {
            Spec.Requires(!SafetyOk(g, a, ann) ||
                          Shape(g, a, ann) && 0 <= σ && σ < a.NState && RuleOk(g, a, ann, σ, r) && Safe(a, ann, s) &&
                          StatesOf(ann.States[σ], ann.States[σ].Length - g.Rhs[r].Length, s));
            Spec.Ensures(!SafetyOk(g, a, ann) ||
                         0 <= TopState(s) && TopState(s) < a.NState && Describes(a, ann, TopState(s), s) &&
                         a.Goto[TopState(s)][g.Lhs[r] - g.NTerm] != -1 &&
                         TransOk(a, ann, TopState(s), a.Goto[TopState(s)][g.Lhs[r] - g.NTerm]) &&
                         a.Incoming[a.Goto[TopState(s)][g.Lhs[r] - g.NTerm]] == g.Lhs[r]);
            if (SafetyOk(g, a, ann))
            {
                AtStateIfSafe(g, a, ann, s);
                Spec.Assert(RuleOk(g, a, ann, σ, r));
                int x = TopState(s);
                bool[][]? sets = ann.States[σ];
                int[]? rhs = g.Rhs[r];
                if (rhs!.Length < sets!.Length)
                {
                    Spec.Assert(In(sets[sets.Length - 1 - rhs.Length]!, x));
                }
                Spec.Assert(a.Goto[x][g.Lhs[r] - g.NTerm] != -1);
                Spec.Assert(GotoOk(g, a, ann, x, g.Lhs[r] - g.NTerm));
            }
        }

        // ------------------------------------------------------------------------------------------ the validator

        public static bool CheckSymSuffix(int[] ys, int m, int[] xs, int n)
        {
            Spec.Ensures((bool r) => !r || SymSuffix(ys, m, xs, n));
            if (!(0 <= m && m <= n && m <= ys.Length && n <= xs.Length)) return false;
            for (int k = 0; k < m; k++)
            {
                Spec.Invariant(0 <= k && k <= m && Spec.Forall(0, k, j => ys[j] == xs[j + n - m]));
                if (ys[k] != xs[k + (n - m)]) return false;
            }
            return true;
        }

        public static bool CheckSub(bool[] A, bool[] B)
        {
            Spec.Ensures((bool r) => !r || Sub(A, B));
            for (int x = 0; x < A.Length; x++)
            {
                Spec.Invariant(0 <= x && x <= A.Length && Spec.Forall(0, x, y => !A[y] || y < B.Length && B[y]));
                if (A[x] && !(x < B.Length && B[x])) return false;
            }
            return true;
        }

        public static bool CheckStateSuffix(bool[][] ys, int m, bool[][] xs, int n)
        {
            Spec.Ensures((bool r) => !r || StateSuffix(ys, m, xs, n));
            if (!(0 <= m && m <= n && m <= ys.Length && n <= xs.Length)) return false;
            for (int k = 0; k < m; k++)
            {
                Spec.Invariant(0 <= k && k <= m &&
                               Spec.Forall(0, k, j => xs[j + n - m] != null && ys[j] != null && Sub(xs[j + n - m], ys[j])));
                bool[]? A = xs[k + (n - m)], B = ys[k];
                if (A == null || B == null || !CheckSub(A, B)) return false;
                Spec.Assert(xs[k + n - m] != null && ys[k] != null && Sub(xs[k + n - m], ys[k]));
            }
            return true;
        }

        public static bool CheckTrans(Automaton a, Annotations ann, int σ, int σ2)
        {
            Spec.Ensures((bool r) => !r || TransOk(a, ann, σ, σ2));
            if (!(0 < σ2 && σ2 < a.Incoming.Length && σ2 < ann.Syms.Length && σ2 < ann.States.Length &&
                  0 <= σ && σ < ann.Syms.Length && σ < ann.States.Length)) return false;
            int[]? xs = ann.Syms[σ], ys = ann.Syms[σ2];
            bool[][]? xt = ann.States[σ], yt = ann.States[σ2];
            if (xs == null || ys == null || xt == null || yt == null || ys.Length < 1 || yt.Length < 1) return false;
            if (ys[ys.Length - 1] != a.Incoming[σ2]) return false;
            bool[]? last = yt[yt.Length - 1];
            if (last == null || !(σ2 < last.Length && last[σ2])) return false;
            if (!CheckSymSuffix(ys, ys.Length - 1, xs, xs.Length) || !CheckStateSuffix(yt, yt.Length - 1, xt, xt.Length)) return false;
            Spec.Assert(In(last, σ2));
            return true;
        }

        public static bool CheckShape(Grammar g, Automaton a, Annotations ann)
        {
            Spec.Ensures((bool r) => !r || Shape(g, a, ann));
            int n = a.NState;
            if (!(n == a.Incoming.Length && a.Kind.Length == n && a.Arg.Length == n && a.Goto.Length == n &&
                  ann.Syms.Length == n && ann.States.Length == n && 0 < n &&
                  0 < g.NTerm && g.NTerm <= g.NSym && g.Lhs.Length == g.Rhs.Length)) return false;
            for (int σ = 0; σ < n; σ++)
            {
                Spec.Invariant(0 <= σ && σ <= n && n == a.NState && a.Kind.Length == n && a.Arg.Length == n && a.Goto.Length == n &&
                               ann.Syms.Length == n && ann.States.Length == n && g.NTerm <= g.NSym &&
                               Spec.Forall(0, σ, q => ann.Syms[q] != null && ann.States[q] != null) &&
                               Spec.Forall(0, σ, q => a.Kind[q] != null && a.Arg[q] != null && a.Goto[q] != null &&
                                                      a.Kind[q].Length == g.NTerm && a.Arg[q].Length == g.NTerm && a.Goto[q].Length == g.NSym - g.NTerm));
                int[]? k = a.Kind[σ], x = a.Arg[σ], gt = a.Goto[σ];
                if (ann.Syms[σ] == null || ann.States[σ] == null || k == null || x == null || gt == null ||
                    k.Length != g.NTerm || x.Length != g.NTerm || gt.Length != g.NSym - g.NTerm) return false;
            }
            int[]? s0 = ann.Syms[0];
            bool[][]? t0 = ann.States[0];
            if (s0 == null || s0.Length != 0 || t0 == null || t0.Length != 1) return false;
            bool[]? bottom = t0[0];
            if (bottom == null || bottom.Length == 0 || !bottom[0]) return false;
            Spec.Assert(In(ann.States[0][0], 0));
            Spec.Assert(Spec.Forall(0, a.NState, q => ann.Syms[q] != null && ann.States[q] != null));
            return true;
        }

        public static bool CheckRule(Grammar g, Automaton a, Annotations ann, int σ, int r)
        {
            Spec.Requires(Shape(g, a, ann) && 0 <= σ && σ < a.NState);
            Spec.Ensures((bool res) => !res || RuleOk(g, a, ann, σ, r));
            if (!(0 <= r && r < g.Lhs.Length && r < g.Rhs.Length)) return false;
            int[]? rhs = g.Rhs[r];
            int lhs = g.Lhs[r];
            if (rhs == null || !(g.NTerm <= lhs && lhs < g.NSym)) return false;
            int[]? syms = ann.Syms[σ];
            bool[][]? sets = ann.States[σ];
            if (syms == null || sets == null || !CheckSymSuffix(rhs, rhs.Length, syms, syms.Length)) return false;
            bool[]? under = rhs.Length < sets.Length ? sets[sets.Length - 1 - rhs.Length] : null;
            if (rhs.Length < sets.Length && under == null) return false;
            for (int x = 0; x < a.NState; x++)
            {
                Spec.Invariant(0 <= x && x <= a.NState && Shape(g, a, ann) && 0 <= σ && σ < a.NState && g.Rhs[r] == rhs && g.Lhs[r] == lhs &&
                               ann.States[σ] == sets && SymSuffix(rhs, rhs.Length, syms, syms.Length) && ann.Syms[σ] == syms &&
                               (rhs.Length < sets.Length ? under != null && sets[sets.Length - 1 - rhs.Length] == under : true));
                Spec.Invariant(rhs.Length < sets.Length
                    ? Spec.Forall(0, x, y => !In(under!, y) || a.Goto[y][lhs - g.NTerm] != -1)
                    : Spec.Forall(0, x, y => a.Goto[y][lhs - g.NTerm] != -1));
                int[]? gt = a.Goto[x];
                bool needed = under == null || x < under.Length && under[x];
                if (needed && gt![lhs - g.NTerm] == -1) return false;
            }
            return true;
        }

        public static bool CheckState(Grammar g, Automaton a, Annotations ann, int σ)
        {
            Spec.Requires(Shape(g, a, ann) && 0 <= σ && σ < a.NState);
            Spec.Ensures((bool r) => !r || StateOk(g, a, ann, σ));
            int[]? kinds = a.Kind[σ], args = a.Arg[σ], gotos = a.Goto[σ];
            for (int t = 0; t < g.NTerm; t++)
            {
                Spec.Invariant(0 <= t && t <= g.NTerm && Shape(g, a, ann) && a.Kind[σ] == kinds && a.Arg[σ] == args &&
                               Spec.Forall(0, t, u => ShiftOk(g, a, ann, σ, u) && ReduceOk(g, a, ann, σ, u) && AcceptOk(g, a, ann, σ, u)));
                int kind = kinds![t], arg = args![t];
                if (kind == Automaton.Shift)
                {
                    if (t == 0 || !CheckTrans(a, ann, σ, arg) || !Interpreter.Match(g, a.Incoming[arg], t)) return false;
                }
                else if (kind == Automaton.Reduce)
                {
                    if (!CheckRule(g, a, ann, σ, arg)) return false;
                }
                else if (kind == Automaton.Accept)
                {
                    bool[][]? sets = ann.States[σ];
                    if (σ == 0 || a.Incoming[σ] != g.Start || sets == null || sets.Length != 2) return false;
                    bool[]? bottom = sets[0];
                    if (bottom == null) return false;
                    for (int x = 0; x < bottom.Length; x++)
                    {
                        Spec.Invariant(0 <= x && x <= bottom.Length && Spec.Forall(0, x, y => !bottom[y] || y == 0));
                        if (x != 0 && bottom[x]) return false;
                    }
                }
                Spec.Assert(ShiftOk(g, a, ann, σ, t) && ReduceOk(g, a, ann, σ, t) && AcceptOk(g, a, ann, σ, t));
            }
            for (int x = 0; x < g.NSym - g.NTerm; x++)
            {
                Spec.Invariant(0 <= x && x <= g.NSym - g.NTerm && Shape(g, a, ann) && a.Goto[σ] == gotos &&
                               Spec.Forall(0, g.NTerm, u => ShiftOk(g, a, ann, σ, u) && ReduceOk(g, a, ann, σ, u) && AcceptOk(g, a, ann, σ, u)) &&
                               Spec.Forall(0, x, y => GotoOk(g, a, ann, σ, y)));
                int to = gotos![x];
                if (to != -1 && (!CheckTrans(a, ann, σ, to) || a.Incoming[to] != x + g.NTerm)) return false;
                Spec.Assert(GotoOk(g, a, ann, σ, x));
            }
            return true;
        }

        /// <summary>The safety validator: true only if the interpreter can reach no internal error (Parse's postcondition).</summary>
        public static bool Validate(Grammar g, Automaton a, Annotations ann)
        {
            Spec.Ensures((bool r) => !r || SafetyOk(g, a, ann));
            if (!CheckShape(g, a, ann)) return false;
            for (int σ = 0; σ < a.NState; σ++)
            {
                Spec.Invariant(0 <= σ && σ <= a.NState && Shape(g, a, ann) && Spec.Forall(0, σ, q => StateOk(g, a, ann, q)));
                if (!CheckState(g, a, ann, σ)) return false;
            }
            return true;
        }
    }
}
