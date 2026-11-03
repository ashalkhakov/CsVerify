// Lemon's grammar and automaton, as the verified interpreter and validators take them (lemon/Lr/DESIGN.md). This is
// not trusted: whatever it gets wrong, the validators find (or the interpreter's soundness covers).
using System.Text;
using CsVerify;

namespace CsLemon.Lr
{
    public static class Export
    {
        /// <summary>The start symbol, as FindActions takes it.</summary>
        private static Symbol StartSymbol(Lemon lemp)
        {
            Symbol? sp = lemp.start != null ? Tables.Symbol_find(lemp.start) : null;
            return sp ?? lemp.StartRule().lhs;
        }

        /// <summary>
        /// The number of a symbol: Lemon's (terminals first, then nonterminals, below nsymbol), or for a multiterminal
        /// (an A|B in a rule is not in Lemon's symbol table: its index is 0), nsymbol + k, the k-th distinct set of
        /// terminals (Lemon's same_symbol: two multiterminals with the same terminals are one symbol).
        /// </summary>
        private static int Number(Lemon lemp, Symbol sp, System.Collections.Generic.Dictionary<string, int> multis,
                                  System.Collections.Generic.List<int[]> members)
        {
            if (sp.type != SymbolType.MULTITERMINAL) return sp.index;
            var subs = new int[sp.nsubsym > 0 ? sp.nsubsym : 0];
            var key = new StringBuilder();
            for (int k = 0; k < subs.Length; k++)
            {
                Spec.Invariant(0 <= k);
                subs[k] = sp.Sub(k).index;
                key.Append(subs[k]).Append(',');
            }
            string name = key.ToString();
            if (multis.TryGetValue(name, out int known)) return known;
            int id = checked(lemp.nsymbol + members.Count);
            multis[name] = id;
            members.Add(subs);
            return id;
        }

        /// <summary>The grammar, and the symbol of each state's basis (the incoming symbol), numbered alike.</summary>
        public static Grammar GrammarOf(Lemon lemp, out int[] incoming, out int[][] syms)
        {
            int nrule = lemp.nrule, nsymbol = lemp.nsymbol, n = lemp.nstate;
            Checks.That(0 <= nrule && 0 <= nsymbol && 0 < n && n < int.MaxValue);
            var multis = new System.Collections.Generic.Dictionary<string, int>();
            var members = new System.Collections.Generic.List<int[]>();
            var lhs = new int[nrule];
            var rhs = new int[nrule][];
            for (Rule? rp = lemp.rule; rp != null; rp = rp.next)
            {
                Checks.That(0 <= rp.index && rp.index < nrule && 0 <= rp.nrhs); /* (rules are numbered 0 .. nrule-1) */
                lhs[rp.index] = rp.lhs.index;
                var right = new int[rp.nrhs];
                for (int i = 0; i < rp.nrhs; i++)
                {
                    Spec.Invariant(0 <= i && right.Length == rp.nrhs);
                    right[i] = Number(lemp, rp.Rhs(i), multis, members);
                }
                rhs[rp.index] = right;
            }
            /* the incoming symbol of state i: the one before the dot of a basis configuration (one more state: the
            ** accepting one, filled in by AutomatonOf) */
            incoming = new int[n + 1];
            incoming[0] = -1;
            /* the symbols under the dot of the state's longest basis configuration: every stack in the state ends so
            ** (the other basis configurations' are suffixes of it) */
            syms = new int[n + 1][];
            syms[0] = new int[0];
            for (int i = 1; i < n; i++)
            {
                Spec.Invariant(1 <= i && incoming.Length == n + 1 && syms.Length == n + 1);
                Config? longest = null;
                for (Config? bp = lemp.Sorted(i).bp; bp != null; bp = bp.bp)
                    if (longest == null || bp.dot > longest.dot) longest = bp;
                Checks.That(longest != null && 0 < longest.dot && longest.dot <= longest.rp.nrhs);
                var below = new int[longest!.dot];
                for (int k = 0; k < below.Length; k++)
                {
                    Spec.Invariant(0 <= k && below.Length == longest.dot && longest.dot <= longest.rp.nrhs);
                    below[k] = Number(lemp, longest.rp.Rhs(k), multis, members);
                }
                incoming[i] = below[below.Length - 1];
                syms[i] = below;
            }
            return new Grammar(lemp.nterminal, nsymbol, StartSymbol(lemp).index, lhs, rhs, members.ToArray());
        }

        /// <summary>
        /// The automaton after FindActions (conflicts resolved, tables not yet compressed): Lemon's states, and one
        /// more, the goto of state 0 on the start symbol (Lemon's ACCEPT entry), which accepts at the end of input.
        /// </summary>
        public static Automaton AutomatonOf(Lemon lemp, int[] incoming)
        {
            int n = lemp.nstate, nterm = lemp.nterminal, nnonterm = checked(lemp.nsymbol - lemp.nterminal);
            Checks.That(0 < n && n < int.MaxValue && 0 < nterm && 0 <= nnonterm && incoming.Length == n + 1);
            int acc = n;
            var kind = new int[n + 1][];
            var arg = new int[n + 1][];
            var gotos = new int[n + 1][];
            for (int i = 0; i <= n; i++)
            {
                Spec.Invariant(0 <= i && kind.Length == n + 1 && arg.Length == n + 1 && gotos.Length == n + 1 && incoming.Length == n + 1);
                kind[i] = new int[nterm];
                arg[i] = new int[nterm];
                var g = new int[nnonterm];
                for (int k = 0; k < nnonterm; k++)
                {
                    Spec.Invariant(0 <= k && g.Length == nnonterm);
                    g[k] = -1;
                }
                gotos[i] = g;
            }
            for (int i = 0; i < n; i++)
            {
                Spec.Invariant(0 <= i && kind.Length == n + 1 && arg.Length == n + 1 && gotos.Length == n + 1 && incoming.Length == n + 1);
                State stp = lemp.Sorted(i);
                Checks.That(stp.statenum == i); /* (before ResortStates, sorted[i] is state i) */
                int[]? ks = kind[i], args = arg[i], gs = gotos[i];
                Checks.That(ks != null && args != null && gs != null && ks.Length == nterm && args.Length == nterm && gs.Length == nnonterm);
                for (LemonAction? ap = stp.ap; ap != null; ap = ap.next)
                {
                    Spec.Invariant(ks != null && args != null && gs != null && ks.Length == nterm && args.Length == nterm && gs.Length == nnonterm);
                    int x = ap.sp.index;
                    switch (ap.type)
                    {
                        case ActionType.SHIFT:
                        {
                            State? to = ap.stp;
                            Checks.That(to != null);
                            if (0 <= x && x < nterm) { ks![x] = Automaton.Shift; args![x] = to!.statenum; }
                            else if (nterm <= x && x - nterm < nnonterm) gs![x - nterm] = to!.statenum;
                            break;
                        }
                        case ActionType.REDUCE:
                            if (0 <= x && x < nterm) { ks![x] = Automaton.Reduce; args![x] = ap.Rp().index; }
                            break;
                        case ActionType.ACCEPT:
                            if (nterm <= x && x - nterm < nnonterm) gs![x - nterm] = acc;
                            break;
                        case ActionType.ERROR:
                            if (0 <= x && x < nterm) ks![x] = Automaton.Reject;
                            break;
                        default:
                            break; /* (conflicts lost, and resolved-away actions, are not actions) */
                    }
                }
            }
            incoming[acc] = StartSymbol(lemp).index;
            int[]? acck = kind[acc];
            Checks.That(acck != null && acck.Length > 0);
            acck![0] = Automaton.Accept;
            return new Automaton(n + 1, incoming, kind, arg, gotos);
        }

        /// <summary>
        /// The safety annotations: the symbols (given, with the accepting state's: the start symbol), and the state
        /// sets, the least fixed point of "a transition from σ to σ2 puts σ's sets under σ2's own".
        /// </summary>
        public static Annotations AnnotationsOf(Grammar g, Automaton a, int[][] syms)
        {
            int n = a.NState;
            Checks.That(0 < n && syms.Length == n && a.Kind.Length == n && a.Arg.Length == n && a.Goto.Length == n && a.Incoming.Length == n);
            int acc = n - 1;
            syms[acc] = new int[] { g.Start };
            var states = new bool[n][][];
            for (int σ = 0; σ < n; σ++)
            {
                Spec.Invariant(0 <= σ && states.Length == n && syms.Length == n);
                int[]? sy = syms[σ];
                Checks.That(sy != null && sy.Length < int.MaxValue);
                var sets = new bool[sy!.Length + 1][];
                for (int k = 0; k < sets.Length; k++)
                {
                    Spec.Invariant(0 <= k);
                    sets[k] = new bool[n];
                }
                bool[]? own = sets[sets.Length - 1];
                Checks.That(own != null && σ < own.Length);
                own![σ] = true;
                states[σ] = sets;
            }
            bool changed = true;
            while (changed)
            {
                Spec.Invariant(states.Length == n && a.Kind.Length == n && a.Arg.Length == n && a.Goto.Length == n);
                changed = false;
                for (int σ = 0; σ < n; σ++)
                {
                    Spec.Invariant(0 <= σ && states.Length == n && a.Kind.Length == n && a.Arg.Length == n && a.Goto.Length == n);
                    int[]? kinds = a.Kind[σ], args = a.Arg[σ], gotos = a.Goto[σ];
                    Checks.That(kinds != null && args != null && gotos != null);
                    for (int t = 0; t < kinds!.Length && t < args!.Length; t++)
                    {
                        Spec.Invariant(0 <= t && states.Length == n);
                        if (kinds[t] == Automaton.Shift && Under(states, σ, args[t])) changed = true;
                    }
                    for (int x = 0; x < gotos!.Length; x++)
                    {
                        Spec.Invariant(0 <= x && states.Length == n);
                        if (gotos[x] != -1 && Under(states, σ, gotos[x])) changed = true;
                    }
                }
            }
            return new Annotations(syms, states);
        }

        /// <summary>Puts σ's state sets under σ2's own; whether that added anything.</summary>
        private static bool Under(bool[][][] states, int σ, int σ2)
        {
            if (σ < 0 || σ >= states.Length || σ2 < 0 || σ2 >= states.Length) return false;
            bool[][]? from = states[σ], to = states[σ2];
            if (from == null || to == null) return false;
            bool added = false;
            for (int j = 0; j < to.Length - 1 && j < from.Length; j++)
            {
                Spec.Invariant(0 <= j);
                bool[]? src = from[from.Length - 1 - j], dst = to[to.Length - 2 - j];
                if (src == null || dst == null) continue;
                for (int x = 0; x < src.Length && x < dst.Length; x++)
                {
                    Spec.Invariant(0 <= x);
                    if (src[x] && !dst[x]) { dst[x] = true; added = true; }
                }
            }
            return added;
        }

        /// <summary>CSLEMON_VALIDATE: runs the safety validator on the automaton, and says whether it passed.</summary>
        public static void ValidateAll(Lemon lemp)
        {
            var g = GrammarOf(lemp, out int[] incoming, out int[][] syms);
            var a = AutomatonOf(lemp, incoming);
            var ann = AnnotationsOf(g, a, syms);
            System.Console.Out.Write(Safety.Validate(g, a, ann) ? "safety: validated\n" : "safety: NOT validated\n");
            if (System.Environment.GetEnvironmentVariable("CSLEMON_VALIDATE") != "mutate") return;
            /* corrupt one entry at a time (a shift's target, a reduce's rule, a goto), and count the corruptions the
            ** validator rejects: one that keeps the automaton safe (another target with the same past) is no failure,
            ** so this reports, not asserts */
            int tried = 0, rejected = 0;
            for (int σ = 0; σ < a.NState && σ < a.Kind.Length && σ < a.Arg.Length && σ < a.Goto.Length && tried < 300; σ++)
            {
                Spec.Invariant(0 <= σ && 0 <= tried && 0 <= rejected && rejected <= tried);
                int[]? kinds = a.Kind[σ], args = a.Arg[σ], gotos = a.Goto[σ];
                if (kinds == null || args == null || gotos == null) continue;
                for (int t = 0; t < kinds.Length && t < args.Length && tried < 300; t++)
                {
                    Spec.Invariant(0 <= t && 0 <= tried && 0 <= rejected && rejected <= tried);
                    if (kinds[t] != Automaton.Shift && kinds[t] != Automaton.Reduce) continue;
                    int saved = args[t];
                    args[t] = Next(saved, kinds[t] == Automaton.Shift ? a.NState : g.Lhs.Length);
                    var ann2 = AnnotationsOf(g, a, Copy(syms));
                    tried++;
                    if (!Safety.Validate(g, a, ann2)) rejected++;
                    args[t] = saved;
                }
                for (int x = 0; x < gotos.Length && tried < 300; x++)
                {
                    Spec.Invariant(0 <= x && 0 <= tried && 0 <= rejected && rejected <= tried);
                    if (gotos[x] == -1) continue;
                    int saved = gotos[x];
                    gotos[x] = -1;
                    var ann2 = AnnotationsOf(g, a, Copy(syms));
                    tried++;
                    if (!Safety.Validate(g, a, ann2)) rejected++;
                    gotos[x] = saved;
                }
            }
            System.Console.Out.Write("mutations rejected: " + rejected + " of " + tried + "\n");
        }

        /// <summary>The next number below n after v, round to 0.</summary>
        private static int Next(int v, int n) => 0 <= v && v < n && v + 1 < n ? v + 1 : 0;

        private static int[][] Copy(int[][] xs)
        {
            var ys = new int[xs.Length][];
            for (int i = 0; i < xs.Length; i++)
            {
                Spec.Invariant(0 <= i && ys.Length == xs.Length);
                int[]? x = xs[i];
                ys[i] = x == null ? new int[0] : (int[])x.Clone();
            }
            return ys;
        }

        /// <summary>
        /// CSLEMON_PARSE=file: runs the verified interpreter on the terminals named in the file (whitespace-separated)
        /// and prints the outcome to stdout, the parse tree as nested (lhs ...) lists.
        /// </summary>
        public static void ParseFile(Lemon lemp, string file)
        {
            var g = GrammarOf(lemp, out int[] incoming, out int[][] syms);
            var a = AutomatonOf(lemp, incoming);
            var ann = AnnotationsOf(g, a, syms);
            bool safe = Safety.Validate(g, a, ann);
            string[] names = System.IO.File.ReadAllText(file).Split(new[] { ' ', '\t', '\n', '\r' }, System.StringSplitOptions.RemoveEmptyEntries);
            var w = new int[names.Length];
            for (int i = 0; i < names.Length; i++)
            {
                Spec.Invariant(0 <= i && w.Length == names.Length);
                string? name = names[i];
                Symbol? sp = name != null ? Tables.Symbol_find(name) : null;
                w[i] = sp != null && sp.index < lemp.nterminal ? sp.index : -1;
            }
            Result r = Interpreter.Parse(g, a, w, 10000000, Ghost.Of(ann));
            var sb = new StringBuilder();
            sb.Append(safe ? "(safe) " : "(NOT validated safe) ");
            switch (r)
            {
                case Result.Accepted acc:
                    sb.Append("accepted ").Append(acc.Consumed).Append(" of ").Append(w.Length).Append(": ");
                    Show(lemp, acc.T, sb);
                    break;
                case Result.Rejected rej:
                    sb.Append("rejected at ").Append(rej.At);
                    break;
                case Result.OutOfFuel _:
                    sb.Append("out of fuel");
                    break;
                default:
                    sb.Append("internal error");
                    break;
            }
            System.Console.Out.Write(sb.Append('\n').ToString());
        }

        private static void Show(Lemon lemp, Tree t, StringBuilder sb)
        {
            Spec.Decreases(t);
            if (t is Tree.Leaf l)
            {
                sb.Append(0 <= l.Term && l.Term < lemp.symbols.Length ? lemp.Sym(l.Term).name : "?");
                return;
            }
            if (t is Tree.Node n)
            {
                sb.Append('(').Append(LhsName(lemp, n.Rule));
                ShowAll(lemp, n.Kids, sb);
                sb.Append(')');
            }
        }

        private static void ShowAll(Lemon lemp, Forest ts, StringBuilder sb)
        {
            Spec.Decreases(ts);
            if (ts is Forest.Cons c)
            {
                sb.Append(' ');
                Show(lemp, c.Head, sb);
                ShowAll(lemp, c.Tail, sb);
            }
        }

        private static string LhsName(Lemon lemp, int r)
        {
            for (Rule? rp = lemp.rule; rp != null; rp = rp.next)
                if (rp.index == r) return rp.lhs.name;
            return "?";
        }
    }
}
