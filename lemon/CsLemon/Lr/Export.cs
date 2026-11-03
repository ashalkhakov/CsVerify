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
        public static Grammar GrammarOf(Lemon lemp, out int[] incoming)
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
                var syms = new int[rp.nrhs];
                for (int i = 0; i < rp.nrhs; i++)
                {
                    Spec.Invariant(0 <= i && syms.Length == rp.nrhs);
                    syms[i] = Number(lemp, rp.Rhs(i), multis, members);
                }
                rhs[rp.index] = syms;
            }
            /* the incoming symbol of state i: the one before the dot of a basis configuration (one more state: the
            ** accepting one, filled in by AutomatonOf) */
            incoming = new int[n + 1];
            incoming[0] = -1;
            for (int i = 1; i < n; i++)
            {
                Spec.Invariant(1 <= i && incoming.Length == n + 1);
                Config? bp = lemp.Sorted(i).bp;
                Checks.That(bp != null && 0 < bp.dot && bp.dot <= bp.rp.nrhs);
                incoming[i] = Number(lemp, bp!.rp.Rhs(bp.dot - 1), multis, members);
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
        /// CSLEMON_PARSE=file: runs the verified interpreter on the terminals named in the file (whitespace-separated)
        /// and prints the outcome to stdout, the parse tree as nested (lhs ...) lists.
        /// </summary>
        public static void ParseFile(Lemon lemp, string file)
        {
            var g = GrammarOf(lemp, out int[] incoming);
            var a = AutomatonOf(lemp, incoming);
            string[] names = System.IO.File.ReadAllText(file).Split(new[] { ' ', '\t', '\n', '\r' }, System.StringSplitOptions.RemoveEmptyEntries);
            var w = new int[names.Length];
            for (int i = 0; i < names.Length; i++)
            {
                Spec.Invariant(0 <= i && w.Length == names.Length);
                string? name = names[i];
                Symbol? sp = name != null ? Tables.Symbol_find(name) : null;
                w[i] = sp != null && sp.index < lemp.nterminal ? sp.index : -1;
            }
            Result r = Interpreter.Parse(g, a, w, 10000000);
            var sb = new StringBuilder();
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
