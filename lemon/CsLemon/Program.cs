// Main program file for the LEMON parser generator (main.c), with the command-line options of option.c.
using System.Collections.Generic;
using CsVerify;

namespace CsLemon
{
    public static class Program
    {
        /// <summary>The -D options: macros for %ifdef.</summary>
        public static readonly List<string> azDefine = new List<string>();

        /// <summary>The -d option: the output directory (null for the input's).</summary>
        public static string? outputDir;

        /// <summary>The -T option: the template file.</summary>
        public static string? user_templatename;

        /// <summary>The -p option: show conflicts resolved by precedence rules.</summary>
        public static bool showPrecedenceConflict;

        private static void handle_D_option(string z)
        {
            int eq = z.IndexOf('=');
            azDefine.Add(eq >= 0 ? z.Substring(0, eq) : z);
        }

        /// <summary>Merge together two lists of rules ordered by rule.iRule.</summary>
        private static Rule? Rule_merge(Rule? pA, Rule? pB)
        {
            Rule? pFirst = null, last = null;
            while (pA != null && pB != null)
            {
                Rule pick;
                if (pA.iRule < pB.iRule) { pick = pA; pA = pA.next; }
                else { pick = pB; pB = pB.next; }
                if (last == null) pFirst = pick; else last.next = pick;
                last = pick;
            }
            Rule? rest = pA != null ? pA : pB;
            if (last == null) pFirst = rest; else last.next = rest;
            return pFirst;
        }

        /// <summary>Sort a list of rules in order of increasing iRule value.</summary>
        private static Rule? Rule_sort(Rule? rp)
        {
            var x = new Rule?[32];
            while (rp != null)
            {
                Spec.Invariant(x.Length == 32);
                Rule? pNext = rp.next;
                rp.next = null;
                int i;
                for (i = 0; i < x.Length - 1 && x[i] != null; i++)
                {
                    Spec.Invariant(0 <= i && i < x.Length && x.Length == 32);
                    rp = Rule_merge(x[i], rp);
                    x[i] = null;
                }
                x[i] = rp;
                rp = pNext;
            }
            rp = null;
            for (int i = 0; i < x.Length; i++)
            {
                Spec.Invariant(0 <= i);
                rp = Rule_merge(x[i], rp);
            }
            return rp;
        }

        /// <summary>Print a single line of the "Parser Stats" output.</summary>
        private static void stats_line(string zLabel, int iValue)
        {
            int nLabel = zLabel.Length;
            string dots = "................................";
            int nDots = 35 - nLabel;
            if (nDots < 0) nDots = 0;
            if (nDots > dots.Length) nDots = dots.Length;
            System.Console.Out.Write("  " + zLabel + dots.Substring(0, nDots) + " " + iValue.ToString().PadLeft(5) + "\n");
        }

        // ---- option.c, for Lemon's own options

        private sealed class Opt
        {
            public string label = "";
            public bool isFlag;   // OPT_FLAG, else OPT_FSTR
            public bool ignored;  // arg == 0 in C
            public string message = "";
        }

        private static readonly Opt[] options = new Opt[]
        {
            new Opt { label = "b", isFlag = true, message = "Print only the basis in report." },
            new Opt { label = "c", isFlag = true, message = "Don't compress the action table." },
            new Opt { label = "d", message = "Output directory.  Default '.'" },
            new Opt { label = "D", message = "Define an %ifdef macro." },
            new Opt { label = "E", isFlag = true, message = "Print input file after preprocessing." },
            new Opt { label = "f", ignored = true, message = "Ignored.  (Placeholder for -f compiler options.)" },
            new Opt { label = "g", isFlag = true, message = "Print grammar without actions." },
            new Opt { label = "I", ignored = true, message = "Ignored.  (Placeholder for '-I' compiler options.)" },
            new Opt { label = "m", isFlag = true, message = "Output a makeheaders compatible file." },
            new Opt { label = "l", isFlag = true, message = "Do not print #line statements." },
            new Opt { label = "O", ignored = true, message = "Ignored.  (Placeholder for '-O' compiler options.)" },
            new Opt { label = "p", isFlag = true, message = "Show conflicts resolved by precedence rules" },
            new Opt { label = "q", isFlag = true, message = "(Quiet) Don't print the report file." },
            new Opt { label = "r", isFlag = true, message = "Do not sort or renumber states" },
            new Opt { label = "s", isFlag = true, message = "Print parser stats to standard output." },
            new Opt { label = "S", isFlag = true, message = "Generate the *.sql file describing the parser tables." },
            new Opt { label = "x", isFlag = true, message = "Print the version number." },
            new Opt { label = "T", message = "Specify a template file." },
            new Opt { label = "W", ignored = true, message = "Ignored.  (Placeholder for '-W' compiler options.)" },
        };

        private static readonly Dictionary<string, bool> flags = new Dictionary<string, bool>();

        /// <summary>The i-th option (the table is full).</summary>
        private static Opt Option(int i)
        {
            Checks.That(0 <= i && i < options.Length && options[i] != null);
            return options[i];
        }

        private static bool Flag(string label) => flags.TryGetValue(label, out bool v) && v;

        private static bool ISOPT(string x) => x.Length > 0 && (x[0] == '-' || x[0] == '+' || x.IndexOf('=') >= 0);

        private static void OptPrint()
        {
            int max = 0;
            for (int i = 0; i < options.Length; i++)
            {
                int len = checked(Option(i).label.Length + 1);
                if (!Option(i).isFlag) len = checked(len + 8); // length of "<string>"
                if (len > max) max = len;
            }
            var err = System.Console.Error;
            for (int i = 0; i < options.Length; i++)
            {
                Opt o = Option(i);
                if (o.isFlag)
                    err.Write("  -" + o.label.PadRight(max) + "  " + o.message + "\n");
                else
                    err.Write("  -" + o.label + "<string>" + new string(' ', System.Math.Max(0, checked(max - o.label.Length - 8))) + "  " + o.message + "\n");
            }
        }

        /// <summary>OptInit: the switches (as in option.c, "-x" sets, "+x" clears, "-dDIR" passes DIR); the non-switch arguments.</summary>
        private static List<string> OptInit(string[] argv)
        {
            int errcnt = 0;
            var args = new List<string>();
            bool dashdash = false;
            for (int i = 0; i < argv.Length; i++)
            {
                Spec.Invariant(0 <= i);
                string? ai = argv[i];
                Checks.That(ai != null); /* (C's argv holds strings) */
                string a = ai!;
                if (!dashdash && a.Length > 0 && (a[0] == '-' || a[0] == '+'))
                {
                    int j;
                    for (j = 0; j < options.Length; j++)
                    {
                        Spec.Invariant(0 <= j);
                        if (a.Length - 1 >= Option(j).label.Length && string.CompareOrdinal(a, 1, Option(j).label, 0, Option(j).label.Length) == 0) break;
                    }
                    bool v = a[0] == '-';
                    if (j == options.Length)
                    {
                        System.Console.Error.Write("Command line syntax error: undefined option.\n");
                        errcnt = checked(errcnt + 1);
                    }
                    else if (Option(j).ignored) { }
                    else if (Option(j).isFlag) flags[Option(j).label] = v;
                    else
                    {
                        string arg = a.Substring(2);
                        if (Option(j).label == "d") outputDir = arg;
                        else if (Option(j).label == "D") handle_D_option(arg);
                        else if (Option(j).label == "T") user_templatename = arg;
                    }
                }
                else if (!dashdash && a.IndexOf('=') >= 0)
                {
                    System.Console.Error.Write("Command line syntax error: undefined option.\n");
                    errcnt = checked(errcnt + 1);
                }
                else args.Add(a);
                if (a == "--") dashdash = true;
            }
            if (errcnt > 0)
            {
                System.Console.Error.Write("Valid command line options for \"lemon\" are:\n");
                OptPrint();
                System.Environment.Exit(1);
            }
            return args;
        }

        /// <summary>A symbol named with a capital: a terminal.</summary>
        private static bool StartsUpper(Symbol sp) => sp.name.Length > 0 && Chars.ISUPPER(sp.name[0]);

        /// <summary>The main program.  Parse the command line and do it...</summary>
        public static int Main(string[] argv)
        {
            var args = OptInit(argv);
            if (Flag("x"))
            {
                System.Console.Out.Write("Lemon version 1.0\n");
                return 0;
            }
            if (args.Count != 1)
            {
                System.Console.Error.Write("Exactly one filename argument is required.\n");
                return 1;
            }
            showPrecedenceConflict = Flag("p");
            var lem = new Lemon();
            lem.errorcnt = 0;

            /* Initialize the machine */
            Tables.Symbol_init();
            Tables.State_init();
            lem.argv0 = "lemon";
            lem.filename = args[0];
            lem.basisflag = Flag("b");
            lem.nolinenosflag = Flag("l");
            lem.printPreprocessed = Flag("E");
            Tables.Symbol_new("$");

            /* Parse the input file */
            Parser.Parse(lem);
            if (lem.printPreprocessed || lem.errorcnt != 0) return lem.errorcnt;
            if (lem.nrule == 0)
            {
                System.Console.Error.Write("Empty grammar.\n");
                return 1;
            }
            lem.errsym = Tables.Symbol_find("error");

            /* Count and index the symbols of the grammar */
            Tables.Symbol_new("{default}");
            lem.nsymbol = Tables.Symbol_count();
            lem.symbols = Tables.Symbol_arrayof();
            int i;
            for (i = 0; i < lem.nsymbol; i++)
            {
                Spec.Invariant(0 <= i);
                lem.Sym(i).index = i;
            }
            System.Array.Sort(lem.symbols, Tables.Symbolcmpp);
            for (i = 0; i < lem.nsymbol; i++)
            {
                Spec.Invariant(0 <= i);
                lem.Sym(i).index = i;
            }
            while (lem.Sym(i - 1).type == SymbolType.MULTITERMINAL)
            {
                Spec.Invariant(0 <= i);
                i--;
            }
            lem.nsymbol = i - 1;
            /* (C reads name[0] of "" as the terminating '\0') */
            for (i = 1; StartsUpper(lem.Sym(i)); i++)
            {
                Spec.Invariant(1 <= i);
            }
            lem.nterminal = i;

            /* Assign sequential rule numbers.  Start with 0.  Put rules that have no reduce action C-code associated
            ** with them last, so that the switch() statement that selects reduction actions will have a smaller
            ** jump table. */
            Rule? rp;
            for (i = 0, rp = lem.rule; rp != null; rp = rp.next)
                rp.iRule = rp.code != null ? checked(i++) : -1;
            lem.nruleWithAction = i;
            for (rp = lem.rule; rp != null; rp = rp.next)
                if (rp.iRule < 0) rp.iRule = checked(i++);
            lem.startRule = lem.rule;
            lem.rule = Rule_sort(lem.rule);

            /* Generate a reprint of the grammar, if requested on the command line */
            if (Flag("g"))
            {
                Report.Reprint(lem);
            }
            else
            {
                /* Initialize the size for all follow and first sets */
                Sets.SetSize(lem.nterminal + 1);
                /* Find the precedence for every production rule (that has one) */
                Build.FindRulePrecedences(lem);
                /* Compute the lambda-nonterminals and the first-sets for every nonterminal */
                Build.FindFirstSets(lem);
                /* Compute all LR(0) states.  Also record follow-set propagation links so that the follow-set can be
                ** computed later */
                lem.nstate = 0;
                Build.FindStates(lem);
                lem.sorted = Tables.State_arrayof();
                /* Tie up loose ends on the propagation links */
                Build.FindLinks(lem);
                /* Compute the follow set of every reducible configuration */
                Build.FindFollowSets(lem);
                /* Compute the action tables */
                Build.FindActions(lem);
                /* (testing the verified LR interpreter: CSLEMON_PARSE names a file of terminals to parse) */
                string? parseFile = System.Environment.GetEnvironmentVariable("CSLEMON_PARSE");
                if (parseFile != null) Lr.Export.ParseFile(lem, parseFile);
                /* Compress the action tables */
                if (!Flag("c")) Report.CompressTables(lem);
                /* Reorder and renumber the states so that states with fewer choices occur at the end. */
                if (!Flag("r")) Report.ResortStates(lem);
                /* Generate a report of the parser generated.  (the "y.output" file) */
                if (!Flag("q")) Report.ReportOutput(lem);
                /* Generate the source code for the parser */
                Report.ReportTable(lem, Flag("m"), Flag("S"));
                /* Produce a header file for use by the scanner.  (This step is omitted if the "-m" option is used
                ** because makeheaders will generate the file for us.) */
                if (!Flag("m")) Report.ReportHeader(lem);
            }
            if (Flag("s"))
            {
                System.Console.Out.Write("Parser statistics:\n");
                stats_line("terminal symbols", lem.nterminal);
                stats_line("non-terminal symbols", checked(lem.nsymbol - lem.nterminal));
                stats_line("total symbols", lem.nsymbol);
                stats_line("rules", lem.nrule);
                stats_line("states", lem.nxstate);
                stats_line("conflicts", lem.nconflict);
                stats_line("action table entries", lem.nactiontab);
                stats_line("lookahead table entries", lem.nlookaheadtab);
                stats_line("total table size (bytes)", lem.tablesize);
            }
            if (lem.nconflict > 0)
                System.Console.Error.Write(lem.nconflict + " parsing conflicts.\n");

            /* return 0 on success, 1 on failure. */
            return (lem.errorcnt > 0 || lem.nconflict > 0) ? 1 : 0;
        }
    }
}
