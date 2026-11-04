// Procedures for generating reports and tables in the LEMON parser generator (report.c).
// C's printf formats are written out explicitly (D, Rj, Lj below); every file is written byte for byte as
// Latin-1 (one char per byte, as C copies bytes), with "\n" line endings.
using System.IO;
using System.Text;
using CsVerify;

namespace CsLemon
{
    public static class Report
    {
        private const int LINESIZE = 1000;

        /// <summary>ap->x.stp of a shift action (SHIFT, SSCONFLICT, SH_RESOLVED): every such action has its new state.</summary>
        private static State Stp(LemonAction ap)
        {
            Checks.That(ap.stp != null);
            return ap.stp!;
        }

        /// <summary>lemp->outname, named by file_open before any output is written.</summary>
        private static string OutName(Lemon lemp)
        {
            Checks.That(lemp.outname != null);
            return lemp.outname!;
        }

        // ---- printf helpers: %d, %Nd / %Ns (right-justified), %-Nd / %-Ns (left-justified)

        private static string D(int v)
        {
            /* (written out by hand: the verifier takes the library's formatting, which is handed a culture, for code
            ** that may change anything) */
            long x = v;
            bool neg = x < 0;
            if (neg) x = -x;
            var sb = new StringBuilder();
            do
            {
                Spec.Invariant(0 <= x);
                sb.Insert(0, (char)('0' + (int)(x % 10)));
                x /= 10;
            } while (x > 0);
            if (neg) sb.Insert(0, '-');
            return sb.ToString();
        }

        /// <summary>%*s: right-justify s in a field of width w (never truncates).</summary>
        private static string Rj(string s, int w)
        {
            Spec.Requires(w > int.MinValue);
            if (w < 0) return s.PadRight(-w);
            return s.PadLeft(w);
        }

        /// <summary>%-*s: left-justify s in a field of width w (never truncates).</summary>
        private static string Lj(string s, int w)
        {
            Spec.Requires(w > int.MinValue);
            if (w < 0) w = -w;
            return s.PadRight(w);
        }

        /// <summary>A FILE* opened for reading: fgets and fgetc over the file's bytes (Latin-1, one char per byte).</summary>
        private sealed class CReader
        {
            private readonly string data;
            private int pos;

            public CReader(byte[] bytes)
            {
                data = Encoding.Latin1.GetString(bytes);
                pos = 0;
            }

            /// <summary>fgets(buf, size): up to size-1 chars, through the first newline. Null at end of file.
            /// The result is cut at an embedded NUL, as C's string functions see it.</summary>
            public string? fgets(int size)
            {
                Spec.Requires(size > 0);
                if (pos < 0 || pos >= data.Length) return null; /* (pos is never negative) */
                int start = pos;
                int n = 0;
                while (pos < data.Length && n < size - 1)
                {
                    Spec.Invariant(0 <= start && start <= pos && pos <= data.Length && 0 <= n);
                    char c = data[pos];
                    pos++;
                    n++;
                    if (c == '\n') break;
                }
                string line = data.Substring(start, pos - start);
                int z = line.IndexOf('\0');
                if (z >= 0) line = line.Substring(0, z);
                return line;
            }

            /// <summary>fgetc: the next byte, or -1 (EOF).</summary>
            public int fgetc()
            {
                if (pos < 0 || pos >= data.Length) return -1; /* (pos is never negative) */
                int c = data[pos];
                pos++;
                return c;
            }
        }

        // (the writer disposes the stream it is given: so does whoever disposes the writer)
        private static TextWriter NewWriter([TakesOwnership] Stream s)
        {
            return new StreamWriter(s, Encoding.Latin1);
        }

        /// <summary>access(path, mode): the file exists.</summary>
        private static bool access(string path)
        {
            return File.Exists(path) || Directory.Exists(path);
        }

        private static CReader? fopen_read(string path)
        {
            try
            {
                byte[] bytes = File.ReadAllBytes(path);
                return new CReader(bytes);
            }
            catch (System.Exception)
            {
                return null;
            }
        }

        /* Generate a filename with the given suffix. */
        private static string file_makename(Lemon lemp, string suffix)
        {
            string filename = lemp.filename;
            string name;
            int cp;

            if (Program.outputDir != null)
            {
                cp = filename.LastIndexOf('/');
                if (cp >= 0) filename = filename.Substring(checked(cp + 1));
            }
            name = "";
            if (Program.outputDir != null)
            {
                name = Program.outputDir + "/";
            }
            name = name + filename;
            cp = name.LastIndexOf('.');
            if (cp >= 0) name = name.Substring(0, cp);
            name = name + suffix;
            return name;
        }

        /* Open a file with a name based on the name of the input file,
        ** but with a different (specified) suffix, and return a pointer
        ** to the stream */
        private static FileStream? file_open(Lemon lemp, string suffix, string mode)
        {
            Spec.Requires(mode.Length > 0);
            FileStream? fp;

            lemp.outname = file_makename(lemp, suffix);
            try
            {
                if (mode[0] == 'w')
                {
                    fp = new FileStream(lemp.outname, FileMode.Create, FileAccess.Write);
                }
                else
                {
                    fp = new FileStream(lemp.outname, FileMode.Open, FileAccess.Read);
                }
            }
            catch (System.Exception)
            {
                fp = null;
            }
            if (fp == null && mode[0] == 'w')
            {
                System.Console.Error.Write("Can't open file \"" + lemp.outname + "\".\n");
                lemp.errorcnt = checked(lemp.errorcnt + 1);
                return null;
            }
            return fp;
        }

        /* Print the text of a rule */
        public static void rule_print(TextWriter @out, Rule rp)
        {
            int i, j;
            @out.Write(rp.lhs.name);
            /*    if( rp->lhsalias ) fprintf(out,"(%s)",rp->lhsalias); */
            @out.Write(" ::=");
            for (i = 0; i < rp.nrhs; i++)
            {
                Symbol sp = rp.Rhs(i);
                if (sp.type == SymbolType.MULTITERMINAL)
                {
                    @out.Write(" " + sp.Sub(0).name);
                    for (j = 1; j < sp.nsubsym; j++)
                    {
                        @out.Write("|" + sp.Sub(j).name);
                    }
                }
                else
                {
                    @out.Write(" " + sp.name);
                }
                /* if( rp->rhsalias[i] ) fprintf(out,"(%s)",rp->rhsalias[i]); */
            }
        }

        /* Duplicate the input file without comments and without actions
        ** on rules */
        public static void Reprint(Lemon lemp)
        {
            Rule? rp;
            Symbol sp;
            int i, j, maxlen, len, ncolumns, skip;
            TextWriter stdout = NewWriter(System.Console.OpenStandardOutput());
            stdout.Write("// Reprint of input file \"" + lemp.filename + "\".\n// Symbols:\n");
            maxlen = 10;
            for (i = 0; i < lemp.nsymbol; i++)
            {
                Spec.Invariant(0 <= i && maxlen >= 10);
                sp = lemp.Sym(i);
                len = sp.name.Length;
                if (len > maxlen) maxlen = len;
            }
            ncolumns = 76 / checked(maxlen + 5);
            if (ncolumns < 1) ncolumns = 1;
            skip = checked(lemp.nsymbol + ncolumns - 1) / ncolumns;
            for (i = 0; i < skip; i++)
            {
                Spec.Invariant(0 <= i && maxlen >= 10);
                stdout.Write("//");
                for (j = i; j < lemp.nsymbol; j = checked(j + skip))
                {
                    Spec.Invariant(0 <= j);
                    sp = lemp.Sym(j);
                    /* assert( sp->index==j ); */
                    string nm = sp.name.Length > maxlen ? sp.name.Substring(0, maxlen) : sp.name;
                    stdout.Write(" " + Rj(D(j), 3) + " " + Lj(nm, maxlen));
                }
                stdout.Write("\n");
            }
            for (rp = lemp.rule; rp != null; rp = rp.next)
            {
                rule_print(stdout, rp);
                stdout.Write(".");
                if (rp.precsym != null) stdout.Write(" [" + rp.precsym.name + "]");
                /* if( rp->code ) printf("\n    %s",rp->code); */
                stdout.Write("\n");
            }
            stdout.Flush();
        }

        /* Print a single rule. */
        public static void RulePrint(TextWriter fp, Rule rp, int iCursor)
        {
            Symbol sp;
            int i, j;
            fp.Write(rp.lhs.name + " ::=");
            for (i = 0; i <= rp.nrhs; i++)
            {
                if (i == iCursor) fp.Write(" *");
                if (i == rp.nrhs) break;
                sp = rp.Rhs(i);
                if (sp.type == SymbolType.MULTITERMINAL)
                {
                    fp.Write(" " + sp.Sub(0).name);
                    for (j = 1; j < sp.nsubsym; j++)
                    {
                        fp.Write("|" + sp.Sub(j).name);
                    }
                }
                else
                {
                    fp.Write(" " + sp.name);
                }
            }
        }

        /* Print the rule for a configuration. */
        public static void ConfigPrint(TextWriter fp, Config cfp)
        {
            RulePrint(fp, cfp.rp, cfp.dot);
        }

        /* (SetPrint and PlinkPrint are under "#if 0" in C, and are not ported.) */

        /* Print an action to the given file descriptor.  Return FALSE if
        ** nothing was actually printed.
        */
        public static bool PrintAction(
          LemonAction ap,             /* The action to print */
          TextWriter fp,              /* Print the action here */
          int indent                  /* Indent by this amount */
        )
        {
            Spec.Requires(indent > int.MinValue);
            bool result = true;
            switch (ap.type)
            {
                case ActionType.SHIFT:
                    {
                        State stp = Stp(ap);
                        fp.Write(Rj(ap.sp.name, indent) + " shift        " + Lj(D(stp.statenum), 7));
                        break;
                    }
                case ActionType.REDUCE:
                    {
                        Rule rp = ap.Rp();
                        fp.Write(Rj(ap.sp.name, indent) + " reduce       " + Lj(D(rp.iRule), 7));
                        RulePrint(fp, rp, -1);
                        break;
                    }
                case ActionType.SHIFTREDUCE:
                    {
                        Rule rp = ap.Rp();
                        fp.Write(Rj(ap.sp.name, indent) + " shift-reduce " + Lj(D(rp.iRule), 7));
                        RulePrint(fp, rp, -1);
                        break;
                    }
                case ActionType.ACCEPT:
                    fp.Write(Rj(ap.sp.name, indent) + " accept");
                    break;
                case ActionType.ERROR:
                    fp.Write(Rj(ap.sp.name, indent) + " error");
                    break;
                case ActionType.SRCONFLICT:
                case ActionType.RRCONFLICT:
                    fp.Write(Rj(ap.sp.name, indent) + " reduce       " + Lj(D(ap.Rp().iRule), 7) + " ** Parsing conflict **");
                    break;
                case ActionType.SSCONFLICT:
                    fp.Write(Rj(ap.sp.name, indent) + " shift        " + Lj(D(Stp(ap).statenum), 7) + " ** Parsing conflict **");
                    break;
                case ActionType.SH_RESOLVED:
                    if (Program.showPrecedenceConflict)
                    {
                        fp.Write(Rj(ap.sp.name, indent) + " shift        " + Lj(D(Stp(ap).statenum), 7) + " -- dropped by precedence");
                    }
                    else
                    {
                        result = false;
                    }
                    break;
                case ActionType.RD_RESOLVED:
                    if (Program.showPrecedenceConflict)
                    {
                        fp.Write(Rj(ap.sp.name, indent) + " reduce " + Lj(D(ap.Rp().iRule), 7) + " -- dropped by precedence");
                    }
                    else
                    {
                        result = false;
                    }
                    break;
                case ActionType.NOT_USED:
                    result = false;
                    break;
            }
            if (result && ap.spOpt != null)
            {
                fp.Write("  /* because " + ap.sp.name + "==" + ap.spOpt.name + " */");
            }
            return result;
        }

        /* Generate the "*.out" log file */
        public static void ReportOutput(Lemon lemp)
        {
            int i, n;
            State stp;
            Config? cfp;
            LemonAction? ap;
            Rule? rp;
            FileStream? fs;
            TextWriter fp;

            fs = file_open(lemp, ".out", "wb");
            if (fs == null) return;
            fp = NewWriter(fs);
            for (i = 0; i < lemp.nxstate; i++)
            {
                stp = lemp.Sorted(i);
                fp.Write("State " + D(stp.statenum) + ":\n");
                if (lemp.basisflag) cfp = stp.bp;
                else cfp = stp.cfp;
                while (cfp != null)
                {
                    if (cfp.dot == cfp.rp.nrhs)
                    {
                        string buf = "(" + D(cfp.rp.iRule) + ")";
                        fp.Write("    " + Rj(buf, 5) + " ");
                    }
                    else
                    {
                        fp.Write("          ");
                    }
                    ConfigPrint(fp, cfp);
                    fp.Write("\n");
                    if (lemp.basisflag) cfp = cfp.bp;
                    else cfp = cfp.next;
                }
                fp.Write("\n");
                for (ap = stp.ap; ap != null; ap = ap.next)
                {
                    if (PrintAction(ap, fp, 30)) fp.Write("\n");
                }
                fp.Write("\n");
            }
            fp.Write("----------------------------------------------------\n");
            fp.Write("Symbols:\n");
            fp.Write("The first-set of non-terminals is shown after the name.\n\n");
            for (i = 0; i < lemp.nsymbol; i++)
            {
                int j;
                Symbol sp;

                sp = lemp.Sym(i);
                fp.Write("  " + Rj(D(i), 3) + ": " + sp.name);
                if (sp.type == SymbolType.NONTERMINAL)
                {
                    fp.Write(":");
                    if (sp.lambda)
                    {
                        fp.Write(" <lambda>");
                    }
                    for (j = 0; j < lemp.nterminal; j++)
                    {
                        if (sp.firstset != null && Sets.SetFind(sp.firstset, j))
                        {
                            fp.Write(" " + lemp.Sym(j).name);
                        }
                    }
                }
                if (sp.prec >= 0) fp.Write(" (precedence=" + D(sp.prec) + ")");
                fp.Write("\n");
            }
            fp.Write("----------------------------------------------------\n");
            fp.Write("Syntax-only Symbols:\n");
            fp.Write("The following symbols never carry semantic content.\n\n");
            for (i = n = 0; i < lemp.nsymbol; i++)
            {
                int w;
                Symbol sp = lemp.Sym(i);
                if (sp.bContent) continue;
                w = sp.name.Length;
                if (n > 0 && checked(n + w) > 75)
                {
                    fp.Write("\n");
                    n = 0;
                }
                if (n > 0)
                {
                    fp.Write(" ");
                    n++;
                }
                fp.Write(sp.name);
                n += w;
            }
            if (n > 0) fp.Write("\n");
            fp.Write("----------------------------------------------------\n");
            fp.Write("Rules:\n");
            for (rp = lemp.rule; rp != null; rp = rp.next)
            {
                fp.Write(Rj(D(rp.iRule), 4) + ": ");
                rule_print(fp, rp);
                fp.Write(".");
                if (rp.precsym != null)
                {
                    fp.Write(" [" + rp.precsym.name + " precedence=" + D(rp.precsym.prec) + "]");
                }
                fp.Write("\n");
            }
            fp.Dispose();
            return;
        }

        /* Search for the file "name" which is in the same directory as
        ** the executable.  As in C, when PATH is searched and nothing is found, the last candidate is returned. */
        private static string? pathsearch(string argv0, string name, int modemask)
        {
            string? pathlist;
            string pathbuf;
            string? path = null;
            int cp;

            cp = argv0.LastIndexOf('/');
            if (cp >= 0)
            {
                path = argv0.Substring(0, cp) + "/" + name;
            }
            else
            {
                pathlist = System.Environment.GetEnvironmentVariable("PATH");
                if (pathlist == null) pathlist = ".:/bin:/usr/bin";
                pathbuf = pathlist;
                while (pathbuf.Length > 0)
                {
                    cp = pathbuf.IndexOf(':');
                    if (cp < 0)
                    {
                        path = pathbuf + "/" + name;
                        pathbuf = "";
                    }
                    else
                    {
                        path = pathbuf.Substring(0, cp) + "/" + name;
                        pathbuf = pathbuf.Substring(checked(cp + 1));
                    }
                    if (access(path)) break;
                }
            }
            return path;
        }

        /* Given an action, compute the integer value for that action
        ** which is to be put in the action table of the generated machine.
        ** Return negative if no action should be generated.
        */
        private static int compute_action(Lemon lemp, LemonAction ap)
        {
            int act;
            switch (ap.type)
            {
                case ActionType.SHIFT: act = Stp(ap).statenum; break;
                case ActionType.SHIFTREDUCE:
                    {
                        /* Since a SHIFT is inherient after a prior REDUCE, convert any
                        ** SHIFTREDUCE action with a nonterminal on the LHS into a simple
                        ** REDUCE action: */
                        if (ap.sp.index >= lemp.nterminal
                         && (lemp.errsym == null || ap.sp.index != lemp.errsym.index))
                        {
                            act = checked(lemp.minReduce + ap.Rp().iRule);
                        }
                        else
                        {
                            act = checked(lemp.minShiftReduce + ap.Rp().iRule);
                        }
                        break;
                    }
                case ActionType.REDUCE: act = checked(lemp.minReduce + ap.Rp().iRule); break;
                case ActionType.ERROR: act = lemp.errAction; break;
                case ActionType.ACCEPT: act = lemp.accAction; break;
                default: act = -1; break;
            }
            return act;
        }

        /* The next cluster of routines are for reading the template file
        ** and writing the results to the generated parser */
        /* The first function transfers data from "in" to "out" until
        ** a line is seen which begins with "%%".  The line number is
        ** tracked.
        **
        ** if name!=0, then any word that begin with "Parse" is changed to
        ** begin with *name instead.
        */
        private static void tplt_xfer(string? name, CReader @in, TextWriter @out, ref int lineno)
        {
            int i, iStart;
            string? line;
            while ((line = @in.fgets(LINESIZE)) != null
                   && (line.Length < 1 || line[0] != '%' || line.Length < 2 || line[1] != '%'))
            {
                lineno = checked(lineno + 1);
                iStart = 0;
                if (name != null)
                {
                    for (i = 0; i < line.Length; i++)
                    {
                        Spec.Invariant(0 <= iStart && iStart <= i && i <= line.Length);
                        if (line[i] == 'P' && i <= line.Length - 5
                          && string.CompareOrdinal(line, i, "Parse", 0, 5) == 0
                          && (i == 0 || !Chars.ISALPHA(line[i - 1])))
                        {
                            if (i > iStart) @out.Write(line.Substring(iStart, i - iStart));
                            @out.Write(name);
                            i += 4;
                            iStart = i + 1;
                        }
                    }
                }
                @out.Write(line.Substring(iStart));
            }
        }

        /* Skip forward past the header of the template file to the first "%%" */
        private static void tplt_skip_header(CReader @in, ref int lineno)
        {
            string? line;
            while ((line = @in.fgets(LINESIZE)) != null
                   && (line.Length < 1 || line[0] != '%' || line.Length < 2 || line[1] != '%'))
            {
                lineno = checked(lineno + 1);
            }
        }

        /* The next function finds the template file and opens it, returning
        ** a pointer to the opened file.  After C's places (-T, <grammar>.lt, ./lempar.c, the PATH search),
        ** this port also looks for lempar.c next to the executable. */
        private static CReader? tplt_open(Lemon lemp)
        {
            const string templatename = "lempar.c";
            string buf;
            CReader? @in;
            string? tpltname;
            int cp;

            /* first, see if user specified a template filename on the command line. */
            if (Program.user_templatename != null)
            {
                if (!access(Program.user_templatename))
                {
                    System.Console.Error.Write("Can't find the parser driver template file \"" + Program.user_templatename + "\".\n");
                    lemp.errorcnt = checked(lemp.errorcnt + 1);
                    return null;
                }
                @in = fopen_read(Program.user_templatename);
                if (@in == null)
                {
                    System.Console.Error.Write("Can't open the template file \"" + Program.user_templatename + "\".\n");
                    lemp.errorcnt = checked(lemp.errorcnt + 1);
                    return null;
                }
                return @in;
            }

            cp = lemp.filename.LastIndexOf('.');
            if (cp >= 0)
            {
                buf = lemp.filename.Substring(0, cp) + ".lt";
            }
            else
            {
                buf = lemp.filename + ".lt";
            }
            if (access(buf))
            {
                tpltname = buf;
            }
            else if (access(templatename))
            {
                tpltname = templatename;
            }
            else
            {
                tpltname = pathsearch(lemp.argv0, templatename, 0);
                if (tpltname == null || !access(tpltname))
                {
                    /* The port's fallback: lempar.c next to the executable */
                    string exeTplt = Path.Combine(System.AppContext.BaseDirectory, templatename);
                    if (access(exeTplt)) tpltname = exeTplt;
                }
            }
            if (tpltname == null)
            {
                System.Console.Error.Write("Can't find the parser driver template file \"" + templatename + "\".\n");
                lemp.errorcnt = checked(lemp.errorcnt + 1);
                return null;
            }
            @in = fopen_read(tpltname);
            if (@in == null)
            {
                System.Console.Error.Write("Can't open the template file \"" + tpltname + "\".\n");
                lemp.errorcnt = checked(lemp.errorcnt + 1);
            }
            return @in;
        }

        /* Print a #line directive line to the output file. */
        private static void tplt_linedir(TextWriter @out, int lineno, string filename)
        {
            int k;
            @out.Write("#line " + D(lineno) + " \"");
            for (k = 0; k < filename.Length; k++)
            {
                Spec.Invariant(0 <= k);
                if (filename[k] == '\\') @out.Write('\\');
                @out.Write(filename[k]);
            }
            @out.Write("\"\n");
        }

        /* Print a string to the file and keep the linenumber up to date */
        private static void tplt_print(TextWriter @out, Lemon lemp, string? str, ref int lineno)
        {
            tplt_print(@out, lemp, str, ref lineno, false);
        }

        /* prevIsNewline: for an empty str, whether the byte before it in C's memory (str[-1]) is a newline.
        ** True only for %include text that was advanced past leading blank lines. */
        private static void tplt_print(TextWriter @out, Lemon lemp, string? str, ref int lineno, bool prevIsNewline)
        {
            int k;
            bool lastIsNewline;
            if (str == null) return;
            for (k = 0; k < str.Length; k++)
            {
                Spec.Invariant(0 <= k);
                @out.Write(str[k]);
                if (str[k] == '\n') lineno = checked(lineno + 1);
            }
            if (str.Length > 0) lastIsNewline = str[str.Length - 1] == '\n';
            else lastIsNewline = prevIsNewline;
            if (!lastIsNewline)
            {
                @out.Write('\n');
                lineno = checked(lineno + 1);
            }
            if (!lemp.nolinenosflag)
            {
                lineno = checked(lineno + 1); tplt_linedir(@out, lineno, OutName(lemp));
            }
            return;
        }

        /*
        ** The following routine emits code for the destructor for the
        ** symbol sp
        */
        private static void emit_destructor_code(
          TextWriter @out,
          Symbol sp,
          Lemon lemp,
          ref int lineno
        )
        {
            string? cp = null;
            int k;

            if (sp.type == SymbolType.TERMINAL)
            {
                cp = lemp.tokendest;
                if (cp == null) return;
                @out.Write("{\n"); lineno = checked(lineno + 1);
            }
            else if (sp.destructor != null)
            {
                cp = sp.destructor;
                @out.Write("{\n"); lineno = checked(lineno + 1);
                if (!lemp.nolinenosflag)
                {
                    lineno = checked(lineno + 1);
                    tplt_linedir(@out, sp.destLineno, lemp.filename);
                }
            }
            else if (lemp.vardest != null)
            {
                cp = lemp.vardest;
                @out.Write("{\n"); lineno = checked(lineno + 1);
            }
            else
            {
                /* assert( 0 );  Cannot happen */
                return;
            }
            for (k = 0; k < cp.Length; k++)
            {
                Spec.Invariant(0 <= k);
                if (cp[k] == '$' && k + 1 < cp.Length && cp[k + 1] == '$')
                {
                    @out.Write("(yypminor->yy" + D(sp.dtnum) + ")");
                    k++;
                    continue;
                }
                if (cp[k] == '\n') lineno = checked(lineno + 1);
                @out.Write(cp[k]);
            }
            @out.Write("\n"); lineno = checked(lineno + 1);
            if (!lemp.nolinenosflag)
            {
                lineno = checked(lineno + 1); tplt_linedir(@out, lineno, OutName(lemp));
            }
            @out.Write("}\n"); lineno = checked(lineno + 1);
            return;
        }

        /*
        ** Return TRUE (non-zero) if the given symbol has a destructor.
        */
        private static bool has_destructor(Symbol sp, Lemon lemp)
        {
            bool ret;
            if (sp.type == SymbolType.TERMINAL)
            {
                ret = lemp.tokendest != null;
            }
            else
            {
                ret = lemp.vardest != null || sp.destructor != null;
            }
            return ret;
        }

        /*
        ** Append text to a dynamically allocated string.  If zText is 0 then
        ** reset the string to be empty again.  Always return the complete text
        ** of the string (which is overwritten with each call).
        **
        ** n bytes of zText are stored.  If n==0 then all of zText up to the first
        ** \000 terminator is stored.  zText can contain up to two instances of
        ** %d.  The values of p1 and p2 are written into the first and second
        ** %d.
        **
        ** If n==-1, then the previous character is overwritten.
        **
        ** (zText starts at zOff in the C# version, standing for C's pointer into the middle of a string.)
        */
        private static readonly StringBuilder z = new StringBuilder();

        private static string append_str(string? zText, int zOff, int n, int p1, int p2)
        {
            Spec.Requires(zText == null || (0 <= zOff && zOff <= zText.Length && -1 <= n && n <= zText.Length - zOff));
            int c;
            if (zText == null)
            {
                string r = z.ToString();
                z.Clear();
                return r;
            }
            if (n <= 0)
            {
                if (n < 0)
                {
                    Checks.That(z.Length + n >= 0); /* (C: assert( used>=0 )) */
                    z.Length = checked(z.Length + n);
                }
                n = zText.Length - zOff;
            }
            while (n > 0)
            {
                Spec.Invariant(0 <= n && 0 <= zOff && zOff + n <= zText.Length);
                n--;
                c = zText[zOff];
                zOff++;
                if (c == '%' && n > 0 && zText[zOff] == 'd')
                {
                    z.Append(D(p1));
                    p1 = p2;
                    zOff++;
                    n--;
                }
                else
                {
                    z.Append((char)c);
                }
            }
            return z.ToString();
        }

        private static string append_str(string? zText, int n, int p1, int p2)
        {
            Spec.Requires(-1 <= n && n <= 0);
            return append_str(zText, 0, n, p1, p2);
        }

        /*
        ** Write and transform the rp->code string so that symbols are expanded.
        ** Populate the rp->codePrefix and rp->codeSuffix strings, as appropriate.
        **
        ** Return 1 if the expanded code requires that "yylhsminor" local variable
        ** to be defined.
        **
        ** (In four parts, as C's one function has too many paths for the verifier: translate_lhs,
        ** translate_body with translate_label, and translate_labels.)
        */
        private static int translate_code(Lemon lemp, Rule rp)
        {
            Spec.Ensures((int r) => 0 <= r && r <= 1);
            string code;
            int i;
            int rc = 0;               /* True if yylhsminor is used */
            int zSkip = -1;           /* The zOvwrt comment within rp->code, or -1 */
            bool lhsused = false;     /* True if the LHS element has been used */
            bool lhsdirect;           /* True if LHS writes directly into stack */
            bool[] used;              /* True for each RHS element which is used */
            string zLhs;              /* Convert the LHS symbol into this string */
            string zOvwrt = "";       /* Comment that to allow LHS to overwrite RHS */

            Checks.That(0 <= rp.nrhs && rp.nrhs <= rp.rhsalias.Length); /* (the parser makes nrhs aliases) */
            used = new bool[rp.nrhs];
            for (i = 0; i < rp.nrhs; i++)
            {
                Spec.Invariant(0 <= i);
                used[i] = false;
            }
            lhsused = false;

            string? code0 = rp.code;
            if (code0 == null)
            {
                code0 = "\n";
                rp.code = code0;
                rp.line = rp.ruleline;
                rp.noCode = true;
            }
            else
            {
                rp.noCode = false;
            }
            code = code0;

            lhsdirect = translate_lhs(lemp, rp, code, used, ref lhsused, ref zSkip, ref zOvwrt);
            if (lhsdirect)
            {
                zLhs = "yymsp[" + D(1 - rp.nrhs) + "].minor.yy" + D(rp.lhs.dtnum);
            }
            else
            {
                rc = 1;
                zLhs = "yylhsminor.yy" + D(rp.lhs.dtnum);
            }

            append_str(null, 0, 0, 0);

            translate_body(lemp, rp, code, used, zSkip, zOvwrt, zLhs, ref lhsused);

            /* Main code generation completed */
            string cps = append_str(null, 0, 0, 0);
            if (cps.Length > 0) rp.code = Tables.Strsafe(cps);
            append_str(null, 0, 0, 0);

            /* Check to make sure the LHS has been used */
            if (rp.lhsalias != null && !lhsused)
            {
                Errors.ErrorMsg(lemp.filename, rp.ruleline,
                  "Label \"" + rp.lhsalias + "\" for \"" + rp.lhs.name + "(" + rp.lhsalias + ")\" is never used.");
                lemp.errorcnt = checked(lemp.errorcnt + 1);
            }

            translate_labels(lemp, rp, used);

            /* If unable to write LHS values directly into the stack, write the
            ** saved LHS value now. */
            if (!lhsdirect)
            {
                append_str("  yymsp[%d].minor.yy%d = ", 0, 1 - rp.nrhs, rp.lhs.dtnum);
                append_str(zLhs, 0, 0, 0);
                append_str(";\n", 0, 0, 0);
            }

            /* Suffix code generation complete */
            cps = append_str(null, 0, 0, 0);
            if (cps.Length > 0)
            {
                rp.codeSuffix = Tables.Strsafe(cps);
                rp.noCode = false;
            }

            return rc;
        }

        /* translate_code: may the LHS be written directly into the stack?  (Sets up the prefix code, the
        ** labels used so far, and the zOvwrt comment.) */
        private static bool translate_lhs(Lemon lemp, Rule rp, string code, bool[] used, ref bool lhsused, ref int zSkip, ref string zOvwrt)
        {
            Spec.Requires(0 <= rp.nrhs && rp.nrhs <= rp.rhsalias.Length && used.Length == rp.nrhs);
            bool lhsdirect;
            if (rp.nrhs == 0)
            {
                /* If there are no RHS symbols, then writing directly to the LHS is ok */
                lhsdirect = true;
            }
            else if (rp.rhsalias[0] == null)
            {
                /* The left-most RHS symbol has no value.  LHS direct is ok.  But
                ** we have to call the destructor on the RHS symbol first. */
                lhsdirect = true;
                if (has_destructor(rp.Rhs(0), lemp))
                {
                    append_str(null, 0, 0, 0);
                    append_str("  yy_destructor(yypParser,%d,&yymsp[%d].minor);\n", 0,
                               rp.Rhs(0).index, 1 - rp.nrhs);
                    rp.codePrefix = Tables.Strsafe(append_str(null, 0, 0, 0));
                    rp.noCode = false;
                }
            }
            else if (rp.lhsalias == null)
            {
                /* There is no LHS value symbol. */
                lhsdirect = true;
            }
            else if (string.Equals(rp.lhsalias, rp.rhsalias[0], System.StringComparison.Ordinal))
            {
                /* The LHS symbol and the left-most RHS symbol are the same, so
                ** direct writing is allowed */
                lhsdirect = true;
                lhsused = true;
                used[0] = true;
                if (rp.lhs.dtnum != rp.Rhs(0).dtnum)
                {
                    Errors.ErrorMsg(lemp.filename, rp.ruleline,
                      rp.lhs.name + "(" + rp.lhsalias + ") and " + rp.Rhs(0).name + "(" + rp.rhsalias[0]
                      + ") share the same label but have different datatypes.");
                    lemp.errorcnt = checked(lemp.errorcnt + 1);
                }
            }
            else
            {
                zOvwrt = "/*" + rp.lhsalias + "-overwrites-" + rp.rhsalias[0] + "*/";
                zSkip = code.IndexOf(zOvwrt, System.StringComparison.Ordinal);
                if (zSkip >= 0)
                {
                    /* The code contains a special comment that indicates that it is safe
                    ** for the LHS label to overwrite left-most RHS label. */
                    lhsdirect = true;
                }
                else
                {
                    lhsdirect = false;
                }
            }
            return lhsdirect;
        }

        /* translate_code's main loop: copy code, with the labels replaced by the stack elements they name. */
        private static void translate_body(Lemon lemp, Rule rp, string code, bool[] used, int zSkip, string zOvwrt, string zLhs, ref bool lhsused)
        {
            Spec.Requires(0 <= rp.nrhs && rp.nrhs <= rp.rhsalias.Length && used.Length == rp.nrhs);
            int cp, xp;
            bool dontUseRhs0 = false; /* If true, use of left-most RHS label is illegal */
            for (cp = 0; cp < code.Length; cp++)
            {
                Spec.Invariant(0 <= cp && 0 <= rp.nrhs && rp.nrhs <= rp.rhsalias.Length && used.Length == rp.nrhs);
                if (cp == zSkip)
                {
                    append_str(zOvwrt, 0, 0, 0);
                    cp = checked(cp + zOvwrt.Length - 1);
                    dontUseRhs0 = true;
                    continue;
                }
                if (Chars.ISALPHA(code[cp]) && (cp == 0 || (!Chars.ISALNUM(code[cp - 1]) && code[cp - 1] != '_')))
                {
                    for (xp = cp + 1; xp < code.Length && (Chars.ISALNUM(code[xp]) || code[xp] == '_'); xp++)
                    {
                        Spec.Invariant(cp < xp && xp <= code.Length);
                    }
                    string word = code.Substring(cp, xp - cp);
                    if (rp.lhsalias != null && string.Equals(word, rp.lhsalias, System.StringComparison.Ordinal))
                    {
                        append_str(zLhs, 0, 0, 0);
                        cp = xp;
                        lhsused = true;
                    }
                    else if (translate_label(lemp, rp, code, cp, word, used, dontUseRhs0, zOvwrt))
                    {
                        cp = xp;
                    }
                }
                /* C appends the terminating NUL here when a label ends the code, and then reads on past it;
                ** the NUL ends the generated text, so the port stops. */
                if (cp >= code.Length) break;
                append_str(code, cp, 1, 0, 0);
            } /* End loop */
        }

        /* translate_code: if word (at cp in code) is the label of an RHS symbol, append what it stands for, mark
        ** it used, and return true. */
        private static bool translate_label(Lemon lemp, Rule rp, string code, int cp, string word, bool[] used, bool dontUseRhs0, string zOvwrt)
        {
            Spec.Requires(0 <= rp.nrhs && rp.nrhs <= rp.rhsalias.Length && used.Length == rp.nrhs);
            Spec.Requires(0 <= cp && cp < code.Length);
            int i;
            for (i = 0; i < rp.nrhs; i++)
            {
                Spec.Invariant(0 <= i);
                if (rp.rhsalias[i] != null && string.Equals(word, rp.rhsalias[i], System.StringComparison.Ordinal))
                {
                    if (i == 0 && dontUseRhs0)
                    {
                        Errors.ErrorMsg(lemp.filename, rp.ruleline,
                           "Label " + rp.rhsalias[0] + " used after '" + zOvwrt + "'.");
                        lemp.errorcnt = checked(lemp.errorcnt + 1);
                    }
                    else if (cp != 0 && code[cp - 1] == '@')
                    {
                        /* If the argument is of the form @X then substituted
                        ** the token number of X, not the value of X */
                        append_str("yymsp[%d].major", -1, i - rp.nrhs + 1, 0);
                    }
                    else
                    {
                        Symbol sp = rp.Rhs(i);
                        int dtnum;
                        if (sp.type == SymbolType.MULTITERMINAL)
                        {
                            dtnum = sp.Sub(0).dtnum;
                        }
                        else
                        {
                            dtnum = sp.dtnum;
                        }
                        append_str("yymsp[%d].minor.yy%d", 0, i - rp.nrhs + 1, dtnum);
                    }
                    used[i] = true;
                    return true;
                }
            }
            return false;
        }

        /* translate_code: generate destructor code for RHS minor values which are not referenced, and error
        ** messages for unused labels and duplicate labels. */
        private static void translate_labels(Lemon lemp, Rule rp, bool[] used)
        {
            Spec.Requires(0 <= rp.nrhs && rp.nrhs <= rp.rhsalias.Length && used.Length == rp.nrhs);
            int i;
            for (i = 0; i < rp.nrhs; i++)
            {
                Spec.Invariant(0 <= i);
                if (rp.rhsalias[i] != null)
                {
                    if (i > 0)
                    {
                        int j;
                        if (rp.lhsalias != null && string.Equals(rp.lhsalias, rp.rhsalias[i], System.StringComparison.Ordinal))
                        {
                            Errors.ErrorMsg(lemp.filename, rp.ruleline,
                              rp.Rhs(i).name + "(" + rp.rhsalias[i] + ") has the same label as the LHS but is not the left-most symbol on the RHS.");
                            lemp.errorcnt = checked(lemp.errorcnt + 1);
                        }
                        for (j = 0; j < i; j++)
                        {
                            Spec.Invariant(0 <= j);
                            if (rp.rhsalias[j] != null && string.Equals(rp.rhsalias[j], rp.rhsalias[i], System.StringComparison.Ordinal))
                            {
                                Errors.ErrorMsg(lemp.filename, rp.ruleline,
                                  "Label " + rp.rhsalias[i] + " used for multiple symbols on the RHS of a rule.");
                                lemp.errorcnt = checked(lemp.errorcnt + 1);
                                break;
                            }
                        }
                    }
                    if (!used[i])
                    {
                        Errors.ErrorMsg(lemp.filename, rp.ruleline,
                          "Label " + rp.rhsalias[i] + " for \"" + rp.Rhs(i).name + "(" + rp.rhsalias[i] + ")\" is never used.");
                        lemp.errorcnt = checked(lemp.errorcnt + 1);
                    }
                }
                else if (i > 0 && has_destructor(rp.Rhs(i), lemp))
                {
                    append_str("  yy_destructor(yypParser,%d,&yymsp[%d].minor);\n", 0,
                       rp.Rhs(i).index, i - rp.nrhs + 1);
                }
            }
        }

        /*
        ** Generate code which executes when the rule "rp" is reduced.  Write
        ** the code to "out".  Make sure lineno stays up-to-date.
        */
        private static void emit_code(
          TextWriter @out,
          Rule rp,
          Lemon lemp,
          ref int lineno
        )
        {
            int k;

            /* Setup code prior to the #line directive */
            string? codePrefix = rp.codePrefix, code = rp.code, codeSuffix = rp.codeSuffix;
            if (codePrefix != null && codePrefix.Length > 0)
            {
                @out.Write("{" + codePrefix);
                for (k = 0; k < codePrefix.Length; k++)
                {
                    Spec.Invariant(0 <= k);
                    if (codePrefix[k] == '\n') lineno = checked(lineno + 1);
                }
            }

            /* Generate code to do the reduce action */
            if (code != null)
            {
                if (!lemp.nolinenosflag)
                {
                    lineno = checked(lineno + 1);
                    tplt_linedir(@out, rp.line, lemp.filename);
                }
                @out.Write("{" + code);
                for (k = 0; k < code.Length; k++)
                {
                    Spec.Invariant(0 <= k);
                    if (code[k] == '\n') lineno = checked(lineno + 1);
                }
                @out.Write("}\n"); lineno = checked(lineno + 1);
                if (!lemp.nolinenosflag)
                {
                    lineno = checked(lineno + 1);
                    tplt_linedir(@out, lineno, OutName(lemp));
                }
            }

            /* Generate breakdown code that occurs after the #line directive */
            if (codeSuffix != null && codeSuffix.Length > 0)
            {
                @out.Write(codeSuffix);
                for (k = 0; k < codeSuffix.Length; k++)
                {
                    Spec.Invariant(0 <= k);
                    if (codeSuffix[k] == '\n') lineno = checked(lineno + 1);
                }
            }

            if (codePrefix != null)
            {
                @out.Write("}\n"); lineno = checked(lineno + 1);
            }

            return;
        }

        /*
        ** Print the definition of the union used for the parser's data stack.
        ** This union contains fields for every possible data type for tokens
        ** and nonterminals.  In the process of computing and printing this
        ** union, also set the ".dtnum" field of every terminal and nonterminal
        ** symbol.
        */
        private static void print_stack_union(
          TextWriter @out,            /* The output stream */
          Lemon lemp,                 /* The main info structure for this parser */
          ref int plineno,            /* Pointer to the line number */
          bool mhflag                 /* True if generating makeheaders output */
        )
        {
            int lineno;               /* The line number of the output */
            string?[] types;          /* A hash table of datatypes */
            int arraysize;            /* Size of the "types" array */
            string stddt;             /* Standardized name for a datatype */
            int i, j;                 /* Loop counters */
            uint hash;                /* For hashing the name of a type */
            string name;              /* Name of the parser */

            /* Allocate and initialize types[] */
            Checks.That(0 <= lemp.nsymbol); /* (main counts the symbols) */
            arraysize = checked(lemp.nsymbol * 2);
            types = new string?[arraysize];
            for (i = 0; i < arraysize; i++)
            {
                Spec.Invariant(0 <= i);
                types[i] = null;
            }

            /* Build a hash table of datatypes. The ".dtnum" field of each symbol
            ** is filled in with the hash index plus 1.  A ".dtnum" value of 0 is
            ** used for terminal symbols.  If there is no %default_type defined then
            ** 0 is also used as the .dtnum value for nonterminals which do not specify
            ** a datatype using the %type directive.
            */
            for (i = 0; i < lemp.nsymbol; i++)
            {
                Spec.Invariant(0 <= i && types.Length == arraysize && arraysize == lemp.nsymbol * 2);
                Symbol sp = lemp.Sym(i);
                string? cp;
                int b, e;
                if (sp == lemp.errsym)
                {
                    sp.dtnum = checked(arraysize + 1);
                    continue;
                }
                if (sp.type != SymbolType.NONTERMINAL || (sp.datatype == null && lemp.vartype == null))
                {
                    sp.dtnum = 0;
                    continue;
                }
                cp = sp.datatype;
                if (cp == null) cp = lemp.vartype!;
                b = 0;
                while (b < cp.Length && Chars.ISSPACE(cp[b]))
                {
                    Spec.Invariant(0 <= b && b <= cp.Length);
                    b++;
                }
                e = cp.Length;
                while (e > b && Chars.ISSPACE(cp[e - 1]))
                {
                    Spec.Invariant(0 <= b && b <= e && e <= cp.Length);
                    e--;
                }
                stddt = cp.Substring(b, e - b);
                if (lemp.tokentype != null && string.Equals(stddt, lemp.tokentype, System.StringComparison.Ordinal))
                {
                    sp.dtnum = 0;
                    continue;
                }
                hash = 0;
                for (j = 0; j < stddt.Length; j++)
                {
                    Spec.Invariant(0 <= j);
                    /* C's char is signed (x86, Apple arm64): bytes >= 0x80 add negative values */
                    unchecked { hash = hash * 53 + (uint)(int)(sbyte)(byte)stddt[j]; }
                }
                hash = (hash & 0x7fffffff) % (uint)arraysize;
                while (types[hash] != null)
                {
                    Spec.Invariant(hash < (uint)arraysize && types.Length == arraysize);
                    if (string.Equals(types[hash], stddt, System.StringComparison.Ordinal))
                    {
                        sp.dtnum = (int)hash + 1;
                        break;
                    }
                    hash++;
                    if (hash >= (uint)arraysize) hash = 0;
                }
                if (types[hash] == null)
                {
                    sp.dtnum = (int)hash + 1;
                    types[hash] = stddt;
                }
            }

            /* Print out the definition of YYTOKENTYPE and YYMINORTYPE */
            name = lemp.name != null ? lemp.name : "Parse";
            lineno = plineno;
            if (mhflag) { @out.Write("#if INTERFACE\n"); lineno = checked(lineno + 1); }
            @out.Write("#define " + name + "TOKENTYPE " + (lemp.tokentype != null ? lemp.tokentype : "void*") + "\n"); lineno = checked(lineno + 1);
            if (mhflag) { @out.Write("#endif\n"); lineno = checked(lineno + 1); }
            @out.Write("typedef union {\n"); lineno = checked(lineno + 1);
            @out.Write("  int yyinit;\n"); lineno = checked(lineno + 1);
            @out.Write("  " + name + "TOKENTYPE yy0;\n"); lineno = checked(lineno + 1);
            for (i = 0; i < arraysize; i++)
            {
                Spec.Invariant(0 <= i && types.Length == arraysize);
                if (types[i] == null) continue;
                @out.Write("  " + types[i] + " yy" + D(i + 1) + ";\n"); lineno = checked(lineno + 1);
            }
            if (lemp.errsym != null && lemp.errsym.useCnt != 0)
            {
                @out.Write("  int yy" + D(lemp.errsym.dtnum) + ";\n"); lineno = checked(lineno + 1);
            }
            @out.Write("} YYMINORTYPE;\n"); lineno = checked(lineno + 1);
            plineno = lineno;
        }

        /*
        ** Return the name of a C datatype able to represent values between
        ** lwr and upr, inclusive.  Also write the sizeof for that type (1, 2, or 4) into nByte.
        */
        public static string minimum_size_type(int lwr, int upr, out int nByte)
        {
            string zType = "int";
            nByte = 4;
            if (lwr >= 0)
            {
                if (upr <= 255)
                {
                    zType = "unsigned char";
                    nByte = 1;
                }
                else if (upr < 65535)
                {
                    zType = "unsigned short int";
                    nByte = 2;
                }
                else
                {
                    zType = "unsigned int";
                    nByte = 4;
                }
            }
            else if (lwr >= -127 && upr <= 127)
            {
                zType = "signed char";
                nByte = 1;
            }
            else if (lwr >= -32767 && upr < 32767)
            {
                zType = "short";
                nByte = 2;
            }
            return zType;
        }

        /*
        ** Each state contains a set of token transaction and a set of
        ** nonterminal transactions.  Each of these sets makes an instance
        ** of the following structure.  An array of these structures is used
        ** to order the creation of entries in the yy_action[] table.
        */
#pragma warning disable CS8981 // C's struct name, kept
        private sealed class axset
#pragma warning restore CS8981
        {
            public required State stp;  /* A pointer to a state */
            public bool isTkn;         /* True to use tokens.  False for non-terminals */
            public int nAction;        /* Number of actions */
            public int iOrder;         /* Original order of action sets */
        }

        /*
        ** Compare to axset structures for sorting purposes (a total order: iOrder is unique)
        */
        private static int axset_compare(axset p1, axset p2)
        {
            int c;
            /* (the sign of C's difference: all Array.Sort looks at) */
            c = Tables.Cmp(p2.nAction, p1.nAction);
            if (c == 0)
            {
                c = Tables.Cmp(p1.iOrder, p2.iOrder);
            }
            /* assert( c!=0 || p1==p2 ); */
            return c;
        }

        /*
        ** Write text on "out" that describes the rule "rp".
        */
        private static void writeRuleText(TextWriter @out, Rule rp)
        {
            int j;
            @out.Write(rp.lhs.name + " ::=");
            for (j = 0; j < rp.nrhs; j++)
            {
                Symbol sp = rp.Rhs(j);
                if (sp.type != SymbolType.MULTITERMINAL)
                {
                    @out.Write(" " + sp.name);
                }
                else
                {
                    int k;
                    @out.Write(" " + sp.Sub(0).name);
                    for (k = 1; k < sp.nsubsym; k++)
                    {
                        @out.Write("|" + sp.Sub(k).name);
                    }
                }
            }
        }

        /* Generate C source code for the parser
        ** (In parts, as C's one function has too many paths for the verifier: the ReportTable_* functions below
        ** each write one stretch of the output, in C's order.)
        */
        public static void ReportTable(
          Lemon lemp,
          bool mhflag,     /* Output in makeheaders format if true */
          bool sqlFlag     /* Generate the *.sql file too */
        )
        {
            TextWriter @out;
            TextWriter? sql;
            CReader? @in;
            FileStream? fs;
            int lineno;
            LemonAction? ap;
            Rule? rp;
            Acttab pActtab;
            int i;
            int szActionType;     /* sizeof(YYACTIONTYPE) */
            int szCodeType;       /* sizeof(YYCODETYPE)   */
            int mnTknOfst, mxTknOfst;
            int mnNtOfst, mxNtOfst;
            int[] aAction, aLookahead; /* The yy_action table (without its trailing error entries), and yy_lookahead */

            /* (main counts the symbols, terminals first; nxstate is at most nstate, the states in sorted) */
            Checks.That(0 <= lemp.nterminal && lemp.nterminal <= lemp.nsymbol && 0 <= lemp.nxstate);

            lemp.minShiftReduce = lemp.nstate;
            lemp.errAction = checked(lemp.minShiftReduce + lemp.nrule);
            lemp.accAction = checked(lemp.errAction + 1);
            lemp.noAction = checked(lemp.accAction + 1);
            lemp.minReduce = checked(lemp.noAction + 1);
            lemp.maxAction = checked(lemp.minReduce + lemp.nrule);

            @in = tplt_open(lemp);
            if (@in == null) return;
            fs = file_open(lemp, ".c", "wb");
            if (fs == null)
            {
                return;
            }
            @out = NewWriter(fs);
            if (!sqlFlag)
            {
                sql = null;
            }
            else
            {
                FileStream? sqlfs = file_open(lemp, ".sql", "wb");
                if (sqlfs == null)
                {
                    @out.Dispose();
                    return;
                }
                sql = NewWriter(sqlfs);
                ReportTable_sql(lemp, sql);
            }
            lineno = 1;

            ReportTable_head(lemp, mhflag, @in, @out, ref lineno);
            ReportTable_defines(lemp, mhflag, @out, ref lineno, out szCodeType, out szActionType);

            /* Compute the action table, but do not output it yet.  The action
            ** table must be computed before generating the YYNSTATE macro because
            ** we need to know how many states can be eliminated.
            */
            pActtab = ReportTable_acttab(lemp, out mnTknOfst, out mxTknOfst, out mnNtOfst, out mxNtOfst);
            acttab_tables(pActtab, out aAction, out aLookahead);

            /* Mark rules that are actually used for reduce actions after all
            ** optimizations have been applied
            */
            for (rp = lemp.rule; rp != null; rp = rp.next) rp.doesReduce = false;
            for (i = 0; i < lemp.nxstate; i++)
            {
                for (ap = lemp.Sorted(i).ap; ap != null; ap = ap.next)
                {
                    if (ap.type == ActionType.REDUCE || ap.type == ActionType.SHIFTREDUCE)
                    {
                        ap.Rp().doesReduce = true;
                    }
                }
            }

            ReportTable_constants(lemp, @out, ref lineno);
            tplt_xfer(lemp.name, @in, @out, ref lineno);

            /* Now output the action table and its associates:
            **
            **  yy_action[]        A single table containing all actions.
            **  yy_lookahead[]     A table containing the lookahead for each entry in
            **                     yy_action.  Used to detect hash collisions.
            **  yy_shift_ofst[]    For each state, the offset into yy_action for
            **                     shifting terminals.
            **  yy_reduce_ofst[]   For each state, the offset into yy_action for
            **                     shifting non-terminals after a reduce.
            **  yy_default[]       Default action for each state.
            */
            ReportTable_actions(lemp, aAction, aLookahead, @out, ref lineno, szActionType, szCodeType);
            ReportTable_shift_ofst(lemp, @out, ref lineno, mnTknOfst, mxTknOfst);
            ReportTable_reduce_ofst(lemp, @out, ref lineno, mnNtOfst, mxNtOfst);
            ReportTable_default(lemp, @out, ref lineno, szActionType);
            tplt_xfer(lemp.name, @in, @out, ref lineno);

            ReportTable_names(lemp, @in, @out, ref lineno, szCodeType);

            /* Generate code which executes every time a symbol is popped from
            ** the stack while processing errors or while destroying the parser.
            ** (In other words, generate the %destructor actions)
            */
            ReportTable_destructors(lemp, @out, ref lineno);
            tplt_xfer(lemp.name, @in, @out, ref lineno);

            /* Generate code which executes whenever the parser stack overflows */
            tplt_print(@out, lemp, lemp.overflow, ref lineno);
            tplt_xfer(lemp.name, @in, @out, ref lineno);

            ReportTable_ruleinfo(lemp, @in, @out, ref lineno);

            /* Generate code which execution during each REDUCE action */
            ReportTable_reduce(lemp, @out, ref lineno);
            tplt_xfer(lemp.name, @in, @out, ref lineno);

            /* Generate code which executes if a parse fails */
            tplt_print(@out, lemp, lemp.failure, ref lineno);
            tplt_xfer(lemp.name, @in, @out, ref lineno);

            /* Generate code which executes when a syntax error occurs */
            tplt_print(@out, lemp, lemp.error, ref lineno);
            tplt_xfer(lemp.name, @in, @out, ref lineno);

            /* Generate code which executes when the parser accepts its input */
            tplt_print(@out, lemp, lemp.accept, ref lineno);
            tplt_xfer(lemp.name, @in, @out, ref lineno);

            /* Append any addition code the user desires */
            tplt_print(@out, lemp, lemp.extracode, ref lineno);

            Actions.acttab_free(pActtab);
            @out.Dispose();
            if (sql != null) sql.Dispose();
            return;
        }

        /* ReportTable: the *.sql file's contents. */
        private static void ReportTable_sql(Lemon lemp, TextWriter sql)
        {
            int i, j;
            Rule? rp;
            sql.Write(
               "BEGIN;\n"
               + "CREATE TABLE symbol(\n"
               + "  id INTEGER PRIMARY KEY,\n"
               + "  name TEXT NOT NULL,\n"
               + "  isTerminal BOOLEAN NOT NULL,\n"
               + "  fallback INTEGER REFERENCES symbol"
               + " DEFERRABLE INITIALLY DEFERRED\n"
               + ");\n"
            );
            for (i = 0; i < lemp.nsymbol; i++)
            {
                Symbol sp = lemp.Sym(i);
                sql.Write(
                   "INSERT INTO symbol(id,name,isTerminal,fallback)"
                   + "VALUES(" + D(i) + ",'" + sp.name + "',"
                   + (i < lemp.nterminal ? "TRUE" : "FALSE")
                );
                Symbol? fb = sp.fallback;
                if (fb != null)
                {
                    sql.Write("," + D(fb.index) + ");\n");
                }
                else
                {
                    sql.Write(",NULL);\n");
                }
            }
            sql.Write(
              "CREATE TABLE rule(\n"
              + "  ruleid INTEGER PRIMARY KEY,\n"
              + "  lhs INTEGER REFERENCES symbol(id),\n"
              + "  txt TEXT\n"
              + ");\n"
              + "CREATE TABLE rulerhs(\n"
              + "  ruleid INTEGER REFERENCES rule(ruleid),\n"
              + "  pos INTEGER,\n"
              + "  sym INTEGER REFERENCES symbol(id)\n"
              + ");\n"
            );
            for (i = 0, rp = lemp.rule; rp != null; rp = rp.next, i = checked(i + 1))
            {
                /* assert( i==rp->iRule ); */
                sql.Write("INSERT INTO rule(ruleid,lhs,txt)VALUES(" + D(rp.iRule) + "," + D(rp.lhs.index) + ",'");
                writeRuleText(sql, rp);
                sql.Write("');\n");
                for (j = 0; j < rp.nrhs; j++)
                {
                    Symbol sp = rp.Rhs(j);
                    if (sp.type != SymbolType.MULTITERMINAL)
                    {
                        sql.Write("INSERT INTO rulerhs(ruleid,pos,sym)VALUES(" + D(i) + "," + D(j) + "," + D(sp.index) + ");\n");
                    }
                    else
                    {
                        int k;
                        for (k = 0; k < sp.nsubsym; k++)
                        {
                            sql.Write("INSERT INTO rulerhs(ruleid,pos,sym)VALUES(" + D(i) + "," + D(j) + "," + D(sp.Sub(k).index) + ");\n");
                        }
                    }
                }
            }
            sql.Write("COMMIT;\n");
        }

        /* ReportTable: the header comment, the template's header, the %include code, and the token #defines. */
        private static void ReportTable_head(Lemon lemp, bool mhflag, CReader @in, TextWriter @out, ref int lineno)
        {
            int i;
            string prefix;
            bool includeAfterNewline;

            @out.Write(
               "/* This file is automatically generated by Lemon from input grammar\n"
               + "** source file \"" + lemp.filename + "\". */\n"); lineno = checked(lineno + 2);

            /* The first %include directive begins with a C-language comment,
            ** then skip over the header comment of the template file
            ** (include is lemp->include, stored back after the loop)
            */
            string? include0 = lemp.include;
            if (include0 == null) include0 = "";
            string include = include0;
            includeAfterNewline = false;
            for (i = 0; i < include.Length && Chars.ISSPACE(include[i]); i++)
            {
                Spec.Invariant(0 <= i);
                if (include[i] == '\n')
                {
                    include = include.Substring(i + 1);
                    includeAfterNewline = true;
                    i = -1;
                }
            }
            lemp.include = include;
            if (include.Length > 0 && include[0] == '/')
            {
                tplt_skip_header(@in, ref lineno);
            }
            else
            {
                tplt_xfer(lemp.name, @in, @out, ref lineno);
            }

            /* Generate the include code, if any */
            tplt_print(@out, lemp, include, ref lineno, includeAfterNewline);
            if (mhflag)
            {
                string incName = file_makename(lemp, ".h");
                @out.Write("#include \"" + incName + "\"\n"); lineno = checked(lineno + 1);
            }
            tplt_xfer(lemp.name, @in, @out, ref lineno);

            /* Generate #defines for all tokens */
            if (lemp.tokenprefix != null) prefix = lemp.tokenprefix;
            else prefix = "";
            if (mhflag)
            {
                @out.Write("#if INTERFACE\n"); lineno = checked(lineno + 1);
            }
            else
            {
                @out.Write("#ifndef " + prefix + lemp.Sym(1).name + "\n");
            }
            for (i = 1; i < lemp.nterminal; i++)
            {
                @out.Write("#define " + prefix + Lj(lemp.Sym(i).name, 30) + " " + Rj(D(i), 2) + "\n");
                lineno = checked(lineno + 1);
            }
            @out.Write("#endif\n"); lineno = checked(lineno + 1);
            tplt_xfer(lemp.name, @in, @out, ref lineno);
        }

        /* ReportTable: the defines, from YYCODETYPE to YYFALLBACK. */
        private static void ReportTable_defines(Lemon lemp, bool mhflag, TextWriter @out, ref int lineno, out int szCodeType, out int szActionType)
        {
            string name;
            @out.Write("#define YYCODETYPE " + minimum_size_type(0, lemp.nsymbol, out szCodeType) + "\n"); lineno = checked(lineno + 1);
            @out.Write("#define YYNOCODE " + D(lemp.nsymbol) + "\n"); lineno = checked(lineno + 1);
            @out.Write("#define YYACTIONTYPE " + minimum_size_type(0, lemp.maxAction, out szActionType) + "\n"); lineno = checked(lineno + 1);
            if (lemp.wildcard != null)
            {
                @out.Write("#define YYWILDCARD " + D(lemp.wildcard.index) + "\n"); lineno = checked(lineno + 1);
            }
            print_stack_union(@out, lemp, ref lineno, mhflag);
            @out.Write("#ifndef YYSTACKDEPTH\n"); lineno = checked(lineno + 1);
            if (lemp.stacksize != null)
            {
                @out.Write("#define YYSTACKDEPTH " + lemp.stacksize + "\n"); lineno = checked(lineno + 1);
            }
            else
            {
                @out.Write("#define YYSTACKDEPTH 100\n"); lineno = checked(lineno + 1);
            }
            @out.Write("#endif\n"); lineno = checked(lineno + 1);
            if (mhflag)
            {
                @out.Write("#if INTERFACE\n"); lineno = checked(lineno + 1);
            }
            name = lemp.name != null ? lemp.name : "Parse";
            ReportTable_argdefs(@out, ref lineno, name, "ARG", lemp.arg);
            ReportTable_argdefs(@out, ref lineno, name, "CTX", lemp.ctx);
            if (mhflag)
            {
                @out.Write("#endif\n"); lineno = checked(lineno + 1);
            }
            if (lemp.errsym != null && lemp.errsym.useCnt != 0)
            {
                @out.Write("#define YYERRORSYMBOL " + D(lemp.errsym.index) + "\n"); lineno = checked(lineno + 1);
                @out.Write("#define YYERRSYMDT yy" + D(lemp.errsym.dtnum) + "\n"); lineno = checked(lineno + 1);
            }
            if (lemp.has_fallback)
            {
                @out.Write("#define YYFALLBACK 1\n"); lineno = checked(lineno + 1);
            }
        }

        /* ReportTable: the five <name>ARG_ (kind "ARG", for %extra_argument) or <name>CTX_ (kind "CTX", for
        ** %extra_context) defines. */
        private static void ReportTable_argdefs(TextWriter @out, ref int lineno, string name, string kind, string? arg0)
        {
            int i;
            if (arg0 != null && arg0.Length > 0)
            {
                string arg = arg0;
                i = arg.Length;
                while (i >= 1 && Chars.ISSPACE(arg[i - 1]))
                {
                    Spec.Invariant(0 <= i && i <= arg.Length);
                    i--;
                }
                while (i >= 1 && (Chars.ISALNUM(arg[i - 1]) || arg[i - 1] == '_'))
                {
                    Spec.Invariant(0 <= i && i <= arg.Length);
                    i--;
                }
                string argName = arg.Substring(i);
                @out.Write("#define " + name + kind + "_SDECL " + arg + ";\n"); lineno = checked(lineno + 1);
                @out.Write("#define " + name + kind + "_PDECL ," + arg + "\n"); lineno = checked(lineno + 1);
                @out.Write("#define " + name + kind + "_PARAM ," + argName + "\n"); lineno = checked(lineno + 1);
                @out.Write("#define " + name + kind + "_FETCH " + arg + "=yypParser->" + argName + ";\n"); lineno = checked(lineno + 1);
                @out.Write("#define " + name + kind + "_STORE yypParser->" + argName + "=" + argName + ";\n"); lineno = checked(lineno + 1);
            }
            else
            {
                @out.Write("#define " + name + kind + "_SDECL\n"); lineno = checked(lineno + 1);
                @out.Write("#define " + name + kind + "_PDECL\n"); lineno = checked(lineno + 1);
                @out.Write("#define " + name + kind + "_PARAM\n"); lineno = checked(lineno + 1);
                @out.Write("#define " + name + kind + "_FETCH\n"); lineno = checked(lineno + 1);
                @out.Write("#define " + name + kind + "_STORE\n"); lineno = checked(lineno + 1);
            }
        }

        /* ReportTable: compute the action table (and each state's offsets into it, and their ranges). */
        private static Acttab ReportTable_acttab(Lemon lemp, out int mnTknOfst, out int mxTknOfst, out int mnNtOfst, out int mxNtOfst)
        {
            Spec.Requires(0 <= lemp.nterminal && lemp.nterminal <= lemp.nsymbol && 0 <= lemp.nxstate);
            Spec.Ensures((Acttab r) => Actions.Wf(r));
            State stp;
            LemonAction? ap;
            Acttab pActtab;
            int i, nax;
            axset[] ax;

            nax = checked(lemp.nxstate * 2);
            ax = new axset[nax];
            for (i = 0; i < lemp.nxstate; i++)
            {
                Spec.Invariant(0 <= i && ax.Length == nax && nax == lemp.nxstate * 2);
                stp = lemp.Sorted(i);
                /* (iOrder: C sets it in a loop of its own, to the same values) */
                ax[i * 2] = new axset { stp = stp };
                ax[i * 2].isTkn = true;
                ax[i * 2].nAction = stp.nTknAct;
                ax[i * 2].iOrder = i * 2;
                ax[i * 2 + 1] = new axset { stp = stp };
                ax[i * 2 + 1].isTkn = false;
                ax[i * 2 + 1].nAction = stp.nNtAct;
                ax[i * 2 + 1].iOrder = i * 2 + 1;
            }
            mxTknOfst = mnTknOfst = 0;
            mxNtOfst = mnNtOfst = 0;
            /* In an effort to minimize the action table size, use the heuristic
            ** of placing the largest action sets first */
            System.Array.Sort(ax, new System.Comparison<axset>(axset_compare));
            pActtab = Actions.acttab_alloc(lemp.nsymbol, lemp.nterminal);
            for (i = 0; i < nax; i++)
            {
                Spec.Invariant(0 <= i && Actions.Wf(pActtab) && pActtab.nLookahead == 0 &&
                               pActtab.nsymbol == lemp.nsymbol && pActtab.nterminal == lemp.nterminal);
                axset? a = ax[i];
                Checks.That(a != null); /* (the sort permutes the slots, all filled) */
                if (a!.nAction <= 0) break;
                stp = a.stp;
                if (a.isTkn)
                {
                    for (ap = stp.ap; ap != null; ap = ap.next)
                    {
                        Spec.Invariant(Actions.Wf(pActtab) && pActtab.nsymbol == lemp.nsymbol && pActtab.nterminal == lemp.nterminal);
                        int action;
                        if (ap.sp.index >= lemp.nterminal) continue;
                        action = compute_action(lemp, ap);
                        if (action < 0) continue;
                        Checks.That(0 <= ap.sp.index); /* (symbols are numbered from 0) */
                        Actions.acttab_action(pActtab, ap.sp.index, action);
                    }
                    Checks.That(pActtab.nLookahead > 0); /* C's assert in acttab_insert: ResortStates counted these nTknAct actions */
                    stp.iTknOfst = Actions.acttab_insert(pActtab, 1);
                    if (stp.iTknOfst < mnTknOfst) mnTknOfst = stp.iTknOfst;
                    if (stp.iTknOfst > mxTknOfst) mxTknOfst = stp.iTknOfst;
                }
                else
                {
                    for (ap = stp.ap; ap != null; ap = ap.next)
                    {
                        Spec.Invariant(Actions.Wf(pActtab) && pActtab.nsymbol == lemp.nsymbol && pActtab.nterminal == lemp.nterminal);
                        int action;
                        if (ap.sp.index < lemp.nterminal) continue;
                        if (ap.sp.index == lemp.nsymbol) continue;
                        action = compute_action(lemp, ap);
                        if (action < 0) continue;
                        Checks.That(ap.sp.index < lemp.nsymbol); /* (a lookahead is a symbol, or {default}: nsymbol) */
                        Actions.acttab_action(pActtab, ap.sp.index, action);
                    }
                    Checks.That(pActtab.nLookahead > 0); /* C's assert in acttab_insert: ResortStates counted these nNtAct actions */
                    stp.iNtOfst = Actions.acttab_insert(pActtab, 0);
                    if (stp.iNtOfst < mnNtOfst) mnNtOfst = stp.iNtOfst;
                    if (stp.iNtOfst > mxNtOfst) mxNtOfst = stp.iNtOfst;
                }
            }
            return pActtab;
        }

        /* ReportTable: the constants that follow from the action table. */
        private static void ReportTable_constants(Lemon lemp, TextWriter @out, ref int lineno)
        {
            int i;
            /* Finish rendering the constants now that the action table has
            ** been computed */
            @out.Write("#define YYNSTATE             " + D(lemp.nxstate) + "\n"); lineno = checked(lineno + 1);
            @out.Write("#define YYNRULE              " + D(lemp.nrule) + "\n"); lineno = checked(lineno + 1);
            @out.Write("#define YYNRULE_WITH_ACTION  " + D(lemp.nruleWithAction) + "\n"); lineno = checked(lineno + 1);
            @out.Write("#define YYNTOKEN             " + D(lemp.nterminal) + "\n"); lineno = checked(lineno + 1);
            @out.Write("#define YY_MAX_SHIFT         " + D(checked(lemp.nxstate - 1)) + "\n"); lineno = checked(lineno + 1);
            i = lemp.minShiftReduce;
            @out.Write("#define YY_MIN_SHIFTREDUCE   " + D(i) + "\n"); lineno = checked(lineno + 1);
            i = checked(i + lemp.nrule);
            @out.Write("#define YY_MAX_SHIFTREDUCE   " + D(checked(i - 1)) + "\n"); lineno = checked(lineno + 1);
            @out.Write("#define YY_ERROR_ACTION      " + D(lemp.errAction) + "\n"); lineno = checked(lineno + 1);
            @out.Write("#define YY_ACCEPT_ACTION     " + D(lemp.accAction) + "\n"); lineno = checked(lineno + 1);
            @out.Write("#define YY_NO_ACTION         " + D(lemp.noAction) + "\n"); lineno = checked(lineno + 1);
            @out.Write("#define YY_MIN_REDUCE        " + D(lemp.minReduce) + "\n"); lineno = checked(lineno + 1);
            i = checked(lemp.minReduce + lemp.nrule);
            @out.Write("#define YY_MAX_REDUCE        " + D(checked(i - 1)) + "\n"); lineno = checked(lineno + 1);
        }

        /* ReportTable: the entries of the yy_action table, without its trailing error entries, and of yy_lookahead.
        ** (Read out of pActtab before any output: the verifier takes a TextWriter, whose methods may be overridden,
        ** for code that may change any array.) */
        private static void acttab_tables(Acttab p, out int[] aAction, out int[] aLookahead)
        {
            Spec.Requires(Actions.Wf(p));
            int i, n;
            n = Actions.acttab_action_size(p);
            aAction = new int[n];
            for (i = 0; i < n; i++)
            {
                Spec.Invariant(0 <= i && aAction.Length == n && n <= p.nAction && Actions.Wf(p));
                aAction[i] = Actions.acttab_yyaction(p, i);
            }
            n = Actions.acttab_lookahead_size(p);
            aLookahead = new int[n];
            for (i = 0; i < n; i++)
            {
                Spec.Invariant(0 <= i && aLookahead.Length == n && n <= p.nAction && Actions.Wf(p));
                aLookahead[i] = Actions.acttab_yylookahead(p, i);
            }
        }

        /* ReportTable: the yy_action and yy_lookahead tables. */
        private static void ReportTable_actions(Lemon lemp, int[] aAction, int[] aLookahead, TextWriter @out, ref int lineno, int szActionType, int szCodeType)
        {
            int i, j, n;
            int nLookAhead;

            /* Output the yy_action table */
            lemp.nactiontab = n = aAction.Length;
            lemp.tablesize = checked(lemp.tablesize + n * szActionType);
            @out.Write("#define YY_ACTTAB_COUNT (" + D(n) + ")\n"); lineno = checked(lineno + 1);
            @out.Write("static const YYACTIONTYPE yy_action[] = {\n"); lineno = checked(lineno + 1);
            for (i = j = 0; i < n; i++)
            {
                Spec.Invariant(0 <= i && 0 <= j && j <= 9 && n == aAction.Length);
                int action = aAction[i];
                if (action < 0) action = lemp.noAction;
                if (j == 0) @out.Write(" /* " + Rj(D(i), 5) + " */ ");
                @out.Write(" " + Rj(D(action), 4) + ",");
                if (j == 9 || i == n - 1)
                {
                    @out.Write("\n"); lineno = checked(lineno + 1);
                    j = 0;
                }
                else
                {
                    j++;
                }
            }
            @out.Write("};\n"); lineno = checked(lineno + 1);

            /* Output the yy_lookahead table */
            lemp.nlookaheadtab = n = aLookahead.Length;
            lemp.tablesize = checked(lemp.tablesize + n * szCodeType);
            @out.Write("static const YYCODETYPE yy_lookahead[] = {\n"); lineno = checked(lineno + 1);
            for (i = j = 0; i < n; i++)
            {
                Spec.Invariant(0 <= i && 0 <= j && j <= 9 && n == aLookahead.Length);
                int la = aLookahead[i];
                if (la < 0) la = lemp.nsymbol;
                if (j == 0) @out.Write(" /* " + Rj(D(i), 5) + " */ ");
                @out.Write(" " + Rj(D(la), 4) + ",");
                if (j == 9)
                {
                    @out.Write("\n"); lineno = checked(lineno + 1);
                    j = 0;
                }
                else
                {
                    j++;
                }
            }
            /* Add extra entries to the end of the yy_lookahead[] table so that
            ** yy_shift_ofst[]+iToken will always be a valid index into the array,
            ** even for the largest possible value of yy_shift_ofst[] and iToken. */
            nLookAhead = checked(lemp.nterminal + lemp.nactiontab);
            while (i < nLookAhead)
            {
                Spec.Invariant(0 <= j && j <= 9);
                if (j == 0) @out.Write(" /* " + Rj(D(i), 5) + " */ ");
                @out.Write(" " + Rj(D(lemp.nterminal), 4) + ",");
                if (j == 9)
                {
                    @out.Write("\n"); lineno = checked(lineno + 1);
                    j = 0;
                }
                else
                {
                    j++;
                }
                i++;
            }
            if (j > 0) { @out.Write("\n"); lineno = checked(lineno + 1); }
            @out.Write("};\n"); lineno = checked(lineno + 1);
        }

        /* ReportTable: the yy_shift_ofst table. */
        private static void ReportTable_shift_ofst(Lemon lemp, TextWriter @out, ref int lineno, int mnTknOfst, int mxTknOfst)
        {
            int i, j, n, sz;
            State stp;
            n = lemp.nxstate;
            while (n > 0 && lemp.Sorted(n - 1).iTknOfst == Lemon.NO_OFFSET) n--;
            @out.Write("#define YY_SHIFT_COUNT    (" + D(checked(n - 1)) + ")\n"); lineno = checked(lineno + 1);
            @out.Write("#define YY_SHIFT_MIN      (" + D(mnTknOfst) + ")\n"); lineno = checked(lineno + 1);
            @out.Write("#define YY_SHIFT_MAX      (" + D(mxTknOfst) + ")\n"); lineno = checked(lineno + 1);
            @out.Write("static const " + minimum_size_type(mnTknOfst, checked(lemp.nterminal + lemp.nactiontab), out sz)
                       + " yy_shift_ofst[] = {\n"); lineno = checked(lineno + 1);
            lemp.tablesize = checked(lemp.tablesize + n * sz);
            for (i = j = 0; i < n; i++)
            {
                Spec.Invariant(0 <= i && 0 <= j && j <= 9);
                int ofst;
                stp = lemp.Sorted(i);
                ofst = stp.iTknOfst;
                if (ofst == Lemon.NO_OFFSET) ofst = lemp.nactiontab;
                if (j == 0) @out.Write(" /* " + Rj(D(i), 5) + " */ ");
                @out.Write(" " + Rj(D(ofst), 4) + ",");
                if (j == 9 || i == n - 1)
                {
                    @out.Write("\n"); lineno = checked(lineno + 1);
                    j = 0;
                }
                else
                {
                    j++;
                }
            }
            @out.Write("};\n"); lineno = checked(lineno + 1);
        }

        /* ReportTable: the yy_reduce_ofst table. */
        private static void ReportTable_reduce_ofst(Lemon lemp, TextWriter @out, ref int lineno, int mnNtOfst, int mxNtOfst)
        {
            int i, j, n, sz;
            State stp;
            n = lemp.nxstate;
            while (n > 0 && lemp.Sorted(n - 1).iNtOfst == Lemon.NO_OFFSET) n--;
            @out.Write("#define YY_REDUCE_COUNT (" + D(checked(n - 1)) + ")\n"); lineno = checked(lineno + 1);
            @out.Write("#define YY_REDUCE_MIN   (" + D(mnNtOfst) + ")\n"); lineno = checked(lineno + 1);
            @out.Write("#define YY_REDUCE_MAX   (" + D(mxNtOfst) + ")\n"); lineno = checked(lineno + 1);
            @out.Write("static const " + minimum_size_type(checked(mnNtOfst - 1), mxNtOfst, out sz)
                       + " yy_reduce_ofst[] = {\n"); lineno = checked(lineno + 1);
            lemp.tablesize = checked(lemp.tablesize + n * sz);
            for (i = j = 0; i < n; i++)
            {
                Spec.Invariant(0 <= i && 0 <= j && j <= 9);
                int ofst;
                stp = lemp.Sorted(i);
                ofst = stp.iNtOfst;
                if (ofst == Lemon.NO_OFFSET) ofst = checked(mnNtOfst - 1);
                if (j == 0) @out.Write(" /* " + Rj(D(i), 5) + " */ ");
                @out.Write(" " + Rj(D(ofst), 4) + ",");
                if (j == 9 || i == n - 1)
                {
                    @out.Write("\n"); lineno = checked(lineno + 1);
                    j = 0;
                }
                else
                {
                    j++;
                }
            }
            @out.Write("};\n"); lineno = checked(lineno + 1);
        }

        /* ReportTable: the default action table. */
        private static void ReportTable_default(Lemon lemp, TextWriter @out, ref int lineno, int szActionType)
        {
            int i, j, n;
            State stp;
            @out.Write("static const YYACTIONTYPE yy_default[] = {\n"); lineno = checked(lineno + 1);
            n = lemp.nxstate;
            lemp.tablesize = checked(lemp.tablesize + n * szActionType);
            for (i = j = 0; i < n; i++)
            {
                Spec.Invariant(0 <= i && 0 <= j && j <= 9);
                stp = lemp.Sorted(i);
                if (j == 0) @out.Write(" /* " + Rj(D(i), 5) + " */ ");
                if (stp.iDfltReduce < 0)
                {
                    @out.Write(" " + Rj(D(lemp.errAction), 4) + ",");
                }
                else
                {
                    @out.Write(" " + Rj(D(checked(stp.iDfltReduce + lemp.minReduce)), 4) + ",");
                }
                if (j == 9 || i == n - 1)
                {
                    @out.Write("\n"); lineno = checked(lineno + 1);
                    j = 0;
                }
                else
                {
                    j++;
                }
            }
            @out.Write("};\n"); lineno = checked(lineno + 1);
        }

        /* ReportTable: the fallback tokens, the symbols' names and the rules' texts. */
        private static void ReportTable_names(Lemon lemp, CReader @in, TextWriter @out, ref int lineno, int szCodeType)
        {
            int i;
            Rule? rp;

            /* Generate the table of fallback tokens.
            */
            if (lemp.has_fallback)
            {
                int mx = checked(lemp.nterminal - 1);
                /* 2019-08-28:  Generate fallback entries for every token to avoid
                ** having to do a range check on the index */
                /* while( mx>0 && lemp->symbols[mx]->fallback==0 ){ mx--; } */
                lemp.tablesize = checked(lemp.tablesize + (mx + 1) * szCodeType);
                for (i = 0; i <= mx; i++)
                {
                    Spec.Invariant(0 <= i);
                    Symbol p = lemp.Sym(i);
                    Symbol? fb = p.fallback;
                    if (fb == null)
                    {
                        @out.Write("    0,  /* " + Rj(p.name, 10) + " => nothing */\n");
                    }
                    else
                    {
                        @out.Write("  " + Rj(D(fb.index), 3) + ",  /* " + Rj(p.name, 10) + " => " + fb.name + " */\n");
                    }
                    lineno = checked(lineno + 1);
                }
            }
            tplt_xfer(lemp.name, @in, @out, ref lineno);

            /* Generate a table containing the symbolic name of every symbol
            */
            for (i = 0; i < lemp.nsymbol; i++)
            {
                @out.Write("  /* " + Rj(D(i), 4) + " */ \"" + lemp.Sym(i).name + "\",\n"); lineno = checked(lineno + 1);
            }
            tplt_xfer(lemp.name, @in, @out, ref lineno);

            /* Generate a table containing a text string that describes every
            ** rule in the rule set of the grammar.  This information is used
            ** when tracing REDUCE actions.
            */
            for (i = 0, rp = lemp.rule; rp != null; rp = rp.next, i = checked(i + 1))
            {
                /* assert( rp->iRule==i ); */
                @out.Write(" /* " + Rj(D(i), 3) + " */ \"");
                writeRuleText(@out, rp);
                @out.Write("\",\n"); lineno = checked(lineno + 1);
            }
            tplt_xfer(lemp.name, @in, @out, ref lineno);
        }

        /* ReportTable: the %destructor cases. */
        private static void ReportTable_destructors(Lemon lemp, TextWriter @out, ref int lineno)
        {
            int i, j;
            if (lemp.tokendest != null)
            {
                bool once = true;
                for (i = 0; i < lemp.nsymbol; i++)
                {
                    Symbol sp = lemp.Sym(i);
                    if (sp == null || sp.type != SymbolType.TERMINAL) continue;
                    if (once)
                    {
                        @out.Write("      /* TERMINAL Destructor */\n"); lineno = checked(lineno + 1);
                        once = false;
                    }
                    @out.Write("    case " + D(sp.index) + ": /* " + sp.name + " */\n"); lineno = checked(lineno + 1);
                }
                for (i = 0; i < lemp.nsymbol && lemp.Sym(i).type != SymbolType.TERMINAL; i++) { }
                if (i < lemp.nsymbol)
                {
                    emit_destructor_code(@out, lemp.Sym(i), lemp, ref lineno);
                    @out.Write("      break;\n"); lineno = checked(lineno + 1);
                }
            }
            if (lemp.vardest != null)
            {
                Symbol? dflt_sp = null;
                bool once = true;
                for (i = 0; i < lemp.nsymbol; i++)
                {
                    Symbol sp = lemp.Sym(i);
                    if (sp == null || sp.type == SymbolType.TERMINAL ||
                        sp.index <= 0 || sp.destructor != null) continue;
                    if (once)
                    {
                        @out.Write("      /* Default NON-TERMINAL Destructor */\n"); lineno = checked(lineno + 1);
                        once = false;
                    }
                    @out.Write("    case " + D(sp.index) + ": /* " + sp.name + " */\n"); lineno = checked(lineno + 1);
                    dflt_sp = sp;
                }
                if (dflt_sp != null)
                {
                    emit_destructor_code(@out, dflt_sp, lemp, ref lineno);
                }
                @out.Write("      break;\n"); lineno = checked(lineno + 1);
            }
            for (i = 0; i < lemp.nsymbol; i++)
            {
                Symbol sp = lemp.Sym(i);
                if (sp == null || sp.type == SymbolType.TERMINAL || sp.destructor == null) continue;
                if (sp.destLineno < 0) continue;  /* Already emitted */
                @out.Write("    case " + D(sp.index) + ": /* " + sp.name + " */\n"); lineno = checked(lineno + 1);

                /* Combine duplicate destructors into a single case */
                for (j = i + 1; j < lemp.nsymbol; j++)
                {
                    Symbol sp2 = lemp.Sym(j);
                    if (sp2 != null && sp2.type != SymbolType.TERMINAL && sp2.destructor != null
                        && sp2.dtnum == sp.dtnum
                        && string.Equals(sp.destructor, sp2.destructor, System.StringComparison.Ordinal))
                    {
                        @out.Write("    case " + D(sp2.index) + ": /* " + sp2.name + " */\n"); lineno = checked(lineno + 1);
                        sp2.destLineno = -1;  /* Avoid emitting this destructor again */
                    }
                }

                emit_destructor_code(@out, lemp.Sym(i), lemp, ref lineno);
                @out.Write("      break;\n"); lineno = checked(lineno + 1);
            }
        }

        /* ReportTable: the tables of rule information.  yyRuleInfoLhs[] and
        ** yyRuleInfoNRhs[].
        **
        ** Note: This code depends on the fact that rules are number
        ** sequentially beginning with 0.
        */
        private static void ReportTable_ruleinfo(Lemon lemp, CReader @in, TextWriter @out, ref int lineno)
        {
            int i;
            Rule? rp;
            for (i = 0, rp = lemp.rule; rp != null; rp = rp.next, i = checked(i + 1))
            {
                @out.Write("  " + Rj(D(rp.lhs.index), 4) + ",  /* (" + D(i) + ") ");
                rule_print(@out, rp);
                @out.Write(" */\n"); lineno = checked(lineno + 1);
            }
            tplt_xfer(lemp.name, @in, @out, ref lineno);
            for (i = 0, rp = lemp.rule; rp != null; rp = rp.next, i = checked(i + 1))
            {
                @out.Write("  " + Rj(D(checked(-rp.nrhs)), 3) + ",  /* (" + D(i) + ") ");
                rule_print(@out, rp);
                @out.Write(" */\n"); lineno = checked(lineno + 1);
            }
            tplt_xfer(lemp.name, @in, @out, ref lineno);
        }

        /* ReportTable: the code executed during each REDUCE action. */
        private static void ReportTable_reduce(Lemon lemp, TextWriter @out, ref int lineno)
        {
            int i;
            Rule? rp;
            i = 0;
            for (rp = lemp.rule; rp != null; rp = rp.next)
            {
                i = checked(i + translate_code(lemp, rp));
            }
            if (i != 0)
            {
                @out.Write("        YYMINORTYPE yylhsminor;\n"); lineno = checked(lineno + 1);
            }
            /* First output rules other than the default: rule */
            for (rp = lemp.rule; rp != null; rp = rp.next)
            {
                Rule? rp2;               /* Other rules with the same action */
                if (rp.codeEmitted) continue;
                if (rp.noCode)
                {
                    /* No C code actions, so this will be part of the "default:" rule */
                    continue;
                }
                @out.Write("      case " + D(rp.iRule) + ": /* ");
                writeRuleText(@out, rp);
                @out.Write(" */\n"); lineno = checked(lineno + 1);
                for (rp2 = rp.next; rp2 != null; rp2 = rp2.next)
                {
                    /* C compares Strsafe'd pointers, so equal pointers are equal strings */
                    if (string.Equals(rp2.code, rp.code, System.StringComparison.Ordinal)
                        && string.Equals(rp2.codePrefix, rp.codePrefix, System.StringComparison.Ordinal)
                        && string.Equals(rp2.codeSuffix, rp.codeSuffix, System.StringComparison.Ordinal))
                    {
                        @out.Write("      case " + D(rp2.iRule) + ": /* ");
                        writeRuleText(@out, rp2);
                        @out.Write(" */ yytestcase(yyruleno==" + D(rp2.iRule) + ");\n"); lineno = checked(lineno + 1);
                        rp2.codeEmitted = true;
                    }
                }
                emit_code(@out, rp, lemp, ref lineno);
                @out.Write("        break;\n"); lineno = checked(lineno + 1);
                rp.codeEmitted = true;
            }
            /* Finally, output the default: rule.  We choose as the default: all
            ** empty actions. */
            @out.Write("      default:\n"); lineno = checked(lineno + 1);
            for (rp = lemp.rule; rp != null; rp = rp.next)
            {
                if (rp.codeEmitted) continue;
                /* assert( rp->noCode ); */
                @out.Write("      /* (" + D(rp.iRule) + ") ");
                writeRuleText(@out, rp);
                if (rp.neverReduce)
                {
                    @out.Write(" (NEVER REDUCES) */ assert(yyruleno!=" + D(rp.iRule) + ");\n"); lineno = checked(lineno + 1);
                }
                else if (rp.doesReduce)
                {
                    @out.Write(" */ yytestcase(yyruleno==" + D(rp.iRule) + ");\n"); lineno = checked(lineno + 1);
                }
                else
                {
                    @out.Write(" (OPTIMIZED OUT) */ assert(yyruleno!=" + D(rp.iRule) + ");\n"); lineno = checked(lineno + 1);
                }
            }
            @out.Write("        break;\n"); lineno = checked(lineno + 1);
        }

        /* Generate a header file for the parser */
        public static void ReportHeader(Lemon lemp)
        {
            FileStream? fs;
            TextWriter @out;
            string prefix;
            string? line;
            string pattern;
            int i;

            if (lemp.tokenprefix != null) prefix = lemp.tokenprefix;
            else prefix = "";
            fs = file_open(lemp, ".h", "rb");
            if (fs != null)
            {
                int nextChar;
                CReader? @in = null;
                try
                {
                    MemoryStream ms = new MemoryStream();
                    fs.CopyTo(ms);
                    @in = new CReader(ms.ToArray());
                }
                catch (System.Exception)
                {
                    @in = new CReader(new byte[0]);
                }
                fs.Dispose();
                for (i = 1; i < lemp.nterminal && (line = @in.fgets(LINESIZE)) != null; i++)
                {
                    pattern = "#define " + prefix + Lj(lemp.Sym(i).name, 30) + " " + Rj(D(i), 3) + "\n";
                    if (!string.Equals(line, pattern, System.StringComparison.Ordinal)) break;
                }
                nextChar = @in.fgetc();
                if (i == lemp.nterminal && nextChar == -1)
                {
                    /* No change in the file.  Don't rewrite it. */
                    return;
                }
            }
            fs = file_open(lemp, ".h", "wb");
            if (fs != null)
            {
                @out = NewWriter(fs);
                for (i = 1; i < lemp.nterminal; i++)
                {
                    @out.Write("#define " + prefix + Lj(lemp.Sym(i).name, 30) + " " + Rj(D(i), 3) + "\n");
                }
                @out.Dispose();
            }
            return;
        }

        /* Reduce the size of the action tables, if possible, by making use
        ** of defaults.
        **
        ** In this version, we take the most frequent REDUCE action and make
        ** it the default.  Except, there is no default if the wildcard token
        ** is a possible look-ahead.
        */
        public static void CompressTables(Lemon lemp)
        {
            State stp;
            LemonAction? ap, ap2, nextap;
            Rule? rp2, rbest;
            int nbest, n;
            int i;
            bool usesWildcard;

            for (i = 0; i < lemp.nstate; i++)
            {
                stp = lemp.Sorted(i);
                nbest = 0;
                rbest = null;
                usesWildcard = false;

                for (ap = stp.ap; ap != null; ap = ap.next)
                {
                    if (ap.type == ActionType.SHIFT && ap.sp == lemp.wildcard)
                    {
                        usesWildcard = true;
                    }
                    if (ap.type != ActionType.REDUCE) continue;
                    Rule rpa = ap.Rp();
                    if (rpa.lhsStart) continue;
                    if (rpa == rbest) continue;
                    n = 1;
                    for (ap2 = ap.next; ap2 != null; ap2 = ap2.next)
                    {
                        Spec.Invariant(n >= 1);
                        if (ap2.type != ActionType.REDUCE) continue;
                        rp2 = ap2.rp;
                        if (rp2 == rbest) continue;
                        if (rp2 == rpa) n = checked(n + 1);
                    }
                    if (n > nbest)
                    {
                        nbest = n;
                        rbest = rpa;
                    }
                }

                /* Do not make a default if the number of rules to default
                ** is not at least 1 or if the wildcard token is a possible
                ** lookahead.
                */
                if (nbest < 1 || usesWildcard) continue;


                /* Combine matching REDUCE actions into a single default */
                for (ap = stp.ap; ap != null; ap = ap.next)
                {
                    if (ap.type == ActionType.REDUCE && ap.rp == rbest) break;
                }
                Checks.That(ap != null); /* C's assert( ap ): rbest is the rule of one of these REDUCE actions */
                ap!.sp = Tables.Symbol_new("{default}");
                for (ap = ap.next; ap != null; ap = ap.next)
                {
                    if (ap.type == ActionType.REDUCE && ap.rp == rbest) ap.type = ActionType.NOT_USED;
                }
                stp.ap = MSort.SortActions(stp.ap);

                for (ap = stp.ap; ap != null; ap = ap.next)
                {
                    if (ap.type == ActionType.SHIFT) break;
                    if (ap.type == ActionType.REDUCE && ap.rp != rbest) break;
                }
                if (ap == null)
                {
                    stp.autoReduce = true;
                    stp.pDfltReduce = rbest;
                }
            }

            /* Make a second pass over all states and actions.  Convert
            ** every action that is a SHIFT to an autoReduce state into
            ** a SHIFTREDUCE action.
            */
            for (i = 0; i < lemp.nstate; i++)
            {
                stp = lemp.Sorted(i);
                for (ap = stp.ap; ap != null; ap = ap.next)
                {
                    State pNextState;
                    if (ap.type != ActionType.SHIFT) continue;
                    pNextState = Stp(ap);
                    if (pNextState.autoReduce && pNextState.pDfltReduce != null)
                    {
                        ap.type = ActionType.SHIFTREDUCE;
                        ap.rp = pNextState.pDfltReduce;
                    }
                }
            }

            /* If a SHIFTREDUCE action specifies a rule that has a single RHS term
            ** (meaning that the SHIFTREDUCE will land back in the state where it
            ** started) and if there is no C-code associated with the reduce action,
            ** then we can go ahead and convert the action to be the same as the
            ** action for the RHS of the rule.
            */
            for (i = 0; i < lemp.nstate; i++)
            {
                stp = lemp.Sorted(i);
                for (ap = stp.ap; ap != null; ap = nextap)
                {
                    nextap = ap.next;
                    if (ap.type != ActionType.SHIFTREDUCE) continue;
                    Rule rps = ap.Rp();
                    if (!rps.noCode) continue;
                    if (rps.nrhs != 1) continue;
                    /* Only apply this optimization to non-terminals.  It would be OK to
                    ** apply it to terminal symbols too, but that makes the parser tables
                    ** larger. */
                    if (ap.sp.index < lemp.nterminal) continue;
                    /* If we reach this point, it means the optimization can be applied */
                    nextap = ap;
                    for (ap2 = stp.ap; ap2 != null && (ap2 == ap || ap2.sp != rps.lhs); ap2 = ap2.next) { }
                    Checks.That(ap2 != null); /* C's assert( ap2!=0 ): the state has an action on the rule's LHS */
                    ap.spOpt = ap2!.sp;
                    ap.type = ap2.type;
                    ap.stp = ap2.stp;   /* ap->x = ap2->x */
                    ap.rp = ap2.rp;
                }
            }
        }


        /*
        ** Compare two states for sorting purposes.  The smaller state is the
        ** one with the most non-terminal actions.  If they have the same number
        ** of non-terminal actions, then the smaller is the one with the most
        ** token actions.  (A total order: statenum is unique.)
        */
        private static int stateResortCompare(State pA, State pB)
        {
            int n;

            /* (the sign of C's difference: all Array.Sort looks at) */
            n = Tables.Cmp(pB.nNtAct, pA.nNtAct);
            if (n == 0)
            {
                n = Tables.Cmp(pB.nTknAct, pA.nTknAct);
                if (n == 0)
                {
                    n = Tables.Cmp(pB.statenum, pA.statenum);
                }
            }
            /* assert( n!=0 ); */
            return n;
        }


        /*
        ** Renumber and resort states so that states with fewer choices
        ** occur at the end.  Except, keep state 0 as the first state.
        */
        public static void ResortStates(Lemon lemp)
        {
            int i;
            State stp;
            LemonAction? ap;

            for (i = 0; i < lemp.nstate; i++)
            {
                stp = lemp.Sorted(i);
                stp.nTknAct = stp.nNtAct = 0;
                stp.iDfltReduce = -1; /* Init dflt action to "syntax error" */
                stp.iTknOfst = Lemon.NO_OFFSET;
                stp.iNtOfst = Lemon.NO_OFFSET;
                for (ap = stp.ap; ap != null; ap = ap.next)
                {
                    int iAction = compute_action(lemp, ap);
                    if (iAction >= 0)
                    {
                        if (ap.sp.index < lemp.nterminal)
                        {
                            stp.nTknAct = checked(stp.nTknAct + 1);
                        }
                        else if (ap.sp.index < lemp.nsymbol)
                        {
                            stp.nNtAct = checked(stp.nNtAct + 1);
                        }
                        else
                        {
                            /* assert( stp->autoReduce==0 || stp->pDfltReduce==ap->x.rp ); */
                            stp.iDfltReduce = iAction;
                        }
                    }
                }
            }
            /* qsort(&lemp->sorted[1], lemp->nstate-1, ...) */
            if (lemp.nstate > 1)
            {
                int nstate = lemp.nstate;
                State[] tail = new State[nstate - 1];
                for (i = 1; i < nstate; i++)
                {
                    Spec.Invariant(1 <= i && tail.Length == nstate - 1);
                    tail[i - 1] = lemp.Sorted(i);
                }
                System.Array.Sort(tail, stateResortCompare);
                for (i = 1; i < nstate; i++)
                {
                    Spec.Invariant(1 <= i && tail.Length == nstate - 1);
                    State? t = tail[i - 1];
                    Checks.That(t != null && i < lemp.sorted.Length); /* (the sort permutes the states of sorted[1..]) */
                    lemp.sorted[i] = t!;
                }
            }
            for (i = 0; i < lemp.nstate; i++)
            {
                Spec.Invariant(0 <= i);
                lemp.Sorted(i).statenum = i;
            }
            lemp.nxstate = lemp.nstate;
            while (lemp.nxstate > 1 && lemp.Sorted(lemp.nxstate - 1).autoReduce)
            {
                lemp.nxstate--;
            }
        }
    }
}
