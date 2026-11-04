// Input file parser for the LEMON parser generator (parse.c).
// The input is read into a char[] buffer, one char per byte (Latin-1), terminated by 0 as in C; tokens are
// copied out of it as C# strings (Strsafe). Function, field and local names are those of parse.c.
using CsVerify;

namespace CsLemon
{
    /* The state of the parser */
    public enum e_state
    {
        INITIALIZE,
        WAITING_FOR_DECL_OR_RULE,
        WAITING_FOR_DECL_KEYWORD,
        WAITING_FOR_DECL_ARG,
        WAITING_FOR_PRECEDENCE_SYMBOL,
        WAITING_FOR_ARROW,
        IN_RHS,
        LHS_ALIAS_1,
        LHS_ALIAS_2,
        LHS_ALIAS_3,
        RHS_ALIAS_1,
        RHS_ALIAS_2,
        PRECEDENCE_MARK_1,
        PRECEDENCE_MARK_2,
        RESYNC_AFTER_RULE_ERROR,
        RESYNC_AFTER_DECL_ERROR,
        WAITING_FOR_DESTRUCTOR_SYMBOL,
        WAITING_FOR_DATATYPE_SYMBOL,
        WAITING_FOR_FALLBACK_ID,
        WAITING_FOR_WILDCARD_ID,
        WAITING_FOR_CLASS_ID,
        WAITING_FOR_CLASS_TOKEN,
        WAITING_FOR_TOKEN_NAME
    }

    /// <summary>
    /// The char** declargslot of C: which string field the declaration argument goes into. The fields of struct
    /// lemon are named here; destructor and datatype are fields of the symbol pstate.declargsym.
    /// </summary>
    public enum DeclSlot
    {
        NONE,
        name, include, extracode, tokendest, vardest, tokenprefix, error, accept, failure, overflow,
        arg, ctx, tokentype, vartype, stacksize, start,
        destructor,     /* &declargsym->destructor */
        datatype        /* &declargsym->datatype */
    }

#pragma warning disable CS8981 // C's lower-case struct name, kept
    public sealed class pstate
    {
        public const int MAXRHS = 1000;
        public string filename = "";          /* Name of the input file */
        public int tokenlineno;               /* Linenumber at which current token starts */
        public int errorcnt;                  /* Number of errors so far */
        public int tokenstart;                /* Text of current token (index into the file buffer) */
        public char[] filebuf = new char[1];  /* The file buffer that tokenstart indexes */
        public required Lemon gp;              /* Global state vector */
        public e_state state;                 /* The state of the parser */
        public Symbol? fallback;              /* The fallback token */
        public Symbol? tkclass;               /* Token class symbol */
        public Symbol? lhs;                   /* Left-hand side of current rule */
        public string? lhsalias;              /* Alias for the LHS */
        public int nrhs;                      /* Number of right-hand side symbols seen */
        public required Symbol[] rhs;         /* RHS symbols (MAXRHS of them) */
        public required string?[] alias;      /* Aliases for each RHS symbol (or NULL) (MAXRHS of them) */
        public Rule? prevrule;                /* Previous rule parsed */
        public string? declkeyword;           /* Keyword of a declaration */
        public DeclSlot declargslot;          /* Where the declaration argument should be put */
        public Symbol? declargsym;            /* The symbol of a destructor or datatype declargslot */
        public bool insertLineMacro;          /* Add #line before declaration insert */
        public Symbol? decllinenoslot;        /* Where to write declaration line number (&decllinenoslot->destLineno) */
        public Assoc declassoc;               /* Assign this association to decl arguments */
        public int preccounter;               /* Assign this precedence to decl arguments */
        public Rule? firstrule;               /* Pointer to first rule in the grammar */
        public Rule? lastrule;                /* Pointer to the most recently parsed rule */
    }
#pragma warning restore CS8981

    public static class Parser
    {
        /*
        ** The pstate invariant: the token starts inside the file buffer; nrhs symbols (at most MAXRHS) are stored
        ** in rhs; a rule being parsed (the states after its LHS) has its LHS, an RHS alias follows a symbol, a token
        ** class being declared is set, and the rule list has a last rule once it has a first.  (That the first nrhs
        ** entries of rhs are set is checked where they are read, by Rhs: a fact about array contents, which every
        ** ErrorMsg call makes the verifier forget, Console.Error.Write being a virtual call.)
        */
        [GhostFunction]
        private static bool Wf(pstate psp) =>
            0 <= psp.tokenstart && psp.tokenstart < psp.filebuf.Length &&
            psp.rhs.Length == pstate.MAXRHS && psp.alias.Length == pstate.MAXRHS &&
            0 <= psp.nrhs && psp.nrhs <= pstate.MAXRHS &&
            (psp.state == e_state.WAITING_FOR_ARROW || psp.state == e_state.LHS_ALIAS_1 ||
             psp.state == e_state.LHS_ALIAS_2 || psp.state == e_state.LHS_ALIAS_3 || psp.state == e_state.IN_RHS ||
             psp.state == e_state.RHS_ALIAS_1 || psp.state == e_state.RHS_ALIAS_2 ? psp.lhs != null : true) &&
            (psp.state == e_state.RHS_ALIAS_1 ? psp.nrhs > 0 : true) &&
            (psp.state == e_state.WAITING_FOR_CLASS_TOKEN ? psp.tkclass != null : true) &&
            (psp.firstrule != null ? psp.lastrule != null : true);

        /// <summary>psp->rhs[i], one of the nrhs symbols of the rule being parsed.</summary>
        private static Symbol Rhs(pstate psp, int i)
        {
            Spec.Requires(Wf(psp) && 0 <= i && i < psp.nrhs);
            Symbol? sp = psp.rhs[i];
            Checks.That(sp != null); /* (IN_RHS stores a symbol in each of the first nrhs entries) */
            return sp!;
        }

        /// <summary>
        /// z[i] of the file buffer.  The buffer ends in two 0s, C's terminator at filesize and one more (see Parse),
        /// which nothing overwrites: every write is over a non-zero character, or a 0 written and then restored.  So
        /// this is z[i] wherever C reads, and it gives the verifier the bound that C's terminator gives: a scan
        /// stepping over non-zero characters stays below z.Length - 2, and may step one past a 0.  (The verifier
        /// cannot keep the two 0s as a fact: every ErrorMsg call makes it forget array contents.)
        /// </summary>
        private static char Ch(char[] z, int i)
        {
            Spec.Requires(0 <= i);
            Spec.Ensures((char r) => r == '\0' || i < z.Length - 2);
            return i < z.Length - 2 ? z[i] : '\0';
        }

        /// <summary>x[i] of a C string: 0 past its end.</summary>
        private static char At(string x, int i)
        {
            Spec.Requires(0 <= i);
            Spec.Ensures<char>(r => i < x.Length || r == '\0');
            return i < x.Length ? x[i] : '\0';
        }

        /// <summary>A "%s" argument: printf prints a null pointer as "(null)".</summary>
        private static string S(string? s)
        {
            return s == null ? "(null)" : s;
        }

        /// <summary>strncmp(&z[i], lit, strlen(lit))==0 on the 0-terminated buffer z.</summary>
        private static bool StartsWith(char[] z, int i, string lit)
        {
            Spec.Requires(0 <= i && lit.Length > 0);
            Spec.Ensures((bool r) => !r || i + lit.Length <= z.Length - 2);
            for (int m = 0; m < lit.Length; m++)
            {
                Spec.Invariant(0 <= m && m <= lit.Length && (m == 0 || i + m <= z.Length - 2));
                char c = Ch(z, i + m);
                /* (the literals hold no 0, so the compare stops at z's terminator) */
                if (c == '\0' || c != lit[m]) return false;
            }
            return true;
        }

        /// <summary>
        /// new string(z, from, len), copied one char at a time: the verifier takes a library call that is handed
        /// the array as one that may change it.
        /// </summary>
        private static string Str(char[] z, int from, int len)
        {
            Spec.Requires(0 <= from && 0 <= len && from <= z.Length - len);
            var sb = new System.Text.StringBuilder(len);
            for (int k = 0; k < len; k++)
            {
                Spec.Invariant(0 <= k && k <= len);
                sb.Append(z[from + k]);
            }
            return sb.ToString();
        }

        /// <summary>*psp->declargslot</summary>
        private static string? GetSlot(pstate psp)
        {
            Lemon gp = psp.gp;
            switch (psp.declargslot)
            {
                case DeclSlot.name: return gp.name;
                case DeclSlot.include: return gp.include;
                case DeclSlot.extracode: return gp.extracode;
                case DeclSlot.tokendest: return gp.tokendest;
                case DeclSlot.vardest: return gp.vardest;
                case DeclSlot.tokenprefix: return gp.tokenprefix;
                case DeclSlot.error: return gp.error;
                case DeclSlot.accept: return gp.accept;
                case DeclSlot.failure: return gp.failure;
                case DeclSlot.overflow: return gp.overflow;
                case DeclSlot.arg: return gp.arg;
                case DeclSlot.ctx: return gp.ctx;
                case DeclSlot.tokentype: return gp.tokentype;
                case DeclSlot.vartype: return gp.vartype;
                case DeclSlot.stacksize: return gp.stacksize;
                case DeclSlot.start: return gp.start;
                case DeclSlot.destructor: return psp.declargsym != null ? psp.declargsym.destructor : null;
                case DeclSlot.datatype: return psp.declargsym != null ? psp.declargsym.datatype : null;
                default: return null;
            }
        }

        /// <summary>*psp->declargslot = v</summary>
        private static void SetSlot(pstate psp, string v)
        {
            Lemon gp = psp.gp;
            switch (psp.declargslot)
            {
                case DeclSlot.name: gp.name = v; break;
                case DeclSlot.include: gp.include = v; break;
                case DeclSlot.extracode: gp.extracode = v; break;
                case DeclSlot.tokendest: gp.tokendest = v; break;
                case DeclSlot.vardest: gp.vardest = v; break;
                case DeclSlot.tokenprefix: gp.tokenprefix = v; break;
                case DeclSlot.error: gp.error = v; break;
                case DeclSlot.accept: gp.accept = v; break;
                case DeclSlot.failure: gp.failure = v; break;
                case DeclSlot.overflow: gp.overflow = v; break;
                case DeclSlot.arg: gp.arg = v; break;
                case DeclSlot.ctx: gp.ctx = v; break;
                case DeclSlot.tokentype: gp.tokentype = v; break;
                case DeclSlot.vartype: gp.vartype = v; break;
                case DeclSlot.stacksize: gp.stacksize = v; break;
                case DeclSlot.start: gp.start = v; break;
                case DeclSlot.destructor: if (psp.declargsym != null) psp.declargsym.destructor = v; break;
                case DeclSlot.datatype: if (psp.declargsym != null) psp.declargsym.datatype = v; break;
                default: break;
            }
        }

        /// <summary>realloc(subsym, nsubsym): grow msp.subsym to msp.nsubsym entries.</summary>
        private static void GrowSubsym(Symbol msp)
        {
            Spec.Requires(msp.nsubsym >= 0);
            Spec.Modifies(ObjSet.Of(msp));
            Spec.Ensures(msp.subsym != null && msp.subsym.Length == msp.nsubsym);
            Symbol[] n = new Symbol[msp.nsubsym];
            Symbol[]? old = msp.subsym;
            if (old != null)
            {
                for (int i = 0; i < old.Length && i < n.Length; i++)
                {
                    Spec.Invariant(0 <= i && n.Length == msp.nsubsym);
                    n[i] = old[i];
                }
            }
            msp.subsym = n;
        }

        /// <summary>msp->nsubsym++ and the realloc of subsym that follows it.</summary>
        private static void AddSubsym(Symbol msp)
        {
            Spec.Ensures(msp.subsym != null && msp.subsym.Length == msp.nsubsym && msp.nsubsym >= 1);
            Spec.Modifies(ObjSet.Of(msp));
            Checks.That(msp.nsubsym >= 0); /* (nsubsym counts the symbols in subsym: never negative) */
            msp.nsubsym = checked(msp.nsubsym + 1);
            GrowSubsym(msp);
        }

        /* Parse a single token */
        private static void parseonetoken(pstate psp)
        {
            Spec.Requires(Wf(psp));
            Spec.Ensures(Wf(psp));
            string x;
            /* Save the token permanently: the C string at tokenstart (it ends at the first 0) */
            {
                char[] buf = psp.filebuf;
                int e = psp.tokenstart;
                while (Ch(buf, e) != '\0')
                {
                    Spec.Invariant(psp.tokenstart <= e && e <= buf.Length && Wf(psp) && buf == psp.filebuf);
                    e++;
                }
                x = Tables.Strsafe(Str(buf, psp.tokenstart, e - psp.tokenstart));
            }
            switch (psp.state)
            {
                case e_state.INITIALIZE:
                case e_state.WAITING_FOR_DECL_OR_RULE:
                    if (psp.state == e_state.INITIALIZE)
                    {
                        psp.prevrule = null;
                        psp.preccounter = 0;
                        psp.firstrule = psp.lastrule = null;
                        psp.gp.nrule = 0;
                        /* fall through */
                    }
                    if (At(x, 0) == '%')
                    {
                        psp.state = e_state.WAITING_FOR_DECL_KEYWORD;
                    }
                    else if (Chars.ISLOWER(At(x, 0)))
                    {
                        psp.lhs = Tables.Symbol_new(x);
                        psp.nrhs = 0;
                        psp.lhsalias = null;
                        psp.state = e_state.WAITING_FOR_ARROW;
                    }
                    else if (At(x, 0) == '{')
                    {
                        if (psp.prevrule == null)
                        {
                            Errors.ErrorMsg(psp.filename, psp.tokenlineno,
                              "There is no prior rule upon which to attach the code "
                              + "fragment which begins on this line.");
                            psp.errorcnt = checked(psp.errorcnt + 1);
                        }
                        else if (psp.prevrule.code != null)
                        {
                            Errors.ErrorMsg(psp.filename, psp.tokenlineno,
                              "Code fragment beginning on this line is not the first "
                              + "to follow the previous rule.");
                            psp.errorcnt = checked(psp.errorcnt + 1);
                        }
                        else if (string.Equals(x, "{NEVER-REDUCE", System.StringComparison.Ordinal))
                        {
                            psp.prevrule.neverReduce = true;
                        }
                        else
                        {
                            psp.prevrule.line = psp.tokenlineno;
                            psp.prevrule.code = x.Substring(1);
                            psp.prevrule.noCode = false;
                        }
                    }
                    else if (At(x, 0) == '[')
                    {
                        psp.state = e_state.PRECEDENCE_MARK_1;
                    }
                    else
                    {
                        Errors.ErrorMsg(psp.filename, psp.tokenlineno,
                          "Token \"" + x + "\" should be either \"%\" or a nonterminal name.");
                        psp.errorcnt = checked(psp.errorcnt + 1);
                    }
                    break;
                case e_state.PRECEDENCE_MARK_1:
                    if (!Chars.ISUPPER(At(x, 0)))
                    {
                        Errors.ErrorMsg(psp.filename, psp.tokenlineno,
                          "The precedence symbol must be a terminal.");
                        psp.errorcnt = checked(psp.errorcnt + 1);
                    }
                    else if (psp.prevrule == null)
                    {
                        Errors.ErrorMsg(psp.filename, psp.tokenlineno,
                          "There is no prior rule to assign precedence \"[" + x + "]\".");
                        psp.errorcnt = checked(psp.errorcnt + 1);
                    }
                    else if (psp.prevrule.precsym != null)
                    {
                        Errors.ErrorMsg(psp.filename, psp.tokenlineno,
                          "Precedence mark on this line is not the first "
                          + "to follow the previous rule.");
                        psp.errorcnt = checked(psp.errorcnt + 1);
                    }
                    else
                    {
                        psp.prevrule.precsym = Tables.Symbol_new(x);
                    }
                    psp.state = e_state.PRECEDENCE_MARK_2;
                    break;
                case e_state.PRECEDENCE_MARK_2:
                    if (At(x, 0) != ']')
                    {
                        Errors.ErrorMsg(psp.filename, psp.tokenlineno,
                          "Missing \"]\" on precedence mark.");
                        psp.errorcnt = checked(psp.errorcnt + 1);
                    }
                    psp.state = e_state.WAITING_FOR_DECL_OR_RULE;
                    break;
                case e_state.WAITING_FOR_ARROW:
                    if (At(x, 0) == ':' && At(x, 1) == ':' && At(x, 2) == '=')
                    {
                        psp.state = e_state.IN_RHS;
                    }
                    else if (At(x, 0) == '(')
                    {
                        psp.state = e_state.LHS_ALIAS_1;
                    }
                    else
                    {
                        Errors.ErrorMsg(psp.filename, psp.tokenlineno,
                          "Expected to see a \":\" following the LHS symbol \"" + psp.lhs!.name + "\".");
                        psp.errorcnt = checked(psp.errorcnt + 1);
                        psp.state = e_state.RESYNC_AFTER_RULE_ERROR;
                    }
                    break;
                case e_state.LHS_ALIAS_1:
                    if (Chars.ISALPHA(At(x, 0)))
                    {
                        psp.lhsalias = x;
                        psp.state = e_state.LHS_ALIAS_2;
                    }
                    else
                    {
                        Errors.ErrorMsg(psp.filename, psp.tokenlineno,
                          "\"" + x + "\" is not a valid alias for the LHS \"" + psp.lhs!.name + "\"\n");
                        psp.errorcnt = checked(psp.errorcnt + 1);
                        psp.state = e_state.RESYNC_AFTER_RULE_ERROR;
                    }
                    break;
                case e_state.LHS_ALIAS_2:
                    if (At(x, 0) == ')')
                    {
                        psp.state = e_state.LHS_ALIAS_3;
                    }
                    else
                    {
                        Errors.ErrorMsg(psp.filename, psp.tokenlineno,
                          "Missing \")\" following LHS alias name \"" + S(psp.lhsalias) + "\".");
                        psp.errorcnt = checked(psp.errorcnt + 1);
                        psp.state = e_state.RESYNC_AFTER_RULE_ERROR;
                    }
                    break;
                case e_state.LHS_ALIAS_3:
                    if (At(x, 0) == ':' && At(x, 1) == ':' && At(x, 2) == '=')
                    {
                        psp.state = e_state.IN_RHS;
                    }
                    else
                    {
                        Errors.ErrorMsg(psp.filename, psp.tokenlineno,
                          "Missing \"->\" following: \"" + psp.lhs!.name + "(" + S(psp.lhsalias) + ")\".");
                        psp.errorcnt = checked(psp.errorcnt + 1);
                        psp.state = e_state.RESYNC_AFTER_RULE_ERROR;
                    }
                    break;
                case e_state.IN_RHS:
                    if (At(x, 0) == '.')
                    {
                        /* (calloc cannot fail here: no "Can't allocate enough memory for this rule.") */
                        Rule rp = new Rule { lhs = psp.lhs!, rhs = new Symbol[psp.nrhs], rhsalias = new string?[psp.nrhs] };
                        int i;
                        rp.ruleline = psp.tokenlineno;
                        for (i = 0; i < psp.nrhs; i++)
                        {
                            Spec.Invariant(0 <= i && Wf(psp) && psp.state == e_state.IN_RHS &&
                                           rp.rhs.Length == psp.nrhs && rp.rhsalias.Length == psp.nrhs);
                            rp.rhs[i] = Rhs(psp, i);
                            rp.rhsalias[i] = psp.alias[i];
                            if (rp.rhsalias[i] != null) { rp.rhs[i].bContent = true; }
                        }
                        rp.lhsalias = psp.lhsalias;
                        rp.nrhs = psp.nrhs;
                        rp.code = null;
                        rp.noCode = true;
                        rp.precsym = null;
                        rp.index = psp.gp.nrule;
                        psp.gp.nrule = checked(psp.gp.nrule + 1);
                        rp.nextlhs = rp.lhs.rule;
                        rp.lhs.rule = rp;
                        rp.next = null;
                        if (psp.firstrule == null)
                        {
                            psp.firstrule = psp.lastrule = rp;
                        }
                        else
                        {
                            psp.lastrule!.next = rp;
                            psp.lastrule = rp;
                        }
                        psp.prevrule = rp;
                        psp.state = e_state.WAITING_FOR_DECL_OR_RULE;
                    }
                    else if (Chars.ISALPHA(At(x, 0)))
                    {
                        if (psp.nrhs >= pstate.MAXRHS)
                        {
                            Errors.ErrorMsg(psp.filename, psp.tokenlineno,
                              "Too many symbols on RHS of rule beginning at \"" + x + "\".");
                            psp.errorcnt = checked(psp.errorcnt + 1);
                            psp.state = e_state.RESYNC_AFTER_RULE_ERROR;
                        }
                        else
                        {
                            psp.rhs[psp.nrhs] = Tables.Symbol_new(x);
                            psp.alias[psp.nrhs] = null;
                            psp.nrhs = psp.nrhs + 1;
                        }
                    }
                    else if ((At(x, 0) == '|' || At(x, 0) == '/') && psp.nrhs > 0 && Chars.ISUPPER(At(x, 1)))
                    {
                        Symbol msp = Rhs(psp, psp.nrhs - 1);
                        if (msp.type != SymbolType.MULTITERMINAL)
                        {
                            Symbol origsp = msp;
                            msp = new Symbol();   /* calloc: all fields zero */
                            msp.type = SymbolType.MULTITERMINAL;
                            msp.nsubsym = 1;
                            msp.subsym = new Symbol[1];
                            msp.subsym[0] = origsp;
                            msp.name = origsp.name;
                            psp.rhs[psp.nrhs - 1] = msp;
                        }
                        AddSubsym(msp);
                        msp.subsym![msp.nsubsym - 1] = Tables.Symbol_new(x.Substring(1));
                        if (Chars.ISLOWER(At(x, 1)) || Chars.ISLOWER(At(msp.Sub(0).name, 0)))
                        {
                            Errors.ErrorMsg(psp.filename, psp.tokenlineno,
                              "Cannot form a compound containing a non-terminal");
                            psp.errorcnt = checked(psp.errorcnt + 1);
                        }
                    }
                    else if (At(x, 0) == '(' && psp.nrhs > 0)
                    {
                        psp.state = e_state.RHS_ALIAS_1;
                    }
                    else
                    {
                        Errors.ErrorMsg(psp.filename, psp.tokenlineno,
                          "Illegal character on RHS of rule: \"" + x + "\".");
                        psp.errorcnt = checked(psp.errorcnt + 1);
                        psp.state = e_state.RESYNC_AFTER_RULE_ERROR;
                    }
                    break;
                case e_state.RHS_ALIAS_1:
                    if (Chars.ISALPHA(At(x, 0)))
                    {
                        psp.alias[psp.nrhs - 1] = x;
                        psp.state = e_state.RHS_ALIAS_2;
                    }
                    else
                    {
                        Errors.ErrorMsg(psp.filename, psp.tokenlineno,
                          "\"" + x + "\" is not a valid alias for the RHS symbol \"" + Rhs(psp, psp.nrhs - 1).name + "\"\n");
                        psp.errorcnt = checked(psp.errorcnt + 1);
                        psp.state = e_state.RESYNC_AFTER_RULE_ERROR;
                    }
                    break;
                case e_state.RHS_ALIAS_2:
                    if (At(x, 0) == ')')
                    {
                        psp.state = e_state.IN_RHS;
                    }
                    else
                    {
                        /* (sic: C names the LHS alias here) */
                        Errors.ErrorMsg(psp.filename, psp.tokenlineno,
                          "Missing \")\" following LHS alias name \"" + S(psp.lhsalias) + "\".");
                        psp.errorcnt = checked(psp.errorcnt + 1);
                        psp.state = e_state.RESYNC_AFTER_RULE_ERROR;
                    }
                    break;
                case e_state.WAITING_FOR_DECL_KEYWORD:
                    if (Chars.ISALPHA(At(x, 0)))
                    {
                        psp.declkeyword = x;
                        psp.declargslot = DeclSlot.NONE;
                        psp.declargsym = null;
                        psp.decllinenoslot = null;
                        psp.insertLineMacro = true;
                        psp.state = e_state.WAITING_FOR_DECL_ARG;
                        if (x == "name")
                        {
                            psp.declargslot = DeclSlot.name;
                            psp.insertLineMacro = false;
                        }
                        else if (x == "include")
                        {
                            psp.declargslot = DeclSlot.include;
                        }
                        else if (x == "code")
                        {
                            psp.declargslot = DeclSlot.extracode;
                        }
                        else if (x == "token_destructor")
                        {
                            psp.declargslot = DeclSlot.tokendest;
                        }
                        else if (x == "default_destructor")
                        {
                            psp.declargslot = DeclSlot.vardest;
                        }
                        else if (x == "token_prefix")
                        {
                            psp.declargslot = DeclSlot.tokenprefix;
                            psp.insertLineMacro = false;
                        }
                        else if (x == "syntax_error")
                        {
                            psp.declargslot = DeclSlot.error;
                        }
                        else if (x == "parse_accept")
                        {
                            psp.declargslot = DeclSlot.accept;
                        }
                        else if (x == "parse_failure")
                        {
                            psp.declargslot = DeclSlot.failure;
                        }
                        else if (x == "stack_overflow")
                        {
                            psp.declargslot = DeclSlot.overflow;
                        }
                        else if (x == "extra_argument")
                        {
                            psp.declargslot = DeclSlot.arg;
                            psp.insertLineMacro = false;
                        }
                        else if (x == "extra_context")
                        {
                            psp.declargslot = DeclSlot.ctx;
                            psp.insertLineMacro = false;
                        }
                        else if (x == "token_type")
                        {
                            psp.declargslot = DeclSlot.tokentype;
                            psp.insertLineMacro = false;
                        }
                        else if (x == "default_type")
                        {
                            psp.declargslot = DeclSlot.vartype;
                            psp.insertLineMacro = false;
                        }
                        else if (x == "stack_size")
                        {
                            psp.declargslot = DeclSlot.stacksize;
                            psp.insertLineMacro = false;
                        }
                        else if (x == "start_symbol")
                        {
                            psp.declargslot = DeclSlot.start;
                            psp.insertLineMacro = false;
                        }
                        else if (x == "left")
                        {
                            psp.preccounter = checked(psp.preccounter + 1);
                            psp.declassoc = Assoc.LEFT;
                            psp.state = e_state.WAITING_FOR_PRECEDENCE_SYMBOL;
                        }
                        else if (x == "right")
                        {
                            psp.preccounter = checked(psp.preccounter + 1);
                            psp.declassoc = Assoc.RIGHT;
                            psp.state = e_state.WAITING_FOR_PRECEDENCE_SYMBOL;
                        }
                        else if (x == "nonassoc")
                        {
                            psp.preccounter = checked(psp.preccounter + 1);
                            psp.declassoc = Assoc.NONE;
                            psp.state = e_state.WAITING_FOR_PRECEDENCE_SYMBOL;
                        }
                        else if (x == "destructor")
                        {
                            psp.state = e_state.WAITING_FOR_DESTRUCTOR_SYMBOL;
                        }
                        else if (x == "type")
                        {
                            psp.state = e_state.WAITING_FOR_DATATYPE_SYMBOL;
                        }
                        else if (x == "fallback")
                        {
                            psp.fallback = null;
                            psp.state = e_state.WAITING_FOR_FALLBACK_ID;
                        }
                        else if (x == "token")
                        {
                            psp.state = e_state.WAITING_FOR_TOKEN_NAME;
                        }
                        else if (x == "wildcard")
                        {
                            psp.state = e_state.WAITING_FOR_WILDCARD_ID;
                        }
                        else if (x == "token_class")
                        {
                            psp.state = e_state.WAITING_FOR_CLASS_ID;
                        }
                        else
                        {
                            Errors.ErrorMsg(psp.filename, psp.tokenlineno,
                              "Unknown declaration keyword: \"%" + x + "\".");
                            psp.errorcnt = checked(psp.errorcnt + 1);
                            psp.state = e_state.RESYNC_AFTER_DECL_ERROR;
                        }
                    }
                    else
                    {
                        Errors.ErrorMsg(psp.filename, psp.tokenlineno,
                          "Illegal declaration keyword: \"" + x + "\".");
                        psp.errorcnt = checked(psp.errorcnt + 1);
                        psp.state = e_state.RESYNC_AFTER_DECL_ERROR;
                    }
                    break;
                case e_state.WAITING_FOR_DESTRUCTOR_SYMBOL:
                    if (!Chars.ISALPHA(At(x, 0)))
                    {
                        Errors.ErrorMsg(psp.filename, psp.tokenlineno,
                          "Symbol name missing after %destructor keyword");
                        psp.errorcnt = checked(psp.errorcnt + 1);
                        psp.state = e_state.RESYNC_AFTER_DECL_ERROR;
                    }
                    else
                    {
                        Symbol sp = Tables.Symbol_new(x);
                        psp.declargslot = DeclSlot.destructor;
                        psp.declargsym = sp;
                        psp.decllinenoslot = sp;
                        psp.insertLineMacro = true;
                        psp.state = e_state.WAITING_FOR_DECL_ARG;
                    }
                    break;
                case e_state.WAITING_FOR_DATATYPE_SYMBOL:
                    if (!Chars.ISALPHA(At(x, 0)))
                    {
                        Errors.ErrorMsg(psp.filename, psp.tokenlineno,
                          "Symbol name missing after %type keyword");
                        psp.errorcnt = checked(psp.errorcnt + 1);
                        psp.state = e_state.RESYNC_AFTER_DECL_ERROR;
                    }
                    else
                    {
                        Symbol? sp = Tables.Symbol_find(x);
                        if (sp != null && sp.datatype != null)
                        {
                            Errors.ErrorMsg(psp.filename, psp.tokenlineno,
                              "Symbol %type \"" + x + "\" already defined");
                            psp.errorcnt = checked(psp.errorcnt + 1);
                            psp.state = e_state.RESYNC_AFTER_DECL_ERROR;
                        }
                        else
                        {
                            if (sp == null)
                            {
                                sp = Tables.Symbol_new(x);
                            }
                            psp.declargslot = DeclSlot.datatype;
                            psp.declargsym = sp;
                            psp.insertLineMacro = false;
                            psp.state = e_state.WAITING_FOR_DECL_ARG;
                        }
                    }
                    break;
                case e_state.WAITING_FOR_PRECEDENCE_SYMBOL:
                    if (At(x, 0) == '.')
                    {
                        psp.state = e_state.WAITING_FOR_DECL_OR_RULE;
                    }
                    else if (Chars.ISUPPER(At(x, 0)))
                    {
                        Symbol sp;
                        sp = Tables.Symbol_new(x);
                        if (sp.prec >= 0)
                        {
                            Errors.ErrorMsg(psp.filename, psp.tokenlineno,
                              "Symbol \"" + x + "\" has already be given a precedence.");
                            psp.errorcnt = checked(psp.errorcnt + 1);
                        }
                        else
                        {
                            sp.prec = psp.preccounter;
                            sp.assoc = psp.declassoc;
                        }
                    }
                    else
                    {
                        Errors.ErrorMsg(psp.filename, psp.tokenlineno,
                          "Can't assign a precedence to \"" + x + "\".");
                        psp.errorcnt = checked(psp.errorcnt + 1);
                    }
                    break;
                case e_state.WAITING_FOR_DECL_ARG:
                    if (At(x, 0) == '{' || At(x, 0) == '"' || Chars.ISALNUM(At(x, 0)))
                    {
                        string zOld, zNew;
                        System.Text.StringBuilder zBuf;
                        int nOld, nLine = 0, nNew;
                        bool addLineMacro;
                        string zLine = "";
                        zNew = x;
                        if (At(zNew, 0) == '"' || At(zNew, 0) == '{') zNew = zNew.Substring(1);
                        nNew = zNew.Length;
                        string? cur = GetSlot(psp);
                        if (cur != null)
                        {
                            zOld = cur;
                        }
                        else
                        {
                            zOld = "";
                        }
                        nOld = zOld.Length;
                        addLineMacro = !psp.gp.nolinenosflag
                                       && psp.insertLineMacro
                                       && psp.tokenlineno > 1
                                       && (psp.decllinenoslot == null || psp.decllinenoslot.destLineno != 0);
                        zBuf = new System.Text.StringBuilder(zOld);
                        if (addLineMacro)
                        {
                            zLine = "#line " + psp.tokenlineno + " ";
                            nLine = zLine.Length;
                            if (nOld != 0 && zOld[nOld - 1] != '\n')
                            {
                                zBuf.Append('\n');
                            }
                            zBuf.Append(zLine);
                            zBuf.Append('"');
                            string z = psp.filename;
                            for (int iz = 0; iz < z.Length; iz++)
                            {
                                Spec.Invariant(0 <= iz);
                                if (z[iz] == '\\')
                                {
                                    zBuf.Append('\\');
                                }
                                zBuf.Append(z[iz]);
                            }
                            zBuf.Append('"');
                            zBuf.Append('\n');
                        }
                        if (psp.decllinenoslot != null && psp.decllinenoslot.destLineno == 0)
                        {
                            psp.decllinenoslot.destLineno = psp.tokenlineno;
                        }
                        zBuf.Append(zNew);
                        SetSlot(psp, zBuf.ToString());
                        psp.state = e_state.WAITING_FOR_DECL_OR_RULE;
                    }
                    else
                    {
                        Errors.ErrorMsg(psp.filename, psp.tokenlineno,
                          "Illegal argument to %" + S(psp.declkeyword) + ": " + x);
                        psp.errorcnt = checked(psp.errorcnt + 1);
                        psp.state = e_state.RESYNC_AFTER_DECL_ERROR;
                    }
                    break;
                case e_state.WAITING_FOR_FALLBACK_ID:
                    if (At(x, 0) == '.')
                    {
                        psp.state = e_state.WAITING_FOR_DECL_OR_RULE;
                    }
                    else if (!Chars.ISUPPER(At(x, 0)))
                    {
                        Errors.ErrorMsg(psp.filename, psp.tokenlineno,
                          "%fallback argument \"" + x + "\" should be a token");
                        psp.errorcnt = checked(psp.errorcnt + 1);
                    }
                    else
                    {
                        Symbol sp = Tables.Symbol_new(x);
                        if (psp.fallback == null)
                        {
                            psp.fallback = sp;
                        }
                        else if (sp.fallback != null)
                        {
                            Errors.ErrorMsg(psp.filename, psp.tokenlineno,
                              "More than one fallback assigned to token " + x);
                            psp.errorcnt = checked(psp.errorcnt + 1);
                        }
                        else
                        {
                            sp.fallback = psp.fallback;
                            psp.gp.has_fallback = true;
                        }
                    }
                    break;
                case e_state.WAITING_FOR_TOKEN_NAME:
                    /* Tokens do not have to be declared before use.  But they can be in order to control their
                    ** assigned integer number.  The number for each token is assigned when it is first seen.  So by
                    ** including "%token ONE TWO THREE." early in the grammar file, that assigns small consecutive
                    ** values to each of the tokens ONE TWO and THREE. */
                    if (At(x, 0) == '.')
                    {
                        psp.state = e_state.WAITING_FOR_DECL_OR_RULE;
                    }
                    else if (!Chars.ISUPPER(At(x, 0)))
                    {
                        Errors.ErrorMsg(psp.filename, psp.tokenlineno,
                          "%token argument \"" + x + "\" should be a token");
                        psp.errorcnt = checked(psp.errorcnt + 1);
                    }
                    else
                    {
                        Tables.Symbol_new(x);
                    }
                    break;
                case e_state.WAITING_FOR_WILDCARD_ID:
                    if (At(x, 0) == '.')
                    {
                        psp.state = e_state.WAITING_FOR_DECL_OR_RULE;
                    }
                    else if (!Chars.ISUPPER(At(x, 0)))
                    {
                        Errors.ErrorMsg(psp.filename, psp.tokenlineno,
                          "%wildcard argument \"" + x + "\" should be a token");
                        psp.errorcnt = checked(psp.errorcnt + 1);
                    }
                    else
                    {
                        Symbol sp = Tables.Symbol_new(x);
                        if (psp.gp.wildcard == null)
                        {
                            psp.gp.wildcard = sp;
                        }
                        else
                        {
                            Errors.ErrorMsg(psp.filename, psp.tokenlineno,
                              "Extra wildcard to token: " + x);
                            psp.errorcnt = checked(psp.errorcnt + 1);
                        }
                    }
                    break;
                case e_state.WAITING_FOR_CLASS_ID:
                    if (!Chars.ISLOWER(At(x, 0)))
                    {
                        Errors.ErrorMsg(psp.filename, psp.tokenlineno,
                          "%token_class must be followed by an identifier: " + x);
                        psp.errorcnt = checked(psp.errorcnt + 1);
                        psp.state = e_state.RESYNC_AFTER_DECL_ERROR;
                    }
                    else if (Tables.Symbol_find(x) != null)
                    {
                        Errors.ErrorMsg(psp.filename, psp.tokenlineno,
                          "Symbol \"" + x + "\" already used");
                        psp.errorcnt = checked(psp.errorcnt + 1);
                        psp.state = e_state.RESYNC_AFTER_DECL_ERROR;
                    }
                    else
                    {
                        psp.tkclass = Tables.Symbol_new(x);
                        psp.tkclass.type = SymbolType.MULTITERMINAL;
                        psp.state = e_state.WAITING_FOR_CLASS_TOKEN;
                    }
                    break;
                case e_state.WAITING_FOR_CLASS_TOKEN:
                    if (At(x, 0) == '.')
                    {
                        psp.state = e_state.WAITING_FOR_DECL_OR_RULE;
                    }
                    else if (Chars.ISUPPER(At(x, 0)) || ((At(x, 0) == '|' || At(x, 0) == '/') && Chars.ISUPPER(At(x, 1))))
                    {
                        Symbol msp = psp.tkclass!;
                        AddSubsym(msp);
                        if (At(x, 0) == '|' || At(x, 0) == '/') x = x.Substring(1); // (not upper case: Lemon's !ISUPPER)
                        msp.subsym![msp.nsubsym - 1] = Tables.Symbol_new(x);
                    }
                    else
                    {
                        Errors.ErrorMsg(psp.filename, psp.tokenlineno,
                          "%token_class argument \"" + x + "\" should be a token");
                        psp.errorcnt = checked(psp.errorcnt + 1);
                        psp.state = e_state.RESYNC_AFTER_DECL_ERROR;
                    }
                    break;
                case e_state.RESYNC_AFTER_RULE_ERROR:
                /*      if( x[0]=='.' ) psp->state = WAITING_FOR_DECL_OR_RULE;
                **      break; */
                case e_state.RESYNC_AFTER_DECL_ERROR:
                    if (At(x, 0) == '.') psp.state = e_state.WAITING_FOR_DECL_OR_RULE;
                    if (At(x, 0) == '%') psp.state = e_state.WAITING_FOR_DECL_KEYWORD;
                    break;
            }
        }

        /// <summary>An identifier character: ISALNUM(c) || c=='_' (never the terminator).</summary>
        private static bool IsIdChar(char c)
        {
            Spec.Ensures((bool r) => !r || c != '\0');
            return c != '\0' && (Chars.ISALNUM(c) || c == '_');
        }

        /* The text in the input is part of the argument to an %ifdef or %ifndef.  Evaluate the text as a boolean
        ** expression.  Return true or false.  (z is the C string &zbuf[zoff], terminated by 0.  A syntax error
        ** returns -(1 + its offset in z) to a nested call, lineno -1; the top-level call reports it and exits.) */
        private static int eval_preprocessor_boolean(char[] zbuf, int zoff, int lineno)
        {
            Spec.Requires(0 <= zoff && zoff <= zbuf.Length - 2);
            Spec.Decreases(zbuf.Length - zoff);
            Spec.Ensures((int r) => r <= 1 && zoff - (zbuf.Length - 2) <= r && (lineno > 0 ? r >= 0 : true));
            int neg = 0;
            int res = 0;
            int okTerm = 1;
            int i;
            bool syntaxError = false;
            for (i = 0; Ch(zbuf, zoff + i) != '\0'; i++)
            {
                Spec.Invariant(0 <= i && zoff + i <= zbuf.Length - 2 && 0 <= res && res <= 1 && !syntaxError);
                char zi = zbuf[zoff + i];
                if (Chars.ISSPACE(zi)) continue;
                if (zi == '!')
                {
                    if (okTerm == 0) { syntaxError = true; break; }
                    neg = neg == 0 ? 1 : 0;
                    continue;
                }
                if (zi == '|' && Ch(zbuf, zoff + i + 1) == '|')
                {
                    if (okTerm != 0) { syntaxError = true; break; }
                    if (res != 0) return 1;
                    i++;
                    okTerm = 1;
                    continue;
                }
                if (zi == '&' && Ch(zbuf, zoff + i + 1) == '&')
                {
                    if (okTerm != 0) { syntaxError = true; break; }
                    if (res == 0) return 0;
                    i++;
                    okTerm = 1;
                    continue;
                }
                if (zi == '(')
                {
                    int k;
                    int n = 1;
                    if (okTerm == 0) { syntaxError = true; break; }
                    bool innerError = false;
                    for (k = i + 1; Ch(zbuf, zoff + k) != '\0'; k++)
                    {
                        Spec.Invariant(0 <= i && i < k && zoff + k <= zbuf.Length - 2 && 1 <= n && n <= k - i &&
                                       zoff + i < zbuf.Length - 2 && 0 <= res && res <= 1 && !innerError);
                        if (zbuf[zoff + k] == ')')
                        {
                            n--;
                            if (n == 0)
                            {
                                zbuf[zoff + k] = '\0';
                                res = eval_preprocessor_boolean(zbuf, zoff + i + 1, -1);
                                zbuf[zoff + k] = ')';
                                if (res < 0)
                                {
                                    i = i - res;
                                    innerError = true;
                                    break;
                                }
                                i = k;
                                break;
                            }
                        }
                        else if (zbuf[zoff + k] == '(')
                        {
                            n++;
                        }
                        /* (C's "else if( z[k]==0 )" branch cannot be reached: the loop stops at 0) */
                    }
                    if (innerError) { syntaxError = true; break; }
                    if (neg != 0)
                    {
                        res = res == 0 ? 1 : 0;
                        neg = 0;
                    }
                    okTerm = 0;
                    continue;
                }
                if (Chars.ISALPHA(zi))
                {
                    int j, k, n;
                    if (okTerm == 0) { syntaxError = true; break; }
                    for (k = i + 1; IsIdChar(Ch(zbuf, zoff + k)); k++)
                    {
                        Spec.Invariant(0 <= i && i < k && zoff + k <= zbuf.Length - 2);
                    }
                    n = k - i;
                    res = 0;
                    for (j = 0; j < Program.azDefine.Count; j++)
                    {
                        Spec.Invariant(0 <= j && res == 0);
                        string? d = Program.azDefine[j];
                        if (d != null && d.Length == n && string.CompareOrdinal(d, 0, Str(zbuf, zoff + i, n), 0, n) == 0)
                        {
                            res = 1;
                            break;
                        }
                    }
                    i = k - 1;
                    if (neg != 0)
                    {
                        res = res == 0 ? 1 : 0;
                        neg = 0;
                    }
                    okTerm = 0;
                    continue;
                }
                syntaxError = true;
                break;
            }
            if (!syntaxError) return res;

            /* pp_syntax_error: */
            if (lineno > 0)
            {
                System.Console.Error.Write("%if syntax error on line " + lineno + ".\n");
                /* "%.*s": at most i+1 characters of z, stopping at its 0 */
                int m = 0;
                while (m < i + 1 && Ch(zbuf, zoff + m) != '\0')
                {
                    Spec.Invariant(0 <= m && zoff + m <= zbuf.Length - 2);
                    m++;
                }
                System.Console.Error.Write("  " + Str(zbuf, zoff, m) + " <-- syntax error here\n");
                System.Environment.Exit(1);
                return 0;
            }
            else
            {
                return -(i + 1);
            }
        }

        /// <summary>Blank out z from i to the end of its line (to the newline or the terminator).</summary>
        private static void BlankLine(char[] z, int i)
        {
            Spec.Requires(0 <= i && i <= z.Length - 2);
            for (int j = i; Ch(z, j) != '\0' && z[j] != '\n'; j++)
            {
                Spec.Invariant(i <= j && j <= z.Length - 2);
                z[j] = ' ';
            }
        }

        /// <summary>Blank out z from start up to i, keeping its newlines (excluded text).</summary>
        private static void BlankRange(char[] z, int start, int i)
        {
            Spec.Requires(0 <= start && i <= z.Length);
            for (int j = start; j < i; j++)
            {
                Spec.Invariant(start <= j);
                if (z[j] != '\n') z[j] = ' ';
            }
        }

        /* Run the preprocessor over the input file text.  The global variables azDefine[0] through
        ** azDefine[nDefine-1] contains the names of all defined macros.  This routine looks for "%ifdef" and
        ** "%ifndef" and "%endif" and comments them out.  Text in between is also commented out as appropriate. */
        private static void preprocess_input(char[] z)
        {
            Spec.Requires(z.Length >= 2);
            int i, j;
            char k;
            int exclude = 0;
            int start = 0;
            int lineno = 1;
            int start_lineno = 1;
            for (i = 0; Ch(z, i) != '\0'; i++)
            {
                Spec.Invariant(0 <= i && i <= z.Length - 2 && 0 <= exclude && exclude <= i &&
                               0 <= start && start <= i && 1 <= lineno && lineno <= i + 1);
                if (z[i] == '\n') lineno++;
                if (z[i] != '%' || (i > 0 && z[i - 1] != '\n')) continue;
                if (StartsWith(z, i, "%endif") && Chars.ISSPACE(z[i + 6]))
                {
                    if (exclude != 0)
                    {
                        exclude--;
                        if (exclude == 0)
                        {
                            BlankRange(z, start, i);
                        }
                    }
                    BlankLine(z, i);
                }
                else if (StartsWith(z, i, "%else") && Chars.ISSPACE(z[i + 5]))
                {
                    if (exclude == 1)
                    {
                        exclude = 0;
                        BlankRange(z, start, i);
                    }
                    else if (exclude == 0)
                    {
                        exclude = 1;
                        start = i;
                        start_lineno = lineno;
                    }
                    BlankLine(z, i);
                }
                else if (StartsWith(z, i, "%ifdef ")
                      || StartsWith(z, i, "%if ")
                      || StartsWith(z, i, "%ifndef "))
                {
                    if (exclude != 0)
                    {
                        exclude++;
                    }
                    else
                    {
                        bool isNot;
                        int iBool;
                        for (j = i; Ch(z, j) != '\0' && !Chars.ISSPACE(z[j]); j++)
                        {
                            Spec.Invariant(i <= j && j <= z.Length - 2);
                        }
                        iBool = j;
                        isNot = (j - i == 7);  /* (j == i + 7) */
                        while (Ch(z, j) != '\0' && z[j] != '\n')
                        {
                            Spec.Invariant(iBool <= j && j <= z.Length - 2);
                            j++;
                        }
                        k = z[j];
                        z[j] = '\0';
                        exclude = eval_preprocessor_boolean(z, iBool, lineno);
                        z[j] = k;
                        if (!isNot) exclude = exclude == 0 ? 1 : 0;
                        if (exclude != 0)
                        {
                            start = i;
                            start_lineno = lineno;
                        }
                    }
                    BlankLine(z, i);
                }
            }
            if (exclude != 0)
            {
                System.Console.Error.Write("unterminated %ifdef starting on line " + start_lineno + "\n");
                System.Environment.Exit(1);
            }
        }

        /* In spite of its name, this function is really a scanner.  It read in the entire input file (all at once)
        ** then tokenizes it.  Each token is passed to the function "parseonetoken" which builds all the
        ** appropriate data structures in the global state vector "gp". */
        public static void Parse(Lemon gp)
        {
            pstate ps;
            char[] filebuf;
            int filesize;
            int lineno;
            char c;
            int cp, nextcp;
            int startline = 0;

            ps = new pstate { gp = gp, rhs = new Symbol[pstate.MAXRHS], alias = new string?[pstate.MAXRHS] };
            ps.filename = gp.filename;
            ps.errorcnt = 0;
            ps.state = e_state.INITIALIZE;

            /* Begin by reading the input file */
            byte[]? bytes = null;
            try
            {
                bytes = System.IO.File.ReadAllBytes(ps.filename);
            }
            catch (System.Exception)
            {
                bytes = null;
            }
            if (bytes == null)
            {
                Errors.ErrorMsg(ps.filename, 0, "Can't open this file for reading.");
                gp.errorcnt = checked(gp.errorcnt + 1);
                return;
            }
            filesize = bytes.Length;
            if (filesize > 100000000)
            {
                Errors.ErrorMsg(ps.filename, 0, "Input file too large.");
                gp.errorcnt = checked(gp.errorcnt + 1);
                return;
            }
            /* filebuf[filesize] = 0, and one more 0: C's scanner can step one past the terminator after an
            ** unterminated comment or literal inside a code block (where C reads past its buffer). */
            filebuf = new char[filesize + 2];
            for (int b = 0; b < filesize; b++)
            {
                Spec.Invariant(0 <= b && filesize == bytes.Length && filebuf.Length == filesize + 2);
                filebuf[b] = (char)bytes[b];
            }
            filebuf[filesize] = '\0';
            filebuf[filesize + 1] = '\0';
            ps.filebuf = filebuf;

            /* Make an initial pass through the file to handle %ifdef and %ifndef */
            preprocess_input(filebuf);
            if (gp.printPreprocessed)
            {
                /* printf("%s\n", filebuf): the bytes up to the first 0 */
                int len = 0;
                while (Ch(filebuf, len) != '\0')
                {
                    Spec.Invariant(0 <= len && len <= filebuf.Length - 2);
                    len++;
                }
                byte[] outb = new byte[len + 1];
                for (int b = 0; b < len; b++)
                {
                    Spec.Invariant(0 <= b && outb.Length == len + 1 && len <= filebuf.Length - 2);
                    outb[b] = unchecked((byte)filebuf[b]); /* (the chars are bytes of the file, or blanks) */
                }
                outb[len] = (byte)'\n';
                System.Console.Out.Flush();
                System.IO.Stream stdout = System.Console.OpenStandardOutput();
                stdout.Write(outb, 0, outb.Length);
                stdout.Flush();
                return;
            }

            /* Now scan the text of the input file */
            lineno = 1;
            for (cp = 0; (c = Ch(filebuf, cp)) != '\0';)
            {
                Spec.Invariant(0 <= cp && cp <= filebuf.Length - 1 && ps.filebuf == filebuf && Wf(ps));
                if (c == '\n') lineno = checked(lineno + 1);              /* Keep track of the line number */
                if (Chars.ISSPACE(c)) { cp++; continue; }  /* Skip all white space */
                if (c == '/' && Ch(filebuf, cp + 1) == '/')
                {          /* Skip C++ style comments */
                    cp += 2;
                    while ((c = Ch(filebuf, cp)) != '\0' && c != '\n')
                    {
                        Spec.Invariant(2 <= cp && cp <= filebuf.Length - 2 && ps.filebuf == filebuf && Wf(ps));
                        cp++;
                    }
                    continue;
                }
                if (c == '/' && Ch(filebuf, cp + 1) == '*')
                {          /* Skip C style comments */
                    cp += 2;
                    while ((c = Ch(filebuf, cp)) != '\0' && (c != '/' || filebuf[cp - 1] != '*'))
                    {
                        Spec.Invariant(2 <= cp && cp <= filebuf.Length - 2 && ps.filebuf == filebuf && Wf(ps));
                        if (c == '\n') lineno = checked(lineno + 1);
                        cp++;
                    }
                    if (c != '\0') cp++;
                    continue;
                }
                ps.tokenstart = cp;                /* Mark the beginning of the token */
                ps.tokenlineno = lineno;           /* Linenumber on which token begins */
                if (c == '"')
                {                                  /* String literals */
                    cp++;
                    while ((c = Ch(filebuf, cp)) != '\0' && c != '"')
                    {
                        Spec.Invariant(1 <= cp && cp <= filebuf.Length - 2 && ps.filebuf == filebuf && Wf(ps));
                        if (c == '\n') lineno = checked(lineno + 1);
                        cp++;
                    }
                    if (c == '\0')
                    {
                        Errors.ErrorMsg(ps.filename, startline,
                            "String starting on this line is not terminated before "
                            + "the end of the file.");
                        ps.errorcnt = checked(ps.errorcnt + 1);
                        nextcp = cp;
                    }
                    else
                    {
                        nextcp = cp + 1;
                    }
                }
                else if (c == '{')
                {                                  /* A block of C code */
                    int level;
                    cp++;
                    for (level = 1; (c = Ch(filebuf, cp)) != '\0' && (level > 1 || c != '}'); cp++)
                    {
                        Spec.Invariant(1 <= cp && cp <= filebuf.Length - 1 && 1 <= level && level <= cp &&
                                       ps.filebuf == filebuf && Wf(ps));
                        if (c == '\n') lineno = checked(lineno + 1);
                        else if (c == '{') level++;
                        else if (c == '}') level--;
                        else if (c == '/' && Ch(filebuf, cp + 1) == '*')
                        {  /* Skip comments */
                            char prevc;
                            cp = cp + 2;
                            prevc = '\0';
                            while ((c = Ch(filebuf, cp)) != '\0' && (c != '/' || prevc != '*'))
                            {
                                Spec.Invariant(1 <= level && level <= cp && cp <= filebuf.Length - 2 &&
                                               ps.filebuf == filebuf && Wf(ps));
                                if (c == '\n') lineno = checked(lineno + 1);
                                prevc = c;
                                cp++;
                            }
                        }
                        else if (c == '/' && Ch(filebuf, cp + 1) == '/')
                        {  /* Skip C++ style comments too */
                            cp = cp + 2;
                            while ((c = Ch(filebuf, cp)) != '\0' && c != '\n')
                            {
                                Spec.Invariant(1 <= level && level <= cp && cp <= filebuf.Length - 2 &&
                                               ps.filebuf == filebuf && Wf(ps));
                                cp++;
                            }
                            if (c != '\0') lineno = checked(lineno + 1);
                        }
                        else if (c == '\'' || c == '"')
                        {    /* String a character literals */
                            char startchar, prevc;
                            startchar = c;
                            prevc = '\0';
                            for (cp++; (c = Ch(filebuf, cp)) != '\0' && (c != startchar || prevc == '\\'); cp++)
                            {
                                Spec.Invariant(1 <= level && level <= cp && cp <= filebuf.Length - 2 &&
                                               ps.filebuf == filebuf && Wf(ps));
                                if (c == '\n') lineno = checked(lineno + 1);
                                if (prevc == '\\') prevc = '\0';
                                else prevc = c;
                            }
                        }
                    }
                    if (c == '\0')
                    {
                        Errors.ErrorMsg(ps.filename, ps.tokenlineno,
                          "C code starting on this line is not terminated before "
                          + "the end of the file.");
                        ps.errorcnt = checked(ps.errorcnt + 1);
                        nextcp = cp;
                    }
                    else
                    {
                        nextcp = cp + 1;
                    }
                }
                else if (Chars.ISALNUM(c))
                {                                  /* Identifiers */
                    while ((c = Ch(filebuf, cp)) != '\0' && (Chars.ISALNUM(c) || c == '_'))
                    {
                        Spec.Invariant(0 <= cp && cp <= filebuf.Length - 2 && ps.filebuf == filebuf && Wf(ps));
                        cp++;
                    }
                    nextcp = cp;
                }
                else if (c == ':' && Ch(filebuf, cp + 1) == ':' && Ch(filebuf, cp + 2) == '=')
                {                                  /* The operator "::=" */
                    cp += 3;
                    nextcp = cp;
                }
                else if ((c == '/' || c == '|') && Chars.ISALPHA(Ch(filebuf, cp + 1)))
                {
                    cp += 2;
                    while ((c = Ch(filebuf, cp)) != '\0' && (Chars.ISALNUM(c) || c == '_'))
                    {
                        Spec.Invariant(2 <= cp && cp <= filebuf.Length - 1 && ps.filebuf == filebuf && Wf(ps));
                        cp++;
                    }
                    nextcp = cp;
                }
                else
                {                                  /* All other (one character) operators */
                    cp++;
                    nextcp = cp;
                }
                c = filebuf[cp];
                filebuf[cp] = '\0';                /* Null terminate the token */
                parseonetoken(ps);                 /* Parse the token */
                filebuf[cp] = c;                   /* Restore the buffer */
                cp = nextcp;
            }
            gp.rule = ps.firstrule;
            gp.errorcnt = ps.errorcnt;
        }
    }
}
