// Principal data structures for the LEMON parser generator (struct.h).
// The C struct fields keep their names, so this port reads side by side with the C original; pointers are
// nullable references, char* sets are bool[] (see Sets).
namespace CsLemon
{
    public enum SymbolType { TERMINAL, NONTERMINAL, MULTITERMINAL }

    public enum Assoc { LEFT, RIGHT, NONE, UNK }

    /// <summary>Symbols (terminals and nonterminals) of the grammar.</summary>
    public sealed class Symbol
    {
        public string name = "";          /* Name of the symbol */
        public int index;                 /* Index number for this symbol */
        public SymbolType type;           /* Symbols are all either TERMINALS or NTs */
        public Rule? rule;                /* Linked list of rules of this (if an NT) */
        public Symbol? fallback;          /* fallback token in case this token doesn't parse */
        public int prec;                  /* Precedence if defined (-1 otherwise) */
        public Assoc assoc;               /* Associativity if precedence is defined */
        public bool[]? firstset;          /* First-set for all rules of this symbol */
        public bool lambda;               /* True if NT and can generate an empty string */
        public int useCnt;                /* Number of times used */
        public string? destructor;        /* Code which executes whenever this symbol is popped from the stack */
        public int destLineno;            /* Line number for start of destructor; -1 for duplicate destructors */
        public string? datatype;          /* The data type of information held by this object (NT only) */
        public int dtnum;                 /* The data type number (.yy%d element of the value union) */
        public bool bContent;             /* True if this symbol ever carries content */
        /* The following fields are used by MULTITERMINALs only */
        public int nsubsym;               /* Number of constituent symbols in the MULTI */
        public Symbol[]? subsym;          /* Array of constituent symbols */
    }

    /// <summary>Each production rule in the grammar.</summary>
    public sealed class Rule
    {
        public Symbol lhs = null!;        /* Left-hand side of the rule */
        public string? lhsalias;          /* Alias for the LHS (null if none) */
        public bool lhsStart;             /* True if left-hand side is the start symbol */
        public int ruleline;              /* Line number for the rule */
        public int nrhs;                  /* Number of RHS symbols */
        public Symbol[] rhs = null!;      /* The RHS symbols */
        public string?[] rhsalias = null!;/* An alias for each RHS symbol (null if none) */
        public int line;                  /* Line number at which code begins */
        public string? code;              /* The code executed when this rule is reduced */
        public string? codePrefix;        /* Setup code before code[] above */
        public string? codeSuffix;        /* Breakdown code after code[] above */
        public Symbol? precsym;           /* Precedence symbol for this rule */
        public int index;                 /* An index number for this rule */
        public int iRule;                 /* Rule number as used in the generated tables */
        public bool noCode;               /* True if this rule has no associated C code */
        public bool codeEmitted;          /* True if the code has been emitted already */
        public bool canReduce;            /* True if this rule is ever reduced */
        public bool doesReduce;           /* Reduce actions occur after optimization */
        public bool neverReduce;          /* Reduce is theoretically possible, but prevented */
        public Rule? nextlhs;             /* Next rule with the same LHS */
        public Rule? next;                /* Next rule in the global list */
    }

    public enum CfgStatus { COMPLETE, INCOMPLETE }

    /// <summary>A production rule together with a mark (dot) showing how much of it has been processed.</summary>
    public sealed class Config
    {
        public Rule rp = null!;           /* The rule upon which the configuration is based */
        public int dot;                   /* The parse point */
        public bool[]? fws;               /* Follow-set for this configuration only */
        public Plink? fplp;               /* Follow-set forward propagation links */
        public Plink? bplp;               /* Follow-set backwards propagation links */
        public State? stp;                /* Pointer to state which contains this */
        public CfgStatus status;          /* used during followset and shift computations */
        public Config? next;              /* Next configuration in the state */
        public Config? bp;                /* The next basis configuration */
    }

    public enum ActionType
    {
        SHIFT,
        ACCEPT,
        REDUCE,
        ERROR,
        SSCONFLICT,              /* A shift/shift conflict */
        SRCONFLICT,              /* Was a reduce, but part of a conflict */
        RRCONFLICT,              /* Was a reduce, but part of a conflict */
        SH_RESOLVED,             /* Was a shift.  Precedence resolved conflict */
        RD_RESOLVED,             /* Was reduce.  Precedence resolved conflict */
        NOT_USED,                /* Deleted by compression */
        SHIFTREDUCE              /* Shift first, then reduce */
    }

    /// <summary>struct action: every shift or reduce operation. (x.stp / x.rp of the C union are two fields.)</summary>
    public sealed class LemonAction
    {
        public Symbol sp = null!;         /* The look-ahead symbol */
        public ActionType type;
        public State? stp;                /* The new state, if a shift (x.stp) */
        public Rule? rp;                  /* The rule, if a reduce (x.rp) */
        public Symbol? spOpt;             /* SHIFTREDUCE optimization to this symbol */
        public LemonAction? next;         /* Next action for this state */
        public LemonAction? collide;      /* Next action with the same hash */
        public int seq;                   /* Allocation order: C compares addresses, which grow with it (actioncmp) */
    }

    /// <summary>Each state of the generated parser's finite state machine.</summary>
    public sealed class State
    {
        public Config? bp;                /* The basis configurations for this state */
        public Config? cfp;               /* All configurations in this set */
        public int statenum;              /* Sequential number for this state */
        public LemonAction? ap;           /* List of actions for this state */
        public int nTknAct, nNtAct;       /* Number of actions on terminals and nonterminals */
        public int iTknOfst, iNtOfst;     /* yy_action[] offset for terminals and nonterms */
        public int iDfltReduce;           /* Default action is to REDUCE by this rule */
        public Rule? pDfltReduce;         /* The default REDUCE rule. */
        public bool autoReduce;           /* True if this is an auto-reduce state */
    }

    /// <summary>A followset propagation link.</summary>
    public sealed class Plink
    {
        public Config cfp = null!;        /* The configuration to which linked */
        public Plink? next;               /* The next propagate link */
    }

    /// <summary>The state vector for the entire parser generator (struct lemon).</summary>
    public sealed class Lemon
    {
        public const int NO_OFFSET = -2147483647;

        public State[] sorted = new State[0]; /* Table of states sorted by state number */
        public Rule? rule;                /* List of all rules */
        public Rule? startRule;           /* First rule */
        public int nstate;                /* Number of states */
        public int nxstate;               /* nstate with tail degenerate states removed */
        public int nrule;                 /* Number of rules */
        public int nruleWithAction;       /* Number of rules with actions */
        public int nsymbol;               /* Number of terminal and nonterminal symbols */
        public int nterminal;             /* Number of terminal symbols */
        public int minShiftReduce;        /* Minimum shift-reduce action value */
        public int errAction;             /* Error action value */
        public int accAction;             /* Accept action value */
        public int noAction;              /* No-op action value */
        public int minReduce;             /* Minimum reduce action */
        public int maxAction;             /* Maximum action value of any kind */
        public Symbol[] symbols = new Symbol[0]; /* Sorted array of pointers to symbols */
        public int errorcnt;              /* Number of errors */
        public Symbol? errsym;            /* The error symbol */
        public Symbol? wildcard;          /* Token that matches anything */
        public string? name;              /* Name of the generated parser */
        public string? arg;               /* Declaration of the 3rd argument to parser */
        public string? ctx;               /* Declaration of 2nd argument to constructor */
        public string? tokentype;         /* Type of terminal symbols in the parser stack */
        public string? vartype;           /* The default type of non-terminal symbols */
        public string? start;             /* Name of the start symbol for the grammar */
        public string? stacksize;         /* Size of the parser stack */
        public string? include;           /* Code to put at the start of the C file */
        public string? error;             /* Code to execute when an error is seen */
        public string? overflow;          /* Code to execute on a stack overflow */
        public string? failure;           /* Code to execute on parser failure */
        public string? accept;            /* Code to execute when the parser excepts */
        public string? extracode;         /* Code appended to the generated file */
        public string? tokendest;         /* Code to execute to destroy token data */
        public string? vardest;           /* Code for the default non-terminal destructor */
        public string filename = "";      /* Name of the input file */
        public string? outname;           /* Name of the current output file */
        public string? tokenprefix;       /* A prefix added to token names in the .h file */
        public int nconflict;             /* Number of parsing conflicts */
        public int nactiontab;            /* Number of entries in the yy_action[] table */
        public int nlookaheadtab;         /* Number of entries in yy_lookahead[] */
        public int tablesize;             /* Total table size of all tables in bytes */
        public bool basisflag;            /* Print only basis configurations */
        public bool printPreprocessed;    /* Show preprocessor output on stdout */
        public bool has_fallback;         /* True if any %fallback is seen in the grammar */
        public bool nolinenosflag;        /* True if #line statements should not be printed */
        public string argv0 = "";         /* Name of the program */
    }
}
