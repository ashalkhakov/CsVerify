// Routines processing parser actions in the LEMON parser generator (action.c), and the "acttab" module that
// builds the yy_action[] table.
using System.Collections.Generic;
using CsVerify;

namespace CsLemon
{
    /*
    ** The state of the yy_action table under construction is an instance of the following structure.
    **
    ** The yy_action table maps the pair (state_number, lookahead) into an action_number.  The table is an array of
    ** integers pairs.  The state_number determines an initial offset into the yy_action array.  The lookahead value
    ** is then added to this initial offset to get an index X into the yy_action array. If the aAction[X].lookahead
    ** equals the value of the of the lookahead input, then the value of the action_number output is
    ** aAction[X].action.  If the lookaheads do not match then the default action for the state_number is returned.
    **
    ** All actions associated with a single state_number are first entered into aLookahead[] using multiple calls to
    ** acttab_action().  Then the actions for that single state_number are placed into the aAction[] array with a
    ** single call to acttab_insert().  The acttab_insert() call also resets the aLookahead[] array in preparation
    ** for the next state number.
    **
    ** The arrays of struct lookahead_action { int lookahead; int action; } are parallel int arrays here:
    ** aAction[X].lookahead is aAction_lookahead[X], and so on.
    */
    public sealed class Acttab
    {
        public int nAction;                 /* Number of used slots in aAction[] */
        public int nActionAlloc;            /* Slots allocated for aAction[] */
        public int[] aAction_lookahead = new int[0];    /* The yy_action[] table under construction */
        public int[] aAction_action = new int[0];
        public int[] aLookahead_lookahead = new int[0]; /* A single new transaction set */
        public int[] aLookahead_action = new int[0];
        public int mnLookahead;             /* Minimum aLookahead[].lookahead */
        public int mnAction;                /* Action associated with mnLookahead */
        public int mxLookahead;             /* Maximum aLookahead[].lookahead */
        public int nLookahead;              /* Used slots in aLookahead[] */
        public int nLookaheadAlloc;         /* Slots allocated in aLookahead[] */
        public int nterminal;               /* Number of terminal symbols */
        public int nsymbol;                 /* total number of symbols */
    }

    public static class Actions
    {
        /*
        ** C breaks the last tie of actioncmp by the actions' addresses (ap2 - ap1).  Lemon allocates actions in
        ** order from blocks of 100, so the addresses grow with allocation order; here each action gets its
        ** allocation sequence number instead.
        */
        private static int nextSeq = 0;

        /* Allocate a new parser action (on look-ahead sp: C fills it in after) */
        public static LemonAction Action_new(Symbol sp)
        {
            LemonAction newaction = new LemonAction { sp = sp };
            newaction.seq = nextSeq;
            nextSeq = checked(nextSeq + 1);
            return newaction;
        }

        /* Compare two actions for sorting purposes.  Return negative, zero, or positive if the first action is less
        ** than, equal to, or greater than the first
        */
        public static int actioncmp(LemonAction ap1, LemonAction ap2)
        {
            /* (the signs of C's differences, which are all msort looks at; a reduce always has its rule) */
            int rc;
            rc = Tables.Cmp(ap1.sp.index, ap2.sp.index);
            if (rc == 0)
            {
                rc = Tables.Cmp((int)ap1.type, (int)ap2.type);
            }
            if (rc == 0 && (ap1.type == ActionType.REDUCE || ap1.type == ActionType.SHIFTREDUCE))
            {
                rc = Tables.Cmp(ap1.rp?.index ?? 0, ap2.rp?.index ?? 0);
            }
            if (rc == 0)
            {
                rc = Tables.Cmp(ap2.seq, ap1.seq);
            }
            return rc;
        }

        /* Sort parser actions */
        public static LemonAction? Action_sort(LemonAction? ap)
        {
            ap = MSort.SortActions(ap);
            return ap;
        }

        /* Add an action to the front of the list app; returns the new list (C writes it through *app).  C's char* arg
        ** is stp for a SHIFT and rp otherwise. */
        public static LemonAction Action_add(LemonAction? app, ActionType type, Symbol sp, State? stp, Rule? rp)
        {
            LemonAction newaction;
            newaction = Action_new(sp);
            newaction.next = app;
            newaction.type = type;
            newaction.sp = sp;
            newaction.spOpt = null;
            if (type == ActionType.SHIFT)
            {
                newaction.stp = stp;
            }
            else
            {
                newaction.rp = rp;
            }
            return newaction;
        }

        /********************** New code to implement the "acttab" module ***********/

        /* Bounds (C's malloc fails long before): symbols, and slots in either table */
        public const int MaxSymbols = 1 << 24;
        public const int MaxAlloc = 1 << 28;

        /*
        ** The acttab invariant.  The four arrays are distinct and as long as their allocations; the lookaheads of
        ** the transaction set are symbols, between mnLookahead and mxLookahead; the action table holds symbols or
        ** -1 (empty), and every slot from nAction on is empty.
        */
        [GhostFunction]
        public static bool Wf(Acttab p) =>
            0 <= p.nterminal && p.nterminal <= p.nsymbol && p.nsymbol <= MaxSymbols &&
            p.aAction_lookahead.Length == p.nActionAlloc && p.aAction_action.Length == p.nActionAlloc &&
            0 <= p.nAction && p.nAction <= p.nActionAlloc && p.nActionAlloc <= MaxAlloc &&
            p.aLookahead_lookahead.Length == p.nLookaheadAlloc && p.aLookahead_action.Length == p.nLookaheadAlloc &&
            0 <= p.nLookahead && p.nLookahead <= p.nLookaheadAlloc && p.nLookaheadAlloc <= MaxAlloc &&
            p.aAction_lookahead != p.aAction_action && p.aAction_lookahead != p.aLookahead_lookahead &&
            p.aAction_lookahead != p.aLookahead_action && p.aAction_action != p.aLookahead_lookahead &&
            p.aAction_action != p.aLookahead_action && p.aLookahead_lookahead != p.aLookahead_action &&
            (p.nLookahead > 0 ? 0 <= p.mnLookahead && p.mnLookahead <= p.mxLookahead && p.mxLookahead < p.nsymbol : true) &&
            Spec.Forall(0, p.nLookahead, j => p.mnLookahead <= p.aLookahead_lookahead[j] && p.aLookahead_lookahead[j] <= p.mxLookahead) &&
            Spec.Forall(0, p.nActionAlloc, j => -1 <= p.aAction_lookahead[j] && p.aAction_lookahead[j] < p.nsymbol) &&
            Spec.Forall(p.nAction, p.nActionAlloc, j => p.aAction_lookahead[j] == -1);

        /* Return the number of entries in the yy_action table */
        public static int acttab_lookahead_size(Acttab p)
        {
            Spec.Requires(Wf(p));
            Spec.Ensures((int r) => r == p.nAction);
            return p.nAction;
        }

        /* The value for the N-th entry in yy_action */
        public static int acttab_yyaction(Acttab p, int N)
        {
            Spec.Requires(Wf(p) && 0 <= N && N < p.nAction);
            return p.aAction_action[N];
        }

        /* The value for the N-th entry in yy_lookahead */
        public static int acttab_yylookahead(Acttab p, int N)
        {
            Spec.Requires(Wf(p) && 0 <= N && N < p.nAction);
            Spec.Ensures((int r) => -1 <= r && r < p.nsymbol);
            return p.aAction_lookahead[N];
        }

        /* Free all memory associated with the given acttab (the collector does) */
        public static void acttab_free(Acttab p)
        {
        }

        /* Allocate a new acttab structure */
        public static Acttab acttab_alloc(int nsymbol, int nterminal)
        {
            Spec.Ensures((Acttab r) => Wf(r) && r.nsymbol == nsymbol && r.nterminal == nterminal && r.nAction == 0 && r.nLookahead == 0);
            if (!(0 <= nterminal && nterminal <= nsymbol && nsymbol <= MaxSymbols)) throw new System.OutOfMemoryException("malloc failed");
            Acttab p = new Acttab();
            p.nsymbol = nsymbol;
            p.nterminal = nterminal;
            /* (calloc: every count zero, every table empty) */
            p.nAction = 0;
            p.nActionAlloc = 0;
            p.nLookahead = 0;
            p.nLookaheadAlloc = 0;
            p.aAction_lookahead = new int[0];
            p.aAction_action = new int[0];
            p.aLookahead_lookahead = new int[0];
            p.aLookahead_action = new int[0];
            Spec.Assert(p.aAction_lookahead.Length == 0 && p.aLookahead_action.Length == p.nLookaheadAlloc);
            Spec.Assert(p.aAction_lookahead != p.aAction_action && p.aLookahead_lookahead != p.aLookahead_action && p.aAction_lookahead != p.aLookahead_action);
            Spec.Assert(p.nterminal <= p.nsymbol && p.nActionAlloc <= MaxAlloc);
            Spec.Assert(Wf(p));
            return p;
        }

        /* Add a new action to the current transaction set.
        **
        ** This routine is called once for each lookahead for a particular state.
        */
        public static void acttab_action(Acttab p, int lookahead, int action)
        {
            Spec.Requires(Wf(p) && 0 <= lookahead && lookahead < p.nsymbol);
            Spec.Ensures(Wf(p) && p.nLookahead > 0 && p.nsymbol == Spec.Old(p.nsymbol) && p.nterminal == Spec.Old(p.nterminal));
            if (p.nLookahead >= p.nLookaheadAlloc)
            {
                if (p.nLookaheadAlloc > MaxAlloc - 25) throw new System.OutOfMemoryException("malloc failed");
                p.nLookaheadAlloc += 25;
                /* (realloc: the transaction so far, copied into new arrays) */
                int[] lookaheads = new int[p.nLookaheadAlloc], actions = new int[p.nLookaheadAlloc];
                for (int c = 0; c < p.nLookahead; c++)
                {
                    Spec.Invariant(0 <= c && c <= p.nLookahead &&
                                   Spec.Forall(0, c, x => p.mnLookahead <= lookaheads[x] && lookaheads[x] <= p.mxLookahead));
                    lookaheads[c] = p.aLookahead_lookahead[c];
                    actions[c] = p.aLookahead_action[c];
                }
                p.aLookahead_lookahead = lookaheads;
                p.aLookahead_action = actions;
            }
            if (p.nLookahead == 0)
            {
                p.mxLookahead = lookahead;
                p.mnLookahead = lookahead;
                p.mnAction = action;
            }
            else
            {
                if (p.mxLookahead < lookahead) p.mxLookahead = lookahead;
                if (p.mnLookahead > lookahead)
                {
                    p.mnLookahead = lookahead;
                    p.mnAction = action;
                }
            }
            p.aLookahead_lookahead[p.nLookahead] = lookahead;
            p.aLookahead_action[p.nLookahead] = action;
            p.nLookahead++;
        }

        /*
        ** Add the transaction set built up with prior calls to acttab_action() into the current action table.  Then
        ** reset the transaction set back to an empty set in preparation for a new round of acttab_action() calls.
        **
        ** Return the offset into the action table of the new transaction.
        **
        ** If the makeItSafe parameter is true, then the offset is chosen so that it is impossible to overread the
        ** yy_lookaside[] table regardless of the lookaside token.  This is done for the terminal symbols, as they
        ** come from external inputs and can contain syntax errors.  When makeItSafe is false, there is more
        ** flexibility in selecting offsets, resulting in a smaller table.  For non-terminal symbols, which are never
        ** syntax errors, makeItSafe can be false.
        */
        public static int acttab_insert(Acttab p, int makeItSafe)
        {
            Spec.Requires(Wf(p) && p.nLookahead > 0);
            Spec.Ensures(Wf(p) && p.nLookahead == 0 && p.nsymbol == Spec.Old(p.nsymbol) && p.nterminal == Spec.Old(p.nterminal));
            int i, j, k, n, end;
            System.Diagnostics.Debug.Assert(p.nLookahead > 0);

            /* Make sure we have enough space to hold the expanded action table in the worst case.  The worst case
            ** occurs if the transaction set must be appended to the current action table: then it starts at
            ** nAction + mnLookahead + 1 at the latest (below), and reaches mxLookahead - mnLookahead beyond.  (C
            ** reserves nsymbol + 1 slots, which mnLookahead + mxLookahead + 2 may exceed: then C's search for a hole
            ** can stop short and write past the table.  The size changes nothing else.)
            */
            n = 2 * p.nsymbol + 1;
            if (p.nAction + n >= p.nActionAlloc)
            {
                int oldAlloc = p.nActionAlloc;
                Spec.Assert(p.aAction_lookahead.Length == oldAlloc && p.aAction_action.Length == oldAlloc);
                Spec.Assert(Spec.Forall(0, oldAlloc, x => -1 <= p.aAction_lookahead[x] && p.aAction_lookahead[x] < p.nsymbol));
                Spec.Assert(Spec.Forall(p.nAction, oldAlloc, x => p.aAction_lookahead[x] == -1));
                if (p.nActionAlloc > MaxAlloc - p.nAction - n - 20) throw new System.OutOfMemoryException("malloc failed");
                p.nActionAlloc = p.nAction + n + p.nActionAlloc + 20;
                /* (realloc, then the new slots emptied: copied into new arrays) */
                int[] lookaheads = new int[p.nActionAlloc], actions = new int[p.nActionAlloc];
                for (i = 0; i < p.nActionAlloc; i++)
                {
                    Spec.Invariant(0 <= i && i <= p.nActionAlloc && oldAlloc < p.nActionAlloc &&
                                   lookaheads.Length == p.nActionAlloc && actions.Length == p.nActionAlloc &&
                                   p.aAction_lookahead.Length == oldAlloc && p.aAction_action.Length == oldAlloc &&
                                   Spec.Forall(0, oldAlloc, x => -1 <= p.aAction_lookahead[x] && p.aAction_lookahead[x] < p.nsymbol) &&
                                   Spec.Forall(p.nAction, oldAlloc, x => p.aAction_lookahead[x] == -1) &&
                                   Spec.Forall(0, i, x => -1 <= lookaheads[x] && lookaheads[x] < p.nsymbol) &&
                                   Spec.Forall(p.nAction, i, x => lookaheads[x] == -1));
                    lookaheads[i] = i < oldAlloc ? p.aAction_lookahead[i] : -1;
                    actions[i] = i < oldAlloc ? p.aAction_action[i] : -1;
                }
                p.aAction_lookahead = lookaheads;
                p.aAction_action = actions;
            }

            /* Scan the existing action table looking for an offset that is a duplicate of the current transaction
            ** set.  Fall out of the loop if and when the duplicate is found.
            **
            ** i is the index in p->aAction[] where p->mnLookahead is inserted.
            */
            end = makeItSafe != 0 ? p.mnLookahead : 0;
            for (i = p.nAction - 1; i >= end; i--)
            {
                Spec.Invariant(Wf(p) && -1 <= i && i < p.nAction && (end - 1 <= i || i == p.nAction - 1) && p.nActionAlloc > p.nAction + 2 * p.nsymbol);
                if (p.aAction_lookahead[i] == p.mnLookahead)
                {
                    /* All lookaheads and actions in the aLookahead[] transaction must match against the candidate
                    ** aAction[i] entry. */
                    if (p.aAction_action[i] != p.mnAction) continue;
                    for (j = 0; j < p.nLookahead; j++)
                    {
                        Spec.Invariant(0 <= j && j <= p.nLookahead);
                        k = p.aLookahead_lookahead[j] - p.mnLookahead + i;
                        if (k < 0 || k >= p.nAction) break;
                        if (p.aLookahead_lookahead[j] != p.aAction_lookahead[k]) break;
                        if (p.aLookahead_action[j] != p.aAction_action[k]) break;
                    }
                    if (j < p.nLookahead) continue;

                    /* No possible lookahead value that is not in the aLookahead[] transaction is allowed to match
                    ** aAction[i] */
                    n = 0;
                    for (j = 0; j < p.nAction; j++)
                    {
                        Spec.Invariant(0 <= j && j <= p.nAction && 0 <= n && n <= j);
                        if (p.aAction_lookahead[j] < 0) continue;
                        if (p.aAction_lookahead[j] == j + p.mnLookahead - i) n++;
                    }
                    if (n == p.nLookahead)
                    {
                        break;  /* An exact match is found at offset i */
                    }
                }
            }

            /* If no existing offsets exactly match the current transaction, find an an empty offset in the aAction[]
            ** table in which we can add the aLookahead[] transaction.
            */
            if (i < end)
            {
                /* Look for holes in the aAction[] table that fit the current aLookahead[] transaction.  Leave i set
                ** to the offset of the hole. If no holes are found, i is left at p->nAction, which means the
                ** transaction will be appended. */
                i = makeItSafe != 0 ? p.mnLookahead : 0;
                for (; i < p.nActionAlloc - p.mxLookahead; i++)
                {
                    /* (a hole is found at nAction + mnLookahead + 1 at the latest: every slot from there is empty,
                    ** and no slot below nAction holds j + mnLookahead - i, which is less than -1) */
                    Spec.Invariant(Wf(p) && 0 <= i && i <= p.nAction + p.mnLookahead + 1 && p.nActionAlloc > p.nAction + 2 * p.nsymbol);
                    if (p.aAction_lookahead[i] < 0)
                    {
                        for (j = 0; j < p.nLookahead; j++)
                        {
                            Spec.Invariant(0 <= j && j <= p.nLookahead);
                            k = p.aLookahead_lookahead[j] - p.mnLookahead + i;
                            if (k < 0) break;
                            if (p.aAction_lookahead[k] >= 0) break;
                        }
                        if (j < p.nLookahead) continue;
                        for (j = 0; j < p.nAction; j++)
                        {
                            Spec.Invariant(0 <= j && j <= p.nAction);
                            if (p.aAction_lookahead[j] == j + p.mnLookahead - i) break;
                        }
                        if (j == p.nAction)
                        {
                            break;  /* Fits in empty slots */
                        }
                    }
                }
            }
            /* Insert transaction set at index i. */
            for (j = 0; j < p.nLookahead; j++)
            {
                Spec.Invariant(Wf(p) && 0 <= j && j <= p.nLookahead && 0 <= i && i + p.mxLookahead - p.mnLookahead < p.nActionAlloc &&
                               i + p.nterminal < p.nActionAlloc);
                k = p.aLookahead_lookahead[j] - p.mnLookahead + i;
                p.aAction_lookahead[k] = p.aLookahead_lookahead[j];
                p.aAction_action[k] = p.aLookahead_action[j];
                if (k >= p.nAction) p.nAction = k + 1;
            }
            if (makeItSafe != 0 && i + p.nterminal >= p.nAction) p.nAction = i + p.nterminal + 1;
            p.nLookahead = 0;

            /* Return the offset that is added to the lookahead in order to get the index into yy_action of the
            ** action */
            return i - p.mnLookahead;
        }

        /*
        ** Return the size of the action table without the trailing syntax error entries.
        */
        public static int acttab_action_size(Acttab p)
        {
            Spec.Requires(Wf(p));
            Spec.Ensures((int r) => 0 <= r && r <= p.nAction);
            int n = p.nAction;
            while (n > 0 && p.aAction_lookahead[n - 1] < 0)
            {
                Spec.Invariant(0 <= n && n <= p.nAction);
                n--;
            }
            return n;
        }
    }
}
