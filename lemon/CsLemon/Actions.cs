// Routines processing parser actions in the LEMON parser generator (action.c), and the "acttab" module that
// builds the yy_action[] table.
using System.Collections.Generic;

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

        /* Allocate a new parser action */
        public static LemonAction Action_new()
        {
            LemonAction newaction = new LemonAction();
            newaction.seq = nextSeq;
            nextSeq++;
            return newaction;
        }

        /* Compare two actions for sorting purposes.  Return negative, zero, or positive if the first action is less
        ** than, equal to, or greater than the first
        */
        public static int actioncmp(LemonAction ap1, LemonAction ap2)
        {
            int rc;
            rc = ap1.sp.index - ap2.sp.index;
            if (rc == 0)
            {
                rc = (int)ap1.type - (int)ap2.type;
            }
            if (rc == 0 && (ap1.type == ActionType.REDUCE || ap1.type == ActionType.SHIFTREDUCE))
            {
                rc = ap1.rp!.index - ap2.rp!.index;
            }
            if (rc == 0)
            {
                rc = ap2.seq - ap1.seq;
            }
            return rc;
        }

        /* Sort parser actions */
        public static LemonAction? Action_sort(LemonAction? ap)
        {
            ap = MSort.SortActions(ap);
            return ap;
        }

        /* Add an action to the front of the list *app.  C's char* arg is stp for a SHIFT and rp otherwise. */
        public static void Action_add(ref LemonAction? app, ActionType type, Symbol sp, State? stp, Rule? rp)
        {
            LemonAction newaction;
            newaction = Action_new();
            newaction.next = app;
            app = newaction;
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
        }

        /********************** New code to implement the "acttab" module ***********/

        /* Return the number of entries in the yy_action table */
        public static int acttab_lookahead_size(Acttab p)
        {
            return p.nAction;
        }

        /* The value for the N-th entry in yy_action */
        public static int acttab_yyaction(Acttab p, int N)
        {
            return p.aAction_action[N];
        }

        /* The value for the N-th entry in yy_lookahead */
        public static int acttab_yylookahead(Acttab p, int N)
        {
            return p.aAction_lookahead[N];
        }

        /* Free all memory associated with the given acttab (the collector does) */
        public static void acttab_free(Acttab p)
        {
        }

        /* Allocate a new acttab structure */
        public static Acttab acttab_alloc(int nsymbol, int nterminal)
        {
            Acttab p = new Acttab();
            p.nsymbol = nsymbol;
            p.nterminal = nterminal;
            return p;
        }

        /* realloc of an int array to n slots, keeping the old contents */
        private static int[] realloc(int[] a, int n)
        {
            int[] b = new int[n];
            int i;
            for (i = 0; i < a.Length && i < n; i++) b[i] = a[i];
            return b;
        }

        /* Add a new action to the current transaction set.
        **
        ** This routine is called once for each lookahead for a particular state.
        */
        public static void acttab_action(Acttab p, int lookahead, int action)
        {
            if (p.nLookahead >= p.nLookaheadAlloc)
            {
                p.nLookaheadAlloc += 25;
                p.aLookahead_lookahead = realloc(p.aLookahead_lookahead, p.nLookaheadAlloc);
                p.aLookahead_action = realloc(p.aLookahead_action, p.nLookaheadAlloc);
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
            int i, j, k, n, end;
            System.Diagnostics.Debug.Assert(p.nLookahead > 0);

            /* Make sure we have enough space to hold the expanded action table in the worst case.  The worst case
            ** occurs if the transaction set must be appended to the current action table
            */
            n = p.nsymbol + 1;
            if (p.nAction + n >= p.nActionAlloc)
            {
                int oldAlloc = p.nActionAlloc;
                p.nActionAlloc = p.nAction + n + p.nActionAlloc + 20;
                p.aAction_lookahead = realloc(p.aAction_lookahead, p.nActionAlloc);
                p.aAction_action = realloc(p.aAction_action, p.nActionAlloc);
                for (i = oldAlloc; i < p.nActionAlloc; i++)
                {
                    p.aAction_lookahead[i] = -1;
                    p.aAction_action[i] = -1;
                }
            }

            /* Scan the existing action table looking for an offset that is a duplicate of the current transaction
            ** set.  Fall out of the loop if and when the duplicate is found.
            **
            ** i is the index in p->aAction[] where p->mnLookahead is inserted.
            */
            end = makeItSafe != 0 ? p.mnLookahead : 0;
            for (i = p.nAction - 1; i >= end; i--)
            {
                if (p.aAction_lookahead[i] == p.mnLookahead)
                {
                    /* All lookaheads and actions in the aLookahead[] transaction must match against the candidate
                    ** aAction[i] entry. */
                    if (p.aAction_action[i] != p.mnAction) continue;
                    for (j = 0; j < p.nLookahead; j++)
                    {
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
                    if (p.aAction_lookahead[i] < 0)
                    {
                        for (j = 0; j < p.nLookahead; j++)
                        {
                            k = p.aLookahead_lookahead[j] - p.mnLookahead + i;
                            if (k < 0) break;
                            if (p.aAction_lookahead[k] >= 0) break;
                        }
                        if (j < p.nLookahead) continue;
                        for (j = 0; j < p.nAction; j++)
                        {
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
            int n = p.nAction;
            while (n > 0 && p.aAction_lookahead[n - 1] < 0) { n--; }
            return n;
        }
    }
}
