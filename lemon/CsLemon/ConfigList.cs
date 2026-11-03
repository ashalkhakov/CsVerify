// Routines to processing a configuration list and building a state in the LEMON parser generator (configlist.c).
// The free list of configurations is gone (the collector frees them). C's "pointer to the last next/bp field"
// (currentend, basisend) becomes the last configuration on the list, null standing for "&current" / "&basis".
namespace CsLemon
{
    public static class ConfigList
    {
        private static Config? current = null;       /* Top of list of configurations */
        private static Config? currentend = null;    /* Last on list of configs (null: the list is empty) */
        private static Config? basis = null;         /* Top of list of basis configs */
        private static Config? basisend = null;      /* End of list of basis configs (null: the list is empty) */

        /* Return a pointer to a new configuration */
        private static Config newconfig()
        {
            return new Config();
        }

        /* Initialized the configuration list builder */
        public static void Configlist_init()
        {
            current = null;
            currentend = null;
            basis = null;
            basisend = null;
            Tables.Configtable_init();
        }

        /* Initialized the configuration list builder */
        public static void Configlist_reset()
        {
            current = null;
            currentend = null;
            basis = null;
            basisend = null;
            Tables.Configtable_clear();
        }

        /* Add another configuration to the configuration list */
        public static Config Configlist_add(
          Rule rp,    /* The rule */
          int dot     /* Index into the RHS of the rule where the dot goes */
        )
        {
            Config? cfp;
            Config model = new Config();
            model.rp = rp;
            model.dot = dot;
            cfp = Tables.Configtable_find(model);
            if (cfp == null)
            {
                cfp = newconfig();
                cfp.rp = rp;
                cfp.dot = dot;
                cfp.fws = Sets.SetNew();
                cfp.stp = null;
                cfp.fplp = null;
                cfp.bplp = null;
                cfp.next = null;
                cfp.bp = null;
                if (currentend == null) current = cfp; else currentend.next = cfp;
                currentend = cfp;
                Tables.Configtable_insert(cfp);
            }
            return cfp;
        }

        /* Add a basis configuration to the configuration list */
        public static Config Configlist_addbasis(Rule rp, int dot)
        {
            Config? cfp;
            Config model = new Config();
            model.rp = rp;
            model.dot = dot;
            cfp = Tables.Configtable_find(model);
            if (cfp == null)
            {
                cfp = newconfig();
                cfp.rp = rp;
                cfp.dot = dot;
                cfp.fws = Sets.SetNew();
                cfp.stp = null;
                cfp.fplp = null;
                cfp.bplp = null;
                cfp.next = null;
                cfp.bp = null;
                if (currentend == null) current = cfp; else currentend.next = cfp;
                currentend = cfp;
                if (basisend == null) basis = cfp; else basisend.bp = cfp;
                basisend = cfp;
                Tables.Configtable_insert(cfp);
            }
            return cfp;
        }

        /* Compute the closure of the configuration list */
        public static void Configlist_closure(Lemon lemp)
        {
            Config? cfp;
            Config newcfp;
            Rule rp;
            Rule? newrp;
            Symbol sp, xsp;
            int i, dot;

            for (cfp = current; cfp != null; cfp = cfp.next)
            {
                rp = cfp.rp;
                dot = cfp.dot;
                if (dot >= rp.nrhs) continue;
                sp = rp.rhs[dot];
                if (sp.type == SymbolType.NONTERMINAL)
                {
                    if (sp.rule == null && sp != lemp.errsym)
                    {
                        Errors.ErrorMsg(lemp.filename, rp.line, "Nonterminal \"" + sp.name + "\" has no rules.");
                        lemp.errorcnt++;
                    }
                    for (newrp = sp.rule; newrp != null; newrp = newrp.nextlhs)
                    {
                        newcfp = Configlist_add(newrp, 0);
                        for (i = dot + 1; i < rp.nrhs; i++)
                        {
                            xsp = rp.rhs[i];
                            if (xsp.type == SymbolType.TERMINAL)
                            {
                                Sets.SetAdd(newcfp.fws!, xsp.index);
                                break;
                            }
                            else if (xsp.type == SymbolType.MULTITERMINAL)
                            {
                                int k;
                                for (k = 0; k < xsp.nsubsym; k++)
                                {
                                    Sets.SetAdd(newcfp.fws!, xsp.subsym![k].index);
                                }
                                break;
                            }
                            else
                            {
                                Sets.SetUnion(newcfp.fws!, xsp.firstset!);
                                if (xsp.lambda == false) break;
                            }
                        }
                        if (i == rp.nrhs) Plinks.Plink_add(ref cfp.fplp, newcfp);
                    }
                }
            }
        }

        /* Sort the configuration list */
        public static void Configlist_sort()
        {
            current = MSort.SortConfigsByNext(current);
            currentend = null;
        }

        /* Sort the basis configuration list.  As in C, the sort starts at "current" and follows the bp links:
        ** only Configlist_addbasis has added to the lists, so current heads the basis list too. */
        public static void Configlist_sortbasis()
        {
            basis = MSort.SortConfigsByBp(current);
            basisend = null;
        }

        /* Return a pointer to the head of the configuration list and reset the list */
        public static Config? Configlist_return()
        {
            Config? old;
            old = current;
            current = null;
            currentend = null;
            return old;
        }

        /* Return a pointer to the head of the configuration list and reset the list */
        public static Config? Configlist_basis()
        {
            Config? old;
            old = basis;
            basis = null;
            basisend = null;
            return old;
        }

        /* Free all elements of the given configuration list (the collector frees them; only the checks remain) */
        public static void Configlist_eat(Config? cfp)
        {
            Config? nextcfp;
            for (; cfp != null; cfp = nextcfp)
            {
                nextcfp = cfp.next;
                System.Diagnostics.Debug.Assert(cfp.fplp == null);
                System.Diagnostics.Debug.Assert(cfp.bplp == null);
                cfp.fws = null;
            }
        }
    }
}
