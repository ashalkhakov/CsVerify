// Small modules of LEMON: set.c, plink.c, error.c, msort.c, and the hash tables of table.c (x1..x4).
using System.Collections.Generic;

namespace CsLemon
{
    /// <summary>set.c: sets of terminal numbers 0..size-1 (char* in C, bool[] here).</summary>
    public static class Sets
    {
        private static int size;

        /// <summary>Set the set size (n terminals and one more).</summary>
        public static void SetSize(int n)
        {
            size = n + 1;
        }

        public static int Size => size;

        /// <summary>Allocate a new set.</summary>
        public static bool[] SetNew()
        {
            return new bool[size];
        }

        /// <summary>Add a new element to the set.  Return true if the element was added and false if it was already there.</summary>
        public static bool SetAdd(bool[] s, int e)
        {
            bool rv = s[e];
            s[e] = true;
            return !rv;
        }

        /// <summary>Add every element of s2 to s1.  Return true if s1 changes.</summary>
        public static bool SetUnion(bool[] s1, bool[] s2)
        {
            bool progress = false;
            for (int i = 0; i < size && i < s1.Length && i < s2.Length; i++)
            {
                if (!s2[i]) continue;
                if (!s1[i])
                {
                    progress = true;
                    s1[i] = true;
                }
            }
            return progress;
        }

        /// <summary>SetFind: true if e is in s.</summary>
        public static bool SetFind(bool[] s, int e) => s[e];
    }

    /// <summary>plink.c: follow-set propagation links (the free list is the collector's).</summary>
    public static class Plinks
    {
        /// <summary>Add a plink to a plink list.</summary>
        public static void Plink_add(ref Plink? plpp, Config cfp)
        {
            var newlink = new Plink { cfp = cfp, next = plpp };
            plpp = newlink;
        }

        /// <summary>Transfer every plink on the list "from" to the list "to".</summary>
        public static void Plink_copy(ref Plink? to, Plink? from)
        {
            while (from != null)
            {
                Plink? nextpl = from.next;
                from.next = to;
                to = from;
                from = nextpl;
            }
        }

        /// <summary>Delete every plink on the list (the collector frees them).</summary>
        public static void Plink_delete(Plink? plp)
        {
        }
    }

    /// <summary>error.c.</summary>
    public static class Errors
    {
        public static void ErrorMsg(string filename, int lineno, string message)
        {
            System.Console.Error.Write(filename + ":" + lineno + ": " + message + "\n");
        }
    }

    /// <summary>
    /// msort.c: a merge sort of linked lists, kept exactly (ties are decided as in C, so outputs match). One copy
    /// per list: configurations by next, configurations by bp (the basis), actions by next.
    /// </summary>
    public static class MSort
    {
        private const int LISTSIZE = 30;

        // ---- configurations, linked by next

        private static Config? MergeNext(Config? a, Config? b)
        {
            Config? head;
            if (a == null) head = b;
            else if (b == null) head = a;
            else
            {
                Config ptr;
                if (Tables.Configcmp(a, b) <= 0) { ptr = a; a = a.next; }
                else { ptr = b; b = b.next; }
                head = ptr;
                while (a != null && b != null)
                {
                    if (Tables.Configcmp(a, b) <= 0) { ptr.next = a; ptr = a; a = a.next; }
                    else { ptr.next = b; ptr = b; b = b.next; }
                }
                ptr.next = a != null ? a : b;
            }
            return head;
        }

        public static Config? SortConfigsByNext(Config? list)
        {
            var set = new Config?[LISTSIZE];
            while (list != null)
            {
                Config? ep = list;
                list = list.next;
                ep.next = null;
                int i;
                for (i = 0; i < LISTSIZE - 1 && set[i] != null; i++)
                {
                    ep = MergeNext(ep, set[i]);
                    set[i] = null;
                }
                set[i] = ep;
            }
            Config? res = null;
            for (int i = 0; i < LISTSIZE; i++) if (set[i] != null) res = MergeNext(set[i], res);
            return res;
        }

        // ---- configurations, linked by bp

        private static Config? MergeBp(Config? a, Config? b)
        {
            Config? head;
            if (a == null) head = b;
            else if (b == null) head = a;
            else
            {
                Config ptr;
                if (Tables.Configcmp(a, b) <= 0) { ptr = a; a = a.bp; }
                else { ptr = b; b = b.bp; }
                head = ptr;
                while (a != null && b != null)
                {
                    if (Tables.Configcmp(a, b) <= 0) { ptr.bp = a; ptr = a; a = a.bp; }
                    else { ptr.bp = b; ptr = b; b = b.bp; }
                }
                ptr.bp = a != null ? a : b;
            }
            return head;
        }

        public static Config? SortConfigsByBp(Config? list)
        {
            var set = new Config?[LISTSIZE];
            while (list != null)
            {
                Config? ep = list;
                list = list.bp;
                ep.bp = null;
                int i;
                for (i = 0; i < LISTSIZE - 1 && set[i] != null; i++)
                {
                    ep = MergeBp(ep, set[i]);
                    set[i] = null;
                }
                set[i] = ep;
            }
            Config? res = null;
            for (int i = 0; i < LISTSIZE; i++) if (set[i] != null) res = MergeBp(set[i], res);
            return res;
        }

        // ---- actions, linked by next (compared by actioncmp, action.c)

        private static LemonAction? MergeActions(LemonAction? a, LemonAction? b)
        {
            LemonAction? head;
            if (a == null) head = b;
            else if (b == null) head = a;
            else
            {
                LemonAction ptr;
                if (Actions.actioncmp(a, b) <= 0) { ptr = a; a = a.next; }
                else { ptr = b; b = b.next; }
                head = ptr;
                while (a != null && b != null)
                {
                    if (Actions.actioncmp(a, b) <= 0) { ptr.next = a; ptr = a; a = a.next; }
                    else { ptr.next = b; ptr = b; b = b.next; }
                }
                ptr.next = a != null ? a : b;
            }
            return head;
        }

        public static LemonAction? SortActions(LemonAction? list)
        {
            var set = new LemonAction?[LISTSIZE];
            while (list != null)
            {
                LemonAction? ep = list;
                list = list.next;
                ep.next = null;
                int i;
                for (i = 0; i < LISTSIZE - 1 && set[i] != null; i++)
                {
                    ep = MergeActions(ep, set[i]);
                    set[i] = null;
                }
                set[i] = ep;
            }
            LemonAction? res = null;
            for (int i = 0; i < LISTSIZE; i++) if (set[i] != null) res = MergeActions(set[i], res);
            return res;
        }
    }

    /// <summary>
    /// table.c: Lemon's associative arrays x1 (strings), x2 (symbols), x3 (states by basis), x4 (configurations).
    /// Lemon only ever reads them back in insertion order (Symbol_arrayof, State_arrayof), which these keep.
    /// </summary>
    public static class Tables
    {
        // ---- x1: Strsafe. C# strings are values: the "safe copy" is the string itself.

        public static string Strsafe(string y) => y;

        // ---- x2: symbols by name

        private static readonly List<Symbol> symbolList = new List<Symbol>();
        private static readonly Dictionary<string, Symbol> symbolMap = new Dictionary<string, Symbol>();

        public static void Symbol_init()
        {
            symbolList.Clear();
            symbolMap.Clear();
        }

        /// <summary>Return a pointer to the (terminal or nonterminal) symbol "x".  Create a new symbol if this is the first time "x" has been seen.</summary>
        public static Symbol Symbol_new(string x)
        {
            Symbol? sp = Symbol_find(x);
            if (sp == null)
            {
                sp = new Symbol
                {
                    name = Strsafe(x),
                    type = x.Length > 0 && Chars.ISUPPER(x[0]) ? SymbolType.TERMINAL : SymbolType.NONTERMINAL,
                    prec = -1,
                    assoc = Assoc.UNK,
                };
                symbolList.Add(sp);
                symbolMap[x] = sp;
            }
            sp.useCnt++;
            return sp;
        }

        public static Symbol? Symbol_find(string key) => symbolMap.TryGetValue(key, out var sp) ? sp : null;

        public static int Symbol_count() => symbolList.Count;

        /// <summary>Symbol_arrayof: the symbols, in the order they were first seen.</summary>
        public static Symbol[] Symbol_arrayof() => symbolList.ToArray();

        /// <summary>
        /// Compare two symbols for sorting purposes.  Return negative, zero, or positive if a is less then, equal
        /// to, or greater than b.  Symbols that begin with upper case letters (terminals or tokens) must sort before
        /// symbols that begin with lower case letters (non-terminals).  And MULTITERMINAL symbols must sort at the
        /// very end. Other than that, the order does not matter.
        /// </summary>
        public static int Symbolcmpp(Symbol a, Symbol b)
        {
            int i1 = a.type == SymbolType.MULTITERMINAL ? 3 : a.name[0] > 'Z' ? 2 : 1;
            int i2 = b.type == SymbolType.MULTITERMINAL ? 3 : b.name[0] > 'Z' ? 2 : 1;
            return i1 == i2 ? a.index - b.index : i1 - i2;
        }

        // ---- configurations

        /// <summary>Compare two configurations.</summary>
        public static int Configcmp(Config a, Config b)
        {
            int x = a.rp.index - b.rp.index;
            if (x == 0) x = a.dot - b.dot;
            return x;
        }

        private static string BasisKey(Config? a)
        {
            var sb = new System.Text.StringBuilder();
            while (a != null)
            {
                sb.Append(a.rp.index).Append('.').Append(a.dot).Append(';');
                a = a.bp;
            }
            return sb.ToString();
        }

        // ---- x3: states by their basis

        private static readonly List<State> stateList = new List<State>();
        private static readonly Dictionary<string, State> stateMap = new Dictionary<string, State>();

        public static void State_init()
        {
            stateList.Clear();
            stateMap.Clear();
        }

        /// <summary>Insert a new state, keyed by its basis configurations (statecmp: the same rules and dots, in order).</summary>
        public static bool State_insert(State data, Config? key)
        {
            string k = BasisKey(key);
            if (stateMap.ContainsKey(k)) return false;
            stateMap[k] = data;
            stateList.Add(data);
            return true;
        }

        public static State? State_find(Config? key) => stateMap.TryGetValue(BasisKey(key), out var s) ? s : null;

        /// <summary>State_arrayof: the states, in the order they were made.</summary>
        public static State[] State_arrayof() => stateList.ToArray();

        // ---- x4: configurations by rule and dot

        private static readonly Dictionary<long, Config> configMap = new Dictionary<long, Config>();

        private static long ConfigKey(Config c) => ((long)c.rp.index << 32) | (uint)c.dot;

        public static void Configtable_init()
        {
            configMap.Clear();
        }

        public static bool Configtable_insert(Config data)
        {
            long k = ConfigKey(data);
            if (configMap.ContainsKey(k)) return false;
            configMap[k] = data;
            return true;
        }

        public static Config? Configtable_find(Config key) => configMap.TryGetValue(ConfigKey(key), out var c) ? c : null;

        /// <summary>Configtable_clear: forget every configuration (they live on in their states).</summary>
        public static void Configtable_clear()
        {
            configMap.Clear();
        }
    }

    /// <summary>The ctype.h tests Lemon uses (ISSPACE, ISDIGIT, ISALNUM, ISALPHA, ISUPPER, ISLOWER), on ASCII as C's do in the "C" locale.</summary>
    public static class Chars
    {
        public static bool ISSPACE(char c) => c == ' ' || c == '\t' || c == '\n' || c == '\v' || c == '\f' || c == '\r';
        public static bool ISDIGIT(char c) => c >= '0' && c <= '9';
        public static bool ISUPPER(char c) => c >= 'A' && c <= 'Z';
        public static bool ISLOWER(char c) => c >= 'a' && c <= 'z';
        public static bool ISALPHA(char c) => ISUPPER(c) || ISLOWER(c);
        public static bool ISALNUM(char c) => ISALPHA(c) || ISDIGIT(c);
    }
}
