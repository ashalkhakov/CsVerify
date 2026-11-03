using System.Diagnostics;
using CsVerify;

namespace Samples
{
    // A port, and a clean-up, of dafny-lemon (Artyom Shalkhakov, 2024): Lemon's data structures, translated to
    // Dafny, translated again to C#.
    //
    // dafny-lemon's hashset.dfy and hashmap.dfy (two near-copies, as Lemon's x1..x4 are) build the table from linked
    // node objects with ghost lists, sets and node sets, and gave up on parts of it: resize is commented out,
    // resize_aux ends in `assume false`, and keeping the count in the invariant is a "FIXME: ... makes [insert]
    // verification to time out". Here the table goes back to Lemon's own layout, which needs none of that:
    //   tbl[0..count) holds the entries, in the order they came; ht[h] is the newest entry of bucket h (or -1); an
    //   entry's next is the newest earlier entry of its bucket (or -1).
    // Chains run to smaller indices, so a walk ends, and the whole invariant is a few quantifiers over arrays (Wf).
    // One table serves as set and map (values ignored for the set); insert grows it by doubling, as Lemon does,
    // keeping every entry at its index; find is complete (not found means absent). Keys are ints (interned
    // strings: CsVerify does not model a C# string's characters).

    /// <summary>s_x2: the table's arrays (tbl split into keys, values and next links), its size and its count.</summary>
    [Owned]
    public sealed class LemonTable
    {
        public int[] Keys, Values, Next, Ht;
        public int Size, Count;

        public LemonTable(int[] keys, int[] values, int[] next, int[] ht, int size)
        {
            Spec.Ensures(Keys == keys && Values == values && Next == next && Ht == ht && Size == size && Count == 0);
            Keys = keys; Values = values; Next = next; Ht = ht; Size = size;
        }
    }

    public static class LemonHash
    {
        public const int MaxSize = 1 << 28;

        /// <summary>The bucket of a key: ph % size, made non-negative (Lemon masks with size - 1).</summary>
        [Pure]
        public static int Slot(int key, int size)
        {
            Spec.Requires(size > 0);
            Spec.Ensures((int r) => 0 <= r && r < size);
            int m = key % size;
            return m < 0 ? m + size : m;
        }

        /// <summary>
        /// The table is well formed: heads and links are entries or -1, a head is its bucket's newest entry, an
        /// entry's next is the newest earlier entry of its bucket, and keys are distinct.
        /// </summary>
        [GhostFunction]
        public static bool Wf(int[] keys, int[] next, int[] ht, int count, int size)
        {
            Spec.Requires(0 < size && 0 <= count && count <= size && keys.Length == size && next.Length == size && ht.Length == size);
            return Spec.Forall(0, size, h => -1 <= ht[h] && ht[h] < count) &&
                   Spec.Forall(0, size, h => ht[h] == -1
                       ? Spec.Forall(0, count, i => Slot(keys[i], size) != h)
                       : Slot(keys[ht[h]], size) == h && Spec.Forall(ht[h] + 1, count, i => Slot(keys[i], size) != h)) &&
                   Spec.Forall(0, count, i => -1 <= next[i] && next[i] < i) &&
                   Spec.Forall(0, count, i => next[i] == -1
                       ? Spec.Forall(0, i, j => Slot(keys[j], size) != Slot(keys[i], size))
                       : Slot(keys[next[i]], size) == Slot(keys[i], size) &&
                         Spec.Forall(next[i] + 1, i, j => Slot(keys[j], size) != Slot(keys[i], size))) &&
                   Spec.Forall(0, count, i => Spec.Forall(0, i, j => keys[j] != keys[i]));
        }

        // ------------------------------------------------------------------------------------------ on the arrays

        /// <summary>x2find's walk: the entry with the key, or -1 when no entry has it.</summary>
        public static int FindIn(int[] keys, int[] next, int[] ht, int count, int size, int key)
        {
            Spec.Requires(0 < size && 0 <= count && count <= size && keys.Length == size && next.Length == size && ht.Length == size);
            Spec.Requires(Wf(keys, next, ht, count, size));
            Spec.Ensures((int r) => r == -1 ? Spec.Forall(0, count, i => keys[i] != key) : 0 <= r && r < count && keys[r] == key);
            int h = Slot(key, size);
            int np = ht[h];
            while (np != -1)
            {
                // every entry of the bucket above np has been looked at
                Spec.Invariant(-1 <= np && np < count && (np == -1 || Slot(keys[np], size) == h));
                Spec.Invariant(Spec.Forall(np + 1, count, i => Slot(keys[i], size) == h ? keys[i] != key : true));
                Spec.Decreases(np + 1);
                if (keys[np] == key) return np;
                np = next[np];
            }
            // and the entries of other buckets do not have the key: it would be in bucket h
            Spec.Assert(Spec.Forall(0, count, i => Slot(keys[i], size) != h ? keys[i] != key : true));
            return -1;
        }

        /// <summary>
        /// Puts a new key at entry count, at the head of its bucket (np->next = ht[h]; ht[h] = np): the next entry of
        /// a table with room.
        /// </summary>
        public static void AddAt(int[] keys, int[] values, int[] next, int[] ht, int count, int size, int key, int value)
        {
            Spec.Requires(0 < size && 0 <= count && count < size && keys.Length == size && values.Length == size && next.Length == size && ht.Length == size);
            Spec.Requires(keys != values && keys != next && keys != ht && values != next && values != ht && next != ht);
            Spec.Requires(Spec.Acc(keys) && Spec.Acc(values) && Spec.Acc(next) && Spec.Acc(ht));
            Spec.Requires(Wf(keys, next, ht, count, size) && Spec.Forall(0, count, i => keys[i] != key));
            Spec.Ensures(Spec.Acc(keys) && Spec.Acc(values) && Spec.Acc(next) && Spec.Acc(ht));
            Spec.Ensures(Wf(keys, next, ht, count + 1, size) && keys[count] == key && values[count] == value);
            Spec.Ensures(Spec.Forall(0, count, i => keys[i] == Spec.Old(keys[i]) && values[i] == Spec.Old(values[i])));
            int h = Slot(key, size);
            keys[count] = key;
            values[count] = value;
            next[count] = ht[h];
            ht[h] = count;
        }

        // ------------------------------------------------------------------------------------------ the table
        // Table(t): the table's header and arrays held, and well formed.

        [Predicate]
        public static bool Table(LemonTable t) =>
            t != null && Spec.Acc(t) && t.Keys != null && t.Values != null && t.Next != null && t.Ht != null &&
            0 < t.Size && t.Size <= MaxSize && 0 <= t.Count && t.Count <= t.Size &&
            t.Keys.Length == t.Size && t.Values.Length == t.Size && t.Next.Length == t.Size && t.Ht.Length == t.Size &&
            Spec.Acc(t.Keys) && Spec.Acc(t.Values) && Spec.Acc(t.Next) && Spec.Acc(t.Ht) &&
            Wf(t.Keys, t.Next, t.Ht, t.Count, t.Size);

        /// <summary>The number of entries (x2a->count).</summary>
        [Pure]
        public static int Count(LemonTable t)
        {
            Spec.Requires(Table(t));
            Spec.Ensures((int r) => 0 <= r && r <= MaxSize);
            Spec.Unfold(Table(t));
            return t.Count;
        }

        /// <summary>Entry i's key (tbl[i].key), for specifications and Symbol_Nth.</summary>
        [Pure]
        public static int Key(LemonTable t, int i)
        {
            Spec.Requires(Table(t) && 0 <= i && i < Count(t));
            Spec.Unfold(Table(t));
            return t.Keys[i];
        }

        /// <summary>Entry i's value.</summary>
        [Pure]
        public static int Value(LemonTable t, int i)
        {
            Spec.Requires(Table(t) && 0 <= i && i < Count(t));
            Spec.Unfold(Table(t));
            return t.Values[i];
        }

        /// <summary>The key is in the table.</summary>
        [GhostFunction]
        public static bool Contains(LemonTable t, int key)
        {
            Spec.Requires(Table(t));
            Spec.Unfold(Table(t));
            return Spec.Exists(0, t.Count, i => t.Keys[i] == key);
        }

        // ------------------------------------------------------------------------------------------ x2 operations

        /// <summary>x2init: an empty table with room for size entries.</summary>
        public static LemonTable Init(int size)
        {
            Spec.Requires(0 < size && size <= MaxSize);
            Spec.Ensures((LemonTable r) => Table(r) && Count(r) == 0);
            var keys = new int[size];
            var values = new int[size];
            var next = new int[size];
            var ht = new int[size];
            for (int h = 0; h < size; h++)
            {
                Spec.Invariant(0 <= h && h <= size && Spec.Forall(0, h, k => ht[k] == -1));
                ht[h] = -1;
            }
            var t = Own.New(new LemonTable(keys, values, next, ht, size), out var view);
            Own.ToAcc(view);
            Spec.Fold(Table(t));
            return t;
        }

        /// <summary>x2find: the entry with the key (its index), or -1 if the key is not in the table.</summary>
        public static int Find(LemonTable t, int key)
        {
            Spec.Requires(Table(t));
            Spec.Ensures((int r) => Table(t) && Count(t) == Spec.Old(Count(t)) && Spec.Forall(0, Count(t), i => Key(t, i) == Spec.Old(Key(t, i)) && Value(t, i) == Spec.Old(Value(t, i))));
            Spec.Ensures((int r) => r == -1 ? !Contains(t, key) : 0 <= r && r < Count(t) && Key(t, r) == key);
            Spec.Unfold(Table(t));
            int r = FindIn(t.Keys, t.Next, t.Ht, t.Count, t.Size, key);
            Spec.Fold(Table(t));
            return r;
        }

        /// <summary>
        /// x2insert: adds the key and its value unless the key is there already (prior data is NOT overwritten).
        /// A full table first doubles (Lemon's arrSize = size * 2): every entry is added again, at its own index,
        /// to fresh arrays. Entries keep their indices, so Nth is stable.
        /// </summary>
        public static bool Insert(LemonTable t, int key, int value)
        {
            Spec.Requires(Table(t) && Count(t) < MaxSize / 2);
            Spec.Ensures((bool added) => Table(t) && added == !Spec.Old(Contains(t, key)) && Count(t) == Spec.Old(Count(t)) + (added ? 1 : 0));
            Spec.Ensures(Spec.Forall(0, Spec.Old(Count(t)), i => Key(t, i) == Spec.Old(Key(t, i)) && Value(t, i) == Spec.Old(Value(t, i))));
            Spec.Ensures((bool added) => added ? Key(t, Spec.Old(Count(t))) == key && Value(t, Spec.Old(Count(t))) == value : true);
            Spec.Unfold(Table(t));
            int found = FindIn(t.Keys, t.Next, t.Ht, t.Count, t.Size, key);
            if (found != -1)
            {
                Spec.Fold(Table(t));
                return false;
            }
            if (t.Count == t.Size) Grow(t);
            AddAt(t.Keys, t.Values, t.Next, t.Ht, t.Count, t.Size, key, value);
            t.Count = t.Count + 1;
            Spec.Fold(Table(t));
            return true;
        }

        /// <summary>The doubling: fresh arrays of twice the size, every entry added again at its index.</summary>
        private static void Grow(LemonTable t)
        {
            Spec.Requires(Spec.Acc(t) && t.Keys != null && t.Values != null && t.Next != null && t.Ht != null);
            Spec.Requires(0 < t.Size && t.Size <= MaxSize / 2 && t.Count == t.Size);
            Spec.Requires(t.Keys.Length == t.Size && t.Values.Length == t.Size && t.Next.Length == t.Size && t.Ht.Length == t.Size);
            Spec.Requires(Wf(t.Keys, t.Next, t.Ht, t.Count, t.Size));
            Spec.Ensures(Spec.Acc(t) && t.Keys != null && t.Values != null && t.Next != null && t.Ht != null);
            Spec.Ensures(t.Size == 2 * Spec.Old(t.Size) && t.Count == Spec.Old(t.Count) && t.Count < t.Size);
            Spec.Ensures(t.Keys.Length == t.Size && t.Values.Length == t.Size && t.Next.Length == t.Size && t.Ht.Length == t.Size);
            Spec.Ensures(Spec.Acc(t.Keys) && Spec.Acc(t.Values) && Spec.Acc(t.Next) && Spec.Acc(t.Ht));
            Spec.Ensures(Wf(t.Keys, t.Next, t.Ht, t.Count, t.Size));
            Spec.Ensures(Spec.Forall(0, t.Count, i => t.Keys[i] == Spec.Old(t.Keys[i]) && t.Values[i] == Spec.Old(t.Values[i])));
            int size2 = t.Size * 2;
            int[] keys = t.Keys, values = t.Values;
            Spec.Assert(Spec.Forall(0, t.Count, a => Spec.Forall(0, a, b => keys[b] != keys[a]))); // (from Wf)
            var k2 = new int[size2];
            var v2 = new int[size2];
            var n2 = new int[size2];
            var h2 = new int[size2];
            for (int h = 0; h < size2; h++)
            {
                Spec.Invariant(0 <= h && h <= size2 && Spec.Forall(0, h, k => h2[k] == -1));
                h2[h] = -1;
            }
            for (int i = 0; i < t.Count; i++)
            {
                Spec.Invariant(0 <= i && i <= t.Count && Spec.Acc(k2) && Spec.Acc(v2) && Spec.Acc(n2) && Spec.Acc(h2));
                Spec.Invariant(Wf(k2, n2, h2, i, size2));
                Spec.Invariant(Spec.Forall(0, i, j => k2[j] == keys[j] && v2[j] == values[j]));
                // the old arrays are not given to AddAt: their cells stay as they were, keys distinct
                Spec.Invariant(Spec.Forall(0, t.Count, j => keys[j] == Spec.Old(t.Keys[j]) && values[j] == Spec.Old(t.Values[j])));
                Spec.Invariant(Spec.Forall(0, t.Count, a => Spec.Forall(0, a, b => keys[b] != keys[a])));
                AddAt(k2, v2, n2, h2, i, size2, keys[i], values[i]);
            }
            t.Keys = k2;
            t.Values = v2;
            t.Next = n2;
            t.Ht = h2;
            t.Size = size2;
        }

        /// <summary>Symbol_Nth: entry n's key.</summary>
        public static int Nth(LemonTable t, int n)
        {
            Spec.Requires(Table(t) && 0 <= n && n < Count(t));
            Spec.Ensures((int r) => Table(t) && Count(t) == Spec.Old(Count(t)) && Spec.Forall(0, Count(t), i => Key(t, i) == Spec.Old(Key(t, i)) && Value(t, i) == Spec.Old(Value(t, i))) && r == Key(t, n));
            Spec.Unfold(Table(t));
            int r = t.Keys[n];
            Spec.Fold(Table(t));
            return r;
        }

        /// <summary>Symbol_arrayof: the keys, in entry order, in a fresh array.</summary>
        public static int[] ArrayOf(LemonTable t)
        {
            Spec.Requires(Table(t));
            Spec.Ensures((int[] r) => Table(t) && Count(t) == Spec.Old(Count(t)) && Spec.Forall(0, Count(t), i => Key(t, i) == Spec.Old(Key(t, i)) && Value(t, i) == Spec.Old(Value(t, i))) && r.Length == Count(t) && Spec.Forall(0, Count(t), i => r[i] == Key(t, i)));
            Spec.Unfold(Table(t));
            var arr = new int[t.Count];
            for (int i = 0; i < t.Count; i++)
            {
                Spec.Invariant(0 <= i && i <= t.Count && Spec.Forall(0, i, j => arr[j] == t.Keys[j]));
                arr[i] = t.Keys[i];
            }
            Spec.Fold(Table(t));
            return arr;
        }
    }

    /// <summary>struct.dfy's LTable: Lemon's string-safe set (x1) and symbol map (x2), each a LemonTable.</summary>
    [Owned]
    public sealed class LemonTables
    {
        public LemonTable Strings, Symbols;

        public LemonTables(LemonTable strings, LemonTable symbols)
        {
            Spec.Ensures(Strings == strings && Symbols == symbols);
            Strings = strings;
            Symbols = symbols;
        }
    }

    public static class LemonStruct
    {
        /// <summary>
        /// LTable.Valid. dafny-lemon asserts its two tables' footprints disjoint by hand (symbols.Repr() !!
        /// strings.Repr()); here two predicates held together are disjoint, and that is all.
        /// </summary>
        [Predicate]
        public static bool Tables(LemonTables lt) =>
            lt != null && Spec.Acc(lt) && lt.Strings != null && lt.Symbols != null &&
            LemonHash.Table(lt.Strings) && LemonHash.Table(lt.Symbols);

        public static LemonTables Init()
        {
            Spec.Ensures((LemonTables r) => Tables(r));
            var lt = Own.New(new LemonTables(LemonHash.Init(1024), LemonHash.Init(64)), out var view);
            Own.ToAcc(view);
            Spec.Fold(Tables(lt));
            return lt;
        }

        /// <summary>Strsafe_insert: the string (its id) is in the string table afterwards.</summary>
        public static bool StrsafeInsert(LemonTables lt, int s)
        {
            Spec.Requires(Tables(lt));
            Spec.Ensures(Tables(lt));
            Spec.Unfold(Tables(lt));
            bool added = LemonHash.Count(lt.Strings) < LemonHash.MaxSize / 2 && LemonHash.Insert(lt.Strings, s, 0);
            Spec.Fold(Tables(lt));
            return added;
        }

        /// <summary>Symbol_insert / Symbol_find: a symbol's index by its name, inserting it the first time.</summary>
        public static int Symbol(LemonTables lt, int name)
        {
            Spec.Requires(Tables(lt));
            Spec.Ensures((int r) => Tables(lt) && -1 <= r);
            Spec.Unfold(Tables(lt));
            int at = LemonHash.Find(lt.Symbols, name);
            if (at == -1 && LemonHash.Count(lt.Symbols) < LemonHash.MaxSize / 2)
            {
                int index = LemonHash.Count(lt.Symbols);
                LemonHash.Insert(lt.Symbols, name, index);
                at = index;
            }
            int r = at;
            Spec.Fold(Tables(lt));
            return r;
        }
    }

    /// <summary>set.dfy (Lemon's set.c): sets of 0..size-1 as bool arrays.</summary>
    public static class LemonSet
    {
        /// <summary>SetNew: an empty set.</summary>
        public static bool[] SetNew(int size)
        {
            Spec.Requires(size > 0);
            Spec.Ensures((bool[] r) => r.Length == size && Spec.Acc(r) && Spec.Forall(0, size, k => !r[k]));
            return new bool[size];
        }

        /// <summary>SetAdd: true if e was already there.</summary>
        public static bool SetAdd(bool[] s, int e)
        {
            Spec.Requires(0 <= e && e < s.Length && Spec.Acc(s, e, e + 1));
            Spec.Ensures((bool rv) => Spec.Acc(s, e, e + 1) && rv == Spec.Old(s[e]) && s[e]);
            bool rv = s[e];
            s[e] = true;
            return rv;
        }

        /// <summary>SetUnion: s1 gets every element of s2; true if s1 changed.</summary>
        public static bool SetUnion(bool[] s1, bool[] s2)
        {
            Spec.Requires(s1.Length == s2.Length && s1 != s2 && Spec.Acc(s1));
            Spec.Ensures((bool progress) => Spec.Acc(s1) && Spec.Forall(0, s1.Length, k => s1[k] == (Spec.Old(s1[k]) || s2[k])));
            Spec.Ensures((bool progress) => progress == Spec.Exists(0, s1.Length, k => s1[k] != Spec.Old(s1[k])));
            bool progress = false;
            for (int i = 0; i < s1.Length; i++)
            {
                Spec.Invariant(0 <= i && i <= s1.Length);
                Spec.Invariant(Spec.Forall(0, i, k => s1[k] == (Spec.Old(s1[k]) || s2[k])) && Spec.Forall(i, s1.Length, k => s1[k] == Spec.Old(s1[k])));
                Spec.Invariant(progress == Spec.Exists(0, i, k => s1[k] != Spec.Old(s1[k])));
                if (s2[i] && !s1[i])
                {
                    progress = true;
                    s1[i] = true;
                }
            }
            return progress;
        }

        /// <summary>SetFind.</summary>
        public static bool SetFind(bool[] s, int i)
        {
            Spec.Requires(0 <= i && i < s.Length);
            Spec.Ensures((bool x) => x == s[i]);
            return s[i];
        }
    }

    /// <summary>option.dfy (Lemon's option.c): ISOPT.</summary>
    public static class LemonOption
    {
        /// <summary>ISOPT(X): X starts with '-' or '+', or contains '='.</summary>
        public static bool IsOpt(char[] x)
        {
            Spec.Requires(x.Length > 0);
            Spec.Ensures((bool r) => r == (x[0] == '-' || x[0] == '+' || Spec.Exists(0, x.Length, i => x[i] == '=')));
            if (x[0] == '-' || x[0] == '+') return true;
            for (int i = 0; i < x.Length; i++)
            {
                Spec.Invariant(0 <= i && i <= x.Length && Spec.Forall(0, i, k => x[k] != '='));
                if (x[i] == '=') return true;
            }
            return false;
        }

        /// <summary>A table of ids, a lookup, a growth, the entries in order.</summary>
        public static int Demo()
        {
            Spec.Ensures((int r) => r == 3);
            var t = LemonHash.Init(2);
            LemonHash.Insert(t, 10, 100);
            LemonHash.Insert(t, 20, 200);
            bool again = LemonHash.Insert(t, 10, 999);  // there already: not overwritten
            LemonHash.Insert(t, 30, 300);               // full: the table doubles
            int at = LemonHash.Find(t, 20);
            Spec.Assert(!again && at == 1 && LemonHash.Value(t, 0) == 100);
            var keys = LemonHash.ArrayOf(t);
            return keys.Length;
        }
    }
}
