#nullable enable
namespace CsVerify.Bcl
{
    using System.Collections.Generic;

    /// <summary>
    /// The model functions of the BCL collections the CsVerify contracts specify: what a list or a dictionary holds,
    /// as ghost state. Use them in specifications (<c>using CsVerify.Bcl;</c>, then <c>list.Items()</c>); they never run.
    /// </summary>
    public static class Models
    {
        /// <summary>The elements of a list, in order: those at 0 to <c>Size() - 1</c>.</summary>
        [Model] public static Seq<T> Items<T>(this List<T> list) => throw null!;

        /// <summary>How many elements a list has (its Count).</summary>
        [Model]
        public static int Size<T>(this List<T> list)
        {
            Spec.Ensures<int>(r => r >= 0);
            throw null!;
        }

        /// <summary>Which keys a dictionary has.</summary>
        [Model] public static Map<K, bool> Domain<K, V>(this Dictionary<K, V> dictionary) where K : notnull => throw null!;

        /// <summary>The value a dictionary has at each key (meaningful where <see cref="Domain"/> has the key).</summary>
        [Model] public static Map<K, V> Entries<K, V>(this Dictionary<K, V> dictionary) where K : notnull => throw null!;

        /// <summary>How many keys a dictionary has (its Count).</summary>
        [Model]
        public static int Size<K, V>(this Dictionary<K, V> dictionary) where K : notnull
        {
            Spec.Ensures<int>(r => r >= 0);
            throw null!;
        }
    }

    /// <summary>
    /// Contracts for <see cref="List{T}"/>: its contents are <c>Items()</c> up to <c>Size()</c>.
    /// Indices out of range are preconditions (the list would throw).
    /// </summary>
    [ContractsFor(typeof(List<>))]
    public static class ListContracts<T>
    {
        public static List<T> @new()
        {
            Spec.Ensures<List<T>>(r => r.Size() == 0);
            throw null!;
        }

        public static List<T> @new(int capacity)
        {
            Spec.Requires(capacity >= 0);
            Spec.Ensures<List<T>>(r => r.Size() == 0);
            throw null!;
        }

        [Pure]
        public static int get_Count(List<T> @this)
        {
            Spec.Ensures<int>(r => r == @this.Size() && r >= 0);
            throw null!;
        }

        [Pure]
        public static T get_Item(List<T> @this, int index)
        {
            Spec.Requires(0 <= index && index < @this.Size());
            Spec.Ensures<T>(r => Ghost.Of(r) == @this.Items()[index]);
            throw null!;
        }

        public static void set_Item(List<T> @this, int index, T value)
        {
            Spec.Requires(0 <= index && index < @this.Size());
            Spec.Modifies(ObjSet.Of(@this));
            Spec.Ensures(@this.Size() == Spec.Old(@this.Size()));
            Spec.Ensures(@this.Items() == Spec.Old(@this.Items()).Update(index, Ghost.Of(value)));
            throw null!;
        }

        public static void Add(List<T> @this, T item)
        {
            Spec.Modifies(ObjSet.Of(@this));
            Spec.Ensures(@this.Size() == Spec.Old(@this.Size()) + 1);
            Spec.Ensures(@this.Items() == Spec.Old(@this.Items()).Update(Spec.Old(@this.Size()), Ghost.Of(item)));
            throw null!;
        }

        public static void RemoveAt(List<T> @this, int index)
        {
            Spec.Requires(0 <= index && index < @this.Size());
            Spec.Modifies(ObjSet.Of(@this));
            Spec.Ensures(@this.Size() == Spec.Old(@this.Size()) - 1);
            Spec.Ensures(@this.Items() == Spec.Old(@this.Items()).Concat(index, Spec.Old(@this.Items()).Drop(index + 1)));
            throw null!;
        }

        public static void Insert(List<T> @this, int index, T item)
        {
            Spec.Requires(0 <= index && index <= @this.Size());
            Spec.Modifies(ObjSet.Of(@this));
            Spec.Ensures(@this.Size() == Spec.Old(@this.Size()) + 1);
            Spec.Ensures(@this.Items()[index] == Ghost.Of(item));
            Spec.Ensures(Spec.Forall(0, index, i => @this.Items()[i] == Spec.Old(@this.Items())[i]));
            Spec.Ensures(Spec.Forall(index + 1, @this.Size(), i => @this.Items()[i] == Spec.Old(@this.Items())[i - 1]));
            throw null!;
        }

        public static void RemoveRange(List<T> @this, int index, int count)
        {
            Spec.Requires(0 <= index && 0 <= count && index <= @this.Size() - count);
            Spec.Modifies(ObjSet.Of(@this));
            Spec.Ensures(@this.Size() == Spec.Old(@this.Size()) - count);
            Spec.Ensures(@this.Items() == Spec.Old(@this.Items()).Concat(index, Spec.Old(@this.Items()).Drop(index + count)));
            throw null!;
        }

        // (what the collection holds is not known: the list keeps its elements and grows)
        public static void AddRange(List<T> @this, IEnumerable<T> collection)
        {
            Spec.Modifies(ObjSet.Of(@this));
            Spec.Ensures(@this.Size() >= Spec.Old(@this.Size()));
            Spec.Ensures(Spec.Forall(0, Spec.Old(@this.Size()), i => @this.Items()[i] == Spec.Old(@this.Items())[i]));
            throw null!;
        }

        public static void Reverse(List<T> @this)
        {
            Spec.Modifies(ObjSet.Of(@this));
            Spec.Ensures(@this.Size() == Spec.Old(@this.Size()));
            Spec.Ensures(Spec.Forall(0, @this.Size(), i => @this.Items()[i] == Spec.Old(@this.Items())[@this.Size() - 1 - i]));
            throw null!;
        }

        // (how it orders elements is the comparer's: only that it keeps the count)
        public static void Sort(List<T> @this)
        {
            Spec.Modifies(ObjSet.Of(@this));
            Spec.Ensures(@this.Size() == Spec.Old(@this.Size()));
            throw null!;
        }

        public static T[] ToArray(List<T> @this)
        {
            Spec.Ensures<T[]>(r => Spec.Fresh(r) && r.Length == @this.Size());
            Spec.Ensures<T[]>(r => Spec.Forall(0, r.Length, i => Ghost.Of(r[i]) == @this.Items()[i]));
            throw null!;
        }

        public static List<T> GetRange(List<T> @this, int index, int count)
        {
            Spec.Requires(0 <= index && 0 <= count && index <= @this.Size() - count);
            Spec.Ensures<List<T>>(r => Spec.Fresh(r) && r.Size() == count);
            Spec.Ensures<List<T>>(r => Spec.Forall(0, count, i => r.Items()[i] == @this.Items()[index + i]));
            throw null!;
        }

        // (equality is EqualityComparer<T>.Default's, Spec.Equal: exact where the verifier knows T's Equals)
        [Pure]
        public static int IndexOf(List<T> @this, T item)
        {
            Spec.Ensures<int>(r => -1 <= r && r < @this.Size());
            Spec.Ensures<int>(r => r < 0 || Spec.Equal(@this.Items()[r], Ghost.Of(item)));
            Spec.Ensures<int>(r => Spec.Forall(0, r < 0 ? @this.Size() : r, i => !Spec.Equal(@this.Items()[i], Ghost.Of(item))));
            throw null!;
        }

        [Pure]
        public static bool Contains(List<T> @this, T item)
        {
            Spec.Ensures<bool>(r => r == Spec.Exists(0, @this.Size(), i => Spec.Equal(@this.Items()[i], Ghost.Of(item))));
            throw null!;
        }

        // (the first element equal to item goes, as RemoveAt(IndexOf(item)) would)
        public static bool Remove(List<T> @this, T item)
        {
            Spec.Modifies(ObjSet.Of(@this));
            Spec.Ensures<bool>(r => r == (Spec.Old(@this.IndexOf(item)) >= 0));
            Spec.Ensures(Spec.Old(@this.IndexOf(item)) < 0 || @this.Size() == Spec.Old(@this.Size()) - 1 &&
                         @this.Items() == Spec.Old(@this.Items()).Concat(Spec.Old(@this.IndexOf(item)), Spec.Old(@this.Items()).Drop(Spec.Old(@this.IndexOf(item)) + 1)));
            Spec.Ensures(Spec.Old(@this.IndexOf(item)) >= 0 || @this.Size() == Spec.Old(@this.Size()) && @this.Items() == Spec.Old(@this.Items()));
            throw null!;
        }

        // (it changes nothing: a foreach over a list that a loop may change goes through it, and its MoveNext and Current)
        public static List<T>.Enumerator GetEnumerator(List<T> @this)
        {
            throw null!;
        }

        public static void Clear(List<T> @this)
        {
            Spec.Modifies(ObjSet.Of(@this));
            Spec.Ensures(@this.Size() == 0);
            throw null!;
        }
    }

    /// <summary>
    /// Contracts for <see cref="Dictionary{TKey, TValue}"/>: its keys are <see cref="Models.Domain"/>, its values
    /// <see cref="Models.Entries"/>. Keys are compared as the verifier compares values of their type, which is the
    /// dictionary's own comparison for integers, enums and other values, and for classes that keep reference
    /// equality; not for strings or classes that override Equals (see docs/limitations.md).
    /// </summary>
    [ContractsFor(typeof(Dictionary<,>))]
    public static class DictionaryContracts<K, V> where K : notnull
    {
        public static Dictionary<K, V> @new()
        {
            Spec.Ensures<Dictionary<K, V>>(r => r.Size() == 0 && r.Domain() == Map.Const<K, bool>(false));
            throw null!;
        }

        [Pure]
        public static int get_Count(Dictionary<K, V> @this)
        {
            Spec.Ensures<int>(r => r == @this.Size() && r >= 0);
            throw null!;
        }

        [Pure]
        public static bool ContainsKey(Dictionary<K, V> @this, K key)
        {
            Spec.Ensures<bool>(r => r == @this.Domain()[key].Value);
            throw null!;
        }

        [Pure]
        public static V get_Item(Dictionary<K, V> @this, K key)
        {
            Spec.Requires(@this.Domain()[key].Value);
            Spec.Ensures<V>(r => Ghost.Of(r) == @this.Entries()[key]);
            throw null!;
        }

        public static void set_Item(Dictionary<K, V> @this, K key, V value)
        {
            Spec.Modifies(ObjSet.Of(@this));
            Spec.Ensures(@this.Domain() == Spec.Old(@this.Domain()).Update(key, Ghost.Of(true)));
            Spec.Ensures(@this.Entries() == Spec.Old(@this.Entries()).Update(key, Ghost.Of(value)));
            Spec.Ensures(@this.Size() == Spec.Old(@this.Size()) + (Spec.Old(@this.Domain())[key].Value ? 0 : 1));
            throw null!;
        }

        public static void Add(Dictionary<K, V> @this, K key, V value)
        {
            Spec.Requires(!@this.Domain()[key].Value);
            Spec.Modifies(ObjSet.Of(@this));
            Spec.Ensures(@this.Domain() == Spec.Old(@this.Domain()).Update(key, Ghost.Of(true)));
            Spec.Ensures(@this.Entries() == Spec.Old(@this.Entries()).Update(key, Ghost.Of(value)));
            Spec.Ensures(@this.Size() == Spec.Old(@this.Size()) + 1);
            throw null!;
        }

        public static bool Remove(Dictionary<K, V> @this, K key)
        {
            Spec.Modifies(ObjSet.Of(@this));
            Spec.Ensures<bool>(r => r == Spec.Old(@this.Domain())[key].Value);
            Spec.Ensures(@this.Domain() == Spec.Old(@this.Domain()).Update(key, Ghost.Of(false)));
            Spec.Ensures(@this.Entries() == Spec.Old(@this.Entries()));
            Spec.Ensures(@this.Size() == Spec.Old(@this.Size()) - (Spec.Old(@this.Domain())[key].Value ? 1 : 0));
            throw null!;
        }

        public static bool TryGetValue(Dictionary<K, V> @this, K key, out V value)
        {
            value = default!; // (C# wants it set before the postconditions name it; a stub's body never runs)
            Spec.Ensures(Spec.Result<bool>() == @this.Domain()[key].Value);
            Spec.Ensures(!Spec.Result<bool>() || Ghost.Of(value) == @this.Entries()[key]);
            throw null!;
        }
    }
}
