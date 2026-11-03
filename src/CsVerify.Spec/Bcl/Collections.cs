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
