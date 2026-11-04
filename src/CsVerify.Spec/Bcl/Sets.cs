#nullable enable
namespace CsVerify.Bcl
{
    using System.Collections.Generic;

    /// <summary>
    /// The model functions of HashSet, Stack and Queue: what they hold, as ghost state. A set's members are a Map keyed
    /// as EqualityComparer&lt;T&gt;.Default compares (Spec.Equal); a stack's items run from the bottom (Items()[Size() - 1]
    /// is the top), a queue's from the head.
    /// </summary>
    public static class CollectionModels
    {
        [Model] public static Map<T, bool> Members<T>(this HashSet<T> set) => throw null!;

        [Model]
        public static int Size<T>(this HashSet<T> set)
        {
            Spec.Ensures<int>(r => r >= 0);
            throw null!;
        }

        /// <summary>The set's version: what its enumerators check (see Models.Version).</summary>
        [Model] public static int Version<T>(this HashSet<T> set) => throw null!;

        [Model] public static int Version<T>(this Stack<T> stack) => throw null!;

        [Model] public static int Version<T>(this Queue<T> queue) => throw null!;

        [Model] public static Seq<T> Items<T>(this Stack<T> stack) => throw null!;

        [Model]
        public static int Size<T>(this Stack<T> stack)
        {
            Spec.Ensures<int>(r => r >= 0);
            throw null!;
        }

        [Model] public static Seq<T> Items<T>(this Queue<T> queue) => throw null!;

        [Model]
        public static int Size<T>(this Queue<T> queue)
        {
            Spec.Ensures<int>(r => r >= 0);
            throw null!;
        }
    }

    [ContractsFor(typeof(HashSet<>))]
    public static class HashSetContracts<T>
    {
        public static HashSet<T> @new()
        {
            Spec.Ensures<HashSet<T>>(r => r.Size() == 0 && r.Members() == Map.Const<T, bool>(false));
            throw null!;
        }

        [Pure]
        public static int get_Count(HashSet<T> @this)
        {
            Spec.Ensures<int>(r => r == @this.Size());
            throw null!;
        }

        [Pure]
        public static bool Contains(HashSet<T> @this, T item)
        {
            Spec.Ensures<bool>(r => r == @this.Members()[item].Value);
            throw null!;
        }

        public static bool Add(HashSet<T> @this, T item)
        {
            Spec.Modifies(ObjSet.Of(@this));
            Spec.Ensures<bool>(r => r == !Spec.Old(@this.Members()[item].Value));
            Spec.Ensures(@this.Members() == Spec.Old(@this.Members()).Update(item, Ghost.Of(true)));
            Spec.Ensures(@this.Size() == Spec.Old(@this.Size()) + (Spec.Old(@this.Members()[item].Value) ? 0 : 1));
            throw null!;
        }

        public static bool Remove(HashSet<T> @this, T item)
        {
            Spec.Modifies(ObjSet.Of(@this));
            Spec.Ensures<bool>(r => r == Spec.Old(@this.Members()[item].Value));
            Spec.Ensures(@this.Members() == Spec.Old(@this.Members()).Update(item, Ghost.Of(false)));
            Spec.Ensures(@this.Size() == Spec.Old(@this.Size()) - (Spec.Old(@this.Members()[item].Value) ? 1 : 0));
            throw null!;
        }

        public static void Clear(HashSet<T> @this)
        {
            Spec.Modifies(ObjSet.Of(@this));
            Spec.Ensures(@this.Size() == 0 && @this.Members() == Map.Const<T, bool>(false));
            throw null!;
        }
    }

    [ContractsFor(typeof(Stack<>))]
    public static class StackContracts<T>
    {
        public static Stack<T> @new()
        {
            Spec.Ensures<Stack<T>>(r => r.Size() == 0);
            throw null!;
        }

        [Pure]
        public static int get_Count(Stack<T> @this)
        {
            Spec.Ensures<int>(r => r == @this.Size());
            throw null!;
        }

        public static void Push(Stack<T> @this, T item)
        {
            Spec.Modifies(ObjSet.Of(@this));
            Spec.Ensures(@this.Size() == Spec.Old(@this.Size()) + 1);
            Spec.Ensures(@this.Items() == Spec.Old(@this.Items()).Update(Spec.Old(@this.Size()), Ghost.Of(item)));
            throw null!;
        }

        public static T Pop(Stack<T> @this)
        {
            Spec.Requires(@this.Size() > 0);
            Spec.Modifies(ObjSet.Of(@this));
            Spec.Ensures(@this.Size() == Spec.Old(@this.Size()) - 1);
            Spec.Ensures<T>(r => Ghost.Of(r) == Spec.Old(@this.Items())[Spec.Old(@this.Size()) - 1]);
            Spec.Ensures(Spec.Forall(0, @this.Size(), i => @this.Items()[i] == Spec.Old(@this.Items())[i]));
            throw null!;
        }

        [Pure]
        public static T Peek(Stack<T> @this)
        {
            Spec.Requires(@this.Size() > 0);
            Spec.Ensures<T>(r => Ghost.Of(r) == @this.Items()[@this.Size() - 1]);
            throw null!;
        }

        public static void Clear(Stack<T> @this)
        {
            Spec.Modifies(ObjSet.Of(@this));
            Spec.Ensures(@this.Size() == 0);
            throw null!;
        }
    }

    [ContractsFor(typeof(Queue<>))]
    public static class QueueContracts<T>
    {
        public static Queue<T> @new()
        {
            Spec.Ensures<Queue<T>>(r => r.Size() == 0);
            throw null!;
        }

        [Pure]
        public static int get_Count(Queue<T> @this)
        {
            Spec.Ensures<int>(r => r == @this.Size());
            throw null!;
        }

        public static void Enqueue(Queue<T> @this, T item)
        {
            Spec.Modifies(ObjSet.Of(@this));
            Spec.Ensures(@this.Size() == Spec.Old(@this.Size()) + 1);
            Spec.Ensures(@this.Items() == Spec.Old(@this.Items()).Update(Spec.Old(@this.Size()), Ghost.Of(item)));
            throw null!;
        }

        public static T Dequeue(Queue<T> @this)
        {
            Spec.Requires(@this.Size() > 0);
            Spec.Modifies(ObjSet.Of(@this));
            Spec.Ensures(@this.Size() == Spec.Old(@this.Size()) - 1);
            Spec.Ensures<T>(r => Ghost.Of(r) == Spec.Old(@this.Items())[0]);
            Spec.Ensures(@this.Items() == Spec.Old(@this.Items()).Drop(1));
            throw null!;
        }

        [Pure]
        public static T Peek(Queue<T> @this)
        {
            Spec.Requires(@this.Size() > 0);
            Spec.Ensures<T>(r => Ghost.Of(r) == @this.Items()[0]);
            throw null!;
        }

        public static void Clear(Queue<T> @this)
        {
            Spec.Modifies(ObjSet.Of(@this));
            Spec.Ensures(@this.Size() == 0);
            throw null!;
        }
    }
}
