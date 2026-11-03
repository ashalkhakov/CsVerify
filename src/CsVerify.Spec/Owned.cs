namespace CsVerify
{
    /// <summary>
    /// The view of an object of an <see cref="OwnedAttribute"/> class (ATS-style ownership): a zero-size linear
    /// token. Writing the object's fields needs it in hand (as a local, a <c>ref</c> parameter, or the receiver of
    /// the object's own methods); the object's [Invariant] holds whenever it is handed over. A call can change the
    /// object only if the view goes in by <c>ref</c> or by value, or comes out.
    /// </summary>
    [Linear]
    public readonly struct Own<T> where T : class
    {
        /// <summary>The object this view owns.</summary>
        public Ghost<T> Obj => default;
    }

    public static class Own
    {
        /// <summary>Takes ownership of a new object: <c>var c = Own.New(new Counter(), out var view);</c> (only of a <c>new</c>).</summary>
        [Trusted]
        public static T New<T>(T obj, out Own<T> view) where T : class
        {
            view = default;
            return obj;
        }

        /// <summary>
        /// Unfolds one level of an ownership tree: takes the object an <see cref="OwnsAttribute"/> field owns out of
        /// it, with its view (ATS: getting the view of a node out of its parent's). The field becomes null. Needs the
        /// container's view; the field must not be null.
        /// </summary>
        [Trusted]
        public static T Take<T>(ref T? slot, out Own<T> view) where T : class
        {
            var obj = slot!;
            slot = null;
            view = default;
            return obj;
        }

        /// <summary>
        /// Folds back: gives an object and its view to an empty <see cref="OwnsAttribute"/> field, which then owns it
        /// (its invariant is proved, as at any hand-over). The object may not be the container or own it.
        /// </summary>
        [Trusted]
        public static void Give<T>(ref T? slot, T obj, Own<T> view) where T : class
        {
            slot = obj;
        }

        /// <summary>
        /// The footprint of an ownership tree, as a ghost set of objects (for Dafny-style frames): every object in the
        /// tree <paramref name="obj"/> belongs to, its root and everything the root owns, transitively.
        /// </summary>
        [GhostFunction]
        public static ObjSet Tree(object obj) => throw GhostException.Instance;

        /// <summary>Gives the view up for good: nobody can write the object any more.</summary>
        [Trusted]
        public static void Drop<T>(Own<T> view) where T : class { }
    }
}
