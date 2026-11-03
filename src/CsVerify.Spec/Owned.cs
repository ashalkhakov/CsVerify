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

    /// <summary>
    /// A read share of an owned object's view (counting permissions, a form of fractional permission): a linear
    /// token split off a view by <see cref="Own.Share{T}"/> and joined back by <see cref="Own.Unshare{T}"/>. Any
    /// number may be out at once, and two may share one object. A share lets its holder rely on the object's
    /// [Invariant] and on nobody writing the object while it holds the share; the view it came from cannot write
    /// the object (or be lent to code that does) until every share is back.
    /// </summary>
    [Linear]
    public readonly struct Shared<T> where T : class
    {
        /// <summary>The object this share reads.</summary>
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

        /// <summary>
        /// Splits a read share off a view (ATS: a fraction of the view). The view keeps the rest; it may write the
        /// object again once every share split off it is back.
        /// </summary>
        [Trusted]
        public static void Share<T>(ref Own<T> view, out Shared<T> share) where T : class
        {
            share = default;
        }

        /// <summary>Joins a share back into the view of the same object.</summary>
        [Trusted]
        public static void Unshare<T>(ref Own<T> view, Shared<T> share) where T : class { }

        /// <summary>Gives a share up for good: its view can no longer get the object back whole.</summary>
        [Trusted]
        public static void Drop<T>(Shared<T> share) where T : class { }

        /// <summary>Gives the view up for good: nobody can write the object any more.</summary>
        [Trusted]
        public static void Drop<T>(Own<T> view) where T : class { }
    }
}
