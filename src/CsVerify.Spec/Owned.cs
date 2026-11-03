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

        /// <summary>Gives the view up for good: nobody can write the object any more.</summary>
        [Trusted]
        public static void Drop<T>(Own<T> view) where T : class { }
    }
}
