namespace CsVerify
{
    using System;
    using System.Diagnostics;

    /// <summary>
    /// Specification statements. Every method is <c>[Conditional("CSVERIFY_SPEC")]</c>: in a normal build the
    /// compiler removes the call <em>and the evaluation of its arguments</em>, so specifications cost nothing at
    /// run time. The CsVerify verifier compiles with <c>CSVERIFY_SPEC</c> defined and reads them as proof obligations.
    /// </summary>
    public static class Spec
    {
        public const string Symbol = "CSVERIFY_SPEC";

        /// <summary>Precondition. A top-level statement of a method body (contracts are read from there).</summary>
        [Conditional(Symbol)] public static void Requires(bool condition) { }

        /// <summary>Postcondition over the return value, bound to the lambda's parameter.</summary>
        [Conditional(Symbol)] public static void Ensures<R>(Func<R, bool> condition) { }

        /// <summary>
        /// Postcondition evaluated in the final state. Use <see cref="Result{T}"/> for the return value and
        /// <see cref="Old{T}"/> for entry values (needed for <c>ref</c> parameters, which lambdas cannot capture).
        /// </summary>
        [Conditional(Symbol)] public static void Ensures(bool condition) { }

        /// <summary>
        /// Exceptional postcondition (Code Contracts' <c>Contract.EnsuresOnThrow</c>): if the method exits by throwing
        /// a <typeparamref name="TException"/>, the condition holds then (<see cref="Old{T}"/> for entry values). A
        /// method may throw any exception (it is verified for partial correctness): this says what holds if it does.
        /// </summary>
        [Conditional(Symbol)] public static void EnsuresOnThrow<TException>(bool condition) where TException : System.Exception { }

        /// <summary>Loop invariant: the leading statements of a loop body; holds every time the loop condition is tested.</summary>
        [Conditional(Symbol)] public static void Invariant(bool condition) { }

        /// <summary>Termination measure: leading statement of a loop body or of a recursive method's body.</summary>
        [Conditional(Symbol)] public static void Decreases(int measure) { }

        /// <summary>Lexicographic termination measure (ATS's <c>.&lt;m, n&gt;.</c>): the first component that changes must go down.</summary>
        [Conditional(Symbol)] public static void Decreases(int measure1, int measure2) { }

        /// <summary>Lexicographic termination measure with three components.</summary>
        [Conditional(Symbol)] public static void Decreases(int measure1, int measure2, int measure3) { }

        /// <summary>
        /// Structural termination measure: <paramref name="structure"/>, a value of a data type (a closed positional
        /// record hierarchy), is smaller at every recursive call, as when recursing on a sub-term (ATS's datatype metrics).
        /// </summary>
        [Conditional(Symbol)] public static void Decreases<T>(T structure) where T : class { }

        /// <summary>
        /// Dynamic frame (Dafny's <c>modifies</c>): a top-level statement of a method body. The method may write fields
        /// only of objects in <paramref name="frame"/> (as it is on entry) and of objects it allocates. Its callers then
        /// know every other object is unchanged.
        /// </summary>
        [Conditional(Symbol)] public static void Modifies(ObjSet frame) { }

        /// <summary>
        /// Dynamic frame of a [Pure] function (Dafny's <c>reads</c>): its body reads fields only of objects in
        /// <paramref name="frame"/>, so its value survives any change outside the frame.
        /// </summary>
        [Conditional(Symbol)] public static void Reads(ObjSet frame) { }

        /// <summary>Proof obligation at this point.</summary>
        [Conditional(Symbol)] public static void Assert(bool condition) { }

        /// <summary>Unchecked assumption at this point (the specification analogue of <c>$UNSAFE</c>).</summary>
        [Conditional(Symbol)] public static void Assume(bool condition) { }

        /// <summary>
        /// What <c>EqualityComparer&lt;T&gt;.Default.Equals(a, b)</c> gives: equal values for numbers, enums, strings
        /// and classes that do not override Equals; whatever T's Equals says otherwise (which the verifier does not know).
        /// For library contracts over any T (List&lt;T&gt;.IndexOf). Ghost.
        /// </summary>
        public static bool Equal<T>(Ghost<T> a, Ghost<T> b) => throw GhostException.Instance;

        /// <summary>
        /// Hands a disposable over to whoever will dispose it (a container, a dependency-injection scope, a framework):
        /// the disposal check counts it as handed over here. Trusted, like Assume.
        /// </summary>
        [Conditional(Symbol)] public static void HandOver(object resource) { }

        /// <summary>The method's return value; only meaningful inside <see cref="Ensures(bool)"/>.</summary>
        public static T Result<T>() => throw GhostException.Instance;

        /// <summary>Bounded universal quantifier: <paramref name="body"/> holds for every i with from &lt;= i &lt; to.</summary>
        public static bool Forall(int from, int to, Func<int, bool> body) => throw GhostException.Instance;

        // ---- what a delegate accepts and gives (Dafny's f.requires and f.ensures)
        //
        // Every call of a delegate proves Spec.Pre and gives a result for which Spec.Post holds. No delegate is taken
        // to accept anything: what a parameter or field accepts is what a specification says (Spec.Pre, Spec.Total).
        // A lambda's Spec.Pre is its own Spec.Requires (none: total), and its Spec.Post what it ensures and, for an
        // expression, its value; both only as far as they depend on its parameters and on captured variables that
        // never change.
        /// <summary>A call <c>f()</c> is allowed: its precondition holds.</summary>
        public static bool Pre<R>(Func<R> f) => throw GhostException.Instance;
        /// <summary><paramref name="r"/> is a result <c>f()</c> may give.</summary>
        public static bool Post<R>(Func<R> f, R r) => throw GhostException.Instance;
        public static bool Pre(Action f) => throw GhostException.Instance;
        /// <summary>A call <c>f(...)</c> may return normally.</summary>
        public static bool Post(Action f) => throw GhostException.Instance;
        /// <summary>A call <c>f(a1)</c> is allowed: its precondition holds.</summary>
        public static bool Pre<A1, R>(Func<A1, R> f, A1 a1) => throw GhostException.Instance;
        /// <summary><paramref name="r"/> is a result <c>f(a1)</c> may give.</summary>
        public static bool Post<A1, R>(Func<A1, R> f, A1 a1, R r) => throw GhostException.Instance;
        public static bool Pre<A1>(Action<A1> f, A1 a1) => throw GhostException.Instance;
        /// <summary>A call <c>f(...)</c> may return normally.</summary>
        public static bool Post<A1>(Action<A1> f, A1 a1) => throw GhostException.Instance;
        /// <summary>A call <c>f(a1, a2)</c> is allowed: its precondition holds.</summary>
        public static bool Pre<A1, A2, R>(Func<A1, A2, R> f, A1 a1, A2 a2) => throw GhostException.Instance;
        /// <summary><paramref name="r"/> is a result <c>f(a1, a2)</c> may give.</summary>
        public static bool Post<A1, A2, R>(Func<A1, A2, R> f, A1 a1, A2 a2, R r) => throw GhostException.Instance;
        public static bool Pre<A1, A2>(Action<A1, A2> f, A1 a1, A2 a2) => throw GhostException.Instance;
        /// <summary>A call <c>f(...)</c> may return normally.</summary>
        public static bool Post<A1, A2>(Action<A1, A2> f, A1 a1, A2 a2) => throw GhostException.Instance;
        /// <summary>A call <c>f(a1, a2, a3)</c> is allowed: its precondition holds.</summary>
        public static bool Pre<A1, A2, A3, R>(Func<A1, A2, A3, R> f, A1 a1, A2 a2, A3 a3) => throw GhostException.Instance;
        /// <summary><paramref name="r"/> is a result <c>f(a1, a2, a3)</c> may give.</summary>
        public static bool Post<A1, A2, A3, R>(Func<A1, A2, A3, R> f, A1 a1, A2 a2, A3 a3, R r) => throw GhostException.Instance;
        public static bool Pre<A1, A2, A3>(Action<A1, A2, A3> f, A1 a1, A2 a2, A3 a3) => throw GhostException.Instance;
        /// <summary>A call <c>f(...)</c> may return normally.</summary>
        public static bool Post<A1, A2, A3>(Action<A1, A2, A3> f, A1 a1, A2 a2, A3 a3) => throw GhostException.Instance;
        /// <summary>A call <c>f(a1, a2, a3, a4)</c> is allowed: its precondition holds.</summary>
        public static bool Pre<A1, A2, A3, A4, R>(Func<A1, A2, A3, A4, R> f, A1 a1, A2 a2, A3 a3, A4 a4) => throw GhostException.Instance;
        /// <summary><paramref name="r"/> is a result <c>f(a1, a2, a3, a4)</c> may give.</summary>
        public static bool Post<A1, A2, A3, A4, R>(Func<A1, A2, A3, A4, R> f, A1 a1, A2 a2, A3 a3, A4 a4, R r) => throw GhostException.Instance;
        public static bool Pre<A1, A2, A3, A4>(Action<A1, A2, A3, A4> f, A1 a1, A2 a2, A3 a3, A4 a4) => throw GhostException.Instance;
        /// <summary>A call <c>f(...)</c> may return normally.</summary>
        public static bool Post<A1, A2, A3, A4>(Action<A1, A2, A3, A4> f, A1 a1, A2 a2, A3 a3, A4 a4) => throw GhostException.Instance;

        /// <summary>f accepts every argument: Spec.Pre holds for all of them.</summary>
        public static bool Total<R>(Func<R> f) => throw GhostException.Instance;
        public static bool Total(Action f) => throw GhostException.Instance;
        /// <summary>f accepts every argument: Spec.Pre holds for all of them.</summary>
        public static bool Total<A1, R>(Func<A1, R> f) => throw GhostException.Instance;
        public static bool Total<A1>(Action<A1> f) => throw GhostException.Instance;
        /// <summary>f accepts every argument: Spec.Pre holds for all of them.</summary>
        public static bool Total<A1, A2, R>(Func<A1, A2, R> f) => throw GhostException.Instance;
        public static bool Total<A1, A2>(Action<A1, A2> f) => throw GhostException.Instance;
        /// <summary>f accepts every argument: Spec.Pre holds for all of them.</summary>
        public static bool Total<A1, A2, A3, R>(Func<A1, A2, A3, R> f) => throw GhostException.Instance;
        public static bool Total<A1, A2, A3>(Action<A1, A2, A3> f) => throw GhostException.Instance;
        /// <summary>f accepts every argument: Spec.Pre holds for all of them.</summary>
        public static bool Total<A1, A2, A3, A4, R>(Func<A1, A2, A3, A4, R> f) => throw GhostException.Instance;
        public static bool Total<A1, A2, A3, A4>(Action<A1, A2, A3, A4> f) => throw GhostException.Instance;

        // ---- what a delegate may change (a modifies frame, as a function of its arguments)

        /// <summary>A call of f changes no array, field or model state that exists before it (it may make new objects).</summary>
        public static bool ChangesNothing(Delegate f) => throw GhostException.Instance;
        /// <summary>A call <c>f(...)</c> changes only the objects and arrays in <paramref name="frame"/> of its arguments (and new ones).</summary>
        public static bool Changes<R>(Func<R> f, ObjSet frame) => throw GhostException.Instance;
        public static bool Changes(Action f, ObjSet frame) => throw GhostException.Instance;
        /// <summary>A call <c>f(...)</c> changes only the objects and arrays in <paramref name="frame"/> of its arguments (and new ones).</summary>
        public static bool Changes<A1, R>(Func<A1, R> f, Func<A1, ObjSet> frame) => throw GhostException.Instance;
        public static bool Changes<A1>(Action<A1> f, Func<A1, ObjSet> frame) => throw GhostException.Instance;
        /// <summary>A call <c>f(...)</c> changes only the objects and arrays in <paramref name="frame"/> of its arguments (and new ones).</summary>
        public static bool Changes<A1, A2, R>(Func<A1, A2, R> f, Func<A1, A2, ObjSet> frame) => throw GhostException.Instance;
        public static bool Changes<A1, A2>(Action<A1, A2> f, Func<A1, A2, ObjSet> frame) => throw GhostException.Instance;
        /// <summary>A call <c>f(...)</c> changes only the objects and arrays in <paramref name="frame"/> of its arguments (and new ones).</summary>
        public static bool Changes<A1, A2, A3, R>(Func<A1, A2, A3, R> f, Func<A1, A2, A3, ObjSet> frame) => throw GhostException.Instance;
        public static bool Changes<A1, A2, A3>(Action<A1, A2, A3> f, Func<A1, A2, A3, ObjSet> frame) => throw GhostException.Instance;
        public static bool Changes<T>(Predicate<T> f, Func<T, ObjSet> frame) => throw GhostException.Instance;

        // ---- what a delegate's Spec.Pre and Spec.Post read (a reads frame, as a function of its arguments)
        //
        // Without one, a delegate's Spec.Pre and Spec.Post are the same in every state (steady), and a method whose
        // specifications speak of them takes that for granted of its parameters (its callers prove it). With one, they
        // are of the state they are taken in, and stay as they are while the fields and cells of the objects in the
        // frame do.

        /// <summary>What <c>Spec.Pre(f, ...)</c> and <c>Spec.Post(f, ...)</c> depend on: the fields and cells of the objects in <paramref name="frame"/> of the arguments.</summary>
        public static bool Reads<A1, R>(Func<A1, R> f, Func<A1, ObjSet> frame) => throw GhostException.Instance;
        public static bool Reads<A1>(Action<A1> f, Func<A1, ObjSet> frame) => throw GhostException.Instance;
        /// <summary>What <c>Spec.Pre(f, ...)</c> and <c>Spec.Post(f, ...)</c> depend on: the fields and cells of the objects in <paramref name="frame"/> of the arguments.</summary>
        public static bool Reads<A1, A2, R>(Func<A1, A2, R> f, Func<A1, A2, ObjSet> frame) => throw GhostException.Instance;
        public static bool Reads<A1, A2>(Action<A1, A2> f, Func<A1, A2, ObjSet> frame) => throw GhostException.Instance;
        /// <summary>What <c>Spec.Pre(f, ...)</c> and <c>Spec.Post(f, ...)</c> depend on: the fields and cells of the objects in <paramref name="frame"/> of the arguments.</summary>
        public static bool Reads<A1, A2, A3, R>(Func<A1, A2, A3, R> f, Func<A1, A2, A3, ObjSet> frame) => throw GhostException.Instance;
        public static bool Reads<A1, A2, A3>(Action<A1, A2, A3> f, Func<A1, A2, A3, ObjSet> frame) => throw GhostException.Instance;
        public static bool Reads<R>(Func<R> f, ObjSet frame) => throw GhostException.Instance;
        public static bool Reads(Action f, ObjSet frame) => throw GhostException.Instance;
        public static bool Reads<T>(Predicate<T> f, Func<T, ObjSet> frame) => throw GhostException.Instance;

        // (the BCL's other delegates that collections take)
        public static bool Pre<T>(Predicate<T> f, T a) => throw GhostException.Instance;
        public static bool Post<T>(Predicate<T> f, T a, bool r) => throw GhostException.Instance;
        public static bool Total<T>(Predicate<T> f) => throw GhostException.Instance;
        public static bool Pre<T>(Comparison<T> f, T a, T b) => throw GhostException.Instance;
        public static bool Post<T>(Comparison<T> f, T a, T b, int r) => throw GhostException.Instance;
        public static bool Total<T>(Comparison<T> f) => throw GhostException.Instance;
        public static bool Pre<TIn, TOut>(Converter<TIn, TOut> f, TIn a) => throw GhostException.Instance;
        public static bool Post<TIn, TOut>(Converter<TIn, TOut> f, TIn a, TOut r) => throw GhostException.Instance;
        public static bool Total<TIn, TOut>(Converter<TIn, TOut> f) => throw GhostException.Instance;

        /// <summary>Bounded existential quantifier: <paramref name="body"/> holds for some i with from &lt;= i &lt; to.</summary>
        public static bool Exists(int from, int to, Func<int, bool> body) => throw GhostException.Instance;

        /// <summary>The multiset of <c>items[0..count)</c> (Dafny's <c>multiset(a[..n])</c>).</summary>
        public static Bag Multiset(int[] items, int count) => throw GhostException.Instance;

        /// <summary>In a postcondition: the object was allocated by the method (Dafny's <c>fresh</c>).</summary>
        public static bool Fresh(object item) => throw GhostException.Instance;

        /// <summary>In a postcondition: every object in the set was allocated by the method.</summary>
        public static bool Fresh(ObjSet items) => throw GhostException.Instance;

        /// <summary>
        /// Permission to write an [Owned] object (Viper's <c>acc</c>): in contracts, loop invariants and predicate
        /// bodies, as a conjunct. As a condition elsewhere, "the permission is in hand".
        /// </summary>
        public static bool Acc(object obj) => throw GhostException.Instance;

        /// <summary>
        /// Permission to write one field of an [Owned] object (Viper's <c>acc(o.f)</c>): <c>Spec.Acc(node, nameof(Node.Val))</c>.
        /// Two pieces of code may hold different fields of one object. For sealed classes without an [Invariant].
        /// </summary>
        public static bool Acc(object obj, string field) => throw GhostException.Instance;

        /// <summary>
        /// Permission to write the cells <paramref name="from"/> (inclusive) to <paramref name="to"/> (exclusive) of
        /// an array, in a method's contract and loop invariants (<c>Spec.Acc(array)</c> is the whole array). A method
        /// whose contract gives it array permissions writes only cells it has permission to, and calls to it change
        /// only those cells (and arrays it allocates).
        /// </summary>
        public static bool Acc<T>(T[] array, int from, int to) => throw GhostException.Instance;

        /// <summary>
        /// A share of permission to read an array's cells: in a contract, the method only reads them (it cannot write them,
        /// and a call to it changes none of them), and any number of tasks may hold a share at once, while nobody can write
        /// them. Reading in code that runs alongside other code needs one, or Spec.Acc.
        /// </summary>
        public static bool AccRead<T>(T[] array) => throw GhostException.Instance;

        /// <summary>A share of permission to read the cells <paramref name="from"/> (inclusive) to <paramref name="to"/> (exclusive).</summary>
        public static bool AccRead<T>(T[] array, int from, int to) => throw GhostException.Instance;

        /// <summary>Folds a predicate instance: its body's permissions go into it, and its facts must hold.</summary>
        [Conditional(Symbol)] public static void Fold(bool predicate) { }

        /// <summary>Unfolds a held predicate instance: its body's permissions come out, and its facts hold.</summary>
        [Conditional(Symbol)] public static void Unfold(bool predicate) { }

        /// <summary>
        /// The index of <paramref name="element"/>, the iteration variable of a <c>foreach</c> over an array: in the
        /// loop's invariants, the number of elements already gone through; in its body, the index of the element.
        /// </summary>
        public static int Index<T>(T element) => throw GhostException.Instance;

        /// <summary>The value an expression had on method entry; only meaningful inside <see cref="Ensures(bool)"/>.</summary>
        public static T Old<T>(T value) => throw GhostException.Instance;
    }

    /// <summary>Thrown when ghost-only code is reached at run time; the analyzers make this unreachable.</summary>
    public sealed class GhostException : InvalidOperationException
    {
        internal static readonly GhostException Instance = new GhostException();
        private GhostException() : base("Ghost code is only meaningful inside CsVerify specifications.") { }
    }
}
