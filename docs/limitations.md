# Limitations

**What "verified" does not cover** (deliberate choices, documented rather than hidden)
- **Integers** are bounded by default (see [Bounded integers](semantics.md#bounded-integers)). `--no-overflow` makes them mathematical, as ATS's constraint solver does, which is unsound where code can overflow.
- **Threads.** A method is proved correct for runs where no other thread writes the state it uses while it runs (see [Async and concurrency](semantics.md#async-and-concurrency)). Races, deadlocks and lock-free code are not covered, and an async method of the program must be awaited where it is called.
- **Exceptions and `null`.** Ordinary methods are verified for partial correctness with respect to exceptions: a path that throws need not meet the postcondition, only `Spec.EnsuresOnThrow` clauses. Handlers are verified (see Exceptions). Proofs may not throw (CSV1011). Null dereferences are not exceptions in this sense: they are proved absent (CSV1013/CSV1014), and so never reach a handler.
- **Mutable objects.**
  - **Dynamic frames.**
    - Virtual and interface calls, and library calls that can run user code, can't be checked against `Spec.Modifies`.
    - The frame rule for `[Pure]` functions follows at most 16 changes back.
    - Loops forget the fields they write for every object; restate what is kept in the invariant.
  - **`[Invariant]` on an ordinary mutable class** (neither a data record, immutable nor `[Owned]`) is not used, with a warning.
  - **Loops** that write owned fields, or move views, forget those fields and the tree roots for every object.
  - **`Own.Take` splits a tree imprecisely.** The container's other children stay with it, but which of their descendants went with the taken object is not tracked, so a call that touches either part may forget those.
  - **Proofs about trees can need a hint,** much like an ATS `prval` step: the unfolded fact stated where a child is taken out (`Spec.Assert(Size.Value == 1 + l.Size.Value + ...)`).
  - **`[Pure]` functions get no view.** They can't assume an owned object's invariant, so recursion over an ownership tree (a measure from the invariant) is done in ordinary methods that take and give.
  - **Library code** is trusted not to write source objects' fields except by running user code it is handed, so reflection is not covered. A call is judged by what it is handed: an object whose class overrides nothing and implements no interface gives it no code to run. A library method without a stub that is handed an object with `[Model]` functions (or an `object`, interface or type parameter that may be one) may change any model state, and can't be checked against `Spec.Modifies`.
- **Null and object state.** Fields and auto-properties of nullable type are maybe-null; array elements are maybe-null whatever their type. Library nullability annotations are trusted, not checked.
- **Changing a collection while it is enumerated** is reported for `List`, `Dictionary` (and its `Keys` and `Values`), `HashSet`, `Stack` and `Queue`. It is not reported for enumeration through an interface (`IEnumerable<T>`), or for LINQ. A change that .NET does not count (`AddRange` of nothing) is still taken to be one.
- **List interfaces** (`IReadOnlyList<T>` and the others): library collections other than `List` and arrays are trusted to be consistent (`Contains` as the indexer reads, enumeration as indexing, a `Dispose` of their enumerator that does nothing). A `foreach` whose loop changes state goes through the enumerator, with unknown elements. A class of the program implementing one of the interfaces makes every read through them unknown, and every `foreach` over them go through the enumerator. `IEnumerable<T>` alone has no model.
- **Objects a framework builds** (`[JsonRequired]` members) are trusted to have those members set: code that builds one itself and leaves one out is not checked.
- **Disposables** are checked on normal paths only: an exception may leak one (as it may a linear value), unless a `using` or `finally` disposes it. Ownership is by variable: a disposable kept in a collection, or captured by a lambda, needs `Spec.HandOver`. `[TakesOwnership]` and `Spec.HandOver` are trusted.
- **State across `await`** is still forgotten at each `await`, even for objects the method made itself and never let escape.
- **Check profiles** (`--checks`) assume the obligations of the kinds they leave out, and treat constructs the verifier does not model as unknown values. A method verified under a profile is correct only where those hold (see [Check profiles](running.md#check-profiles)).
- **Patterns.** Positional patterns work on tuples and data records, list patterns on one-dimensional arrays (a slice with a pattern of its own, `[1, .. var rest]`, is not supported), and property patterns on any member. A type with a `Deconstruct` method of its own is not matched positionally.
- **Struct members by reference** (`out a[i].X`, `ref s.X`) are written back after the call. A callee that may touch array contents itself can't be handed an array cell's member this way (CSV1901), since the cell and the parameter would disagree.
- **Data types.** Closedness is checked within the compilation. A hierarchy whose root has only private constructors is closed, except that the record's synthesized protected copy constructor could in principle be derived through from another assembly. Data values have no identity, so code that relies on reference identity of records is not verified for it.
- **Unfolding depth.** `Length(Cons(1, Nil))` needs `Length(Nil)` stated too, because a `[Pure]` definition unfolds one level per use. Concrete values are not evaluated to the end.
- **Termination of ordinary methods** is only checked where `Spec.Decreases` is given (a warning otherwise).
- **Virtual dispatch** is modular: a call uses the declared member's contract, and overrides are checked against it.
  - **Generic types:** their dynamic types are not modelled.
  - **Non-sealed overrides:** a `[Pure]` override's body defines the query only if the override is final.
  - **Lemmas and ghost functions** cannot be virtual (CSV0013).
- **`[Trusted]` and `Spec.Assume`** are axioms by definition.
- **Library contracts** (`[ContractsFor]` stubs, CsVerify's and yours) are trusted: their postconditions, the frames they declare, and the facts their `[Model]` functions state are assumed, not checked against the library. The summary line counts the ones a run used, and `-v` lists them. In particular (see [Contracts for code without sources](library-contracts.md)):
  - a stub without `Spec.Modifies` is taken to change no model state, and a `[Pure]` one to have no effects at all;
  - `Dictionary` and `HashSet` keys compare as `EqualityComparer<T>.Default` does (see [Equality](library-contracts.md)): exactly for numbers, enums, strings and classes without their own `Equals`, through an unknown key function otherwise. A custom comparer (`new Dictionary<string, int>(StringComparer.OrdinalIgnoreCase)`) is not taken into account: its contracts still compare by the default;
  - running out of memory is not modelled: a list can grow without bound (its `Size()` is a mathematical integer), as in Dafny;
  - model state over strings never changes (they are immutable);
  - a library class's overrides of a stubbed member (`StreamWriter.Write`) keep its contract, and a `TextWriter`'s writes change nothing the verifier models;
  - `List<T>.Enumerator.Dispose` is taken to do nothing, and a `foreach` over a list to see the list as it was when the loop began.

**Unsupported constructs**
- Rejected as CSV1901 (the method is not verified): see [What it cannot model, it rejects](how-it-works.md) in How it works.
- Unknown values, which are sound (CSV1900 warning): shifts and bitwise operators on integers, floating-point `%` and transcendental functions, string characters, library properties without a `[Pure]` stub, non-pure calls in specifications, the elements of a `foreach` over a library collection (a `List<T>` whose loop may change a list included), a string or a span.
- `Spec.Acc` permissions cover one-dimensional arrays only: a method whose contract gives array permissions cannot write a rectangular array's cells (CSV1016).
- Library members without a stub have no contract beyond their nullability annotations (see [Contracts for code without sources](library-contracts.md)). Arrays, strings' `Length` and indexer, spans (their indexer, `Slice`, `CopyTo`, `TryCopyTo`, `Fill`, `Clear`, `ToArray`, `AsSpan`) and `Math.Min`/`Max`/`Abs` are built in, and a stub for them is not used.
- **Spans** of a string have the string as their base, but its characters are unknown values. A method with array permissions (`Spec.Acc`) can't write through a span, and reads through one are unknown. `ReadOnlySequence<byte>` and System.IO.Pipelines are not modeled.
- Not verified as separate units: local functions and lambdas. The method's locals they write are forgotten after every call and at every `await`.

**Completeness limits** (true things that may not be proved)
- A new array is known to differ from the arrays in local variables and fields where it is created, not from arrays held elsewhere (inside other arrays).
- Side facts under a quantifier (non-negative lengths, `[Pure]` unfolding) are a separate quantified axiom, instantiated by e-matching only. A fact needed at a term that never appears may be missing.

**Precision limits**
- `[Pure]` definitions are unfolded one level per use. Deeper facts need a lemma, as in ATS.
- Verification explores paths depth-first (`MaxPaths` = 5000 per method), so many sequential branches can be slow.
- Every method is verified separately against its callees' contracts.

**Views versus ATS/SV** (Zhu & Xi, *Safe Programming with Pointers through Stateful Views*)
- `PointsTo<T>` tracks address and value, so `T @ l` plus more.
- Array views (`array_v`), split/join, take-out, pointer arithmetic and `mfree_gc_v` are provided as library axioms. There is still no way to declare your own `dataview` with checked proof constructors: a `[Linear]` struct plus `[Trusted]` functions is how you would add one, and those functions are trusted, not checked.
- There is no general `⊗`/`−◦` view algebra, no type-changing `setVar`, and no uninitialized `top @ l`.
- Take-out's linear function `a @ (l+i) -<lin> array_v(a, n, l)` is a linear token (`ArrayHole<T>`) that only `Mem.PutBack` consumes; there are no linear proof functions in general.
- View-changing proof functions (`Split`, `Join`, `TakeOut`, `PutBack`) cannot be `[Conditional]`, because C# forbids `out` parameters on conditional methods. In a normal build they are empty, inlined methods on data-less structs, erased by the JIT. The erasure pass removes them, and the views, outright.
- Contents of a view are compared as whole sequences (`Elems == ...`), because C# lambdas cannot capture `ref`/`in` parameters. Element-wise properties go through a `[GhostFunction]` that takes the `Seq<T>` by value (see `ArrayViews.AllEqual`).
- With e-matching only, a property that needs a cleverer quantifier instantiation may come back "not proved" even though it is true. Add an intermediate `Spec.Assert` or a lemma.
- The analyzer does not track linear fields inside a linear struct separately: the struct is one resource.

**Packaging**
- Views and ghosts cost nothing in an erased build (`-p:CsVerifyErase=true`): the erasure pass deletes the types, parameters and calls, so nothing of them reaches the IL. In a normal build they are still empty structs (one byte each to the CLR, no data) passed to empty, inlined methods.
- The packages (`CsVerify` and the `dotnet-csverify` tool) are released by the release workflow, on GitHub and, once trusted publishing is set up, on nuget.org (see [CI](ci.md#building-and-releasing-csverify)).
