# CsVerify

An applied type system for C#, written entirely in C#.

CsVerify brings the ideas of ATS (Hongwei Xi's *Applied Type System*) to C#. In the imperative style of Xanadu, ATS's C-like sibling, it gives you:

- static indices,
- dependent refinements,
- loop invariants,
- termination metrics,
- proof functions,
- linear *views* of memory.

It adds **no syntax**. There is no preprocessor, desugaring step or compiler fork. Every file you write is ordinary C#: it compiles with the normal compiler and gets full IDE support. The extensions are:

- a small specification library (`CsVerify.Spec`). Its statements are erased from normal builds.
- Roslyn analyzers that check linearity and ghost hygiene as you type.
- a verifier that turns specifications into verification conditions and proves them with Z3.
- an optional proof-erasure pass (`csverify erase`, or `-p:CsVerifyErase=true`). It builds the program with every proof removed and checks that what is left compiles. This is not a language layer: the sources stay plain C#, and a normal build of them is the reference meaning, which erasure must and does preserve.

CsVerify is the proving counterpart of [Tarp](https://github.com/ashalkhakov/Tarp). Tarp measures, by running your tests, which conditions and decisions were exercised (MC/DC). CsVerify proves statically that index bounds, contracts, invariants and termination hold on *every* path. Both work on the same plain C# sources.

```csharp
public static int BinarySearch(int[] a, int key)
{
    Spec.Requires(Spec.Forall(0, a.Length, i => Spec.Forall(i, a.Length, j => a[i] <= a[j])));
    Spec.Ensures<int>(r => -1 <= r && r < a.Length);
    Spec.Ensures<int>(r => r < 0 || a[r] == key);
    Spec.Ensures<int>(r => r >= 0 || Spec.Forall(0, a.Length, i => a[i] != key));
    int lo = 0, hi = a.Length;
    while (lo < hi)
    {
        Spec.Invariant(0 <= lo && lo <= hi && hi <= a.Length);
        Spec.Invariant(Spec.Forall(0, lo, i => a[i] < key));
        Spec.Invariant(Spec.Forall(hi, a.Length, i => a[i] > key));
        Spec.Decreases(hi - lo);
        int mid = lo + (hi - lo) / 2;          // every a[...] below is proved in bounds
        if (a[mid] < key) lo = mid + 1;
        else if (a[mid] > key) hi = mid;
        else return mid;
    }
    return -1;
}
```

## The encoding: ATS concept → C# construct

ATS separates the **statics** (types and indices, reasoned about at compile time) from the **dynamics** (programs that run). Proofs and indices are erased before run time. CsVerify keeps the same split. Everything static is either a `[Conditional("CSVERIFY_SPEC")]` call, which the C# compiler deletes together with its arguments, or a type that carries no data.

| ATS / Xanadu | CsVerify (plain C#) |
|---|---|
| static index `{n:int}`, `{n:nat}` | `Ghost<int> n` parameter, read as `n.Value` inside specs; `Ghost.Of(e)` to pass one |
| singleton / indexed types `int(n)`, `array(T, n)` | a refinement on the value: `Spec.Requires(a.Length == n.Value)` |
| guard `P ⊃ T` | `Spec.Requires(P)` (top-level statement of the body) |
| assertion `∃r. P ∧ T` on the result | `Spec.Ensures<R>(r => P)`, or `Spec.Ensures(P)` with `Spec.Result<R>()` / `Spec.Old(x)` |
| constraint solving over static terms | the verifier sends the constraints to Z3 (linear and non-linear integer arithmetic, quantifiers) |
| Xanadu loop invariant at the loop head | `Spec.Invariant(P)` as the first statements of a `while`/`for`/`do` body |
| termination metric `.<n>.` | `Spec.Decreases(e)` on a recursive method or loop body |
| lexicographic metric `.<m, n>.` | `Spec.Decreases(m, n)` (up to three components) |
| `prfun` (proof function, total, erased) | `[Lemma, Conditional("CSVERIFY_SPEC")] void L(...)`: body is the proof, recursion is induction |
| `prval () = lemma(...)` | a plain call `L(x);` (erased; adds L's postconditions) |
| `datatype` (ATS), `datatype` (Dafny) | a closed positional record hierarchy, generic or not: `abstract record List<T> { private List() { } public sealed record Nil() : List<T>; public sealed record Cons(T Head, List<T> Tail) : List<T>; }` |
| `case`/`match` on constructors | `switch` and `is` patterns (`Cons c`, `Cons(var h, Nil)`, `{ Head: > 0 }`), exhaustiveness proved |
| metric on a datatype (structural recursion) | `Spec.Decreases(xs)`: the size of a data value |
| `dataprop` (proof as data: `FACT(n, r)`) | a closed record hierarchy whose cases are the proof rules (`record Ind(Fact Prev) : Fact(Prev.N + 1, ...)`), passed as `Ghost<Fact>` in run-time code; case analysis is `switch`, induction is recursion |
| an index's sort `{n:nat}` on a dataprop or datatype | an object invariant: `[Invariant, Pure] bool Natural() => N >= 0;` |
| static function in constraints | `[Pure]` method: an uninterpreted function whose `return` body is unfolded at each use |
| view `T @ l` | `[Linear] struct PointsTo<T>` with ghost `Addr` (the `l`) and `Value` |
| `ptr(l)` | `Ptr<T>` with ghost `Addr` |
| `getVar (pf: a@l \| p: ptr l)` | `Mem.Read(in view, p)`: `in` borrows the view (ATS `!pf`) |
| `setVar` | `Mem.Write(ref view, p, v)`: `ref` borrows the view and updates it |
| `allocVar` / `freeVar` | `Mem.Alloc(init, out view)` produces a view; `Mem.Free(view, p)` consumes it |
| array view `array_v(T, n, l)` | `[Linear] struct ArrayView<T>` with ghost `Addr`, `Length` and contents `Elems : Seq<T>` |
| `p->[i]`, `p->[i] := x` | `Mem.Get(in view, p, i)`, `Mem.Set(ref view, p, i, x)` (bounds are preconditions on the view) |
| `array_v_split` / `array_v_unsplit` (`praxi`) | `Mem.Split(whole, Ghost.Of(i), out left, out right)` / `Mem.Join(left, right, out whole)` |
| `array_v_takeout`: `a @ (l+i)` and a linear function `a @ (l+i) -<lin> array_v(a, n, l)` | `Mem.TakeOut(whole, Ghost.Of(i), out cell, out hole)` gives a `PointsTo<T>` and a `[Linear] ArrayHole<T>` token standing for the linear function; `Mem.PutBack(cell, hole, out whole)` applies it |
| pointer arithmetic `l + i` | `p.Offset(i)` (`Addr` of the result is `p.Addr + i`) |
| `mfree_gc_v(l)` | `[Linear] FreeGc<T>` from `Mem.AllocArray`; `Mem.FreeArray(gc, view, p)` needs it and the whole view |
| static lists of elements | `Seq<T>`: ghost sequence with `s[i]`, `Update`, `Drop`, `Concat`, `Seq.Const`, `==` |
| static function | `[GhostFunction]`: specification-only, its body is ghost context (quantifiers, `Seq`), unfolded at each use |
| linear logic on views (used exactly once) | `[Linear]` types checked by the `LinearityAnalyzer` on Roslyn's control-flow graph |
| frame rule `(ext)` | calls only change what they receive by `ref`/`out`, and the arrays and fields they may write (inferred) |
| Dafny's `ghost var Repr: set<object>`, `Valid()`, `modifies`, `reads`, `fresh` | `Ghost<ObjSet> Repr` field, `[GhostFunction] bool Valid()`, `Spec.Modifies(Repr.Value)`, `Spec.Reads(Repr.Value.Add(this))`, `Spec.Fresh(Repr.Value)` |
| a view of an object's fields, `(pf \| p)` | `[Owned]` class; `Own.New(new C(...), out Own<C> view)`; pass `(C obj, ref Own<C> view)` with `Spec.Requires(view.Obj.Value == obj)` |
| several results, `[r1, r2: int] (...)` (Dafny `returns (k, m)`) | a C# tuple `(int k, int m)`; `Spec.Ensures<(int k, int m)>(r => ... r.k ... r.m ...)`; callers read `t.k` or deconstruct with `var (k, m) = ...` |
| `$UNSAFE` | `[Trusted]`: the body is not verified, its contract is taken as an axiom, linearity is not checked |
| proof erasure | `[Conditional]` erasure: in a normal build no spec, lemma call or argument remains |

## How it works

### Layer 1: analyzers (IDE squiggles, no solver)

`CsVerify.Analyzers` (netstandard2.0) comes inside the `CsVerify` package, so any IDE shows its diagnostics.

**Linearity** (`LinearityAnalyzer`): this is the ephemeral, linear-logic half of ATS's constraints. For every method body it builds the Roslyn `ControlFlowGraph`.

- **Tracked:** every local and by-value parameter whose type is `[Linear]`.
- **States:** each is in a set of states {Unassigned, Live, Consumed}. Sets are joined by union where paths meet, iterated to a fixpoint.
- **Consumes:** passing by value, `return`, and moving into another variable (`var w = v;`).
- **Borrows:** `ref`/`in` arguments and member reads. The value must be Live.
- **`ref` parameters are ATS's `!pf`:** inside the method a `ref` view may be consumed, for example split, as long as it holds a value again on every return (it is joined back). An `in` parameter is read-only and can never be consumed.
- **Defines:** `out var v` and assignment.
- **Exceptions:** throw edges are not exits (as in ATS, an exception may leak a view).
- **Errors:**
  - a borrow or consume where Consumed is possible: CSV0002;
  - Live at the method exit, i.e. not consumed on every path: CSV0001;
  - a `ref` parameter not holding a value on return: CSV0001;
  - consuming an `in` parameter: CSV0005;
  - capture by a lambda or local function: CSV0003;
  - boxing, or storing in a field of a non-linear type: CSV0004;
  - creating a view with `default`/`new` outside `[Trusted]` (forging a proof): CSV0006;
  - one linear value passed to two parameters of a call (`Swap(ref v, ref v, ...)`): CSV0007. C# allows the aliasing; ATS's linearity does not. Several `in` borrows may share a value.
- **Ghost uses don't count:** a use inside a `Spec.*` argument is ghost, like a proof term.

**Ghost hygiene** (`GhostAnalyzer`):
- `Ghost<T>.Value`, `Spec.Forall`/`Exists` only in ghost context: `Spec.*` arguments, lemma arguments, lemma bodies (CSV0010).
- `Spec.Result` only inside `Spec.Ensures`; `Spec.Old` inside `Spec.Ensures`, `Spec.Invariant` and `Spec.Assert` (CSV0012). `Old` rewinds the heap and the parameters to method entry; locals keep their current values, as in Dafny.
- A `[Lemma]` must be `void` and `[Conditional("CSVERIFY_SPEC")]`, so its calls are erased (CSV0011).

**Purity** (`PurityAnalyzer`, CSV0013). Proofs and specifications have no side effects. The rule covers the bodies of lemmas, `[Pure]` and `[GhostFunction]` methods, and every `Spec.*` argument; the verifier relies on it.
- **What's allowed:** a proof may assign only its own locals and value parameters, and may call only lemmas, pure functions, the spec library and `System.Math`.
- **What's not:**
  - writing an array element, field or property;
  - calling ordinary code, a delegate or a virtual method;
  - allocating;
  - `ref`/`out` parameters on a pure function;
  - a virtual, abstract or interface proof.
- **Why each matters:**
  - A lemma call is erased from the program, so a write inside it would happen only in the verifier's model.
  - A pure function is an SMT function of its arguments, so an allocation would make `f() == f()` false.
  - An override could have a different body from the one the verifier unfolds.

The verifier runs all three analyzers over the compilation it verifies: a method with an analyzer error is not verified.

### Layer 2: the verifier (Z3, separate process)

`csverify` loads the sources with `CSVERIFY_SPEC` defined. It compiles them against the Spec library's *sources* (embedded in the tool), so library contracts such as `Mem.*` are read like any other. Then it verifies each method on its own:

1. **Contract.** Read from the `Spec.Requires`/`Ensures`/`Decreases` statements at the top level of the body.
2. **Symbolic execution.** Walk the method's `IOperation` control-flow graph from an entry state where the parameters are fresh SMT constants and the preconditions are assumed. This is forward verification-condition generation, equivalent to weakest precondition per path.
   - `int`-like values are SMT integers, `bool`s are SMT booleans, and `Ghost<T>` is its `T`.
   - Arrays and spans are references with an uninterpreted `length` and contents in a heap `Array Int (Array Int Int)`.
   - Other properties and fields are uninterpreted functions of their object, so `view.Addr == p.Addr` is a constraint about addresses, as in ATS.
3. **Obligations.** Every proof obligation is a query to Z3: "path condition ∧ ¬goal" must be unsatisfiable. Obligations are:
   - callee preconditions,
   - array/span bounds (implicit on every `a[i]`),
   - division by zero,
   - null references (see *Null references* below),
   - `Spec.Assert`,
   - loop invariants (on entry and when maintained),
   - loop and recursion measures. A measure goes down lexicographically: some component decreases from a non-negative value, and every component before it is unchanged. A call is recursive when the callee can reach the caller again through source methods (calls inside specifications don't count), so mutually recursive methods are checked against each other's measures. Their measures must have the same number of components.
   - postconditions at each return,
   - well-definedness of the method's own specifications (CSV1012). Every array index in a spec must be in bounds, every dereference must be of a non-null reference, every `[Pure]` call must be within its precondition, and every divisor must be non-zero. Each condition is guarded by what protects it:
     - the left side of `&&`/`||`;
     - the branch of `?:`;
     - the range of `Spec.Forall`/`Exists` (the obligation becomes `forall i. lo ≤ i < hi ⇒ …`);
     - earlier preconditions and invariants.

     So `a.Length > 0 && a[0] > 0` is fine, and `a[0] > 0` alone is not. Outside its precondition a pure function's value is unspecified, so a spec using it there could be proved vacuously. Preconditions are checked at entry, invariants and measures at an arbitrary iteration, and postconditions at each return. A callee's contract is not re-checked at the call site, since it is checked when the callee is verified.
   - overflow (only with `--overflow`).
4. **Loops.** Each loop is cut at its head. The invariant is checked, the variables and arrays the loop assigns are havocked, and the invariant is assumed. A back edge re-checks the invariant and that the measure decreases while staying ≥ 0.
5. **Calls are modular.** At a call the verifier:
   - checks the callee's `Requires`;
   - havocs `ref`/`out` arguments, and the heap if the callee (transitively) writes array elements (an inferred frame condition);
   - assumes the callee's `Ensures`.
   Lemma calls are the same, so they add their postconditions. `[Pure]` calls are also equal to an uninterpreted function whose single-`return` body is unfolded once. That is what lets a lemma prove `2 * Tri(n) == n * (n + 1)` by induction.
6. **Trusted bodies** are skipped. Their contracts are still used.
7. **Proofs are total** (CSV1011). Ordinary methods are verified for partial correctness: a path that loops forever or throws proves nothing, and doesn't need to. A lemma or a `[Pure]`/`[GhostFunction]` definition must terminate, though. A lemma that loops forever would "prove" its postcondition, and `f(x) = f(x) + 1` has no solution, so assuming it would prove anything. So in proof code:
   - every recursive call, including mutual recursion, needs `Spec.Decreases` on both ends;
   - every loop needs `Spec.Decreases`;
   - a `throw` is an error.
   `[GhostFunction]` bodies are verified too, for this.
8. **What it cannot model, it rejects** (CSV1901, an error): the method is reported as not verified rather than "ok". This covers:
   - `foreach`, `goto` cycles, `try`/`catch`/`finally` (including `using` and `lock`), and hitting the path limit;
   - static fields, mutable fields of structs, and fields of library classes;
   - computed properties other than members of strings, readonly structs and the spec library (`List<T>.Count` changes, so it is not a function of its object);
   - assignments to anything but locals, parameters, array elements and heap fields;
   - constructor chaining (`this(...)`, or `base(...)` of a source class);
   - `ref` locals, and passing array elements or fields by `ref`/`in` (aliases of the heap);
   - object initializers and other unsupported operations.
   Constructors are calls (see *Mutable objects*). Span elements are not tracked, since a span may view any array at an offset: reading one gives an unknown value, and writing one havocs the heap. Constructs whose result is merely unknown, such as shifts and bitwise operators, are still sound and stay CSV1900 warnings.

Ghost sequences are SMT arrays. `Drop` and `Concat` are defined as array lambdas rather than quantified axioms. Quantifiers (`Spec.Forall`) are instantiated by e-matching only (`smt.mbqi false`): when Z3 cannot decide a query it answers "unknown" at once instead of searching until the timeout, and CsVerify reports "unknown" like "sat", as not proved.

Z3 is reset before each method (`(reset)`, then the options and theory again), and fresh names are numbered from zero again, so a method's result never depends on which methods were verified before it. Z3's search is history-dependent, and an "unknown" from e-matching could otherwise come and go with unrelated code.

Z3 runs as a separate process speaking SMT-LIB2, by design. Neither the analyzer nor MSBuild loads native code, any Z3 build for any OS or CPU works (including arm64, where the `Microsoft.Z3` NuGet package's x64-only binaries cannot load), you can upgrade Z3 independently of CsVerify, a solver crash or hang cannot take the build down with it, and `--smt-log` shows exactly what was asked.

### Data types and object invariants

A **data record** is a record class whose whole state is its positional properties. A hierarchy of them is **closed** when the abstract root can't be extended from outside: its constructors are private (cases nested inside it), or the type isn't visible outside the assembly. The verifier then treats it as an algebraic data type:
- **Construction** `new Cons(h, t)` is the term `Cons(h, t)`. Its fields read back, it is not null, its tag is `Cons`'s, and its size is one more than its parts'. A case's base fields are computed from its header (`Ind(Prev) : Fact(Prev.N + 1, ...)` gives `N == Prev.N + 1`).
- **Downcasts.** `(Cons)xs` throws unless `xs` is a `Cons`. Ordinary code that goes on may assume it was. A lemma, a `[Pure]` function or a specification may not throw, so there the cast must be proved (CSV1011, or CSV1012 in a specification).
- **Case analysis.** `is`, `switch` statements and switch expressions test the tag. A value of a closed type is one of its cases, and on each branch it is that case's constructor applied to its own fields. A switch that misses a case throws, which a `[Pure]` function or lemma may not do (CSV1011), and a specification may not do either (CSV1012).
- **Equality.** The synthesized record `==` is equality of values, as long as every field compares the way the verifier models it (integers, booleans, arrays by reference, data records).
- **No identity.** A data value is its contents, so reference identity (`ReferenceEquals`, or `==` at type `object` or an interface) is not modeled. Only comparisons with `null` are known.
- **Structural recursion.** `Spec.Decreases(xs)` measures the value's size, so recursion on a sub-value terminates, and a lemma recursing that way is a proof by structural induction.
- **Fields keep their nullability.** A positional field of a non-nullable type is not null, because the constructor's argument was proved not null.
- **Generic records** (`List<T>`, `Option<T>` with cases `Some<T>`, `None<T>`) are one data type for all instantiations. Tags, constructors and fields are those of the definition, so the `List<int>` a caller builds is what a generic `Length<T>` and its lemmas take apart. Two limits follow from that:
  - **Nullability.** A field of type `T` is maybe-null even in a `List<string>`, because generic code with an unconstrained `T` can build a `List<string>` holding null.
  - **Equality.** `==` is value equality when the type arguments compare as modeled: `List<int>` does, `List<string>` doesn't. In that case the result is unknown, with a warning.

An **object invariant** is a `[Pure]` parameterless `bool` method marked `[Invariant]` on a data record or its base. It is proved at every `new` (CSV1015) and assumed of every object of the type, since the fields never change afterwards. While verifying the invariant itself, or anything it calls, it is not assumed: otherwise a helper could be "proved" from the very invariant it defines. Invariants may read fields and their lengths but not array contents, which can change.

**Constructors** of other classes are calls: `new C(args)` checks the constructor's `Spec.Requires` and assumes its `Spec.Ensures`, about the new object as `this`.

### Mutable objects

**Heap fields.** An instance field or auto-property of a class in the sources is a map from object to value:
- **Reads, writes and aliasing.** `o.F` reads the map and `o.F = v` updates it, so two references to the same object see each other's writes, and different objects don't.
- **Calls.** A call forgets only the fields its callee, or anything it reaches, may write: an inferred frame condition per field. After a virtual or interface call, or a library call handed a callback or a source object, any field may have changed.
- **Loops** forget only the fields they write.
- **`[Pure]` functions** take the field maps they read as arguments, so their value is never stale after a write.
- **Constructors.**
  - Verifying one: the new object's fields start at their defaults and the field initializers run.
  - At `new C(...)`: the constructor's preconditions are checked and its postconditions assumed about the new object. That object is distinct from every reference in scope, and its fields are their defaults unless the constructor or an initializer sets them.
- **Nullability.** Heap fields are maybe-null.

**Owned objects (ATS style).** A class marked `[Owned]` is written only through its object's **view**, `Own<C>`. That is a zero-size `[Linear]` token, so the linearity analyzer ensures at most one exists per object. Views erase like the other proof types.
- **Making a view.** `Own.New(new C(...), out var view)` takes ownership of a new object, and only a new one (CSV1016).
- **Writing.** Writing an owned field needs a live view of the object in hand (CSV1016): a local, a `ref` parameter (an `in` parameter is read-only), or `this` inside the class's own methods. Calling a method of the class needs the receiver's view.
- **Exact frames for free.** A call can change an owned object only if its view goes in (by `ref` or by value), comes out, or the object is the receiver. So even unknown code, such as an interface call, leaves every other owned object as it was, with no frame annotations.
- **Distinctness.** Two views in hand own two different objects, so `(a, ref va, b, ref vb)` needs no `a != b` precondition.
- **The class's `[Invariant]` travels with the view.** It is assumed where a view is received (a parameter, a call's result, and `this` at entry to the class's methods). It is proved where the view is handed over or given back (CSV1015): a call's `ref` or by-value argument, a `ref`/`out` parameter or `this` at return, and `Own.New`. In between, the holder may break it temporarily. Without the view nothing is assumed, because whoever holds it may be mid-update.
- **Reads need no view.** Objects are garbage-collected, and while a method runs nobody else holds a view it lent.
- **Giving up.** `Own.Drop(view)` gives the object up for good.
- **The ATS idiom.** Methods take the object and its view side by side, `Transfer(Account from, ref Own<Account> fromView, ...)`, tied by `Spec.Requires(fromView.Obj.Value == from)`.

**Dafny-style objects (dynamic frames).** For ordinary mutable classes, Dafny's `Valid()`/`Repr` idiom is available:
- **The pieces.** An object keeps a ghost set of the objects it is made of, `Ghost<ObjSet> Repr`, which is erased like every ghost. `ObjSet` has `Empty`, `Of`, `Add`, `Union`, `Contains`, `IsSubsetOf` and `IsDisjointFrom`. A ghost `[GhostFunction] bool Valid()` states the object's invariant over `Repr`.
- **`Spec.Modifies(W)`:** the method writes fields only of objects in `W` (as on entry) or of objects it allocates (CSV1017). A callee that writes fields but has no frame, or a wider one, is reported there too. A call to such a method changes nothing outside `W`: every other object's fields stay as they were, and only the callee's own Modifies is needed, not inferred effects.
- **`Spec.Reads(R)`:** a `[Pure]` or `[GhostFunction]` reads fields only of objects in `R` (CSV1017), and calls only functions whose `Reads` are within `R`. Its value then survives any change of fields that touches nothing in `R`. The verifier follows each change back (a field write touches one object, a call touches its `Modifies` and what it allocates) and keeps the old value whenever the change is disjoint from `R`. So `q.Valid()` survives `p.Swap()` when their representations are disjoint.
- **`Spec.Fresh(x)` / `Spec.Fresh(set)`** in a postcondition: allocated by the method, as Dafny's `fresh`. A constructor that ensures `Spec.Fresh(Repr.Value)` lets clients know two new objects have disjoint representations.
- **Allocation is tracked** (which objects exist), but only in programs that use dynamic frames.
- **Arrays are outside dynamic frames.** Their contents are the array heap, as before, and any change to it ends the frame reasoning for `[Pure]` functions.
- **One style per class.** An `[Owned]` class is framed by its views; `Spec.Modifies`/`Spec.Reads` on its methods is an error (CSV1017).

### Null references

C#'s nullable reference types are only warnings, and deliberately unsound ones: `null!` silences them, `new string[n]` is an array of nulls typed `string[]`, and a field can be read before the constructor sets it. CsVerify takes the annotations as contracts and proves them instead:
- **Every dereference** (`a.Length`, `a[i]`, `x.F`, `x.M()`) must be of a reference proved not null (CSV1013). `this` and `new` objects and arrays are never null. Conditions guard it as for the other checks: `if (a == null) return`, `a != null && a.Length > 0`, `s is not null`, `s is { }`, `?.` and `??`, in code and in specifications.
- **A non-nullable parameter** (`int[] a` in an enabled nullable context) is a precondition: the method assumes it, and each caller proves its argument (CSV1014). `int[]? a` promises nothing, so the method must check before use.
- **A non-nullable return type**, `out` or `ref` parameter is a postcondition: proved at each return (CSV1014), assumed by callers.
- **`!` proves nothing.** It has no run-time effect, so the verifier ignores it: `Len(null!)` is reported.
- **Array elements are maybe-null**, whatever the element type says. Say otherwise with a precondition, `Spec.Requires(Spec.Forall(0, a.Length, i => a[i] != null))`.
- **Oblivious types** (code with nullable disabled) promise nothing, so they are maybe-null too. Only an enabled nullable context lets the verifier know anything is not null. The MSBuild target passes the project's `<Nullable>`, and the command line takes `--nullable` (default `enable`).
- **Library methods** are trusted for their annotations: a non-nullable return type, `[NotNull]` parameters after the call (`ArgumentNullException.ThrowIfNull`), `[NotNullWhen(b)]` parameters when the call returns `b` (`string.IsNullOrEmpty`), and `[AllowNull]` and `[MaybeNull]`.
- **Fields and properties of objects** are maybe-null, except positional fields of data records (above). For other classes, nothing says a constructor set them.

On `samples/Buggy/NullBugs.cs` the C# compiler warns about 3 of the 5 planted bugs. It says nothing about the two `null!` ones and `new string[2]`, and it warns falsely after the precondition that rules null out.

## Enabling `CSVERIFY_SPEC`

You normally **don't** define it. All `Spec` statements and `[Lemma]` methods are `[Conditional("CSVERIFY_SPEC")]`. In a build without the symbol, the C# compiler removes each call and the evaluation of its arguments, so specifications cost nothing at run time (`ErasureTests` checks this). The verifier defines the symbol itself when it compiles your code for analysis.

Do not define `CSVERIFY_SPEC` in a real build. The statements would then be kept, and ghost-only members (`Ghost<T>.Value`, `Spec.Result`, `Spec.Old`, `Spec.Forall`) throw `GhostException` when evaluated at run time.

Use CsVerify in a project:

```xml
<ItemGroup>
  <ProjectReference Include="path/to/src/CsVerify.Spec/CsVerify.Spec.csproj" />
  <!-- the NuGet package brings the analyzer automatically; with a project reference, add it explicitly: -->
  <ProjectReference Include="path/to/src/CsVerify.Analyzers/CsVerify.Analyzers.csproj"
                    OutputItemType="Analyzer" ReferenceOutputAssembly="false" />
</ItemGroup>
```

`dotnet pack src/CsVerify.Spec` produces a `CsVerify` package with the analyzer under `analyzers/dotnet/cs`.

## Running the verifier

Requirements: the .NET 10 SDK and Z3 on `PATH` (`brew install z3`, `apt install z3`, `winget install z3`), or set `CSVERIFY_Z3=/path/to/z3`.

```bash
dotnet run --project src/CsVerify.Verifier -- -v samples/Good
```

```
  ok   Arrays.BinarySearch: 20/20 obligations proved
  ...
csverify: 13 of 13 methods verified, 72/72 obligations proved
```

```bash
dotnet run --project src/CsVerify.Verifier -- samples/Buggy
```

```
samples/Buggy/Bugs.cs(15,24): error CSV1003: index in 'a[i]' might be out of range
samples/Buggy/Bugs.cs(34,60): error CSV1001: precondition 'y != 0' of 'Div' might not hold
samples/Buggy/Bugs.cs(71,21): error CSV1001: precondition 'view.Addr == p.Addr' of 'Read' might not hold
...
```

Arguments are `.cs` files, directories (searched recursively, skipping `bin/` and `obj/`), `.csproj` files (meaning their directory), or `@file.rsp`. The exit code is 0 when everything is proved, 1 on verification errors, 2 on usage errors.

| option | meaning |
|---|---|
| `--nullable <ctx>` | the nullable context: `enable` (default), `disable`, `annotations`, `warnings`; only non-nullable reference types are known not to be null |
| `--overflow` | also prove that `int`/`long`/... arithmetic and narrowing conversions stay in range |
| `--timeout <ms>` | per-query Z3 timeout (default 10000) |
| `--z3 <path>` | Z3 executable |
| `-d <SYMBOL>` / `-r <dll>` | extra preprocessor symbol / metadata reference |
| `--smt-log <file>` | dump the whole SMT-LIB2 conversation |
| `-v` | list every method with its proved/total obligations |

**From MSBuild:** import `CsVerify.Verifier.targets`, copied next to `csverify.dll` under `build/` (the sample projects show how), then build with:

```bash
dotnet build -p:CsVerifyEnabled=true
```

The verifier runs after `Build` on the project's `Compile` items. Its `file(line,col): error CSVnnnn` output appears as build errors. Pass extra flags with `-p:CsVerifyArgs=--overflow`.

### Diagnostics

| id | from | meaning |
|---|---|---|
| CSV0001 | analyzer | linear value not consumed on every path (leak), or overwritten while live |
| CSV0002 | analyzer | linear value used or consumed after it may have been consumed |
| CSV0003 | analyzer | linear value captured by a lambda / local function |
| CSV0004 | analyzer | linear value boxed, or stored in a non-linear type |
| CSV0005 | analyzer | read-only borrowed (`in`) linear value consumed |
| CSV0006 | analyzer | linear value created by `default`/`new` outside `[Trusted]` |
| CSV0010 | analyzer | ghost value (`Ghost.Value`, `Spec.Forall`/`Exists`, `Seq` members, `[GhostFunction]` calls) outside a specification |
| CSV0011 | analyzer | `[Lemma]` not `void` + `[Conditional("CSVERIFY_SPEC")]` |
| CSV0007 | analyzer | one linear value passed to two parameters of a call |
| CSV0012 | analyzer | `Spec.Result` outside `Spec.Ensures`; `Spec.Old` outside `Ensures`/`Invariant`/`Assert` |
| CSV0013 | analyzer | side effect in a proof (lemma, `[Pure]`, `[GhostFunction]`) or a specification argument |
| CSV1001 | verifier | callee precondition might not hold |
| CSV1002 | verifier | postcondition might not hold on a return path |
| CSV1003 | verifier | index might be out of range / negative array size |
| CSV1004 | verifier | `Spec.Assert` might not hold |
| CSV1005 / CSV1006 | verifier | loop invariant might not hold on entry / might not be maintained |
| CSV1007 | verifier | loop measure might not decrease or might be negative |
| CSV1008 | verifier | recursion measure (own or of a mutually recursive callee) might not decrease or might be negative |
| CSV1009 | verifier | possible division by zero |
| CSV1010 | verifier | possible overflow (`--overflow`) |
| CSV1012 | verifier | a specification might not be well-defined: index out of range, null dereference, `[Pure]` call outside its precondition, or division by zero inside a spec |
| CSV1013 | verifier | a dereference (`a.Length`, `a[i]`, `x.M()`) of a reference that might be null |
| CSV1014 | verifier | a possibly-null value where a non-nullable type promises otherwise: an argument, a return value, an `out`/`ref` parameter on return |
| CSV1015 | verifier | an object invariant might not hold for a new object |
| CSV1016 | verifier | an [Owned] object written without its view in hand, or a view made for an object that is not new |
| CSV1017 | verifier | a dynamic frame broken: a write outside `Spec.Modifies`, a read outside `Spec.Reads`, a callee with no or a wider frame, or `Spec.Modifies`/`Reads` on an `[Owned]` class |
| CSV1011 | verifier | a lemma or `[Pure]`/`[GhostFunction]` might not terminate: recursion or loop without `Spec.Decreases`, or a `throw` |
| CSV1901 | verifier | error: a construct the verifier cannot model soundly; the method is not verified |
| CSV1900 | verifier | warning: a value the verifier treats as unknown (sound), or a misplaced spec |
| CSV1999 | verifier | internal or solver error |
| CSV2001 | erase | the erased program does not compile: run-time code depends on ghost code |

## Proof erasure

In ATS, proofs and static indices exist only at compile time and are erased before the program runs. CsVerify gets most of that from C# itself:
- `[Conditional("CSVERIFY_SPEC")]` deletes specification statements and lemma calls, arguments included.
- Views are empty structs.
- `Split`/`Join` are empty methods the JIT inlines.

Ghost parameters and view tokens are still in the signatures, though. The erasure pass removes all of it, and turns "proofs don't affect the program" from a promise into a check.

```bash
dotnet build -p:CsVerifyErase=true          # build the erased program
csverify erase --out erased/ src/           # or write it out to look at
```

**What it removes:**
- Specification statements.
- Lemmas and `[GhostFunction]`s, with their calls.
- Every parameter, argument, local, field and property of a **proof type**: `Ghost<T>`, `Seq<T>`, and data-less `[Linear]` structs (views such as `PointsTo<T>`, `ArrayView<T>` and `FreeGc<T>`, or your own tokens).
- Trusted view functions that only consume and produce proofs (`Mem.Split`, `Join`, `TakeOut`, `PutBack`), with their calls.
- Proof results: a method returning a view returns `void`.

What is left is ATS's erased program:

```csharp
// before                                                        // after erasure
public static void Fill(ref ArrayView<int> view, Ptr<int> p,     public static void Fill(Ptr<int> p, int n, int x)
                        int n, int x)                            {
{                                                                    if (n == 0) return;
    Spec.Requires(view.Addr == p.Addr && view.Length.Value == n);    if (n == 1) { Mem.Set(p, 0, x); return; }
    ...                                                              int mid = n / 2;
    Mem.Split(view, Ghost.Of(mid), out var left, out var right);     Fill(p, mid, x);
    Fill(ref left, p, mid, x);                                       Fill(p.Offset(mid), n - mid, x);
    Fill(ref right, p.Offset(mid), n - mid, x);                  }
    Mem.Join(left, right, out view);
}
```

**The runtime.** The Spec library goes through the same pass and becomes a small runtime that is compiled into the program in place of the CsVerify assembly. It keeps `Ptr<T>`, `Mem.Read(p)`, `Mem.AllocArray(n, fill)` and the like, and has no `Spec`, `Ghost`, `Seq` or view types at all.

**The check.** If the erased program does not compile, run-time code still depends on a proof, for example a view hidden in a tuple or a `Ghost` boxed into an `object`. That is error CSV2001, reported at the original line.

**How it builds.** Like Tarp's instrumentation:
- the rewrite happens right before the compiler runs, into `obj/.../csverify-erased/`;
- deletions keep their line breaks, and each file starts with a `#line` naming the original, so errors, stack traces and the debugger stay on your sources;
- switching between erased and normal builds recompiles.

**Tested:** the erased samples carry no ghost types or ghost references, and running them returns exactly the values their verified postconditions state.

**Limitations:**
- Erasure works per project. The runtime is compiled into each erased project, so `Ptr<T>` from two erased projects are different types.
- A proof type inside a generic or a tuple is not erased; the check reports it.

## Specification rules

- `Requires`, `Ensures` and `Decreases` must be **top-level statements of the method body** (anywhere among them, conventionally first). An `out` parameter must be assigned before an `Ensures` mentions it, because C#'s definite assignment applies to the erased call too.
- `Invariant` and a loop `Decreases` must be the **leading statements of the loop body**. They hold each time the loop condition is tested, Xanadu-style, not only inside the body.
- `Spec.Ensures<R>(r => …)` binds `r` to the return value. Lambdas cannot capture `ref`/`in` parameters, so for those use `Spec.Ensures(bool)` with `Spec.Result<R>()` and `Spec.Old(x)`.
- `Spec.Forall(lo, hi, i => P)` / `Spec.Exists(...)` are bounded integer quantifiers.
- Specification expressions should be side-effect free. Calls in them must be `[Pure]`.

## Samples

`samples/Good` (verifies completely, no analyzer diagnostics):
- `Arrays.Sum`: safe array sum against a recursive `[Pure]` definition.
- `Arrays.BinarySearch`: binary search with invariants and the full functional spec.
- `Arrays.Append`: length and contents postcondition.
- `Arrays.Last`: a ghost static index.
- `Lemmas.TriFormula`: `2·Tri(n) = n(n+1)` by induction, used by `TriFast`.
- `Lemmas.Power2`: recursion termination.
- `Memory.*`: alloc / read / write / free with linear `PointsTo` views, including a function that borrows a view and gives it back.
- `ArrayViews.Fill`: divide-and-conquer fill. It splits `array_v(n, l)` into `array_v(n/2, l) * array_v(n - n/2, l + n/2)`, recurses on each half through its own pointer, and joins them back.
- `DataTypes.cs` (lists after ATS and Dafny, expressions after Dafny's tutorial, FACT from INT2PROGINATS):
  - `Length`, `Append` and `Reverse` on a generic `List<T>`, with `AppendLength` and `ReverseLength` proved by structural induction. `Countdown` builds a `List<int>` whose length is proved, and `ReversedCount` applies the generic lemma to it.
  - `Eval` and constant folding `Fold` on expressions, with `FoldPreservesEval`.
  - The dataprop `FACT` as a closed record (`Bas`, `Ind`), with its `nat` index as an invariant. `FactIsFunctional` is ATS's `fact_isfun`, by induction on one proof and case analysis on the other. `Factorial` returns `r` together with a `Ghost<Fact>` proof of `FACT(n, r)` built in its loop; the erased program never builds it.
  - `Interval`, a record with the invariant `Lo <= Hi`, and `Widen`, which keeps it.
- `Trees.cs`, after ATS's verified AVL and red-black trees. ATS indexes the types, `avltree(h)` and `rbtree(color, bh, violation)`, so an unbalanced tree does not type-check. Here those indices are invariants of the node records, so no unbalanced node can be built:
  - **AVL:** `Node`, both rotations (single and double), and `Insert`, proved to raise the height by at most one.
  - **Red-black, after Okasaki:** `BalanceL` and `BalanceR` handle the four rotation cases as nested C# patterns, such as `Ins.Viol(Rb.T { Red: true } a, var y, var c)`. `Ins` keeps the black height. `Insert` raises it by at most one. ATS's violation index becomes a type of its own, `Ins = Fine(Rb) | Viol(l, k, r)`: an intermediate tree that may have a red-red violation at its root cannot be an `Rb`.
  - **Hints and dead branches:** `Spec.Assert(Bh(a) == Bh(a.L))` hints play the part of ATS's `prval` steps, because definitions unfold one level per use. Unreachable branches carry a `Spec.Assert(false)` that the verifier checks.
- `DynamicFrames.cs`: Dafny's `Valid()`/`Repr` idiom. A `Pair` of two cells has a ghost representation set, a ghost `Valid()` that reads only it, and `IncA`/`Swap` that modify only it. `Demo` builds two pairs, updates one, and proves the other unchanged and still valid.
- `Owned.cs`: an `[Owned]` bank `Account` whose invariant (never overdrawn) travels with its view. `Bank.Transfer` takes two accounts with their views, and `Demo` calls unknown `IAudit` code between updates and still knows both balances.
- `Nulls.*`: nullable parameters checked before use, `??`, a `string[]` whose elements a precondition proves non-null, and a caller that proves it.
- `ArrayViews.SwapEnds`: exchanges the first and last cells through two disjoint views. The postcondition is an exact sequence equation: `Elems == Old.Update(0, Old[n-1]).Update(n-1, Old[0])`.

### Ported from ATS and Dafny

Rewritten in C#, not copied. Each program names its source in its doc comment.
- `AtsIntro.cs`, from Xi's *Introduction to Programming in ATS* (INT2PROGINATS) and the Stateful Views paper:
  - `FactIter` and `FibIter` against `[Pure]` versions of the FACT and FIB dataprops.
  - `Mul` by repeated addition (the MUL relation) and the inductive lemma `MulSucc`.
  - Euclid's `GcdIter`.
  - `Swap` of two cells through two borrowed `T @ l` views.
  - `Ackermann`, with the lexicographic metric `(m, n)`.
  - `IsEven`/`IsOdd`, mutually recursive, with metrics `2n` and `2n + 1`.
- `AtsMatrixAndTakeOut.cs`, from INT2PROGINATS and `matrixSub` in Xi's ICFP'05 paper:
  - `IncrementAt`, which takes cell i out of an array view as a plain `int @ (l + i)`, updates it with the single-cell `Read`/`Write`, and puts it back.
  - `MatGet` and `FillRows`, which index an m × n matrix in row-major order. The nonlinear bound `i·n + j < m·n` comes from the lemma `RowMajorInBounds`, which is built on an inductive `MulMonotone`.
- `AtsArrays.cs`:
  - DML's `DotProd`: only bounds, the point of the PLDI'98 paper.
  - A view-based `Copy`: `!array_v` × 2, element-wise postcondition.
  - `InsertionSort`, sortedness only.
- `DafnyClassics.cs`, from the Dafny tutorial and the Dafny test suite:
  - `FindMax`, `Find`, `Reverse` in place (uses `Spec.Old` inside the loop invariant), `Sqrt`.
  - `FastPow`, exponentiation by squaring, with the inductive lemma `PowAdd`.
  - `DutchFlag`, sortedness only.
  - `McCarthy91`, whose nested recursion terminates only thanks to the inner call's postcondition.
  - `FindZero`, which skips ahead justified by a lemma containing a loop.
- `DafnyMore.cs`, from Dafny's test suite:
  - `MaxSegSum`, Kadane's algorithm. It returns the optimal segment `(k, m)` as a tuple and proves it beats every segment, with doubly quantified invariants over a `[Pure] Sum`.
  - `Cubes`, which fills `a[i] = i³` with additions only.
  - `SumOfCubes`, through Nicomachus' theorem `Σ i³ = (Σ i)²`, which uses two inductive lemmas.
  - `AdditiveFactorial`, nested loops of additions.

`samples/Buggy/PortBugs.cs` holds the same programs with planted bugs:
- a wrong initial accumulator;
- a mirror index off by one;
- squaring without the lemma;
- a wrong termination metric;
- a Dutch flag that forgets `mid++`;
- Ackermann with only `m` as its metric;
- `Even`/`Odd` both measured by `n`.

`samples/Buggy/PortBugs2.cs` does the same for the second batch:
- a taken-out cell written through the wrong pointer;
- a matrix stride by rows instead of columns;
- Kadane without the restart;
- a wrong finite difference in `Cubes`;
- sum of cubes without the Nicomachus lemma.

**What the ports could not say yet:**
- **Permutation.** Sorts and partitions don't prove that the output is a permutation of the input. ATS proves it with a dataprop over lists, Dafny with `multiset`.
- **Dataviews.** Singly-linked list segments (`slseg`, PADL'05) need views defined by cases over mutable memory. That is stage 2: mutable objects, owned through views.
- **Proofs returned by lemmas.** ATS's `fact_istot` returns a proof. A lemma is a `[Conditional]` void method, which can't have `out` parameters, so only run-time functions can return a `Ghost<T>` proof (`Factorial`).
- **Sets and cardinalities.** Pigeonhole proofs like Dafny's TwoDuplicates need them.

Of the surveyed programs, the ones that remain need the features above. One exception: Dafny's `MinWindowMax` is feasible but heavy.

Sources and licences:
- The ATS-CodeBook is MIT licensed (its only relevant recipe is binary search, already covered by `Arrays.BinarySearch`).
- The INT2PROGINATS code carries an MIT-style notice, © Hongwei Xi.
- Dafny is MIT licensed, © Microsoft.
- The papers' programs are re-implemented, not copied.

`samples/Buggy` holds deliberate errors:
- `Bugs.cs` has one verifier error per method.
- `FrameBugs.cs`: a `Valid()`-style function reading outside its `Spec.Reads`, a write outside `Spec.Modifies`, and two objects whose constructor promises no freshness, so updating one says nothing about the other.
- `OwnedBugs.cs`: a method that leaves the object breaking its invariant, a write without the view, a forged second view, reading the invariant without the view, and a write after `Drop`.
- `TreeBugs.cs`: an AVL insert that never rotates, a single rotation where a double one is needed, and a red-black rebalance that leaves a red node over a red child.
- `DataBugs.cs`: a switch missing a case, recursion on the same tree instead of a subtree, a constant folder that breaks its correctness lemma, a FACT proof step that does not match the computation, an interval built the wrong way round, and an assertion that two equal values are the same object.
- `NullBugs.cs`: an unchecked `T?`, `null!` passed and returned, an element of `new string[2]`, and a precondition that reads `a.Length` before checking `a`.
- `ArrayViewBugs.cs`: a wrong pointer offset, halves never joined back, and a read one past the end of a view.
- `Linearity.cs` has leak, double free, use-after-free, forging and run-time ghost reads. Its analyzer errors are downgraded to warnings in that project's `.editorconfig` so the solution still builds.
- `ProofBugs.cs` holds proofs that would be unsound if accepted:
  - a circular lemma that "proves" `n != n` (CSV1011);
  - an inconsistent definition `f(x) = f(x) + 1` (CSV1011);
  - a lemma that writes an array (CSV0013);
  - one view passed as two `ref` arguments, so the contract says +1 while the cell gets +2 (CSV0007).

## Layout

```
src/CsVerify.Spec        Spec, Ghost<T>, attributes, Ptr<T>/PointsTo<T>/Mem    (net10.0, package "CsVerify")
src/CsVerify.Analyzers   LinearityAnalyzer, GhostAnalyzer, PurityAnalyzer      (netstandard2.0)
src/CsVerify.Verifier    csverify: contracts, CFG symbolic execution, SMT-LIB/Z3, erasure, MSBuild targets (net10.0)
tests/CsVerify.Tests     xUnit: analyzer rules, erasure, verifier proved/refuted per feature, samples
samples/Good, samples/Buggy
```

`dotnet build` builds everything; `dotnet test` runs the 159 tests (they need Z3 on `PATH`).

## Limitations (honest list)

**What "verified" does not cover** (deliberate choices, documented rather than hidden)
- **Integers.** Without `--overflow`, integers are mathematical. C#'s unchecked `int` wraps, so a proof can hold for ℤ and fail at run time on overflow. ATS makes the same idealization for its constraint solver. Use `--overflow` to close it, at the price of range preconditions.
- **Exceptions and `null`.** Ordinary methods are verified for partial correctness with respect to exceptions: a path that throws is not followed further. Proofs may not throw (CSV1011). Null dereferences are not exceptions in this sense: they are proved absent (CSV1013/CSV1014).
- **Mutable objects.**
  - **Dynamic frames.**
    - Virtual and interface calls, and library calls handed source objects, can't be checked against `Spec.Modifies`.
    - The frame rule for `[Pure]` functions follows at most 16 changes back.
    - Loops forget the fields they write for every object; restate what is kept in the invariant.
  - **`[Invariant]` on an ordinary mutable class** (neither a data record nor `[Owned]`) is not used: it is neither assumed nor proved.
  - **Loops** that write owned fields forget them for every object, not just the ones whose views they hold.
  - **Library code** is trusted not to write source objects' fields except through what it is handed, so reflection is not covered.
- **Null and object state.** Fields and properties are maybe-null, except positional fields of data records. Library nullability annotations are trusted, not checked.
- **Data types.** Closedness is checked within the compilation. A hierarchy whose root has only private constructors is closed, except that the record's synthesized protected copy constructor could in principle be derived through from another assembly. Data values have no identity, so code that relies on reference identity of records is not verified for it.
- **Unfolding depth.** `Length(Cons(1, Nil))` needs `Length(Nil)` stated too, because a `[Pure]` definition unfolds one level per use. Concrete values are not evaluated to the end.
- **Termination of ordinary methods** is only checked where `Spec.Decreases` is given (a warning otherwise).
- **Virtual dispatch.** Calls through interfaces or virtual methods use the contract written on the declared member (an interface member has none, so its result is unknown). Proofs cannot be virtual (CSV0013).
- **`[Trusted]` and `Spec.Assume`** are axioms by definition.

**Unsupported constructs**
- Rejected as CSV1901 (the method is not verified): see "What it cannot model, it rejects" above.
- Unknown values, which are sound (CSV1900 warning): shifts and bitwise operators on integers, floating point, string characters, non-pure calls in specifications.
- Not verified as separate units: local functions and lambdas.

**Completeness limits** (true things that may not be proved)
- A new array is known to differ only from the arrays visible in local variables where it is created.
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
- The `CsVerify` package produced by `dotnet pack` is not published. The verifier is a `dotnet tool` (`PackAsTool`) that is not published either.

## References

- H. Xi, *Applied Type System* (extended abstract), TYPES 2003.
- H. Xi, *Applied Type System: An Approach to Practical Programming with Theorem-Proving*, arXiv:1703.08683.
- D. Zhu, H. Xi, *Safe Programming with Pointers through Stateful Views*, PADL 2005.
- H. Xi, *Imperative Programming with Dependent Types* (Xanadu), LICS 2000.
- H. Xi, F. Pfenning, *Eliminating Array Bound Checking Through Dependent Types*, PLDI 1998.
- H. Xi, *Introduction to Programming in ATS*, https://ats-lang.github.io (INT2PROGINATS).
- K. R. M. Leino et al., Dafny tutorial and test suite, https://github.com/dafny-lang/dafny.
