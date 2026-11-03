# How it works

## Layer 1: analyzers (IDE squiggles, no solver)

`CsVerify.Analyzers` (netstandard2.0) comes inside the `CsVerify` package, so any IDE shows its diagnostics.

**Linearity** (`LinearityAnalyzer`): this is the ephemeral, linear-logic half of ATS's constraints. For every method body it builds the Roslyn `ControlFlowGraph`.

- **Tracked:** every local and by-value parameter whose type is `[Linear]`.
- **States:** each is in a set of states {Unassigned, Live, Consumed}. Sets are joined by union where paths meet, iterated to a fixpoint.
- **Consumes:** passing by value, `return`, and moving into another variable (`var w = v;`).
- **Borrows:** `ref`/`in` arguments and member reads. The value must be Live.
- **`ref` parameters are ATS's `!pf`:** inside the method a `ref` view may be consumed, for example split, as long as it holds a value again on every return (it is joined back). An `in` parameter is read-only and can never be consumed.
- **Defines:** `out var v` and assignment.
- **Exceptions:** a throw is not a normal exit, so views need not be consumed on it (as in ATS, an exception may leak a view). A catch or filter loses the linear values its try may have consumed or lent by `ref`; a `finally` may not use linear values from outside it.
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
- **What's allowed:** a proof may assign only its own locals and value parameters, and may call only lemmas, pure functions (library members whose stub is `[Pure]` too), the spec library and `System.Math`.
- **What's not:**
  - writing an array element, field or property;
  - calling ordinary code or a delegate (a virtual `[Pure]` query is fine);
  - allocating;
  - `ref`/`out` parameters on a pure function;
  - a virtual, abstract or interface lemma or ghost function (a `[Pure]` query may be virtual: see [Object-oriented code](objects.md#object-oriented-code)).
- **Why each matters:**
  - A lemma call is erased from the program, so a write inside it would happen only in the verifier's model.
  - A pure function is an SMT function of its arguments, so an allocation would make `f() == f()` false.
  - An override could have a different body from the one the verifier unfolds.

The verifier runs all three analyzers over the compilation it verifies: a method with an analyzer error is not verified.

## Layer 2: the verifier (Z3, separate process)

The verifier (`dotnet csverify`) loads the sources with `CSVERIFY_SPEC` defined. It compiles them against the Spec library's *sources* (embedded in the tool), so library contracts such as `Mem.*` are read like any other. Then it verifies each method on its own:

1. **Contract.** Read from the `Spec.Requires`/`Ensures`/`Decreases` statements at the top level of the body.
2. **Symbolic execution.** Walk the method's `IOperation` control-flow graph from an entry state where the parameters are fresh SMT constants and the preconditions are assumed. This is forward verification-condition generation, equivalent to weakest precondition per path.
   - `int`-like values are SMT integers, `bool`s are SMT booleans, and `Ghost<T>` is its `T`.
   - Arrays and spans are references with an uninterpreted `length` and contents in a heap `Array Int (Array Int Int)`.
   - A rectangular array (`int[,]`, `int[,,]`) also has a length per dimension (`GetLength(d)`, fixed at creation; `Length` is their product). Cell `[i, j]` is at `cv_cell(i, j)` in the same heap row, and `[i, j, k]` at `cv_cell(cv_cell(i, j), k)`. `cv_cell` is uninterpreted, with inverses `cv_row`/`cv_col` given by an axiom triggered on `cv_cell` terms. *Soundness:* the axiom has a model (ℤ² is countable, so an injection of pairs into ℤ with inverses exists), so it adds nothing false. It makes `cv_cell` injective, so two cells are equal exactly when all their indices are, as for real cells. Each index is checked against its own dimension (CSV1003), and `GetLength(d)` against `0 ≤ d < Rank`. Writes, loop havoc and callee frames treat the array like any other. `Spec.Acc` permissions cover one-dimensional arrays only.
   - Fields of source classes, and their auto-properties, are heap fields (see [Mutable objects](objects.md#mutable-objects)). Other fields and properties that never change (readonly ones, properties of immutable types) are uninterpreted functions of their object, so `view.Addr == p.Addr` is a constraint about addresses, as in ATS.
3. **Obligations.** Every proof obligation is a query to Z3: "path condition ∧ ¬goal" must be unsatisfiable. Obligations are:
   - callee preconditions,
   - array/span bounds (implicit on every `a[i]`),
   - division by zero,
   - null references (see [Null references](semantics.md#null-references) below),
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
   - overflow of run-time integer arithmetic and narrowing conversions (see [Bounded integers](semantics.md#bounded-integers)).
4. **Loops.** Each loop is cut at its head. The invariant is checked, the variables and arrays the loop assigns are havocked, and the invariant is assumed. A back edge re-checks the invariant and that the measure decreases while staying ≥ 0.
   - **`foreach` over a one-dimensional array** is modeled as what C# compiles it to: `for (int i = 0; i < a.Length; i++) { var x = a[i]; body }`, with `a` evaluated once (null throws, CSV1013) and no enumerator or finally. The hidden index is `Spec.Index(x)`, a ghost (CSV0010 outside specifications). In the loop's invariants it is the number of elements gone through, and in the body it is the index of `x`, so `Spec.Invariant(s == Sum(a, Spec.Index(x)))` is the usual prefix invariant. *Soundness:* this is the C# compiler's own lowering for arrays, so the model runs exactly what executes. At the head the index is havocked to some value in `0 ≤ i ≤ a.Length`. That range is an inductive invariant the verifier proves itself: `i = 0` on entry, and a back edge comes from an iteration where `i < a.Length` held, giving `i + 1 ≤ a.Length`. It only needs `a.Length`, which cannot change, and the array reference the loop holds, which is not the variable `a` and so is not affected by reassigning it. Each element is read from the heap when its iteration starts, as the compiled code does, so writes made earlier in the loop are seen. The index rises to a fixed bound, so such a loop terminates, and lemmas need no `Spec.Decreases` for it.
   - **`foreach` over anything else** (`List<T>`, `string`, spans, your own enumerables) is the enumerator pattern the flow graph shows. `GetEnumerator()` runs once before the loop. Each iteration calls `MoveNext()` and `Current`, and `Dispose()` runs in a finally. Each is an ordinary modular call, so a library's elements are unknown values (CSV1900). *Soundness:* this is the C# specification's expansion of `foreach`, and the calls are havocked at the head like any call in a loop body: the heap if `MoveNext`/`Current` may write it, and the fields they write. The enumerator is captured once and is the same object in every iteration, so it is kept across the head. `Spec.Index` of such a loop is unknown, with a CSV1900 warning. In a lemma it needs `Spec.Decreases`, like `while`. `await foreach` is rejected (CSV1901).
   - **`goto` cycles** are cut at the head of each natural loop of the flow graph, the block that dominates every block jumping back to it. That is the labelled statement a backward `goto` targets. The loop's invariants and measure are the `Spec.Invariant`/`Spec.Decreases` statements right after the label (`again: Spec.Invariant(x < 3); x++; if (x < 3) goto again;`). *Soundness:* every cycle through a head passes through it. The invariant is proved on the paths that enter it and on every back edge, the measure decreases on every back edge, and everything the loop's blocks may change is havocked at the head. Those blocks include the handlers and finally blocks of any `try` the loop runs through (a `try` around the whole loop is not), and the calls the flow graph makes (`Dispose`, `MoveNext`). So this is the same argument as for loop statements, made over the graph instead of the syntax. A `goto` back to the head of a `while`/`for`/`do` adds the code on the goto's path to that loop's havoc. A cycle with no such head is a jump into the middle of a loop (irreducible flow), and it is still rejected (CSV1901).
5. **Calls are modular.** At a call the verifier:
   - checks the callee's `Requires`;
   - havocs `ref`/`out` arguments, and the heap if the callee (transitively) writes array elements (an inferred frame condition). A library method writes only the arrays (or spans) it is handed, and reaches fields and other arrays only by running user code it is handed: a delegate, an interface, or an object whose class overrides something (a dictionary's key with its own `Equals`). Strings are never written;
   - assumes the callee's `Ensures`.
   - **Array elements by reference** (`Swap(ref a[i], ref a[j])`, `int.TryParse(s, out a[k])`, `in a[i]`) are copied into the callee's parameter and, for `ref`/`out`, back into the cell after the call. The index is checked, and the cell is written after any heap havoc, so the callee's postconditions speak of the heap as it left it. Two arguments passed by reference, one of them `ref` or `out`, must not be the same cell (proved) or the same variable (CSV1020). *Soundness:* the callee is verified with its parameters as variables of their own. That matches the real call only when nothing else looks at the cell while the callee holds it. So a callee given a cell by `ref`/`out` must not read or write array or span contents at all in code, directly or through anything it calls: operators, accessors, constructors, enumerators, overridable or user-code-running callees all count, and specifications and lemmas do not. A library callee qualifies only when every parameter and its receiver are values or strings, so it cannot reach an array. A callee given a cell only by `in` may read arrays but must not write them. Otherwise it is CSV1901. Under these conditions copy-in/copy-out and by-reference passing give the same final state. Two distinct cells and variables cannot interfere through the callee's parameters, so its contract describes the call exactly.
   A library member with a `[ContractsFor]` stub is called the same way, with the stub's contract: its preconditions are proved, its postconditions assumed (trusted, and counted in the summary line), and its `Spec.Modifies` frames the `[Model]` functions, the ghost fields of library objects (see [Contracts for code without sources](library-contracts.md)). A library method without a stub that is handed something that may lead to an object with model functions may change their values.
   Lemma calls are the same, so they add their postconditions. `[Pure]` calls are also equal to an uninterpreted function whose body is unfolded once: a single expression or `return`, or local declarations, `if`s and `return`s (as a conditional term). That is what lets a lemma prove `2 * Tri(n) == n * (n + 1)` by induction.
6. **Trusted bodies** are skipped. Their contracts are still used.
7. **Proofs are total** (CSV1011). Ordinary methods are verified for partial correctness: a path that loops forever or throws proves nothing, and doesn't need to. A lemma or a `[Pure]`/`[GhostFunction]` definition must terminate, though. A lemma that loops forever would "prove" its postcondition, and `f(x) = f(x) + 1` has no solution, so assuming it would prove anything. So in proof code:
   - every recursive call, including mutual recursion, needs `Spec.Decreases` on both ends;
   - every loop needs `Spec.Decreases`;
   - a `throw` is an error.
   `[GhostFunction]` bodies are verified too, for this.
8. **What it cannot model, it rejects** (CSV1901, an error): the method is reported as not verified rather than "ok". This covers:
   - a `goto` into the middle of a loop (a cycle with two entries), `await foreach`, and hitting the path limit;
   - fields of library classes, a struct held in a class's field written in place (`o.p.X = 1`), and a struct method other than a constructor that writes `this`;
   - in specifications, library properties that may change and have no `[Pure]` stub (`StringBuilder.Length` is not a function of its object). Read in code, each is a value of its own, of its declared type (a CSV1900 warning). Properties with code in the sources are calls (see [Object-oriented code](objects.md#object-oriented-code)), and so are stubbed ones (`List<T>.Count`);
   - assignments to anything but locals, parameters, array elements and heap fields;
   - `ref` locals bound to anything but locals, parameters and array elements, or rebound inside a loop; passing fields by `ref`/`in`; an array element by reference to a callee that may touch arrays (see *Calls*);
   - other unsupported operations.
   **Ref locals** name a location: a variable, or an array cell fixed when the local is bound (`ref int r = ref a[i]` keeps naming that cell after `a` is reassigned, as in C#). Reading and writing `r` read and write the location, so an alias is never out of date. *Soundness:* the binding is evaluated once, as C# does, and every access goes to the current value of the location. A loop that writes through `r` havocs every location `r` is ever bound to in the method. A loop that rebinds `r` makes its location unknown at the head, and a later use is CSV1901.
   **Mutable struct members** (fields and settable auto-properties of the program's structs, not data records or views) are uninterpreted functions of the struct's value, as readonly ones are. `s.X = v` makes `s` a fresh value whose `X` is `v` and whose other members are `s`'s, and writes it back to where `s` lives: a local, a parameter (a `ref` one is the caller's variable), a ref local, an array cell, an enclosing struct's member, or `this` in the struct's constructor. *Soundness:* this is value semantics, because a copy (`var t = s`, an argument by value) holds the old value, which no later write changes. A write inside an array element is a heap write for callers' frames (`a[i].X = 1` counts like `a[i] = …`), and a loop writing a member havocs the struct that holds it. In-place writes the caller could not see are rejected: through a class's field, or to `this` outside a constructor.
   Constructors are calls (see [Mutable objects](objects.md#mutable-objects)). Span elements are not tracked, since a span may view any array at an offset: reading one gives an unknown value, and writing one havocs the heap. Constructs whose result is merely unknown, such as shifts and bitwise operators, are still sound and stay CSV1900 warnings.

Multisets (`Bag`) are SMT arrays from value to count. `Spec.Multiset(a, n)` is a function of the array's contents and `n`, and three axioms say what a write does to it:
- the empty prefix is the empty multiset;
- writing `v` at `i` inside the prefix trades the old element for `v`;
- a write outside the prefix changes nothing.

So a swap keeps the multiset with no lemma. Each axiom is triggered only by the multiset of a written array, so they can't loop. A use unfolds one element, and all of them when `n` is a small constant (a concrete array).

Ghost sequences are SMT arrays. `Drop` and `Concat` are defined as array lambdas rather than quantified axioms. Quantifiers (`Spec.Forall`) are instantiated by e-matching only (`smt.mbqi false`): when Z3 cannot decide a query it answers "unknown" at once instead of searching until the timeout, and CsVerify reports "unknown" like "sat", as not proved.

Z3 is reset before each method (`(reset)`, then the options and theory again), and fresh names are numbered from zero again, so a method's result never depends on which methods were verified before it. Z3's search is history-dependent, and an "unknown" from e-matching could otherwise come and go with unrelated code.

Z3 runs as a separate process speaking SMT-LIB2, by design. Neither the analyzer nor MSBuild loads native code, any Z3 build for any OS or CPU works (including arm64, where the `Microsoft.Z3` NuGet package's x64-only binaries cannot load), you can upgrade Z3 independently of CsVerify, a solver crash or hang cannot take the build down with it, and `--smt-log` shows exactly what was asked.
