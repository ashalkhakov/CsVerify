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

## Layer 2: the verifier (Boogie and Z3)

The verifier (`dotnet csverify`) loads the sources with `CSVERIFY_SPEC` defined. It compiles them against the Spec
library's *sources* (embedded in the tool), so library contracts such as `Mem.*` are read like any other. Then it
translates every method to [Boogie](https://github.com/boogie-org/boogie), an intermediate verification language,
and Boogie proves each procedure with Z3. [The Boogie engine](boogie.md) describes the translation construct by
construct; in outline:

1. **Contract.** Read from the `Spec.Requires`/`Ensures`/`Decreases` statements at the top level of the body (and a
   delegate type's or an interface's contract class, a base member's contract, a library member's stub).
2. **Lowering.** Each method's Roslyn control-flow graph becomes a kernel procedure: blocks of assignments, heap
   reads and writes, calls, assumptions and checks. Integers are mathematical, with their ranges checked; arrays,
   fields and the models of collections are maps of a heap; data records are tagged values; lambdas and local
   functions are procedures of their own, with what they capture as inputs.
3. **Obligations.** The checks pass makes each obligation an assertion, labelled with its diagnostic: callee
   preconditions (CSV1001), postconditions at each return (CSV1002), array bounds (CSV1003), `Spec.Assert` (CSV1004),
   loop invariants on entry and maintained (CSV1005, CSV1006), measures of loops and recursion (CSV1008), division by
   zero (CSV1009), overflow of run-time arithmetic and narrowing conversions (CSV1010), proof code's termination
   (CSV1011), well-definedness of the method's own specifications (CSV1012), null references (CSV1013, CSV1014),
   frames (CSV1017), and the rest the [diagnostics](specifications.md) list. A specification's own checks are guarded
   by what protects them: the left side of `&&` and `||`, the branch of `?:`, a quantifier's range, earlier
   preconditions and invariants.
4. **Loops** are cut at their heads, as Boogie does: the invariant is checked on entry and on every back edge, and
   what the loop may change is forgotten at the head. A loop without invariants gets facts inferred from its
   condition and from what it changes (Houdini's way): a fact that doesn't hold on entry or at a back edge is left out
   and the procedure verified again, until those assumed all held. `foreach` over an array, a string or a List that
   the loop doesn't change is the index loop C# compiles it to; `Spec.Index(x)` is that index.
5. **Calls are modular**: the callee's preconditions are checked and its postconditions assumed; what it may change
   is its `Spec.Modifies` frame, or what an effects analysis says it writes (the fields it and its callees write, the
   arrays it is handed). A library member with a `[ContractsFor]` stub is called with the stub's contract (trusted,
   and counted in the summary line); `[Pure]` methods are Boogie functions, unfolded one level per use.
6. **Trusted bodies** are skipped. Their contracts are still used.
7. **Proofs are total** (CSV1011): a lemma or a `[Pure]`/`[GhostFunction]` definition must terminate, so recursion
   and loops in proof code need `Spec.Decreases`, and a `throw` there is an error. Ordinary methods are verified for
   partial correctness.
8. **What it doesn't translate, or Boogie can't decide in time, is not verified** (CSV1902, an error, saying why),
   with what is checked from the syntax and the declarations alone (locking, lock levels, atomics, concurrency
   marks; `StaticChecks`) still reported. Constructs it can't model soundly are rejected (CSV1901).

Each method is verified as a procedure of its own (Boogie's modular verification), with every procedure's contract
in the same program. Boogie first verifies each procedure whole, in a quarter of the time limit; one it can't decide
is verified one assertion at a time, and a failure found only that way is confirmed by a whole run with more time.

Z3 runs as a separate process, by design: neither the analyzer nor MSBuild loads native code, any Z3 build for any OS
or CPU works, you can upgrade Z3 independently of CsVerify, and a solver crash cannot take the build down with it.
`--boogie-out` writes the Boogie program that was verified.
