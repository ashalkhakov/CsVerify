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
| frame rule `(ext)` | calls only change what they receive by `ref`/`out` (and arrays they may write) |
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
   - `Spec.Assert`,
   - loop invariants (on entry and when maintained),
   - loop and recursion measures. A measure goes down lexicographically: some component decreases from a non-negative value, and every component before it is unchanged. A call is recursive when the callee can reach the caller again through source methods (calls inside specifications don't count), so mutually recursive methods are checked against each other's measures. Their measures must have the same number of components.
   - postconditions at each return,
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
   - mutable fields;
   - properties other than get-only/init-only auto-properties and members of strings, readonly structs and the spec library (`List<T>.Count` changes, so it is not a function of its object);
   - assignments to anything but locals, parameters and array elements;
   - `ref` locals, and passing array elements or fields by `ref`/`in` (aliases of the heap);
   - object initializers and other unsupported operations.
   Constructors are calls: the heap is havocked if they may write arrays. Span elements are not tracked, since a span may view any array at an offset: reading one gives an unknown value, and writing one havocs the heap. Constructs whose result is merely unknown, such as shifts and bitwise operators, are still sound and stay CSV1900 warnings.

Ghost sequences are SMT arrays. `Drop` and `Concat` are defined as array lambdas rather than quantified axioms. Quantifiers (`Spec.Forall`) are instantiated by e-matching only (`smt.mbqi false`): when Z3 cannot decide a query it answers "unknown" at once instead of searching until the timeout, and CsVerify reports "unknown" like "sat", as not proved.

Z3 runs as a separate process speaking SMT-LIB2. Neither the analyzer nor MSBuild loads native code, and any Z3 build for any OS or CPU works. See *Limitations* for why this is not the `Microsoft.Z3` NuGet package.

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

Requirements: the .NET 8 SDK and Z3 on `PATH` (`brew install z3`, `apt install z3`, `winget install z3`), or set `CSVERIFY_Z3=/path/to/z3`.

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
| CSV1011 | verifier | a lemma or `[Pure]`/`[GhostFunction]` might not terminate: recursion or loop without `Spec.Decreases`, or a `throw` |
| CSV1901 | verifier | error: a construct the verifier cannot model soundly; the method is not verified |
| CSV1900 | verifier | warning: a value the verifier treats as unknown (sound), or a misplaced spec |
| CSV1999 | verifier | internal or solver error |

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
- **Dataprops.** `FACT(n, r)` and friends become `[Pure]` functions. That is fine for functional relations. A relation that is not a function, or a proof that is case-analysed, has no counterpart.
- **Datatypes and dataviews.** List reverse/append with length indices (Xanadu, ICFP'05), singly-linked list segments (`slseg`, PADL'05), red-black trees (DML) and typed evaluators all need user datatypes or dataviews.
- **Sets and cardinalities.** Pigeonhole proofs like Dafny's TwoDuplicates need them.

Of the surveyed programs, the ones that remain need the features above. One exception: Dafny's `MinWindowMax` is feasible but heavy.

Sources and licences:
- The ATS-CodeBook is MIT licensed (its only relevant recipe is binary search, already covered by `Arrays.BinarySearch`).
- The INT2PROGINATS code carries an MIT-style notice, © Hongwei Xi.
- Dafny is MIT licensed, © Microsoft.
- The papers' programs are re-implemented, not copied.

`samples/Buggy` holds deliberate errors:
- `Bugs.cs` has one verifier error per method.
- `ArrayViewBugs.cs`: a wrong pointer offset, halves never joined back, and a read one past the end of a view.
- `Linearity.cs` has leak, double free, use-after-free, forging and run-time ghost reads. Its analyzer errors are downgraded to warnings in that project's `.editorconfig` so the solution still builds.
- `ProofBugs.cs` holds proofs that would be unsound if accepted:
  - a circular lemma that "proves" `n != n` (CSV1011);
  - an inconsistent definition `f(x) = f(x) + 1` (CSV1011);
  - a lemma that writes an array (CSV0013);
  - one view passed as two `ref` arguments, so the contract says +1 while the cell gets +2 (CSV0007).

## Layout

```
src/CsVerify.Spec        Spec, Ghost<T>, attributes, Ptr<T>/PointsTo<T>/Mem    (net8.0, package "CsVerify")
src/CsVerify.Analyzers   LinearityAnalyzer, GhostAnalyzer                      (netstandard2.0)
src/CsVerify.Verifier    csverify: contracts, CFG symbolic execution, SMT-LIB/Z3, MSBuild targets (net8.0)
tests/CsVerify.Tests     xUnit: analyzer rules, erasure, verifier proved/refuted per feature, samples
samples/Good, samples/Buggy
```

`dotnet build` builds everything; `dotnet test` runs the 103 tests (they need Z3 on `PATH`).

## Limitations (honest list)

**Solver**
- **Z3 runs as a process, not through the `Microsoft.Z3` NuGet package.** The package's managed `Microsoft.Z3.dll` is built for x64 only, and the package ships x64-only native libraries (checked for 4.11.2–4.12.2). It cannot load in an arm64 .NET process, such as on Apple Silicon. Speaking SMT-LIB2 to a `z3` executable works on every platform and keeps native code out of both the analyzer and MSBuild.

**What "verified" does not cover** (deliberate choices, documented rather than hidden)
- **Integers.** Without `--overflow`, integers are mathematical. C#'s unchecked `int` wraps, so a proof can hold for ℤ and fail at run time on overflow. ATS makes the same idealization for its constraint solver. Use `--overflow` to close it, at the price of range preconditions.
- **Exceptions and `null`.** Ordinary methods are verified for partial correctness with respect to exceptions: a path that throws is not followed further. Null dereferences are not checked; enable C#'s nullable reference types for that. Proofs may not throw (CSV1011).
- **Termination of ordinary methods** is only checked where `Spec.Decreases` is given (a warning otherwise).
- **Well-definedness of specifications.** An out-of-range `a[i]` or a `[Pure]` call outside its precondition inside a spec denotes an unspecified value; it is not reported. A spec that relies on such a value cannot be proved, but a vacuous one can.
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
- View-changing proof functions (`Split`, `Join`, `TakeOut`, `PutBack`) cannot be `[Conditional]`, because C# forbids `out` parameters on conditional methods. They are empty, inlined methods on data-less structs instead: proof erasure by the JIT rather than by the compiler.
- Contents of a view are compared as whole sequences (`Elems == ...`), because C# lambdas cannot capture `ref`/`in` parameters. Element-wise properties go through a `[GhostFunction]` that takes the `Seq<T>` by value (see `ArrayViews.AllEqual`).
- With e-matching only, a property that needs a cleverer quantifier instantiation may come back "not proved" even though it is true. Add an intermediate `Spec.Assert` or a lemma.
- The analyzer does not track linear fields inside a linear struct separately: the struct is one resource.

**Packaging**
- "Zero-size" types are empty structs. The CLR still gives them one byte, but they carry no data.
- The `CsVerify` package produced by `dotnet pack` is not published. The verifier is a `dotnet tool` (`PackAsTool`) that is not published either.

## References

- H. Xi, *Applied Type System* (extended abstract), TYPES 2003.
- H. Xi, *Applied Type System: An Approach to Practical Programming with Theorem-Proving*, arXiv:1703.08683.
- D. Zhu, H. Xi, *Safe Programming with Pointers through Stateful Views*, PADL 2005.
- H. Xi, *Imperative Programming with Dependent Types* (Xanadu), LICS 2000.
- H. Xi, F. Pfenning, *Eliminating Array Bound Checking Through Dependent Types*, PLDI 1998.
- H. Xi, *Introduction to Programming in ATS*, https://ats-lang.github.io (INT2PROGINATS).
- K. R. M. Leino et al., Dafny tutorial and test suite, https://github.com/dafny-lang/dafny.
