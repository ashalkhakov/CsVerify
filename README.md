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
| `prfun` (proof function, total, erased) | `[Lemma, Conditional("CSVERIFY_SPEC")] void L(...)`: body is the proof, recursion is induction |
| `prval () = lemma(...)` | a plain call `L(x);` (erased; adds L's postconditions) |
| static function in constraints | `[Pure]` method: an uninterpreted function whose `return` body is unfolded at each use |
| view `T @ l` | `[Linear] struct PointsTo<T>` with ghost `Addr` (the `l`) and `Value` |
| `ptr(l)` | `Ptr<T>` with ghost `Addr` |
| `getVar (pf: a@l \| p: ptr l)` | `Mem.Read(in view, p)`: `in` borrows the view (ATS `!pf`) |
| `setVar` | `Mem.Write(ref view, p, v)`: `ref` borrows the view and updates it |
| `allocVar` / `freeVar` | `Mem.Alloc(init, out view)` produces a view; `Mem.Free(view, p)` consumes it |
| linear logic on views (used exactly once) | `[Linear]` types checked by the `LinearityAnalyzer` on Roslyn's control-flow graph |
| frame rule `(ext)` | calls only change what they receive by `ref`/`out` (and arrays they may write) |
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
- **Defines:** `out var v` and assignment.
- **Exceptions:** throw edges are not exits (as in ATS, an exception may leak a view).
- **Errors:**
  - a borrow or consume where Consumed is possible: CSV0002;
  - Live at the method exit, i.e. not consumed on every path: CSV0001;
  - consuming a `ref`/`in` parameter: CSV0005;
  - capture by a lambda or local function: CSV0003;
  - boxing, or storing in a field of a non-linear type: CSV0004;
  - creating a view with `default`/`new` outside `[Trusted]` (forging a proof): CSV0006.
- **Ghost uses don't count:** a use inside a `Spec.*` argument is ghost, like a proof term.

**Ghost hygiene** (`GhostAnalyzer`):
- `Ghost<T>.Value`, `Spec.Forall`/`Exists` only in ghost context: `Spec.*` arguments, lemma arguments, lemma bodies (CSV0010).
- `Spec.Result`/`Spec.Old` only inside `Spec.Ensures` (CSV0012).
- A `[Lemma]` must be `void` and `[Conditional("CSVERIFY_SPEC")]`, so its calls are erased (CSV0011).

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
   - loop and recursion measures,
   - postconditions at each return,
   - overflow (only with `--overflow`).
4. **Loops.** Each loop is cut at its head. The invariant is checked, the variables and arrays the loop assigns are havocked, and the invariant is assumed. A back edge re-checks the invariant and that the measure decreases while staying ≥ 0.
5. **Calls are modular.** At a call the verifier:
   - checks the callee's `Requires`;
   - havocs `ref`/`out` arguments, and the heap if the callee (transitively) writes array elements (an inferred frame condition);
   - assumes the callee's `Ensures`.
   Lemma calls are the same, so they add their postconditions. `[Pure]` calls are also equal to an uninterpreted function whose single-`return` body is unfolded once. That is what lets a lemma prove `2 * Tri(n) == n * (n + 1)` by induction.
6. **Trusted bodies** are skipped. Their contracts are still used.

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
| CSV0005 | analyzer | borrowed (`ref`/`in`) linear value consumed |
| CSV0006 | analyzer | linear value created by `default`/`new` outside `[Trusted]` |
| CSV0010 | analyzer | ghost value (`Ghost.Value`, `Spec.Forall`/`Exists`) outside a specification |
| CSV0011 | analyzer | `[Lemma]` not `void` + `[Conditional("CSVERIFY_SPEC")]` |
| CSV0012 | analyzer | `Spec.Result`/`Spec.Old` outside `Spec.Ensures` |
| CSV1001 | verifier | callee precondition might not hold |
| CSV1002 | verifier | postcondition might not hold on a return path |
| CSV1003 | verifier | index might be out of range / negative array size |
| CSV1004 | verifier | `Spec.Assert` might not hold |
| CSV1005 / CSV1006 | verifier | loop invariant might not hold on entry / might not be maintained |
| CSV1007 | verifier | loop measure might not decrease or might be negative |
| CSV1008 | verifier | recursion measure might not decrease or might be negative |
| CSV1009 | verifier | possible division by zero |
| CSV1010 | verifier | possible overflow (`--overflow`) |
| CSV1900 | verifier | warning: construct not modeled, path cut, or spec misplaced |
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

`samples/Buggy` holds deliberate errors:
- `Bugs.cs` has one verifier error per method.
- `Linearity.cs` has leak, double free, use-after-free, forging and run-time ghost reads. Its analyzer errors are downgraded to warnings in that project's `.editorconfig` so the solution still builds.

## Layout

```
src/CsVerify.Spec        Spec, Ghost<T>, attributes, Ptr<T>/PointsTo<T>/Mem    (net8.0, package "CsVerify")
src/CsVerify.Analyzers   LinearityAnalyzer, GhostAnalyzer                      (netstandard2.0)
src/CsVerify.Verifier    csverify: contracts, CFG symbolic execution, SMT-LIB/Z3, MSBuild targets (net8.0)
tests/CsVerify.Tests     xUnit: analyzer rules, erasure, verifier proved/refuted per feature, samples
samples/Good, samples/Buggy
```

`dotnet build` builds everything; `dotnet test` runs the 61 tests (they need Z3 on `PATH`).

## Limitations (honest list)

**Solver**
- **Z3 runs as a process, not through the `Microsoft.Z3` NuGet package.** The package's managed `Microsoft.Z3.dll` is built for x64 only, and the package ships x64-only native libraries (checked for 4.11.2–4.12.2). It cannot load in an arm64 .NET process, such as on Apple Silicon. Speaking SMT-LIB2 to a `z3` executable works on every platform and keeps native code out of both the analyzer and MSBuild.

**Soundness gaps in the verifier** (each is a place where it may say "proved" too eagerly)
- Mutable fields and properties are modeled as functions of their object. Writes to them are not tracked (a CSV1900 warning is reported).
- Only arrays of integer-like elements are modeled precisely.
- A new array is known to differ only from the arrays visible in local variables at the point of creation.
- Without `--overflow`, integers are mathematical integers.
- Partial correctness on exceptions: a path that throws proves nothing and is not checked further. Null dereferences are not checked.
- Specification expressions are not checked for well-definedness. Indexing in a spec has no bounds obligation, and a `[Pure]` call's precondition is not checked in specs; its definition is only assumed when its precondition holds.
- Inside a quantifier, side facts (lengths are non-negative, `[Pure]` unfolding) are not added.
- Lemmas are checked for termination, but not for side effects. Keep them ghost.

**Unsupported constructs** (reported as CSV1900 warnings, never silently)
- `foreach`, `try/finally`, `goto` cycles, shifts and bitwise operators on integers, floating point, strings beyond `Length` and bounds, multi-dimensional arrays.
- Local functions and lambdas are not verified as separate units.
- Mutual recursion is not checked for termination.
- Calls through interfaces or virtual methods use the contract written on the declared member (an interface member has none, so its result is unknown).

**Precision limits**
- `[Pure]` definitions are unfolded one level per use. Deeper facts need a lemma, as in ATS.
- Verification explores paths depth-first (`MaxPaths` = 5000 per method), so many sequential branches can be slow.
- Every method is verified separately against its callees' contracts.

**Views versus ATS/SV** (Zhu & Xi, *Safe Programming with Pointers through Stateful Views*)
- `PointsTo<T>` tracks address and value, so `T @ l` plus more.
- There are no user-defined dataviews (`arrayView`), no `⊗`/`−◦` view algebra, no pointer arithmetic `L + I`, no type-changing `setVar`, and no uninitialized `top @ l`.
- A `[Linear]` struct with `[Trusted]` split/join lemmas is the intended route to dataviews, but none ship yet.
- The analyzer does not track linear fields inside a linear struct separately: the struct is one resource.

**Packaging**
- "Zero-size" types are empty structs. The CLR still gives them one byte, but they carry no data.
- The `CsVerify` package produced by `dotnet pack` is not published. The verifier is a `dotnet tool` (`PackAsTool`) that is not published either.

## References

- H. Xi, *Applied Type System* (extended abstract), TYPES 2003.
- H. Xi, *Applied Type System: An Approach to Practical Programming with Theorem-Proving*, arXiv:1703.08683.
- D. Zhu, H. Xi, *Safe Programming with Pointers through Stateful Views*, PADL 2005.
- H. Xi, *Imperative Programming with Dependent Types* (Xanadu), LICS 2000.
