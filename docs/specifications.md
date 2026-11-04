# Writing specifications

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
| nested views: a node's view holding the rest of the list's | `[Owns] Node? Next` in an `[Owned]` class; `Own.Take(ref n.Next, out var v)` unfolds, `Own.Give(ref n.Next, x, v)` folds |
| Dafny's `multiset(a[..n])`, ACSL's `MultisetReorder` | `Spec.Multiset(a, n)`, a ghost `Bag` (`Count`, `Add`, `Union`, `==`); a permutation is `Spec.Multiset(a, n) == Spec.Old(Spec.Multiset(a, n))` |
| Dafny's `ghost var Repr: set<object>`, `Valid()`, `modifies`, `reads`, `fresh` | `Ghost<ObjSet> Repr` field, `[GhostFunction] bool Valid()`, `Spec.Modifies(Repr.Value)`, `Spec.Reads(Repr.Value.Add(this))`, `Spec.Fresh(Repr.Value)` |
| a view of an object's fields, `(pf \| p)` | `[Owned]` class; `Own.New(new C(...), out Own<C> view)`; pass `(C obj, ref Own<C> view)` with `Spec.Requires(view.Obj.Value == obj)` |
| several results, `[r1, r2: int] (...)` (Dafny `returns (k, m)`) | a C# tuple `(int k, int m)`; `Spec.Ensures<(int k, int m)>(r => ... r.k ... r.m ...)`; callers read `t.k` or deconstruct with `var (k, m) = ...` |
| `$UNSAFE` | `[Trusted]`: the body is not verified, its contract is taken as an axiom, linearity is not checked |
| proof erasure | `[Conditional]` erasure: in a normal build no spec, lemma call or argument remains |

## Specification rules

- `Requires`, `Ensures` and `Decreases` must be **top-level statements of the method body** (anywhere among them, conventionally first). An `out` parameter must be assigned before an `Ensures` mentions it, because C#'s definite assignment applies to the erased call too.
- `Invariant` and a loop `Decreases` must be the **leading statements of the loop body**. They hold each time the loop condition is tested, Xanadu-style, not only inside the body. For a `goto` loop they are the statements right after the label the `goto` jumps back to.
- `Spec.Index(x)` is the index of `x`, the iteration variable of a `foreach` over an array. In the loop's invariants it is the number of elements gone through.
- `Spec.Ensures<R>(r => …)` binds `r` to the return value. Lambdas cannot capture `ref`/`in` parameters, so for those use `Spec.Ensures(bool)` with `Spec.Result<R>()` and `Spec.Old(x)`.
- `Spec.Forall(lo, hi, i => P)` / `Spec.Exists(...)` are bounded integer quantifiers.
- Specification expressions should be side-effect free. Calls in them must be `[Pure]`.

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
