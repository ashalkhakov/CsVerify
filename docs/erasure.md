# Proof erasure

In ATS, proofs and static indices exist only at compile time and are erased before the program runs. CsVerify gets most of that from C# itself:
- `[Conditional("CSVERIFY_SPEC")]` deletes specification statements and lemma calls, arguments included.
- Views are empty structs.
- `Split`/`Join` are empty methods the JIT inlines.

Ghost parameters and view tokens are still in the signatures, though. The erasure pass removes all of it, and turns "proofs don't affect the program" from a promise into a check.

```bash
dotnet build -p:CsVerifyErase=true          # build the erased program
dotnet csverify erase --out erased/ src/    # or write it out to look at
```

**What it removes:**
- Specification statements.
- Lemmas, `[GhostFunction]`s and `[Model]` functions, with their calls.
- Classes of contracts: `[ContractsFor]` stubs and `[ContractClassFor]` classes.
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

**The runtime.** The Spec library goes through the same pass and becomes a small runtime that is compiled into the program in place of the CsVerify assembly. It keeps `Ptr<T>`, `Mem.Read(p)`, `Mem.AllocArray(n, fill)` and the like, and has no `Spec`, `Ghost`, `Seq`, `Map` or view types, nor the BCL contracts, at all.

**The check.** If the erased program does not compile, run-time code still depends on a proof, for example a view hidden in a tuple or a `Ghost` boxed into an `object`. That is error CSV2001, reported at the original line.

**How it builds.** Like Tarp's instrumentation:
- the rewrite happens before the compile steps (before `BeforeCompile`), into `obj/csverify-erased/<configuration>/<framework>/`: out of the default `Compile` items, and outside the intermediate directory, so that a coverage tool hooked in after it ([Tarp](ci.md#with-tarp)) instruments the erased program, the one that runs;
- deletions keep their line breaks, and each file starts with a `#line` naming the original, so errors, stack traces and the debugger stay on your sources;
- switching between erased and normal builds recompiles.

**Tested:** the erased samples carry no ghost types or ghost references, and running them returns exactly the values their verified postconditions state.

**Across projects.** A project referencing an erased project calls its methods without their ghost arguments: erasure drops an argument of proof type from a call that no longer binds (a proof value can only be a proof parameter's argument), and the check decides.

## The checked build

A checked build erases the proofs too, but keeps the specifications that can run, as run-time checks: a way to test
the program against them where they weren't proved (`[Trusted]` code, a method the verifier refused, code beyond what
it models), or to hold a run to what was proved, as [the Coyote tests](coyote.md) do.

```bash
dotnet build -p:CsVerifyChecked=true                 # build the checked program
dotnet csverify erase --checked --out checked/ src/  # or write it out to look at
```

**What is checked**, by calls of the runtime's `CsVerify.Checked`:
- `Spec.Requires`, `Spec.Assert` and `Spec.Invariant`, where they stand;
- `Spec.Ensures`, at each `return` and at the end of the body if it is reached, with each `Spec.Old(e)` taken where
  the postcondition is written, on entry. A postcondition is of a normal return: an exception isn't checked;
- a lock's `[LockInvariant]`s when it is taken and when it is given back: in a `lock` statement, on entering and in a
  `finally`; after `Monitor.Enter`, `SemaphoreSlim.Wait` and `await WaitAsync`; before `Monitor.Exit` and `Release`;
- each write of an `[Atomic]` field with a `Step`, and each `Interlocked` change of it (`CompareExchange` when it
  swaps, `Exchange`, `Increment`, `Decrement`, `Add`), as that step from what it overwrote;
- each `lock` statement on a `[LockLevel]` field: every lock the thread holds is lower (or of the same level and a
  lower `OrderedBy` value or index). Locks taken by other means aren't followed.

**What isn't:** a condition that can't run (ghost state: `Seq`, `ObjSet`, views, `[GhostFunction]`s, `Spec.Result`,
`Spec.Old` of a lambda's variable); and one that reads what other threads may change while it is evaluated, so the
value it sees isn't the one the proof speaks of: an `[Atomic]` or volatile field, or a `[GuardedBy]` field outside a
`lock` statement on its lock. Lemmas, frames (`Modifies`, `Reads`) and termination measures go, as in any erased build.

**A failure** throws `CsVerify.SpecificationFailedException`, with the condition and its file and line, or does what
`CsVerify.Checked.Failed` is set to (the Coyote tests make it a Coyote assertion). `CsVerify.Checked.Waiting` and
`Woken` are called around each `Monitor.Wait`, `SemaphoreSlim.Wait` and `WaitAsync`, for a test to follow the waits
(the Coyote tests' liveness monitor).

**Tested:** the checked samples compute the same values as the erased ones, breaking none of their checks, and keep
their line numbers; a program that breaks each kind of check is stopped where it does.

**Limitations:**
- Erasure works per project. The runtime is compiled into each erased project, so `Ptr<T>` from two erased projects are different types.
- A proof type inside a generic or a tuple is not erased; the check reports it.
