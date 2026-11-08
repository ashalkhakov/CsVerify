# Running the verifier

Requirements: the .NET 10 SDK and Z3 on `PATH` (`brew install z3`, `apt install z3`, `winget install z3`), or set `CSVERIFY_Z3=/path/to/z3`.

The verifier is the `dotnet-csverify` tool (`dotnet tool install dotnet-csverify`, as a local or global tool), run as
`dotnet csverify`; in a checkout, `dotnet run --project src/CsVerify.Verifier --` is the same.

```bash
dotnet csverify -v samples/Good
```

```
  ok   Arrays.BinarySearch: 20/20 obligations proved
  ...
csverify: 13 of 13 methods verified, 72/72 obligations proved
```

```bash
dotnet csverify samples/Buggy
```

```
samples/Buggy/Bugs.cs(15,24): error CSV1003: index in 'a[i]' might be out of range
samples/Buggy/Bugs.cs(34,60): error CSV1001: precondition 'y != 0' of 'Div' might not hold
samples/Buggy/Bugs.cs(71,21): error CSV1001: precondition 'view.Addr == p.Addr' of 'Read' might not hold
...
```

When proofs used library contracts, the summary line says how many (`csverify: 6 of 6 methods verified, 151/151 obligations proved, 13 library contract(s) assumed`). They are assumptions, not proofs (see [Contracts for code without sources](library-contracts.md)).

Arguments are `.cs` files, directories (searched recursively, skipping `bin/` and `obj/`), `.csproj` files (meaning their directory), or `@file.rsp`. The exit code is 0 when everything is proved, 1 on verification errors, 2 on usage errors.

| option | meaning |
|---|---|
| `--nullable <ctx>` | the nullable context: `enable` (default), `disable`, `annotations`, `warnings`; only non-nullable reference types are known not to be null |
| `--no-overflow` | make every integer mathematical, which is unsound where code can overflow (by default integers are bounded: see [Bounded integers](semantics.md#bounded-integers)) |
| `--timeout <ms>` | per-query Z3 timeout (default 10000) |
| `--method-budget <ms>` | the most time one method's verification may take, all rounds included; past it, its remaining obligations are not proved (CSV1901), so the method is reported not verified (default: no limit) |
| `--z3 <path>` | Z3 executable |
| `-d <SYMBOL>` / `-r <dll>` | extra preprocessor symbol / metadata reference |
| `--smt-log <file>` | dump the whole SMT-LIB2 conversation |
| `--only <text>` | verify only the methods whose name (`Type.Method`) contains the text (repeatable) |
| `-v` | list every method with its proved/total obligations, and the library contracts (`[ContractsFor]` stubs, trusted) the proofs assumed |
| `--checks <kinds>` | prove only these kinds of obligation: a comma-separated list of `null`, `linear`, `bounds`, `overflow`, `contracts` (or `all`). See [Check profiles](#check-profiles) |
| `--each` | verify each argument as a program of its own (a comma joins paths into one: `lemon/CsLemon,lemon/CsLemon.Runtime`), and combine the results, for programs that cannot be compiled together |
| `--library-report` | after the results, the [library report](#the-library-report) |

## Check profiles

`--checks` proves only the kinds of obligation a program is ready for. An application might start with null safety and
its resources, a parser with its bounds and overflow:

```bash
dotnet csverify --checks null corpus
```

```
csverify: 21 of 21 methods verified, 1004/1004 obligations proved; checks: null, 1213 obligation(s) outside them assumed, 2 construct(s) not modeled
```

| kind | what it proves |
|---|---|
| `null` | dereferences (CSV1013), and non-nullable types' promises (CSV1014) |
| `linear` | the linearity analyzer's rules (CSV0001–CSV0007), owned objects' views (CSV1016), and disposal (CSV0020–CSV0022) |
| `bounds` | array and span indices, and array sizes (CSV1003) |
| `overflow` | arithmetic and conversions (CSV1010), and division by zero (CSV1009) |
| `contracts` | the rest of the specifications: preconditions (library ones too, such as a format's arguments), postconditions, assertions, invariants, measures, frames, well-definedness, and switch expressions that cover what they get (CSV1022) |

Obligations of the other kinds are assumed, so a result holds only where they do. The summary line counts them.
Some diagnostics are reported whatever the profile, because the verifier's own soundness depends on them: the ghost
analyzer (CSV0010–CSV0013), aliased by-reference arguments (CSV1020), and ill-formed stubs (CSV1021).

Within a profile, a construct the verifier does not model is a warning (CSV1901, "not modeled: treated as unknown")
instead of an error. Its value is unknown (not null, if its type is not nullable), and the method is verified around
it. What the construct does (a write, say) is not checked. The summary counts these constructs, and the library report
lists them. Without `--checks`, everything is proved, and an unsupported construct leaves its method unverified.

## The library report

`--library-report` ranks what stands between a program and its proof, so the contracts and verifier features worth
adding first are the ones that unblock the most:

```bash
dotnet csverify --library-report corpus
```

```
library report
  21 methods: 7 verified, 13 with failed obligations, 1 not verified (unsupported constructs)
  95 failed obligations

library members without contracts, by the failures they cause
  failures  calls  member
         1      1  System.CharEnumerator.Current
         0      3  System.Span<T>.Slice(int, int)
  ...
methods of the program without postconditions, by the failures their calls cause
  failures  method
         5  Corpus.Json.Jsmn.AllocToken(Corpus.Json.JsmnParser, Corpus.Json.JsmnToken[], int)
  ...
failed obligations by cause (one may have several)
         1  a library member without a contract
        15  a method without postconditions
        76  a loop without invariants
         8  none of these (the code's own values)
  ...
```

A failed obligation is charged to where the unknown values its condition mentions come from:
- **a library member without a contract:** its result, its `out` values, or the memory and fields it may have changed;
- **a method of the program without postconditions:** what its callers know of its result is only its type;
- **a loop without invariants:** what the loop changes is unknown at its head.

A failure may have several causes, or none: the code's own arithmetic and checks over values it knows. The charge is
a guide, not a proof: a fact can also go missing through a path condition (an `if` on a library result) that the
failed condition does not mention. Below that come the failures by kind (diagnostic id), the unsupported constructs
(CSV1901, each leaving its method unverified), and the unknown values (CSV1900), each grouped by message.
`corpus/report.sh` runs it on the [corpus](../corpus/README.md).

**From MSBuild:** the `CsVerify` package brings the targets (`build/CsVerify.targets`), so a project referencing it is verified when built with:

```bash
dotnet build -p:CsVerifyEnabled=true
```

The verifier runs after `Build` on the project's `Compile` items, with the project's nullable context. Its `file(line,col): error CSVnnnn` output appears as build errors, in the IDE and in CI. Test projects (`IsTestProject`) and projects that set `CsVerifyExclude` are left out. Pass extra flags with `-p:CsVerifyArgs=...`. The targets run the `dotnet-csverify` tool, or the `csverify.dll` next to them (in a checkout, `src/CsVerify.Verifier/bin/<configuration>/net10.0/build/CsVerify.Verifier.targets`, which the projects under `samples/` import); `CsVerifyCommand` overrides both.

## Diagnostics

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
| CSV0020 | analyzer | a disposable this method owns is not disposed on every path (or is overwritten while it holds one) |
| CSV0021 | analyzer | a disposable used, or disposed again, after it may have been disposed |
| CSV0022 | analyzer | a class owns a disposable field but is not IDisposable, or its Dispose never disposes the field |
| CSV1001 | verifier | callee precondition might not hold |
| CSV1002 | verifier | postcondition might not hold on a return path |
| CSV1003 | verifier | index might be out of range / negative array size |
| CSV1004 | verifier | `Spec.Assert` might not hold |
| CSV1005 / CSV1006 | verifier | loop invariant might not hold on entry / might not be maintained |
| CSV1007 | verifier | loop measure might not decrease or might be negative |
| CSV1008 | verifier | recursion measure (own or of a mutually recursive callee) might not decrease or might be negative |
| CSV1009 | verifier | possible division by zero |
| CSV1010 | verifier | possible overflow: run-time arithmetic or a narrowing conversion that might leave its type (or, in a proof, a checked one that might throw) |
| CSV1012 | verifier | a specification might not be well-defined: index out of range, null dereference, `[Pure]` call outside its precondition, or division by zero inside a spec |
| CSV1013 | verifier | a dereference (`a.Length`, `a[i]`, `x.M()`) of a reference that might be null |
| CSV1014 | verifier | a possibly-null value where a non-nullable type promises otherwise: an argument, a return value, an `out`/`ref` parameter on return |
| CSV1015 | verifier | an object invariant might not hold for a new object |
| CSV1016 | verifier | an [Owned] object written without its view in hand, or a view made for an object that is not new |
| CSV1019 | verifier | a predicate's body might not hold where it is folded |
| CSV1018 | verifier | an override breaks behavioural subtyping: it requires more than the member it overrides, or its `Spec.Modifies` is wider |
| CSV1020 | verifier | two arguments passed by reference (one of them `ref`/`out`) might be the same array cell or variable |
| CSV1017 | verifier | a dynamic frame broken: a write outside `Spec.Modifies`, a read outside `Spec.Reads`, a callee with no or a wider frame, or `Spec.Modifies`/`Reads` on an `[Owned]` class |
| CSV1011 | verifier | a lemma or `[Pure]`/`[GhostFunction]` might not terminate: recursion or loop without `Spec.Decreases`, or a `throw` |
| CSV1021 | verifier | an ill-formed `[ContractsFor]` stub or `[Model]` function: a stub method that matches no member of its type, a stub without the type's type parameters, a model function of the wrong shape |
| CSV1022 | verifier | a switch expression might not cover every value it gets: it would throw `SwitchExpressionException` |
| CSV1023 | verifier | a use of state guarded by a lock that might not be held, so it could race: `[GuardedBy]`, or a field written under one lock elsewhere |
| CSV1024 | verifier | a `[LockInvariant]` might not hold where its lock is released, or at a call that may enter it again |
| CSV1025 | verifier | could deadlock: a lock taken, a call, or a wait while a lock is held might take a lock that isn't of a higher level (`[LockLevel]`), or wait for what only another thread can end; a lock taken out of its form; a `Monitor.Wait` holding another lock; blocking on async code that resumes on its context; one object leveled twice |
| CSV1026 | verifier | a task an async method started in a local might not be awaited on every path, so a failure in it would be lost; or its `Result` is read before it is awaited |
| CSV1901 | verifier | error: a construct the verifier cannot model soundly; the method is not verified |
| CSV1027 | verifier | a field or array cell used by code that runs alongside other code, with no lock or permission for it |
| CSV1028 | verifier | a method of the program that runs concurrently (started and not awaited in the same method, handed to a thread, or called by concurrent code), or a delegate type called by concurrent code, but isn't marked `[RunsConcurrently]` |
| CSV1029 | verifier | a delegate handed to a library that may call it with any arguments (not just a list's elements, `Parallel.For`'s indices, or what a stub says), but that isn't known to accept them all (`Spec.Total`); a lambda's precondition that reads state without a `Spec.Reads` frame, or outside it; or a method group made a delegate whose type has a contract |
| CSV1030 | verifier | an `[Atomic]` field's write that might not be a step from what it replaces, a step that might not be transitive, a plain use of one that isn't `volatile`, or one that can't be atomic (its type, `readonly`, `[GuardedBy]`, a struct, an `[Owned]` class, an ill-formed step, a function or invariant reading it) |
| CSV1900 | verifier | warning: a value the verifier treats as unknown (sound), or a misplaced spec |
| CSV1998 | verifier | Z3 stopped answering, past its own timeout, and was stopped: the rest of the method is not verified |
| CSV1999 | verifier | internal or solver error |
| CSV2001 | erase | the erased program does not compile: run-time code depends on ghost code |
