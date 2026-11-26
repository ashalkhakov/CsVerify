# Running the verifier

Requirements: the .NET 10 SDK and Z3 on `PATH` (`brew install z3`, `apt install z3`, `winget install z3`), or set `CSVERIFY_Z3=/path/to/z3`.

The verifier is the `dotnet-csverify` tool (`dotnet tool install dotnet-csverify`, as a local or global tool), run as
`dotnet csverify`; in a checkout, `dotnet run --project src/CsVerify.Verifier --` is the same.

```bash
dotnet csverify -v samples/Good
```

```
  ok   Arrays.BinarySearch: 20/20 obligations proved, 0.3 s
  ...
  time: compile 0.8 s, analyze 1.6 s, collect 2.0 s, translate 4.0 s, type check 1.2 s, solve 106.1 s, ...
csverify: 13 of 13 methods verified, 72/72 obligations proved
```

With `-v`, each method's line says how long the solver took on it (all its rounds together), and the `time:` line how
long each phase of the run took: compiling, the program-wide analyses, translating to Boogie, Boogie's type check,
solving, and the checks made from the syntax. A method that takes long is one to split, or to give its callees
contracts.

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
| `--timeout <ms>` | Boogie's time limit for a procedure (default 10000; a procedure it can't decide is retried assertion by assertion, then whole with more time) |
| `--method-budget <ms>` | the most time one method's verification may take, all rounds included; past it, its remaining obligations are not proved (CSV1901), so the method is reported not verified (default: no limit) |
| `--cores <n>` | the solvers run side by side (Boogie's `/vcsCores`; default: one a core, and no more than one per 4 GB of memory: a solver can take a gigabyte or more on a hard query) |
| `--z3 <path>` | Z3 executable |
| `--cache <file>` | keep the methods proved in this file, and prove one again only when what its proof depends on has changed ([Faster runs](#faster-runs)) |
| `--boogie-out <file>` | write the Boogie program it verified ([the Boogie engine](boogie.md)) |
| `-d <SYMBOL>` / `-r <dll>` | extra preprocessor symbol / metadata reference |
| `--assembly-name <name>` | compile the program under this assembly name, so the internals `InternalsVisibleTo` grants it are visible (the MSBuild targets pass the project's; `csverify erase` takes it too) |
| `-a <dll>` / `--analyzer-config <file>` | run the source generators of this analyzer assembly on the program, with this `.editorconfig` or `.globalconfig` (the MSBuild targets pass the project's) |
| `--only <text>` | verify only the methods whose name (`Type.Method`, or a nested type's `Outer.Type.Method`) contains the text (repeatable); the others are still called by their contracts, and a `[Pure]` one by its body, but aren't verified; only what the selected methods reach is translated ([Faster runs](#faster-runs)) |
| `-v` | list every method with its proved/total obligations and its solving time, the library contracts (`[ContractsFor]` stubs, trusted) the proofs assumed, and the time of each phase |
| `--ef-static-model` | read an EF Core model from the sources only, without loading the program to ask EF for its own ([Entity Framework](entity-framework.md#the-model)) |
| `--native <file>` | a native library the program's packages bring (repeatable; the MSBuild targets pass each runtime's): what a database provider loads where EF's model is built, SQLite's `e_sqlite3`. Without them, the packages beside the references' are searched |
| `--checks <kinds>` | prove only these kinds of obligation: a comma-separated list of `null`, `linear`, `bounds`, `overflow`, `contracts` (or `all`). See [Check profiles](#check-profiles) |
| `--each` | verify each argument as a program of its own (a comma joins paths into one: `lemon/CsLemon,lemon/CsLemon.Runtime`), and combine the results, for programs that cannot be compiled together |
| `--library-report` | after the results, the [library report](#the-library-report) |

## Faster runs

**`--only` translates only what the selected methods reach**: the methods they call, and of those the contracts; what a
virtual call may run; and of each type they use its invariants, operators, conversions, constructors and the members C#
calls without naming them (`GetEnumerator`, `Dispose`, `Deconstruct`, `GetAwaiter`...). The rest of the program isn't
translated, so a run of a few methods costs the compilation and the analyses of the whole program, and those methods.
What isn't translated can only be assumed less, never more, so a method `--only` proves is proved. A fact a selected
method assumes of a helper it calls (what a query helper's result is, given its query) is proved in the same run: the
helper's body is translated and verified for it though it isn't selected, and is reported only as part of that, so a
method is proved alone as a run of every method proves it. The same holds of a project's run for the helpers of the
projects it references. Where what the
selected methods reach doesn't type check in Boogie on its own, the whole program is translated instead (with
`CSVERIFY_TRACE`, a line says so).

**`--cache <file>` proves a method again only when its proof would change.** Each method proved is kept by a key: a hash
of its Boogie procedure and of every declaration its proof reaches (the contracts of what it calls, the functions,
constants and variables it names, the axioms that name any of those, the types), of the options that change a proof
(`--timeout`, `--checks`, `--no-overflow`, `--nullable`), and of the builds of the verifier, Boogie and Z3. A method
whose key is in the cache is reported proved (`cached` in `-v`), and isn't given to the solver; one that failed is
always verified again. So a change to a method's body proves it again, and a change to its contract proves its callers
too. A run of every method keeps only theirs; a run with `--only` adds to what's there.

The MSBuild target keeps the cache in `obj/` (`csverify.cache`): set `CsVerifyCache=false` to prove everything every
time, or `CsVerifyCacheFile` to keep it elsewhere. In CI, restore it from the base branch (`actions/cache` with a key of
the branch and a fallback to the base's) and a pull request is checked in about the time its changed methods take.

## Check profiles

`--checks` proves only the kinds of obligation a program is ready for. An application might start with null safety and
its resources, a parser with its bounds and overflow:

```bash
dotnet csverify --checks null corpus
```

```
csverify: 21 of 21 methods verified, 1004/1004 obligations proved; checks: null, 1213 obligation(s) outside them assumed, 2 construct(s) not modeled, 0 method(s) not verified
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
analyzer (CSV0010–CSV0014), aliased by-reference arguments (CSV1020), and ill-formed stubs (CSV1021).

Within a profile, a construct the verifier does not model is a warning (CSV1901, "not modeled: treated as unknown")
instead of an error. Its value is unknown (not null, if its type is not nullable), and the method is verified around
it. What the construct does (a write, say) is not checked. The summary counts these constructs, and the library report
lists them. A method that isn't verified at all (CSV1902: its body isn't translated, or Boogie couldn't decide it) is a
warning too, so that a profile can gate a build on what it checks; the summary counts these methods ("method(s) not
verified"), and they aren't among those verified. Without `--checks`, everything is proved, and an unsupported
construct leaves its method unverified, an error.

## The library report

`--library-report` ranks what stands between a program and its proof, so the contracts and verifier features worth
adding first are the ones that unblock the most:

```bash
dotnet csverify --library-report corpus
```

```
library report
  21 methods: 7 verified, 13 with failed obligations, 1 not verified (CSV1901, CSV1902)
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
(CSV1901) and the methods not translated or not decided (CSV1902), each leaving its method unverified, and the unknown values
(CSV1900), each grouped by message.
`corpus/report.sh` runs it on the [corpus](../corpus/README.md).

**From MSBuild:** the `CsVerify` package brings the targets (`build/CsVerify.targets`), so a project referencing it is verified when built with:

```bash
dotnet build -p:CsVerifyEnabled=true
```

The verifier runs after `Build` on the project's `Compile` items, with the project's nullable context. The SDK's files under `obj/` (global usings, assembly attributes) are among them, and the project's source generators (`[GeneratedRegex]`, `[LoggerMessage]`) run in the verifier. Generated code (a `*.g.cs` file, or one marked `<auto-generated>`) is compiled with the program but not verified. Its `file(line,col): error CSVnnnn` output appears as build errors, in the IDE and in CI. The program is compiled under the project's assembly name, so the internals another project grants it with `InternalsVisibleTo` are visible, and with the project's references: its packages', its projects' and the shared frameworks' other than `Microsoft.NETCore.App`, which the verifier has a copy of (ASP.NET Core's, for one). The projects it references that use CsVerify too (and theirs, those that set `CsVerifyExclude` among them) are passed as well, each as its build describes it (`--project-reference`: its sources, references, source generators, assembly name and nullable context, what the compiler is given). Each is compiled as a project of its own, and the program's compilation references it in place of its assembly (Roslyn's `CompilationReference`, as the IDE's workspace does), so its types, its contracts (a contract class beside its interface) and its [Entity Framework](entity-framework.md) model are the program's. Every compilation of the program has the same references, one file per assembly as the build resolves them: the program's, or the highest version a project references (a project's older version of a package beside the program's, through a dependency of its own). A project described to the program has its generated sources whether or not it was built in the same run (`dotnet build --no-dependencies`): its assembly attributes, the `InternalsVisibleTo` of its project file among them. Its code is called by its contracts, not verified: each project verifies its own. A referenced project that doesn't use CsVerify is a library, read from its assembly. [`samples/Layered`](../samples/Layered/README.md) is such a solution. Test projects (`IsTestProject`) and projects that set `CsVerifyExclude` are left out. Pass extra flags with `-p:CsVerifyArgs=...`. The targets run the `dotnet-csverify` tool, or the `csverify.dll` next to them (in a checkout, `src/CsVerify.Verifier/bin/<configuration>/net10.0/build/CsVerify.Verifier.targets`, which the projects under `samples/` import); `CsVerifyCommand` overrides both.

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
| CSV0014 | analyzer | a contract (`Spec.Requires`, `Ensures`, `Decreases`, `Modifies`, `Reads`) names a local of the body |
| CSV0020 | analyzer | a disposable this method owns is not disposed on every path (or is overwritten while it holds one) |
| CSV0021 | analyzer | a disposable used, or disposed again, after it may have been disposed |
| CSV0022 | analyzer | a class owns a disposable field but is not IDisposable, or its Dispose never disposes the field |
| CSV0030 | analyzer | a `[Sensitive]` value, or an object whose text shows one, reaches a log, or an exception's message ([Secrets and logs](taint.md)) |
| CSV0031 | analyzer | `Sealed.Unseal` outside the body of an `[Unseals]` method |
| CSV0032 | analyzer | an `[Unseals]` method without a precondition (its access check) |
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
| CSV1023 | verifier | a use of state guarded by a lock that might not be held, so it could race: `[GuardedBy]`, or a field written under one lock elsewhere; or a try-lock flag used out of its form |
| CSV1024 | verifier | a `[LockInvariant]` might not hold where its lock is released, or at a call that may enter it again |
| CSV1025 | verifier | could deadlock: a lock taken, a call, or a wait while a lock is held might take a lock that isn't of a higher level (`[LockLevel]`), or wait for what only another thread can end; a lock taken out of its form; a `Monitor.Wait` holding another lock; blocking on async code that resumes on its context; one object leveled twice |
| CSV1026 | verifier | a task an async method started in a local might not be awaited on every path, so a failure in it would be lost; or its `Result` is read before it is awaited |
| CSV1901 | verifier | error: a construct the verifier cannot model soundly; the method is not verified |
| CSV1902 | verifier | error (a warning within a [check profile](#check-profiles)): the method is not verified: its body isn't translated to Boogie (the message says what), or Boogie couldn't decide it in time |
| CSV1027 | verifier | a field or array cell used by code that runs alongside other code, with no lock or permission for it |
| CSV1028 | verifier | a method of the program that runs concurrently (started and not awaited in the same method, handed to a thread, or called by concurrent code), or a delegate type called by concurrent code, but isn't marked `[RunsConcurrently]` |
| CSV1029 | verifier | a delegate handed to a library that may call it with any arguments (not just a list's elements, `Parallel.For`'s indices, or what a stub says), but that isn't known to accept them all (`Spec.Total`); a lambda's precondition that reads state without a `Spec.Reads` frame, or outside it; or a method group made a delegate whose type has a contract |
| CSV1031 | verifier | a database query keeping rows by their place (`First`, `Take`, `Skip`...) in an order the database doesn't fix: not ordered by a key or unique index, and not shown to match one row at most ([Entity Framework Core](entity-framework.md)) |
| CSV1032 | verifier | a query's lambda EF can't translate to SQL: a method of the program, or a property computed in C# or `[NotMapped]`, applied to the row |
| CSV1033 | verifier | the change tracker misused: an entity attached or updated where the context may track another with its key, `Update` of an entity whose navigations hold something, a context used after a failed save or a rollback, or saving an entity a bulk update made stale |
| CSV1034 | verifier | a concurrency token changed between reading an entity and attaching it (or marking it modified), or a row version written by the program |
| CSV1035 | verifier | a transaction begun where one may be open, a commit with changes not saved, or a second save on a context outside a transaction |
| CSV1036 | verifier | two operations at once on a `DbContext`: an asynchronous one not awaited where it starts, or a context used by code that runs alongside (`Task.Run`, threads, `Parallel`) |
| CSV1037 | verifier | a sequence that writes as it is enumerated, handed on instead of enumerated where it is made: a query of a lambda or a method that writes, an iterator that writes, an object of the program's whose enumerator writes (reported in every check profile: a method reads a sequence it is handed as a value) |
| CSV1030 | verifier | an `[Atomic]` field's write that might not be a step from what it replaces, a step that might not be transitive, a plain use of one that isn't `volatile`, or one that can't be atomic (its type, `readonly`, `[GuardedBy]`, a struct, an `[Owned]` class, an ill-formed step, a function or invariant reading it) |
| CSV1900 | verifier | warning: a value the verifier treats as unknown (sound), or a misplaced spec |
| CSV1998 | verifier | Z3 stopped answering, past its own timeout, and was stopped: the rest of the method is not verified |
| CSV1999 | verifier | internal or solver error |
| CSV2001 | erase | the erased program does not compile: run-time code depends on ghost code |
