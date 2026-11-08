# CsVerify and Coyote

[Coyote](https://github.com/microsoft/coyote) tests concurrent .NET code: it rewrites the assemblies, then runs a test
many times under its own scheduler, choosing a different interleaving each time, and reports any schedule that fails
an assertion or deadlocks, with a trace that replays it. CsVerify proves the same kind of property for every
interleaving. This repository uses Coyote to check that what CsVerify proves of concurrent code holds when that code
runs.

## The tests

`tests/CsVerify.CoyoteTests` runs the concurrent samples under Coyote, with interleaving at every memory access,
volatile and atomic operation, and lock (its race-checking options):

- **GoodSampleTests** check, over every schedule tried, what CsVerify proves of `samples/Good`: lock invariants and
  postconditions, mutual exclusion under the try-lock, that atomic fields only take their steps, that ordered locks
  don't deadlock, and that no update is lost. A failure here would mean the verifier's model of threads, locks or atomic
  fields is unsound.
- **BuggySampleTests** make the planted bugs of `samples/Buggy` happen, and pass when Coyote finds them: so the
  harnesses can see a broken schedule, and GoodSampleTests passing means something.

Specifications are compiled away (`[Conditional]`), so each test states the property it checks as Coyote assertions.

```sh
dotnet tool restore                               # the Coyote CLI, pinned in .config/dotnet-tools.json
dotnet build tests/CsVerify.CoyoteTests -c Release   # rewrites the test assembly and the samples after the build
dotnet test tests/CsVerify.CoyoteTests -c Release --no-build
```

`CSVERIFY_COYOTE_ITERATIONS` sets the schedules per test (1000 by default; CI runs 10,000, in under a minute).

With Coyote 1.7.11 on .NET 10:
- `coyote test` runs on an older runtime and can't load .NET 10 assemblies, so the tests drive Coyote's
  `TestingEngine` themselves; `coyote rewrite` works.
- `Task.WhenAll` isn't controlled: the tests await tasks one after another, and the one sample that calls it runs with
  uncontrolled operations allowed.

## What each finds

Of the 20 concurrency bugs planted in `samples/Buggy`, which CsVerify reports, a Coyote test was written for each:

| | Bugs |
|---|---|
| **Found** (12) | the deadlocks: two transfers locking in opposite orders, a callback under a lock waiting on code that needs it, a wait on a task under a lock the task needs, `Monitor.Wait` holding another lock, a semaphore taken twice, a delegate awaited under a semaphore; a lost update on an atomic field; two reads of it assumed equal; a count written where a try-lock was refused; `Interlocked.Increment` wrapping; invariants broken with the lock or flag free |
| **Only on an exception** (2) | a try-lock and a semaphore given back without a `finally`: nothing between taking and giving back throws in these programs |
| **Needs code that isn't there** (2) | a lower lock taken under a higher one, with nothing taking them the other way round; a task awaited on one path only, whose work never fails |
| **Needs a context Coyote doesn't model** (2) | `.Result` read before `await`, in two places: it blocks for good only on a single-threaded context, such as a UI thread's |
| **No effect to observe** (2) | a read and a write of a guarded field without its lock: a race, but no value these programs can see differs |

The lost update and the two reads were found only with memory-access race checking on; without it, Coyote switches
threads only at its own operations (tasks, locks, `Interlocked`), not between a read and a write.

The two tools answer different questions:

| | CsVerify | Coyote |
|---|---|---|
| Kind | a proof over every interleaving | a test over many interleavings |
| A report | may be a bug no run has shown yet (a lock order, a missing `finally`, a race with no visible effect) | happened, with a trace that replays it |
| A pass | holds for every run, within what is modeled | holds for the schedules tried |
| Needs | specifications (`[GuardedBy]`, `[LockLevel]`, `[Atomic]`, contracts) | a test that builds the situation and states what goes wrong, and mocks for I/O |
| Library code | through its contracts | runs it |
| Liveness (a waiter is woken) | not proved | checked by its liveness monitors |
