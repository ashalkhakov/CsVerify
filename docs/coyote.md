# CsVerify and Coyote

[Coyote](https://github.com/microsoft/coyote) tests concurrent .NET code: it rewrites the assemblies, then runs a test
many times under its own scheduler, choosing a different interleaving each time, and reports any schedule that fails
an assertion or deadlocks, with a trace that replays it. CsVerify proves the same kind of property for every
interleaving. This repository uses Coyote to check that what CsVerify proves of concurrent code holds when that code
runs.

## The tests

`tests/CsVerify.CoyoteTests` runs the concurrent samples under Coyote, with interleaving at every memory access,
volatile and atomic operation, and lock (its race-checking options). The samples are compiled into the test assembly
in a [checked build](erasure.md#the-checked-build): their specifications that can run are run-time checks, and a
check that fails in some schedule is a Coyote assertion that fails there. So each schedule holds the samples to their
own preconditions, postconditions, lock invariants, `[Atomic]` steps and lock levels, besides what each test asserts.

- **GoodSampleTests** check, over every schedule tried, what CsVerify proves of `samples/Good`: lock invariants and
  postconditions, mutual exclusion under the try-lock, that atomic fields only take their steps, that ordered locks
  don't deadlock, and that no update is lost. A failure here would mean the verifier's model of threads, locks or atomic
  fields is unsound.
- **BuggySampleTests** make the planted bugs of `samples/Buggy` happen, and pass when Coyote finds them: so the
  harnesses can see a broken schedule, and GoodSampleTests passing means something.
- **LivenessTests** check that every wait ends (below).

Each test states what else it checks, at the end of a schedule (that no update was lost, say), as Coyote assertions.

## Liveness

CsVerify proves that no threads wait on each other's locks in a cycle, not that a thread waiting on `Monitor.Wait` or
a semaphore is ever woken. The checked build reports each wait (`CsVerify.Checked.Waiting` and `Woken`), and the
tests feed them to a Coyote liveness monitor that is hot while a wait hasn't ended: a schedule that ends with a
waiter still waiting is a liveness bug. A test that waits for the waiter gets a deadlock report from Coyote on its
own; the monitor finds the waiter no one waits for. `Waits/Waits.cs` (written for these tests) has a mailbox whose
waits all end, and a latch with a lost wakeup that Coyote finds through the monitor and misses without it.

```sh
dotnet tool restore                               # the Coyote CLI, pinned in .config/dotnet-tools.json
dotnet build tests/CsVerify.CoyoteTests -c Release   # the checked build of the samples, compiled in; then rewritten
dotnet test tests/CsVerify.CoyoteTests -c Release --no-build
```

`CSVERIFY_COYOTE_ITERATIONS` sets the schedules per test (1000 by default; CI runs 10,000, in under a minute).

With Coyote 1.7.11 on .NET 10:
- Coyote runs a monitor atomically, and this test assembly is rewritten, so the monitor has no code of its own: the
  count of waits is kept outside it, and it only changes state.
- `coyote test` runs on an older runtime and can't load .NET 10 assemblies, so the tests drive Coyote's
  `TestingEngine` themselves; `coyote rewrite` works.
- `Task.WhenAll` isn't controlled: the tests await tasks one after another, and the one sample that calls it runs with
  uncontrolled operations allowed.

## What each finds

Of the 20 concurrency bugs planted in `samples/Buggy`, which CsVerify reports, a Coyote test was written for each:

| | Bugs |
|---|---|
| **Found** (13) | the deadlocks: two transfers locking in opposite orders, a callback under a lock waiting on code that needs it, a wait on a task under a lock the task needs, `Monitor.Wait` holding another lock, a semaphore taken twice, a delegate awaited under a semaphore; a lower lock taken under a higher one; a lost update on an atomic field; two reads of it assumed equal; a count written where a try-lock was refused; `Interlocked.Increment` wrapping; invariants broken with the lock or flag free |
| **Only on an exception** (2) | a try-lock and a semaphore given back without a `finally`: nothing between taking and giving back throws in these programs |
| **Needs code that isn't there** (1) | a task awaited on one path only, whose work never fails |
| **Needs a context Coyote doesn't model** (2) | `.Result` read before `await`, in two places: it blocks for good only on a single-threaded context, such as a UI thread's |
| **No effect to observe** (2) | a read and a write of a guarded field without its lock: a race, but no value these programs can see differs |

The lost update and the two reads were found only with memory-access race checking on; without it, Coyote switches
threads only at its own operations (tasks, locks, `Interlocked`), not between a read and a write.

The checked build finds some of them where the specification breaks, before the symptom: the lower lock under a higher
one by its lock level, though no other code takes them the other way round to deadlock; the transfers that lock in
opposite orders by the second one's level, in schedules that don't deadlock too; the wrapping increment by the
field's step; the broken invariant when the lock is given back; the two reads by the method's own `Spec.Assert`.

The two tools answer different questions:

| | CsVerify | Coyote |
|---|---|---|
| Kind | a proof over every interleaving | a test over many interleavings |
| A report | may be a bug no run has shown yet (a lock order, a missing `finally`, a race with no visible effect) | happened, with a trace that replays it |
| A pass | holds for every run, within what is modeled | holds for the schedules tried |
| Needs | specifications (`[GuardedBy]`, `[LockLevel]`, `[Atomic]`, contracts) | a test that builds the situation and states what goes wrong, and mocks for I/O |
| Library code | through its contracts | runs it |
| Liveness (a waiter is woken) | not proved | checked by a liveness monitor, fed by the checked build's waits |
