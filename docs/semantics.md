# Integers, exceptions, async, floating point and null

## Bounded integers

Run-time integers are C#'s, and specifications are mathematics, as with ACSL's `int` and `integer`:
- **Default context.** C# silently wraps, which is almost always a bug, so overflow is a proof obligation (CSV1010) for `+ - *`, `++`, compound assignment, unary minus and explicit narrowing casts.
- **`unchecked(...)` or an `unchecked { }` block.** The wrap-around is modelled exactly, as modular arithmetic: `unchecked(int.MaxValue + 1) == int.MinValue` is provable. Use it for code that means it, such as hashing.
- **`checked(...)`, `checked { }`, or a project with `CheckForOverflowUnderflow`.** Overflow throws, so ordinary code goes on only if it didn't, and may assume so. That's partial correctness: `checked(sum + a[i])` is the honest "throws if the sum leaves `int`". `Math.Abs(MinValue)` and `MinValue / -1` throw in .NET even when unchecked, and are treated the same way.
- **Proofs.** A `[Pure]` function or lemma may not throw, so there `checked` is no excuse and the bound must be proved.
- **Specifications and ghost code are mathematical:** `Spec.*` arguments, `Ghost.Of(...)` arguments, and lemma and `[GhostFunction]` bodies. So the usual pattern is ACSL's:
  - definitions used only in specifications are `[GhostFunction]` (`Fact`, `Sum`, `Accumulate`, `Length`, `Bh`), mathematical and unbounded;
  - run-time code computes with checked arithmetic or bounds preconditions (ACSL's `AccumulateBounds`), proved to agree with them (`Count` vs `Length`, `Evaluate` vs `Eval`, `BlackHeight` vs `Bh`).
- **Values from memory are in range:** what is read from a field, an array element, or a run-time `[Pure]` function is within its type's range.

## Bits

Shifts and bitwise operators are exact, on `int`, `uint`, `long` and `ulong`, and on smaller types as C# promotes them.
A shift never overflows: it drops bits, even in `checked` code, and its count is taken modulo the width. `>>` keeps a
negative value's sign, and `>>>` doesn't. They mean the same in specifications: unlike `+` and `*` there, which are mathematical,
bits belong to the operands' type.

With one operand constant, each is plain integer arithmetic: `x >> k` is `x` divided by `2^k`, rounding down, and a mask
reads runs of bits. These prove quickly and mix with the rest of a proof. With neither operand constant, the result is
known in two ways: if one operand is a shift by `k` and the other is under `2^k`, as when a word is packed, it is their
sum; otherwise it is known bit by bit. That's exact for known values, but identities over two unknown values, such as
`(x ^ y ^ y) == x` or De Morgan's laws, generally don't prove. A shift by a count the proof doesn't know is correct, but
proves less. Bitwise operators on enums are unknown values, and `~` on `int?` is refused, as `-` on `int?` is. See samples/Good/Utf8.cs and Base64.cs.

## Exceptions

Methods are verified for partial correctness: any call may throw anything, and a path that throws need not meet the postcondition. `try`/`catch`/`finally` handlers are verified on every path that reaches them, and `Spec.EnsuresOnThrow<E>(condition)` (Code Contracts' `Contract.EnsuresOnThrow`) says what holds if the method exits by throwing an `E`.
- **Where exceptions come from.** `throw` (throwing `null` is an error, CSV1013); any call to a method that is not `[Pure]` or a lemma; and the operations that throw: `checked` overflow, `MinValue / -1`, `Math.Abs(MinValue)` (`OverflowException`), and a failed downcast (`InvalidCastException`).
- **Handlers.** An exception is an object of the type thrown, and each `catch (E)` tests its dynamic type, in order; filters (`when`) too. A `finally` runs on every way out of its try: normal, `return`, or an exception, which then goes on outward. `throw;` rethrows. `using` and `lock` are try/finally underneath, and work.
- **What a throw leaves.** A callee that throws gives nothing back: views it got by `ref` are lost, and its postconditions and the invariants it would have restored are not known. Only its `EnsuresOnThrow` clauses for the exception's type hold. For example, `ExceptionSamples.Update` in samples/Good/Exceptions.cs rolls back a first step in a `catch` and rethrows, promising the array is as it was.
- **Leaving the method by an exception,** its own `EnsuresOnThrow` clauses for that type must hold (CSV1002).
- **Proofs** (lemmas, `[Pure]`) may not throw at all (CSV1011): a lemma that escapes by throwing would prove nothing.
- **Cost.** An exceptional path is explored only where something sees it: inside a try, or in a method with `EnsuresOnThrow`. Elsewhere a throw ends the path, as before.
- **Not modeled.** Exceptions from property accessors with code, and from operations the verifier proves cannot fail (null dereference, array bounds, division by zero), are not raised. Catching a generic exception type is not supported (CSV1901). Neither are stack overflow and out-of-memory.

## Async and concurrency

**The guarantee.** A verified method is correct in every run where no other thread writes the state it uses while it runs. That covers single-threaded programs, data confined to one thread, and data handed between threads with proper synchronization when no thread is working on it. Races are not ruled out: two threads writing one object at once are outside what is proved.

**`async` and `await`** fit this guarantee: an async method runs one piece at a time, and between pieces (at an `await`) other code may run.
- **Contracts** of an async method speak of what it returns, the `T` of its `Task<T>`/`ValueTask<T>`: `Spec.Ensures<int>(r => r == 2 * x)`. A non-nullable `T` is a postcondition, as for any method. The contract holds when the task completes.
- **`await F(...)`** of an async method of the program is a call: `F`'s precondition is checked at the call, and its postcondition is assumed for the awaited value. `ConfigureAwait(...)` is seen through.
- **At every `await`, other code may run.** So afterwards the verifier forgets everything the method does not hold: arrays, fields, statics, and the locals that lambdas or local functions write. What it holds stays:
  - locals and parameters;
  - the fields of `[Owned]` objects whose views or permissions are in hand;
  - array cells its `Spec.Acc` contract gave it;
  - memory cells whose views it holds;
  - the fields and cells of objects in **confined locals**. A local is confined when it only ever holds objects the method made itself, and is used only in ways that cannot hand its object to other code:
    - **What it may hold.** `new` arrays, and `new` objects of program classes whose constructors (and the ones they chain to) do not use `this` as a value or call its methods, and whose bases are program classes too. Objects of the base class library may also be held, outside `System.Threading`, `System.Runtime` and `System.Reflection`.
    - **How it may be used.**
      - reading and writing its fields, auto-properties and elements;
      - comparing it with `null`;
      - calling `[Pure]` members on it;
      - calling base class library members on it. A result that may be the object itself (`StringBuilder.Append`) must be used the same way. A task must be awaited at once.
      - `foreach` over it, and `using` it when its type is the library's;
      - passing it to pure functions, specifications, and static library methods whose result cannot refer to it;
      - returning it.
    - **What disqualifies it.** Anything else: storing it in a field, an array or another local, passing it to a method of the program, capturing it in a lambda, or subscribing to its events.

  ```csharp
  var c = new Counter(); c.N = 1;
  await Task.Yield();
  Spec.Assert(c.N == 1);           // proved: nothing else can reach c
  ```

  A loop with an `await` forgets the same things at its head, except that a confined local the loop assigns is not kept.

  *Soundness:*
  - Views are linear and permissions add up to one, so no code that runs in between can hold what this method holds, and so none can write it.
  - A confined local's object is reachable only through that local. It was new when stored there, and no use of the local passes it anywhere else, so code that runs at an await has no reference to it. Members of the base class library are trusted not to keep their receiver. Its threading types are excluded, because they hand objects to other threads.
  - Everything else is forgotten, which is what any code could have done to it.
- **A task held in a local and awaited later** (`var t = F(x); …; await t;`):
  - **At the call:** `F`'s precondition is checked.
  - **While it runs:** other code may run at any moment, so what the method doesn't hold is forgotten from each statement to the next. Locals and confined objects stay.
  - **At `await t`:** what `F`'s postcondition says of the result is known. `await Task.WhenAll(a, b)` awaits both, and gives an array of their results if it has one. `t.Result` gives the result once `t` has been awaited.
  - **Reported (CSV1026):** a path that never awaits it, since a failure in it would be lost, and `t.Result` before that, since it blocks.
  - **Refused (CSV1901):** storing, returning or capturing the task, reassigning the local, a `ref` argument, or lending views or permissions, which wouldn't be back until it returns. So is calling `F` without keeping the task (`F();`), and an `async void` method.
  - **Warned (CSV1900):** two tasks at once where one writes a field or array the other uses, unless a lock guards it: each is proved as if alone. The verifier knows which field, not which object, so this may be a false alarm on tasks working on different objects.
- **Library tasks** are values like any other. Awaiting one gives an unknown result, non-null as the library declares
  it, and may throw. An **async stub** (a `[ContractsFor]` stub method declared `async`, like `Stream.ReadAsync`'s)
  gives the awaited call its contract: its precondition is checked at the call, and its postcondition is of the awaited
  value (`n <= count`). A task of such a member that is not awaited at once is the library's, with no contract.
- **Lemmas and `[Pure]` functions** cannot be async.

**Lambdas and local functions** that write the method's locals (`l.ForEach(x => s += x)`) are not verified on their own. Any call may run one of them, so after every call, other than to a `[Pure]` function or a lemma, and at every `await`, the locals they write are unknown.

**Locks.** A field or auto-property can be guarded by a lock, a readonly field of its class: `[GuardedBy(nameof(_lock))]`. A lock guards only what the attribute says, and only that is used in proofs. Still, a field written inside `lock (_lock)`, and under no other lock, is reported where it's used without the lock (CSV1023), so inconsistent locking is found in code with no specifications. Volatile and readonly fields are left alone.
- **Every use needs the lock (CSV1023).** That covers reads, writes, specifications and methods with `[GuardedBy]`, whose caller must hold it. The lock must be taken on the same object, seen in the lock statements around the use: a lambda or local function in one doesn't count, since it may run later. A constructor has its own object to itself, and so does a new object's initializer. A `ref` to a guarded field outlives the lock, so it is reported.
- **So guarded state has no races, and the guarantee above is proved for it.** Entering a lock forgets what it guards, because others have had it. While it is held, nothing changes that this thread doesn't change.
- **`[LockInvariant(nameof(_lock))]`** on a `[Pure]` bool method says what holds while the lock is free. It is known on entering the lock, and proved on leaving it, on every path, exceptions included (CSV1024). A constructor must establish it, so a class with one must write a constructor. A call under the lock that may enter it again must find it true, unless the callee is `[GuardedBy]` the same lock.
- **Locks taken one inside another** must be taken in increasing order of level (CSV1025); see [Deadlocks](#deadlocks-lock-levels) below.

```csharp
readonly object _lock = new object();
[GuardedBy(nameof(_lock))] int _balance;
[LockInvariant(nameof(_lock)), Pure] bool Valid() => _balance >= 0;
public SharedAccount() { }

public int Balance() { Spec.Ensures<int>(r => r >= 0); lock (_lock) { return _balance; } }
public void Reset() { _balance = 0; }  // CSV1023: it could race
```

What a lock guards is the field itself, not what it refers to: `_items` being guarded says nothing of the array's cells, or of a reference copied out while the lock is held.

**`SemaphoreSlim` as a lock.** A lock can't be held across an `await`; a `SemaphoreSlim` made with a count of 1 can. It guards state just as a lock does, by `[GuardedBy]`, when it is taken in this form:

```csharp
await _gate.WaitAsync();       // or WaitAsync(ct), or _gate.Wait()
try { ... }
finally { _gate.Release(); }
```

- **What it guards stays across an `await` inside it,** since nobody else can have it. Its invariant need not hold there: it is proved at the `Release`.
- **What it guards is forgotten on taking it,** as with a lock, and the lock rules on use apply (CSV1023), including in a `catch`, and in a `finally` before the `Release`.
- **Any other use of it is reported (CSV1023):** another form of taking or releasing it, handing it to anyone, a wait with a timeout, a count other than 1, a field that isn't readonly. So is starting a task of a `[GuardedBy]` method without awaiting it, which would run alongside the holder.
- **It isn't reentrant, unlike a lock.** Taking it while it is held waits forever (CSV1025), which is reported when seen directly or through calls on `this`.

A semaphore of any other count, such as a rate limiter, guards nothing, and is a library call like any other.

**Wrappers: `[Acquires]` and `[Releases]`.** A helper or a lock class around such a semaphore says what it does, and is then used like the semaphore:

```csharp
[Acquires] public async Task<Releaser> LockAsync(CancellationToken ct) { await _gate.WaitAsync(ct); return new Releaser(_gate); }

using (await _lock.LockAsync(ct)) { ... }           // or: using var held = await _lock.LockAsync(ct);

[Acquires(nameof(_gate))] private async Task EnterAsync() { await _gate.WaitAsync(); }
[Releases(nameof(_gate))] private void Exit() { _gate.Release(); }

await EnterAsync(); try { ... } finally { Exit(); }
```

The lock is the field the call is on, which may be a `SemaphoreSlim` with an extension method, or the field the attribute names. The result of a `using` can't be used for anything else, and any other form of the call is CSV1023. That a wrapper does what it says is taken from its shape, not proved: `[Acquires]` must wait on a semaphore of count 1 and its result's `Dispose` must call `Release`; `[Releases]` must call `Release`. On a `[ContractsFor]` stub the attributes say so of a library's lock, on trust. A callback form, `gate.RunLockedAsync(() => ...)`, isn't understood.

**Deadlocks: lock levels.** A lock can have a level, `[LockLevel(n)]`: on its field (an object for `lock`, a semaphore of count 1, a lock class, a `ReaderWriterLockSlim`, `SpinLock` or `Mutex`, an array whose elements are locked), or on a class, for locks on its objects (`lock (this)`, `lock (account)`). While a lock is held, only locks of higher levels may be taken (CSV1025), so every thread takes its locks in increasing order, and no cycle of threads can wait on each other. Locks that are never taken one inside another need no level.

```csharp
[LockLevel(1)] readonly object _accounts = new object();
[LockLevel(2)] readonly SemaphoreSlim _log = new SemaphoreSlim(1, 1);

lock (_accounts) { Audit(); }         // fine if Audit takes only _log, or nothing
```

- **What a lock is.** A field is its own lock; an object of a class with a level is that class's; a local that is only ever given one lock is that lock. A lock on an `object` or an interface, or `typeof(...)`, can't have a level, so taking one inside another lock is reported. One object can't be two locks of different levels: a class can't say a level its base class says, a field can't say one when its objects' class does, and a leveled lock field must be readonly and given a new object of its own (all CSV1025).
- **Checked through calls.** What a call may take is worked out from all it runs: its body, the methods, accessors and constructors it calls, every override or implementation in the program of a virtual or interface member, calls with no call written (operators, conversions, `foreach`, `using`, events, collection initializers, property patterns), a lambda a library call runs at once (`list.ForEach(x => ...)`, not `Task.Run`), and what a library can call back: every override and interface implementation of the program's classes it's handed, through its type arguments, receiver and arguments, and of a comparer for what a collection holds. Taking the same lock of the same object again is fine for a lock, which is reentrant, and reported for a semaphore or a `SpinLock`, which would wait for itself.
- **A delegate could take any lock.** Calling one while a lock is held is reported, unless its delegate type says `[TakesNoLocks]`; then every lambda and method made one is checked to take none. `[TakesNoLocks]` on a method, interface or class is trusted at its calls and checked in its body and in every override and implementation.
- **Waiting is taking.** Waiting for a task or thread while holding a lock (`await t`, `t.Wait()`, `t.Result`, `GetAwaiter().GetResult()`, `Join()`, `Task.WhenAll`) is fine only if what the task may take is above what's held: it may need it to finish. A task the code started is known by the call that started it; one it was given (a parameter, a field) could wait for anything, so waiting for it under a lock is reported. So is waiting under a lock for anything only another thread can end: an event, a countdown, a barrier, a semaphore that isn't a lock.
- **Two locks of one field or class,** on two objects, are ordered by an id of their objects: `[LockLevel(1, OrderedBy = nameof(Id))]`, a readonly int field, and they're proved to be taken in increasing order of it, where both are taken or where a call takes the second: the verifier follows which parameter (or receiver) each lock a call takes belongs to, through any depth of calls, and proves the order of the arguments at the call. An array's elements are ordered by index.

```csharp
public readonly int Id;
[LockLevel(1, OrderedBy = nameof(Id))] public readonly object Lock = new object();

if (from.Id < to.Id) { lock (from.Lock) lock (to.Lock) { ... } }
else                 { lock (to.Lock) lock (from.Lock) { ... } }

static void Credit(Account a) { lock (a.Lock) { ... } }
lock (x.Lock) { Credit(y); }          // proved: x.Id < y.Id
```

- **Other lock primitives** are locks in their form: taken by a statement of its own, then a `try` whose `finally` gives them back, or taken first thing in the `try` (`Monitor.Enter(_l, ref taken)`). That covers `Monitor.Enter`/`Exit`, `ReaderWriterLockSlim`'s `Enter...Lock`/`Exit...Lock` (ordered like an exclusive lock), `SpinLock` and `Mutex`. `Monitor.Enter`'s form also guards state as a lock statement does, with invariants. Taken in any other way, where it's held can't be told, and it is reported (CSV1025).
- **`Monitor.Wait` and `Pulse`** need the lock held (CSV1023, or they throw). `Wait` gives the lock back and takes it again: its invariants must hold at the `Wait` (CSV1024), and what it guards is forgotten after. It may give back only the lock it waits on: waiting while holding another lock is reported, since the thread that would pulse it may need that lock first, and so is calling, under a lock, code that waits.
- **Blocking on async code that comes back to its context.** `F().Result`, `F().Wait()` or `GetAwaiter().GetResult()` on the program's async `F` is reported if `F`, or async code it calls, awaits anything without `ConfigureAwait(false)` (including `Task.Yield()`, `await foreach` and `await using`): on a UI thread or another single-threaded context, the continuation needs the very thread that is blocked. Blocking inside `Task.Run` has no context and is fine.

What lock levels prove is that no set of threads can wait on each other for locks, tasks and the waits above. They don't prove that a thread waiting on `Monitor.Wait` or an event is ever woken: that someone pulses or signals is up to the program's logic, as in any verifier that doesn't prove liveness.

**Cancellation.** A token's `IsCancellationRequested` is a new answer at every read, and specifications can't speak of it, since it could be true by the time they're looked at. Being cancelled comes out as an exception from `ThrowIfCancellationRequested` or any `await`, so a `catch (OperationCanceledException)` is reached, and a `finally` must restore what a lock's or a semaphore's invariant needs. A postcondition is of a normal return: a cancelled method has made no promise, beyond those of `Spec.EnsuresOnThrow`. `CancellationTokenSource` is a library class with nothing modeled, and `CancellationToken.None` is no different from any other token.

**Task.Run and threads.** `Task.Run(d)`, `Task.Factory.StartNew(d)` and `th.Start()` of `new Thread(d)` run alongside the method, so it's as for a task awaited later: from there until `await t` or `th.Join()`, what the method doesn't hold is forgotten from each statement to the next. So is a task from an interface, a delegate or a method that isn't async, since it may run the program's code too; a library's own, like `Task.Delay(1)`'s, doesn't. A task that is stored, returned or dropped, or a thread not joined, runs on to the end of the method, and `ids.Select(id => F(id))` is treated the same, since nothing follows those tasks.
- **The code in the delegate is proved knowing nothing of who started it,** so what it shares needs a lock (see below).
- **Reported (CSV1026):** a task kept in a local and never awaited, or a call of one as a statement of its own. `_ = Task.Run(...)` says it is meant.
- **Warned (CSV1900):** two of them, or one and the method that started it, where one writes a field or an array the other uses, and no lock is held for it; and one that keeps running after the method and writes what no lock guards. The verifier knows which field, not which object, so this may be a false alarm. It's a warning, not a proof either way: nothing here proves code free of races but `[GuardedBy]`.
- **Permissions go with it.** See below.

**Concurrent collections and channels.** Nothing about what they hold is known, since others can change it: `ContainsKey`, `Count`, `IsEmpty` and the indexer give a new answer each time, even right after an `Add`. What is known is what they say of their results: a `TryGetValue`, `TryDequeue` or `TryRead` that returns true gave a value that's not null, if the type says so, and `GetOrAdd` and `ReadAsync` likewise; a null key is reported. `await foreach` is a loop whose every round is an `await`: it needs invariants for what it keeps, and its `MoveNextAsync` can throw.

**Permissions of tasks and threads.** A method whose contract names permissions (`Spec.Acc` of cells or objects, `Spec.AccRead` of cells) can run alongside its caller, and work split between tasks is proved to stay apart:

```csharp
await Task.WhenAll(Fill(a, 0, mid, 1), Fill(a, mid, a.Length, 2));
Spec.Assert(a[0] == 1 && a[mid] == 2);
```

- **At the start** the precondition is proved and its permissions leave the caller, so a second task can't get the same cell (CSV1016), and the caller can't write or read a cell it gave away until it is back.
- **At `await` or `Join`** the postcondition's permissions come back. What it says is of the state when the task ended, so it may read only what comes back, with a `Spec.Acc` to its left, and what never changes: anything else is reported where the task starts (CSV1016), rather than quietly lost. `Spec.Old` in it is of the start. A task awaited at once has no such rule. If the task failed, nothing comes back. A task never awaited keeps what it took.
- **`Spec.AccRead(a, from, to)`** is a share of permission to read. Any number of tasks can hold one at once, nobody can write those cells meanwhile, and a call that only takes a share changes none of them.
- **A delegate** works the same way if it is one call with values that don't change: `Task.Run(() => F(a, 0, mid))`, or `new Thread(() => F(a, 0, mid))` in a local that only gets started and joined. The call is proved where it starts, and the delegate isn't verified apart. Any other delegate is on its own and knows nothing, so it can't be given permissions.
- **Reads are checked too.** A method with cell permissions that runs alongside others, or is called from one that does, reads only cells it has a permission or share for (CSV1016), and it can't call code that may read any array. Calls into the library aren't looked at.
- **Not supported (CSV1901):** views and predicate instances, and instance methods of `[Owned]` classes, since what's lent by a call goes back when it returns.

**What runs concurrently says so (CSV1028).** A method of the program that runs at the same time as other code must be marked `[RunsConcurrently]`, on itself, its property, or its class, struct or interface. The verifier doesn't work it out across the program; it checks each place where it can see the mark is needed:

- a method started and not awaited in the same method (a task kept in a field, returned, or awaited only inside a lambda), or handed to `Task.Run`, a thread or `Parallel` as a method group;
- a method, constructor or property with code that marked code calls, or that a method calls between starting a task and finishing it;
- an override or implementation of a marked method, since a call of it may reach any of them;
- a delegate type of the program whose delegates concurrent code calls; marked, every lambda made one is concurrent code.

A lambda given to `Task.Run`, a thread or `Parallel`, and lambdas and local functions inside concurrent code, are concurrent where they are and need no mark; so is a method started and awaited later in the same method (`var t = A(); ...; await t;`, or `await Task.WhenAll(A(), B())`), since both ends are in sight, though its callees still need the mark; nor do auto-properties and a positional record's own members. An entry point that the program's callers run at once, such as a web handler, is marked the same way.

**Code that runs alongside other code must hold what it uses (CSV1027).** That is a marked method, a delegate given to `Task.Run`, a thread or `Parallel`, and a method between starting a task and finishing it. A field it uses must be one of:

- never changed: `readonly`, or a get-only or `init` property;
- guarded by a lock (CSV1023 says if it's held);
- covered by a permission: `Spec.Acc`, a view or a share, so its class must be `[Owned]`;
- on a new object only a local has, or the one a constructor or initializer is building.

- shared with no lock: `[Atomic]`, below.

Array cells likewise: a permission, or a new array only a local has. Specifications aren't run, and aren't looked at.

**Race warnings** (CSV1900) remain for what that can't see: `[Trusted]` code, and a library's state through its stubs. Two pieces of code are compared by object where that can be told. They prove nothing either way.

**Design.** This follows concurrent separation logic with fractional permissions, in the implicit-dynamic-frames style of Chalice and Viper: starting a task is a fork, which exhales its precondition, and awaiting it is a join, which inhales its postcondition. A lock's invariant, and what it guards, is the resource it holds. An `await` is a point where other code may run, so what isn't held is forgotten, as for an unstable assertion. The theorem to reuse is that a program proved in that logic has no data races. The rule above is what makes concurrent code fall under it. As there, the resources are what the program says, not what the verifier guesses: what runs concurrently is marked, and checked at each start and call, a lock guards only what `[GuardedBy]` names, and a started task's postcondition reads only what it gives back (self-framed), so joining it inhales an assertion that stays true. Outside it are concurrent code that nothing in the source starts and nobody marked, what a library object holds (a `List<T>` in a readonly field), a `Func` or `Action` that concurrent code calls (a delegate type of the program says so), `[Trusted]` code, and reads by other code of an object a task that is never awaited still holds. The verifier's encoding has not itself been proved against the logic.

**Lock-free code: atomic fields.** A field that threads share with no lock is `[Atomic]`, and says the step every change of it keeps, whoever makes it:

```csharp
[Atomic(Step = nameof(Grows))] volatile int _hits;
[Pure] static bool Grows(int old, int now) => old <= now;

int seen = _hits;
if (seen < int.MaxValue) Interlocked.CompareExchange(ref _hits, seen + 1, seen);   // proved a step
int later = _hits;
Spec.Assert(seen <= later);                                                        // proved, whatever the others did
```

- **A read** sees what the other threads have made it since this thread last looked: the same value, or a step on. Since the step is transitive (proved, CSV1030), any number of their changes is one step. So `seen <= later` holds, and `seen == later` doesn't.
- **A write** is proved a step from the value it replaces (CSV1030). A plain write replaces whatever the others have made it, which this thread hasn't read, so `_hits = seen + 1` is reported: another thread may have raised it past that. `Interlocked.CompareExchange` replaces only the value it compares with, and `Exchange`, `Increment`, `Decrement`, `Add`, `And` and `Or` replace the one they read; `Increment` and `Add` wrap at the type's ends, as they do at run time, so on a field that only grows they are reported unless the field has no step. `Volatile.Read`, `Volatile.Write` and `Interlocked.Read` are a read and a write.
- **Without a step** (`[Atomic]` alone) any change is one: every write is allowed, and a read knows nothing of the last.
- **Plain reads and writes** need the field `volatile`, or the compiler may reorder them or reuse an earlier read (CSV1030). A `long` can't be volatile; it's used through `Volatile` and `Interlocked`. A constructor sets its own object's fields freely: no other thread has it yet.
- **What a specification says of one** is of the value this thread last read or wrote. A contract is useful when it stays true under the others' steps: `Spec.Ensures<int>(r => Spec.Old(_hits) <= r && r <= _hits)` does, for a caller reading it later.
- **What forgets it** (a call that uses it, a loop's head, an `await`) keeps that it went by steps, at every object there before.
- **Used anywhere,** not only in code marked to run concurrently, since another thread may be at it: an atomic field needs no lock or permission in concurrent code (CSV1027), and isn't part of the race warnings.
- **Reported (CSV1030):** an atomic field of a type that isn't read and written in one step (an integer, `bool`, `char`, an enum or a reference: not `float`, `double`, `decimal` or a struct), one that is `readonly`, `[GuardedBy]`, a lock, in a struct or in an `[Owned]` class; a step that isn't a static `[Pure]` bool method of two values of the field's type, or that reads state; and a `[Pure]` function, predicate or invariant that reads one, since those are of one state. Passing one by `ref` to anything but `Volatile` and `Interlocked` is refused (CSV1901), as is `Interlocked` on a field that isn't atomic.

Each field is on its own: nothing relates two atomic fields, or an atomic field and other state, so a flag doesn't publish data written before it (that data still needs a lock or a permission). This is what makes it sound under .NET's memory model, which keeps one order of writes for each field, read and written through `volatile` and `Interlocked`, but promises no single order of all of them: per field, a read never sees an older value than a read before it, and each write follows the one before it in that field's order. Lock-free arrays are not covered: an array cell shared with no lock or permission is still reported (CSV1027).

*Design.* This is rely-guarantee reasoning (Jones 1983) with one relation per field as both the rely and the guarantee,: a thread's facts about a field are stable when the step keeps them, and its writes keep the step for the others.

An algorithm can be proved over all interleavings by modeling it, as Leino does in Dafny: its atomic events as methods, and what holds in every state as an invariant each keeps. `samples/Good/TicketLock.cs` and `DiningPhilosophers.cs` do so, including that the ticket lock's display can't stall under a fair schedule, and that philosophers taking forks in order always have someone who can move. That proves the algorithm, not any threads running it.

## Floating point

`float` and `double` are IEEE 754 binary32 and binary64, exactly (Z3's floating-point theory). Every operation rounds as .NET does, to nearest with ties to even, and NaN, the infinities and -0.0 are values like any other. What verifies holds of the program as it runs: `0.1 + 0.2 != 0.3` is provable, and `x + 1.0 > x` is not (NaN, the infinities, large x).
- **Comparisons** are IEEE's. `==` is false for NaN (even `x == x`) and true for `-0.0 == 0.0`, and `<` and the rest are false when an operand is NaN. So `!float.IsNaN(x)` is a common precondition.
- **Arithmetic** `+ - * /` rounds; overflow gives an infinity, as at run time, so it is not an error. `%` is not modeled (an unknown value, with a warning).
- **Casts.** Integer to float and float to float round to nearest. Float to an integer type truncates and must fit: it is CSV1010 if it might be NaN, infinite or out of range, or an `OverflowException` in a checked context. In a specification, where a cast that does not fit has no value, it must be shown to fit too (CSV1012).
- **Library.** `Math`/`MathF` `Min` and `Max` (with .NET's NaN and -0.0 rules), `Abs`, `Sqrt`, `Floor`, `Ceiling`, `Truncate`, `Round` and `FusedMultiplyAdd` are exact, and so are `double`/`float` `IsNaN`, `IsInfinity`, `IsFinite`, `IsPositiveInfinity`, `IsNegativeInfinity`, `IsNormal` and `IsSubnormal`. `Sin`, `Exp`, `Pow` and the like are unknown values.
- **Storage.** Floats live in fields, array cells, sequences and data records (stored through an injective encoding; a new array's cells are +0.0).
- **What proves well.** Comparisons, min and max, and casts to integers within constant bounds prove quickly: the bounding-box code of samples/Good/Floats.cs does. Proofs about rounded arithmetic (`lo + (hi - lo) / 2` stays within `[lo, hi]`) are bit-precise and can be slow, or beyond the solver. Relating a float to a symbolic integer (`x < n` for an `int n`) often is.
- **`Ieee` lemmas.** The monotonicity of rounded operations, which the solver decides only by bit-blasting whole multipliers (minutes, for one `x * z <= y * z`), is a trusted library of lemmas: `Ieee.MulMonotone`, `AddMonotone`, `SubMonotone`, `DivMonotone` and `SqrtMonotone`, for `float` and `double`. Each states exactly when it holds: finite operands, since an infinity times zero is NaN. Call one where a proof needs it.

## Strings

A string is its value. Two strings with the same characters are the same to the verifier, so `==`, `!=`, `Equals`
(ordinal, or with `StringComparison.Ordinal`), a `switch` on strings, and a dictionary's string keys compare contents,
as .NET does. `Length` is a function of the value. A literal is the same value wherever it appears, and different
literals are different values. `a + b` is never null, and as long as both (null counts as empty).

The characters are UTF-16 code units: `s[i]` is a value in `0..65535`, one function of the string and the index. A
literal's are known; `a + b`'s are `a`'s, then `b`'s; and strings of one length with the same characters are one string,
so a proof can show that `s.Substring(0, n) + s.Substring(n) == s`, or that a loop checked what its result claims (see
samples/Good/Strings.cs, StringConversions.cs, StringEscaping.cs and Kmp.cs). Library methods say what they do with characters in their stubs (see
[Contracts for code without sources](library-contracts.md)). `foreach` over a string reads the same characters, by index: `Spec.Index(c)` is its
index, and it ends by itself. Methods that use the current culture (`StartsWith(string)`, `EndsWith(string)`,
`IndexOf(string)`) promise nothing about characters: `"a".StartsWith("a\u00AD")` is true. Use their
`StringComparison.Ordinal` overloads, or the `char` ones.

Comparing strings as objects
(`ReferenceEquals(a, b)`, `(object)a == (object)b`) is unknown, since equal strings may or may not be one object.
Comparisons other than ordinal (culture, `OrdinalIgnoreCase`) are unknown.

## Disposables

Objects that hold a file, a socket, a timer or a connection must be disposed. CsVerify checks them as linear
resources (the `DisposalAnalyzer`, part of the analyzers):
- **Which ones:**
  - objects of a class marked `[MustDispose]`;
  - objects of a library type that a `[ContractsFor]` stub marks `[MustDispose]`: `FileStream`, `StreamReader`/`StreamWriter`, `BinaryReader`/`BinaryWriter`, `GZipStream`, timers, `CancellationTokenSource`, `Mutex`, `Process`, `FileSystemWatcher`, `Socket`, `TcpClient`, `HttpResponseMessage`, `DbConnection`/`DbCommand`/`DbDataReader`;
  - objects of a class that owns a field of such a type.

  `MemoryStream`, `StringReader`, `Task` and `HttpClient` (meant to be shared) are not marked: disposing them is
  harmless or wrong, not required.
- **Who owns one:** a local holding a new one, or one a call or an `await` returns (`File.OpenRead(path)`, `await
  client.GetAsync(url)`). A parameter is borrowed from the caller, unless it is `[TakesOwnership]`.
- **On every path** an owned one is disposed (`Dispose()`, `DisposeAsync()`, `x?.Dispose()`, a `using` declaration or
  statement, a `finally` that disposes it), returned, or handed over. Handing over means storing it in a field (the
  object owns it then), passing it to a `[TakesOwnership]` parameter (`new StreamReader(stream)` takes its stream), or
  giving it to `Spec.HandOver(x)` (a container or a dependency-injection scope that will dispose it; trusted). A path
  where it is null (`if (fs != null)`) holds nothing. Otherwise it leaks (CSV0020), including when the variable is
  overwritten while it holds one. Using it, or disposing it again, after it may have been disposed is CSV0021.
- **Owners.** A class with a field (or auto-property) of a disposable type owns it, unless the field is `[NotOwned]`.
  The class must be IDisposable, and its `Dispose` (or `Dispose(bool)`, `DisposeAsync`) must dispose the field
  (CSV0022). Its own objects must then be disposed in turn.
- **Not checked:** a path that ends in an exception (that is what `using` is for), a disposable captured by a lambda,
  and one kept in a collection without `Spec.HandOver`.

## Null references

C#'s nullable reference types are only warnings, and deliberately unsound ones: `null!` silences them, `new string[n]` is an array of nulls typed `string[]`, and a field can be read before the constructor sets it. CsVerify takes the annotations as contracts and proves them instead:
- **Every dereference** (`a.Length`, `a[i]`, `x.F`, `x.M()`) must be of a reference proved not null (CSV1013). `this` and `new` objects and arrays are never null. Conditions guard it as for the other checks: `if (a == null) return`, `a != null && a.Length > 0`, `s is not null`, `s is { }`, `?.` and `??`, in code and in specifications.
- **A non-nullable parameter** (`int[] a` in an enabled nullable context) is a precondition: the method assumes it, and each caller proves its argument (CSV1014). `int[]? a` promises nothing, so the method must check before use.
- **A non-nullable return type**, `out` or `ref` parameter is a postcondition: proved at each return (CSV1014), assumed by callers.
- **`!` proves nothing.** It has no run-time effect, so the verifier ignores it: `Len(null!)` is reported.
- **Array elements are maybe-null**, whatever the element type says. Say otherwise with a precondition, `Spec.Requires(Spec.Forall(0, a.Length, i => a[i] != null))`.
- **Oblivious types** (code with nullable disabled) promise nothing, so they are maybe-null too. Only an enabled nullable context lets the verifier know anything is not null. The MSBuild target passes the project's `<Nullable>`, and the command line takes `--nullable` (default `enable`).
- **Library methods** are trusted for their annotations: a non-nullable return type, `[NotNull]` parameters after the call (`ArgumentNullException.ThrowIfNull`), `[NotNullWhen(b)]` parameters when the call returns `b` (`string.IsNullOrEmpty`), `[MaybeNullWhen(b)]` out parameters when it returns `!b` (`TryGetValue`), and `[AllowNull]` and `[MaybeNull]`; a type parameter as instantiated (a `List<string>`'s items).
- **Fields** of non-nullable type are not null once their object is built (see [Mutable objects](objects.md#mutable-objects)), and positional fields of data records are not null either (see [Data types and object invariants](objects.md#data-types-and-object-invariants)). Fields and auto-properties of nullable type are maybe-null.
- **A class with no constructor of its own** (or only a primary constructor) has no constructor body to verify, so its
  non-nullable fields' initializers are checked instead. Each must make an object or array, be a string literal or
  interpolation, `string.Empty`, a call to a method that returns non-null, or a non-nullable primary-constructor
  parameter. `= null!`, or no initializer, is reported (CSV1014). Before this, such a class's `= null!` went unchecked,
  and `new C().Name.Length` verified.
- **Objects a framework builds.** `required` members are set by every object initializer, which the compiler checks.
  `[JsonRequired]` members (System.Text.Json) are trusted to be set by whoever builds the object, as the deserializer
  does or throws. Neither has to be set by a constructor, and both are not null on read. So a DTO can say
  `[JsonRequired] public string Owner { get; set; } = null!;`. Code that builds one with `new` and leaves `Owner` out is
  not checked for it.
- **Guard clauses** say what they check: `ArgumentNullException.ThrowIfNull(x)` (its `[NotNull]`),
  `ArgumentException.ThrowIfNullOrEmpty(s)` and `ThrowIfNullOrWhiteSpace(s)` (not null, not empty: stubs), and
  `ArgumentOutOfRangeException.ThrowIfNegative`, `ThrowIfNegativeOrZero`, `ThrowIfZero`, `ThrowIfGreaterThan`,
  `ThrowIfGreaterThanOrEqual`, `ThrowIfLessThan`, `ThrowIfLessThanOrEqual`, `ThrowIfEqual`, `ThrowIfNotEqual` for
  integer types (built in). After the call, the relation holds; otherwise it threw.
- **Library calls keep what they cannot touch.** A library can run the program's code only through overrides and
  interfaces, and can read a field only through reflection, which is not covered. So a call handed an object whose
  class (and its subclasses) overrides nothing and implements no interface keeps its fields' facts: after
  `Console.WriteLine(dto)`, a checked `dto.Notes` is still not null. An object that may be a list or a dictionary,
  or an `object` of unknown class, may still be changed.
- **Locals** declared with a non-nullable type (`Config p`, not `var p`, whose type is nullable) have every write checked, so they stay not null through loops.
- **Never null:** `this`, `new` objects and arrays, string concatenations and interpolations, lambdas and method groups made delegates.
- **`Nullable<T>`** (`int?`) is a value with two parts: whether it has a value, and the value. Conversions wrap
  (`int?  x = 3`) and unwrap it. An explicit unwrap, `(int)x` or `x.Value`, of one with no value is reported (CSV1013),
  since it throws. `HasValue`, `GetValueOrDefault`, `x == null`, `x ?? d`, and patterns (`x is int v`, `x is > 0`)
  read it. Lifted operators work as C# defines them: `x + y` has no value if either has none, `x < y` is false then, and
  `x == y` is true when neither has a value. `bool?` `&`/`|` and floating-point comparisons are unknown values, with a
  warning.

**Why it might be null.** A failed null check says where the value came from, as far as the verifier knows:

```
'u' might be null in 'u.Name': 'Find' may return null (line 12)
's' might be null in 's.Length': parameter 's' is declared 'string?'
'u.Boss' might be null in 'u.Boss.Name': the call to 'WriteLine' (line 9) may change what was checked before it
  (a check made before a call does not hold after it: copy the value to a local, check that, and use the local)
```

The reasons are a call that may return null, a parameter declared nullable, a call after which a checked field may
have changed, and a loop without invariants.

On `samples/Buggy/NullBugs.cs` the C# compiler warns about 3 of the 5 planted bugs. It says nothing about the two `null!` ones and `new string[2]`, and it warns falsely after the precondition that rules null out.
