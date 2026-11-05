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
  - memory cells whose views it holds.

  A loop with an `await` forgets the same things at its head. *Soundness:* views are linear and permissions add up to one, so no code that runs in between can hold what this method holds, and so none can write it. Everything else is forgotten, which is what any code could have done to it.
- **An async method of the program called without being awaited at once** (`var t = F(); …; await t;`, or an `async void` method) is rejected (CSV1901). It would run interleaved with its caller, each changing what the other relies on. Lending it permissions explicitly is the next step (step 2 below).
- **Library tasks** are values like any other. Awaiting one gives an unknown result, non-null as the library declares
  it, and may throw. An **async stub** (a `[ContractsFor]` stub method declared `async`, like `Stream.ReadAsync`'s)
  gives the awaited call its contract: its precondition is checked at the call, and its postcondition is of the awaited
  value (`n <= count`). A task of such a member that is not awaited at once is the library's, with no contract.
- **Lemmas and `[Pure]` functions** cannot be async.

**Lambdas and local functions** that write the method's locals (`l.ForEach(x => s += x)`) are not verified on their own. Any call may run one of them, so after every call, other than to a `[Pure]` function or a lemma, and at every `await`, the locals they write are unknown.

**Not covered (yet).** Threads started with `Task.Run` or `new Thread` are ordinary library calls: the fields and arrays their delegate may write are forgotten at the call, but not afterwards, while the thread runs. `lock`, `Interlocked` and `volatile` are ordinary calls and reads, with no meaning about other threads. Deadlock freedom and progress are not checked, and neither is lock-free code. The plan (step 2) is permission-based, as in Viper and VerCors. Starting a thread would hand it the permissions its delegate's precondition names, and joining it would give back its postcondition's. A lock would get an invariant saying what it protects. Then every verified program would be race-free.

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
literals are different values. `a + b` is never null, and as long as both (null counts as empty). The characters
themselves are not modeled: `s[i]` is an unknown character, and so are the results of most string methods beyond their
stubs (see [Contracts for code without sources](library-contracts.md)). Comparing strings as objects
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
