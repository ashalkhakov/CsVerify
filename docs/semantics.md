# Integers, exceptions, floating point and null

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

## Floating point

`float` and `double` are IEEE 754 binary32 and binary64, exactly (Z3's floating-point theory). Every operation rounds as .NET does, to nearest with ties to even, and NaN, the infinities and -0.0 are values like any other. What verifies holds of the program as it runs: `0.1 + 0.2 != 0.3` is provable, and `x + 1.0 > x` is not (NaN, the infinities, large x).
- **Comparisons** are IEEE's. `==` is false for NaN (even `x == x`) and true for `-0.0 == 0.0`, and `<` and the rest are false when an operand is NaN. So `!float.IsNaN(x)` is a common precondition.
- **Arithmetic** `+ - * /` rounds; overflow gives an infinity, as at run time, so it is not an error. `%` is not modeled (an unknown value, with a warning).
- **Casts.** Integer to float and float to float round to nearest. Float to an integer type truncates and must fit: it is CSV1010 if it might be NaN, infinite or out of range, or an `OverflowException` in a checked context.
- **Library.** `Math`/`MathF` `Min` and `Max` (with .NET's NaN and -0.0 rules), `Abs`, `Sqrt`, `Floor`, `Ceiling`, `Truncate`, `Round` and `FusedMultiplyAdd` are exact, and so are `double`/`float` `IsNaN`, `IsInfinity`, `IsFinite`, `IsPositiveInfinity`, `IsNegativeInfinity`, `IsNormal` and `IsSubnormal`. `Sin`, `Exp`, `Pow` and the like are unknown values.
- **Storage.** Floats live in fields, array cells, sequences and data records (stored through an injective encoding; a new array's cells are +0.0).
- **What proves well.** Comparisons, min and max, and casts to integers within constant bounds prove quickly: the bounding-box code of samples/Good/Floats.cs does. Proofs about rounded arithmetic (`lo + (hi - lo) / 2` stays within `[lo, hi]`) are bit-precise and can be slow, or beyond the solver. Relating a float to a symbolic integer (`x < n` for an `int n`) often is.
- **`Ieee` lemmas.** The monotonicity of rounded operations, which the solver decides only by bit-blasting whole multipliers (minutes, for one `x * z <= y * z`), is a trusted library of lemmas: `Ieee.MulMonotone`, `AddMonotone`, `SubMonotone`, `DivMonotone` and `SqrtMonotone`, for `float` and `double`. Each states exactly when it holds: finite operands, since an infinity times zero is NaN. Call one where a proof needs it.

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
- **Locals** declared with a non-nullable type (`Config p`, not `var p`, whose type is nullable) have every write checked, so they stay not null through loops.
- **Never null:** `this`, `new` objects and arrays, string concatenations, lambdas and method groups made delegates.

On `samples/Buggy/NullBugs.cs` the C# compiler warns about 3 of the 5 planted bugs. It says nothing about the two `null!` ones and `new string[2]`, and it warns falsely after the precondition that rules null out.
