# The Boogie engine

CsVerify's own engine reads a method's operations and writes SMT directly: every C# construct and every library model
(LINQ, Entity Framework, locks, async) is a case in one interpreter, so its soundness is argued across all of it. The
Boogie engine splits that the way Dafny and Spec# do: C# is lowered to [Boogie](https://github.com/boogie-org/boogie),
an intermediate verification language with a small, documented semantics (formalized in Isabelle, with its
verification-condition generation validated per run: Parthasarathy, Müller and Summers, CAV 2021), and Boogie does the
rest. What CsVerify has to get right is then the lowering, one construct at a time, and the models, written as Boogie.

```bash
dotnet csverify --engine boogie src/     # the methods it translates, by Boogie; the rest as always
```

Neither side is designed here: the source is Roslyn's own lowering of C#, its control-flow graph (`foreach`, `using`,
`lock`, `?.`, `&&`, patterns and compound assignments already turned into blocks), and the target is Boogie.

## The translation

Each method is a Boogie procedure:
- its `Spec.Requires` and `Spec.Ensures` are the procedure's `requires` and `ensures` (`Spec.Ensures<R>(r => …)` binds
  `r` to the result, `Spec.Old(x)` is `old(x)`);
- its body is the control-flow graph, block for block, as an unstructured Boogie procedure (blocks and `goto`): a
  branch goes through a block of its own that assumes its condition, so a loop's head stays a plain block;
- a `Spec.Invariant` is an `assert` at the start of its loop's head block, which Boogie takes as the loop's invariant;
- a call of another translated method is a Boogie `call`: its precondition is checked there, its postcondition
  assumed;
- each check is an `assert` on a line of its own; the engine maps the line Boogie reports back to the C# location and
  the CsVerify diagnostic it is (CSV1001 precondition, CSV1002 postcondition, CSV1004 assertion, CSV1005 and CSV1006
  invariant, CSV1009 division by zero, CSV1010 overflow).

Integers follow [the same rules](semantics.md#bounded-integers): a C# `int` or `long` is a Boogie `int` kept in its
range (a parameter, a result and every local, whose `where` clause Boogie assumes after a loop havocs it too); overflow
is an `assert` in the default context and an `assume` in a checked one (the path throws); `/` and `%` truncate, as C#'s
do, where Boogie's `div` and `mod` are Euclidean; `MinValue / -1` throws; specifications are mathematical.

## The subset

So far: static methods of `int`, `long` and `bool` (parameters, locals, results), with arithmetic, comparisons, `if`,
loops with invariants, calls of each other, `Spec.Assert` and `Spec.Assume`. A method outside it (fields, objects,
arrays, `unchecked`, `try`, lambdas, `Spec.Decreases`, a call of one outside it) is verified by CsVerify's own engine,
in the same run. `CSVERIFY_TRACE=1` says why each such method wasn't translated.

## How it's checked

On every method the Boogie engine verifies, it must report what CsVerify's engine reports: the same diagnostics, at
the same lines (`BoogieEngineTests`), on a corpus written for this and on `samples/Good` and `samples/Buggy`.
`--engine boogie-only` verifies only what Boogie translates, to compare the two.

## What comes next

The subset grows a construct at a time, each under the same comparison, until CsVerify's engine is no longer needed:
1. arrays (a Boogie map per element type, and a length) and `unchecked` arithmetic (modular, or bit vectors);
2. the heap: objects, fields and allocation, encoded as Dafny encodes them (a heap map, an allocated set);
3. exceptions (`try`, `catch`, `finally` as blocks, a throw as a jump to its handler), and termination
   (`Spec.Decreases`, which Boogie doesn't check: asserted at each call and back edge);
4. the library models as Boogie: LINQ's definitions, the collections' models, the EF change tracker as ghost state
   with contracts, which a call's frame then covers like any other state;
5. views, permissions and lock invariants, encoded as maps over objects, as CsVerify's engine does now;
6. async and threads.
