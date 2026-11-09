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
  assumed, and what it modifies forgotten;
- the parts of the graph a specification's `&&` or `?:` lowers to are left out: specification arguments never run, and
  their branches meet again at the `Spec` call;
- each check is an `assert` on a line of its own; the engine maps the line Boogie reports back to the C# location and
  the CsVerify diagnostic it is (CSV1001 precondition, CSV1002 postcondition, CSV1004 assertion, CSV1005 and CSV1006
  invariant, CSV1009 division by zero, CSV1010 overflow).

Integers follow [the same rules](semantics.md#bounded-integers): a C# `int` or `long` is a Boogie `int` kept in its
range (a parameter, a result and every local, whose `where` clause Boogie assumes after a loop havocs it too); overflow
is an `assert` in the default context, an `assume` in a checked one (the path throws), and wraps around in an
unchecked one (two's complement, as Euclidean `mod`); `/` and `%` truncate, as C#'s do, where Boogie's `div` and `mod`
are Euclidean; `MinValue / -1` throws; specifications are mathematical.

Arrays are Dafny's encoding: a reference type, an allocated set, a length (an `int`'s range), and a map of elements for
each element type; what is read from one is in its type's range. Reading or writing an element is checked for null
(CSV1013) and bounds (CSV1003); `new T[n]` is a reference not allocated before, of length `n`; a non-nullable array
parameter is checked at each call's argument (CSV1014), and a non-nullable result where it's returned. A procedure
`modifies` the maps it writes, and those of what it calls: as in CsVerify's engine, a call that writes arrays leaves
every array's elements unknown.

A specification is checked well-defined where it is evaluated (CSV1012), as Dafny's are: an array read in range, a
divisor not zero, each under what `&&`, `||` and `?:` make hold there and over a quantifier's range; the check isn't
assumed after it (`{:subsumption 0}`), so what an ill-defined specification says stays unknown, as in CsVerify's
engine. `Spec.Forall(lo, hi, k => …)` and `Spec.Exists` are Boogie's quantifiers over that range.

## The subset

So far: static methods of `int`, `long` and `bool` and one-dimensional arrays of them (parameters, locals, results),
with arithmetic, comparisons, `if`, loops with invariants, array reads, writes, lengths and allocation, calls of each
other, `Spec.Assert` and `Spec.Assume`, and in specifications `Spec.Forall`, `Spec.Exists`, `Spec.Old` and
`Spec.Result`. A method outside it (fields, objects, strings, `try`, lambdas, `foreach`, `Spec.Decreases`, permissions,
a call of one outside it) is verified by CsVerify's own engine, in the same run. `CSVERIFY_TRACE=1` says why each such method wasn't translated.

## How it's checked

On every method the Boogie engine verifies, it must report what CsVerify's engine reports: the same diagnostics, at
the same lines (`BoogieEngineTests`), on a corpus written for this and on `samples/Good` and `samples/Buggy`.
`--engine boogie-only` verifies only what Boogie translates, to compare the two.

## What comes next

The subset grows a construct at a time, each under the same comparison, until CsVerify's engine is no longer needed:
1. `foreach`, `[Pure]` and `[GhostFunction]` definitions (Boogie functions), and the ghost types (`Seq`, `Map`);
2. the heap: objects, fields and allocation, encoded as Dafny encodes them (a heap map, an allocated set);
3. exceptions (`try`, `catch`, `finally` as blocks, a throw as a jump to its handler), and termination
   (`Spec.Decreases`, which Boogie doesn't check: asserted at each call and back edge);
4. the library models as Boogie: LINQ's definitions, the collections' models, the EF change tracker as ghost state
   with contracts, which a call's frame then covers like any other state;
5. views, permissions and lock invariants, encoded as maps over objects, as CsVerify's engine does now;
6. async and threads.
