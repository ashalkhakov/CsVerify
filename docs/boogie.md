# The Boogie engine

CsVerify's own engine reads a method's operations and writes SMT directly: every C# construct and every library model
(LINQ, Entity Framework, locks, async) is a case in one interpreter, so its soundness is argued across all of it. The
Boogie engine splits that the way Dafny and Spec# do: C# is lowered to [Boogie](https://github.com/boogie-org/boogie),
an intermediate verification language with a small, documented semantics (formalized in Isabelle, with its
verification-condition generation validated per run: Parthasarathy, Müller and Summers, CAV 2021), and Boogie does the
rest. What CsVerify has to get right is the lowering, one construct at a time, and the models, written as Boogie.

Neither side is designed here: the source is Roslyn's own lowering of C#, its control-flow graph (`foreach`, `using`,
`lock`, `?.`, `&&`, patterns and compound assignments already turned into blocks), and the target is Boogie. The goal
is that it covers everything, and CsVerify's engine is retired.

```bash
dotnet csverify --engine boogie src/                          # what it translates, by Boogie; the rest as always
dotnet csverify --engine boogie --boogie-out out.bpl src/     # and the Boogie program it verified
CSVERIFY_TRACE=1 dotnet csverify --engine boogie src/         # and why each method left out was
```

## The pipeline

1. **Which methods.** Every method whose signature and contract are in [the subset](#the-subset) is held back; the rest
   is verified by CsVerify's engine as always. Those held back are translated together; one whose body has something
   outside the subset is left out, and so is each method that calls it, until none is (a call needs its callee's
   procedure). They go to CsVerify's engine too.
2. **One program.** The methods translated are one Boogie program: [the prelude](#the-prelude), a function for each
   `[Pure]` or `[GhostFunction]` method, and a procedure for each method.
3. **Boogie verifies it,** in the same process (the `Boogie.ExecutionEngine` package), with the Z3 CsVerify uses.
4. **Back to C#.** Every check is an `assert` on a line of its own, and the translator keeps a table from line to the C#
   location and the CsVerify diagnostic it is; each failure Boogie reports is found there, so the diagnostics are the
   ones CsVerify's engine gives, at the same places (BoogieEngineTests checks that they are).

## An example

```csharp
public static int Max(int[] a)
{
    Spec.Requires(a.Length > 0);
    Spec.Ensures<int>(r => Spec.Forall(0, a.Length, k => a[k] <= r));
    int m = a[0];
    for (int i = 1; i < a.Length; i++)
    {
        Spec.Invariant(1 <= i && i <= a.Length && Spec.Forall(0, i, k => a[k] <= m));
        if (a[i] > m) m = a[i];
    }
    return m;
}
```

becomes (`--boogie-out`, abridged: the blocks the invariant's `&&` lowers to are left out):

```boogie
procedure Example.Max$int__(p$a: Ref) returns (result: int)
  free requires $InRange($E.SByte, $E.Byte, …);              // what is read from memory is in range
  free requires p$a == null || $Alloc[p$a];
  free requires p$a != null;                                  // checked at each call's argument (CSV1014)
  requires (len(p$a) > 0);                                    // checked at each call (CSV1001)
  free ensures (forall q$k: int :: 0 <= q$k && q$k < len(p$a) ==> ($E.Int32[p$a][q$k] <= result));
  free ensures (-2147483648 <= result && result <= 2147483647);
{
  var l$m$210: int where (-2147483648 <= l$m$210 && l$m$210 <= 2147483647);
  var l$i$237: int where (-2147483648 <= l$i$237 && l$i$237 <= 2147483647);
    assert {:subsumption 0} (p$a != null);                    // the precondition well-defined (CSV1012)
  b1:
    assert p$a != null;                                       // CSV1013
    assert 0 <= 0 && 0 < len(p$a);                            // CSV1003
    l$m$210 := $E.Int32[p$a][0];
    goto b2;
  b2:
    l$i$237 := 1;
    goto b3;
  b3:                                                         // the loop head: its asserts are the invariant
    assert {:subsumption 0} …;                                // the invariant well-defined (CSV1012)
    assert ((1 <= l$i$237) && (l$i$237 <= len(p$a))) &&
           (forall q$k: int :: 0 <= q$k && q$k < l$i$237 ==> ($E.Int32[p$a][q$k] <= l$m$210));   // CSV1005, CSV1006
    goto b3$then, b3$else;
  b3$then:
    assume !((l$i$237 < len(p$a)));
    goto b12;
  b3$else:
    assume !(!((l$i$237 < len(p$a))));
    goto b9;
  b9:
    assert p$a != null;
    assert 0 <= l$i$237 && l$i$237 < len(p$a);
    goto b9$then, b9$else;
  b9$then:
    assume !(($E.Int32[p$a][l$i$237] > l$m$210));
    goto b11;
  b9$else:
    assume !(!(($E.Int32[p$a][l$i$237] > l$m$210)));
    goto b10;
  b10:
    l$m$210 := $E.Int32[p$a][l$i$237];
    goto b11;
  b11:
    assert (-2147483648 <= (l$i$237 + 1) && (l$i$237 + 1) <= 2147483647);   // i++ (CSV1010)
    l$i$237 := (l$i$237 + 1);
    goto b3;
  b12:
    result := l$m$210;
    assert {:subsumption 0} …;                                // the postcondition well-defined (CSV1012)
    assert (forall q$k: int :: 0 <= q$k && q$k < len(p$a) ==> ($E.Int32[p$a][q$k] <= result));   // CSV1002, here
    return;
}
```

## The prelude

| Declaration | What it is |
|---|---|
| `cs#div`, `cs#rem` | C#'s `/` and `%`, which truncate toward zero (Boogie's `div` and `mod` are Euclidean) |
| `LayerType`, `$LZ`, `$LS` | fuel, as Dafny's: how many times a function's definition may unfold |
| `Ref`, `null`, `$Alloc` | references, and the allocated ones |
| `len(a)` | an array's length: a function (it never changes), between 0 and `int.MaxValue` |
| `$E.Int32`, `$E.Char`, `$E.Boolean`, … | the elements of the arrays of each element type: `[Ref][int]int` (or `bool`) |
| `$InRange(…)` | every element of each map is in its type's range |

## The translation, construct by construct

**Methods.** Each is a procedure. Its parameters are in-parameters (`p$x`, which the body doesn't assign: a method that
assigns a parameter isn't translated yet), its result is `result`. `Spec.Requires` is a `requires`, checked at each
call (CSV1001); `Spec.Ensures` is a `free ensures`, assumed at each call, and asserted at each return (CSV1002), so that
each return path is reported, as CsVerify's engine reports them. `Spec.Ensures<R>(r => …)` binds `r` to `result`,
`Spec.Old(e)` is `old(e)`, `Spec.Result<R>()` is `result`.

**Bodies.** The control-flow graph, block for block, as an unstructured Boogie procedure: each block `b`*n*, its
operations, then where it goes. A conditional branch goes through two blocks of its own (`b`*n*`$then`, `$else`), each
assuming its condition, so that the blocks the graph has stay plain: a loop's head, which a later block jumps back to,
starts with its invariants. A throw ends the path (`assume false`): a path that throws need not meet the postcondition.

**Specifications in bodies.** `Spec.Assert` is an `assert` (CSV1004), `Spec.Assume` an `assume`. `Spec.Invariant` is an
`assert` at the start of its loop's head, which Boogie takes as the loop's invariant: checked on entry (CSV1005) and
kept by each iteration (CSV1006). The graph lowers `&&`, `||` and `?:` in a specification's argument into blocks and
captures too, but specification arguments never run: what they lower to is left out, and each of their branches is a
choice of either way, which meet again at the `Spec` call. The specification itself is read whole, from the operation
the source has.

**Integers.** Every C# integer type is a Boogie `int` kept in its range: a parameter by a `free requires`, a result by a
`free ensures`, a local by a `where` clause (which Boogie assumes after a loop havocs it too). As
[the semantics](semantics.md#bounded-integers) says, `+ - *`, `++`, compound assignments, unary minus and explicit
narrowing conversions are:
- in the default context, an `assert` that the value is in range (CSV1010);
- in a checked one, an `assume`: overflow throws, which ends the path;
- in an unchecked one, the value wrapped around (two's complement, as Euclidean `mod` of 2 to the type's bits).

`/` and `%` assert a divisor that isn't zero (CSV1009) and assume not `MinValue / -1`, which throws in .NET.

**Arrays.** Dafny's encoding: an array is a `Ref`; `a.Length` is `len(a)`; `a[i]` is `$E.T[a][i]`. A read or a write
asserts `a != null` (CSV1013) and `0 <= i && i < len(a)` (CSV1003). `new T[n]` is a reference not allocated before (`havoc`, then
`assume !$Alloc[t]`), now allocated, of length `n`, its elements the default (or the initializer's). A non-nullable
array parameter is asserted not null at each call's argument (CSV1014), and assumed in the callee; a non-nullable
result is asserted where it's returned.

**Calls and frames.** A call of another translated method is a Boogie `call`. A procedure `modifies` the maps it
writes (an element map, or `$Alloc` when it allocates), and those of everything it calls; after a call, what the
callee modifies is unknown, as CsVerify's engine forgets the arrays a callee may write. Allocation only grows:
`free ensures (forall r: Ref :: old($Alloc[r]) ==> $Alloc[r])`.

**Well-definedness.** A specification is checked well-defined where it's evaluated, as Dafny's are (CSV1012): at entry
for the preconditions (each under those before it), at each return for the postconditions, at the loop head for an
invariant, where an assertion is. Well-defined means an array read is in bounds and of an array that isn't null, a
divisor isn't zero, and a function's precondition holds where it's called; each under what `&&`, `||` and `?:` make
hold there, and over a quantifier's range. The check is `assert {:subsumption 0}`: not assumed after it, so what an
ill-defined specification says stays unknown, as in CsVerify's engine.

**Quantifiers.** `Spec.Forall(lo, hi, k => P)` is `(forall q$k: int :: lo <= q$k && q$k < hi ==> P)`, and
`Spec.Exists` is the `exists` of `lo <= q$k && q$k < hi && P`.

**Functions.** A `[Pure]` or `[GhostFunction]` method whose body is one expression is also a Boogie function, as
Dafny's functions are: on a layer, the heap's maps (as Dafny's take `$Heap`) and its parameters. Its definition is an
axiom: where its precondition holds, its value on layer `$LS(ly)` is its body, whose calls are on layer `ly`. Another
axiom makes every layer's value the same. A specification calls it on `$LS($LZ)`, so each use unfolds the definition
once, as CsVerify's engine does. Its postcondition is an axiom of every value where its precondition holds, and a
run-time `[Pure]` function's value is in its type's range. The method stays a procedure, which verifies the body and
says its result is the function's value. A `[GhostFunction]`, and a lemma, is ghost code: its arithmetic is
mathematical.

**Termination.** Ordinary methods are verified for partial correctness, as in CsVerify's engine, so only what
`Spec.Decreases` gives is checked:
- a call back into its own recursion group (the methods that call each other), of a method with a measure from one
  with a measure: the callee's at the arguments below the caller's, lexicographically (CSV1008);
- a `[Pure]` method or a lemma that recurses without a measure doesn't terminate, which would make its definition
  unsound: CSV1011;
- a loop's `Spec.Decreases`: its value at the head of each iteration, and at each edge back to the head, below it
  (CSV1007).

Below is Dafny's rule: the value before isn't negative, and the one after is less (it may be negative: McCarthy's 91
function's `101 - n`). The measure's check isn't assumed after it (`{:subsumption 0}`), so the loop's invariant is
checked on the same edge whether or not the measure went down.

## The subset

So far: static methods of the C# integer types, `char`, `bool` and one-dimensional arrays of them (parameters, locals,
results), with arithmetic, conversions, comparisons, `if`, loops with invariants and measures, array reads, writes,
lengths and allocation, calls of each other (recursive too), `Spec.Assert` and `Spec.Assume`; `[Pure]` and
`[GhostFunction]` methods, lemmas, `Spec.Decreases`; and in specifications `Spec.Forall`, `Spec.Exists`, `Spec.Old`,
`Spec.Result` and calls of functions.

Not yet (such a method is verified by CsVerify's engine): instance methods, objects and fields, strings, collections,
`foreach`, lambdas, `try`/`catch`/`finally`, a method that assigns a parameter, `Spec.Modifies`, `Spec.Reads`,
`Spec.EnsuresOnThrow`, permissions and views, ghost types (`Seq`, `Map`, `Bag`), async, locks and threads, LINQ, and
library calls with stub contracts.

## How it's checked

On every method the Boogie engine verifies, it must report what CsVerify's engine reports: the same diagnostics, at
the same lines. `BoogieEngineTests` checks that on a corpus written for it (one of each construct, a bug of each kind),
on `samples/Good` and on `samples/Buggy`. `--engine boogie-only` verifies only what Boogie translates, to compare the
two quickly.

## What comes next

The subset grows a construct at a time, each under the same comparison, until CsVerify's engine is no longer needed:
1. the heap: objects, fields, constructors and allocation, instance methods, non-nullable references, as Dafny encodes
   them;
2. strings and the collections' models (`List`, `Dictionary`, `HashSet`), and the ghost types;
3. `foreach`, lambdas and delegates;
4. exceptions (`try`, `catch`, `finally` as blocks, a throw as a jump to its handler), `Spec.EnsuresOnThrow`;
5. frames (`Spec.Modifies`, `Spec.Reads`), and the library's stub contracts;
6. views, permissions and ownership, encoded as maps over objects, as CsVerify's engine does now;
7. locks, async and threads;
8. LINQ and Entity Framework, their definitions and models as Boogie;
9. smoke tests (Boogie's `/smoke`), so that a contradiction in what a translation assumes is found as it is made.

Then the Boogie engine is the default, CsVerify's engine goes, and the rest of the documentation is revised to
describe the one engine there is.
