# The Boogie engine

CsVerify works the way Dafny and Spec# do: C# is lowered to [Boogie](https://github.com/boogie-org/boogie), an
intermediate verification language with a small, documented semantics (formalized in Isabelle, with its
verification-condition generation validated per run: Parthasarathy, Müller and Summers, CAV 2021), and Boogie does the
rest. What CsVerify has to get right is the lowering, one construct at a time, and the models, written as Boogie.

Neither side is designed here: the source is Roslyn's own lowering of C#, its control-flow graph (`foreach`, `using`,
`lock`, `?.`, `&&`, patterns and compound assignments already turned into blocks), and the target is Boogie.

```bash
dotnet csverify src/                          # every method, by Boogie
dotnet csverify --boogie-out out.bpl src/     # and the Boogie program it verified
CSVERIFY_TRACE=1 dotnet csverify src/         # and why each method left out was
```

## The pipeline

1. **Which methods.** Every method whose signature and contract are in [the subset](#the-subset) is held back; the rest
   is not verified (CSV1902, an error, saying why), with the checks made from the syntax and the declarations alone
   (`StaticChecks`: locking, lock levels, atomics, concurrency marks) still reported. Those held back are translated
   together; one whose body has something outside the subset is a procedure of its contract alone, which its callers
   call, and is not verified itself (CSV1902); one whose contract doesn't translate either is left out, and so is each
   method that calls it, until none is.
2. **One program.** Each method goes through [the passes](#the-passes), and the methods translated are one Boogie
   program: [the prelude](#the-prelude), a function for each `[Pure]` or `[GhostFunction]` method, and a procedure
   for each method.
3. **Boogie verifies it,** in the same process (the `Boogie.ExecutionEngine` package), with the Z3 CsVerify uses.
4. **Back to C#.** Every check is an `assert` on a line of its own, and the translator keeps a table from line to the C#
   location and the CsVerify diagnostic it is; each failure Boogie reports is found there.

## The passes

The translation is four passes over a small kernel language (`Boogie/Kernel.cs`), so that each concern is in one
place: Roslyn's lowering in the first, what C# means in the second, how memory is encoded in the third, Boogie's
syntax in the last. The kernel is Boogie's own shape (blocks of statements, each ending in a jump), with a few nodes
that carry C#'s meaning until the pass that gives it.

| Pass | File | In | Out |
|---|---|---|---|
| Lowering | `Lowering.cs` | a method's control-flow graph and its contract | a kernel procedure: blocks, typed nodes, unchecked |
| Checks | `Checks.cs` | that | mathematics, and each obligation an `assert` |
| Heap | `Heap.cs` | that | arrays as element maps and allocation; what it modifies |
| Printer | `BoogiePrinter.cs` | that | Boogie text, and the table from line to check |

`BoogieTranslator.cs` holds them together: which methods are procedures and which are functions, the recursion groups,
and what each procedure modifies, closed over what it calls (which needs all of them, so procedures are printed last).

**Lowering** reads Roslyn's control-flow graph block for block. Each operation becomes a kernel statement: an
assignment, an array write (`KStore`), an allocation (`KNew`), a call (`KCall`, its result in a temporary), an assume,
or a `Spec.Assert` or `Spec.Assume` (`KSpecStmt`). What C# means is kept, not yet given: arithmetic is a `KArith` with
its type and its context (default, checked, unchecked, or mathematical in ghost code), an explicit conversion a
`KConv`, an array read a `KElem`, a length a `KLen`, a function's call in a specification a `KFnCall`. A branch's
condition is evaluated once, into a temporary in its block, and each way assumes it or its negation. Where a later
operand is a call or an allocation (a statement before the expression), each earlier one is evaluated into a
temporary first, so its checks and its reads of memory come first, as in C#. Specifications are read whole, from the
operation the source has, and what the graph lowers their arguments to is left out. The contract, each loop's
invariants and measure (by its head), and a function's body are kernel expressions too. Anything outside the subset
throws `NotTranslated`, and the method is not verified (CSV1902, saying why).

**Checks** turns each typed node into mathematics and emits what it needs before it, in the order C# evaluates:
- an array read or write: `a != null` (CSV1013), then `0 <= i && i < len(a)` (CSV1003); a length: `a != null`;
- arithmetic and narrowing conversions: in range (CSV1010), assumed in range, wrapped, or nothing, by context;
  division: the divisor not zero (CSV1009), and not `MinValue / -1`;
- a call: each argument's checks, a non-nullable array argument not null (CSV1014), the termination of a call in its
  recursion group (CSV1008, CSV1011), then the call (its precondition, CSV1001);
- a specification: what makes it well-defined, under the guards of `&&`, `||`, `?:` and the quantifiers' ranges, as
  Dafny's (CSV1012), then its assert (CSV1004) or assume.

It also places the contract: the preconditions well-defined at entry; at each loop head its invariants (CSV1005,
CSV1006) and the measure's value; on each edge back to a head, the measure gone down (CSV1007); at each return, the
result not null and each postcondition well-defined and holding (CSV1002). A callee's requires and measure are its
contract lowered over its parameters, given the arguments.

**Heap** gives memory Dafny's encoding: an array write is an update of its element type's map, a field write one of
the field's map (`KMapUpdate`); an array allocation is a reference not allocated before, of the length, then
allocated, with its elements the default or the initializer's; `new C(...)` allocates an object the same way, sets its
fields to their defaults and calls the constructor on it. What a procedure writes is what it modifies; a field it
writes only at the object its constructor builds, or at objects it allocates, keeps its value at every other object.
It also gives each loop that writes arrays only through variables it doesn't change a frame: the other arrays are as
they were when the loop was entered.

**Printer** writes the [prelude](#the-prelude), each function's axioms (in a function, the maps are its parameters and
the layer is `ly`), and each procedure: the header (ranges, allocation, the contract, what it modifies), the locals
(an integer one with its range as a `where` clause), and the blocks. Each assert is on a line of its own, with the
check it is.

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

becomes (`--boogie-out`, abridged: the blocks the invariant's `&&` lowers to, which do nothing, are left out):

```boogie
procedure Example.Max$int__(p$a: Ref) returns (result: int)
  free requires $InRange($E.SByte, $E.Byte, …);              // what is read from memory is in range
  free requires p$a == null || $Alloc[p$a];
  free requires p$a != null;                                  // checked at each call's argument (CSV1014)
  requires (len(p$a) > 0);                                    // checked at each call (CSV1001)
  free ensures (forall q$k: int :: ((0 <= q$k) && (q$k < len(p$a))) ==> ($E.Int32[p$a][q$k] <= result));
  free ensures (((-2147483648) <= result) && (result <= 2147483647));
{
  var l$i$237: int where (((-2147483648) <= l$i$237) && (l$i$237 <= 2147483647));
  var l$m$210: int where (((-2147483648) <= l$m$210) && (l$m$210 <= 2147483647));
  var g$3: bool;                                              // the loop's condition, evaluated once
  var g$9: bool;
    assert {:subsumption 0} (p$a != null);                    // the precondition well-defined (CSV1012)
  b0:
    goto b1;
  b1:
    assert (p$a != null);                                     // CSV1013
    assert ((0 <= 0) && (0 < len(p$a)));                      // CSV1003
    l$m$210 := $E.Int32[p$a][0];
    goto b2;
  b2:
    l$i$237 := 1;
    goto b3;
  b3:                                                         // the loop head: its asserts are the invariant
    assert {:subsumption 0} …;                                // the invariant well-defined (CSV1012)
    assert (((1 <= l$i$237) && (l$i$237 <= len(p$a))) &&
           (forall q$k: int :: ((0 <= q$k) && (q$k < l$i$237)) ==> ($E.Int32[p$a][q$k] <= l$m$210)));  // CSV1005, CSV1006
    assert (p$a != null);                                     // a.Length (CSV1013)
    g$3 := (l$i$237 < len(p$a));
    goto b3$then, b3$else;
  b3$then:
    assume !(g$3);
    goto b12;
  b3$else:
    assume !(!(g$3));
    goto b4;
  …
  b9:
    assert (p$a != null);
    assert ((0 <= l$i$237) && (l$i$237 < len(p$a)));
    g$9 := ($E.Int32[p$a][l$i$237] > l$m$210);
    goto b9$then, b9$else;
  b9$then:
    assume !(g$9);
    goto b11;
  b9$else:
    assume !(!(g$9));
    goto b10;
  b10:
    assert (p$a != null);
    assert ((0 <= l$i$237) && (l$i$237 < len(p$a)));
    l$m$210 := $E.Int32[p$a][l$i$237];
    goto b11;
  b11:
    assert (((-2147483648) <= (l$i$237 + 1)) && ((l$i$237 + 1) <= 2147483647));   // i++ (CSV1010)
    l$i$237 := (l$i$237 + 1);
    goto b3;
  b12:
    result := l$m$210;
    assert {:subsumption 0} …;                                // the postcondition well-defined (CSV1012)
    assert (forall q$k: int :: ((0 <= q$k) && (q$k < len(p$a))) ==> ($E.Int32[p$a][q$k] <= result));   // CSV1002, here
    return;
  b13:                                                        // the exit: reached only by a return
    assume false;
    return;
}
```

## The prelude

| Declaration | What it is |
|---|---|
| `cs#div`, `cs#divI`, `cs#remI` | C#'s `/` and `%`, which truncate toward zero (Boogie's `div` and `mod` are Euclidean): a quotient of index arithmetic (variables and literals: a heap's parent `(j - 1) / 2`) the function `cs#div` (declared where it's used), which keeps the triggers of quantifiers over indices simple; other quotients and every remainder `cs#divI`, `cs#remI`, inlined, so the solver reasons on `div` and `mod` themselves (`i % 4 == o % 4` gives `(i - o) % 4 == 0`) |
| `$bit.and32`, `$bit.or64`, …, `$pow32`, `$pow64` | bitwise operators of two variables; a shift count's power of two |
| `LayerType`, `$LZ`, `$LS` | fuel, as Dafny's: how many times a function's definition may unfold |
| `Ref`, `null`, `$Alloc` | references, and the allocated ones |
| `len(a)` | an array's length: a function (it never changes), between 0 and `int.MaxValue` |
| `$E.Int32`, `$E.Char`, `$E.Boolean`, … | the elements of the arrays of each element type: `[Ref][int]int` (or `bool`) |
| `$InRange(…)` | every element of each map is in its type's range |

## The translation, construct by construct

**Methods.** Each is a procedure. Its parameters are in-parameters (`p$x`; one the body assigns is a local of the body,
below), its result is `result`. `Spec.Requires` is a `requires`, checked at each
call (CSV1001); `Spec.Ensures` is a `free ensures`, assumed at each call, and asserted at each return (CSV1002), so that
each return path is reported. `Spec.Ensures<R>(r => …)` binds `r` to `result`,
`Spec.Old(e)` is `old(e)`, `Spec.Result<R>()` is `result`.

**Bodies.** The control-flow graph, block for block, as an unstructured Boogie procedure: each block `b`*n*, its
operations, then where it goes. A conditional branch's condition is evaluated once, into `g$`*n*, and goes through two
blocks of its own (`b`*n*`$then`, `$else`), each assuming it or its negation, so that the blocks the graph has stay plain: a loop's head, which a later block jumps back to,
starts with its invariants. A throw ends the path (`assume false`): a path that throws need not meet the postcondition.

**Checks not assumed after.** A check that isn't assumed after it fails (a race, an order of locks,
a task not awaited, what isn't modeled) is an `assert` on a branch of its own that ends (`goto nc$k, nc$k$go`): Boogie,
once it has reported a failure, assumes it where it looks for the next, which would hide the failures after it on the
same path (a check that no task is running, assumed, makes the rest unreachable).

**Specifications in bodies.** `Spec.Assert` is an `assert` (CSV1004), `Spec.Assume` an `assume`; an asserted
conjunction is asserted a conjunct at a time, each known for the next, as Dafny splits them (so that Z3 needn't find
what the first says while it proves the second). `Debug.Assert(c)` and `Trace.Assert(c)` are asserted too (CSV1004,
their message evaluated, not used), and the guard clauses (`ArgumentOutOfRangeException.ThrowIfNegative(i)`,
`ThrowIfGreaterThanOrEqual(i, n)`, ...) may throw and give, when they return, what they checked. A call with a constant
composite format string that would throw `FormatException` (`string.Format`, `Console.WriteLine`, a `TextWriter`'s,
`AppendFormat`) is CSV1001 (`StaticChecks.FormatProblem`). In a `[Pure]`
member or a lemma, a checked overflow, `MinValue / -1` and `Math.Abs(MinValue)` are CSV1010 (it may not throw).
`a.GetLength(0)` of a one-dimensional array is its length (another dimension, CSV1003). `IList`'s and `ICollection`'s
`Contains` and `IndexOf` are of the elements, as LINQ's are read (strings by content). Their `Add`, `Insert`,
`Remove`, `RemoveAt`, `Clear` and indexer writes go by what the object is: an array's are of a fixed size (the first
five throw `NotSupportedException`, the indexer writes its cell), a `List`'s are the `List`'s stubs, any other's a
library call that says nothing of what it then holds. With a check profile
(`--checks`), the failures of the other kinds are left out, assumed. Warnings
(CSV1900: races, recursion without measures, an enumerator's `Current`) are a procedure's own, reported where Boogie
verifies it. `Spec.Invariant` is an
`assert` at the start of its loop's head, which Boogie takes as the loop's invariant: checked on entry (CSV1005) and
kept by each iteration (CSV1006). The graph lowers `&&`, `||` and `?:` in a specification's argument into blocks and
captures too, but specification arguments never run: what they lower to is left out, and each of their branches is a
choice of either way, which meet again at the `Spec` call. The specification itself is read whole, from the operation
the source has.

**Integers.** Every C# integer type is a Boogie `int` kept in its range: a parameter by a `free requires`, a result by a
`free ensures`, a local by a `where` clause (which Boogie assumes after a loop havocs it too). A float cast to an integer in a specification must fit (CSV1012), as a divisor mustn't be zero. As
[the semantics](semantics.md#bounded-integers) says, `+ - *`, `++`, compound assignments, unary minus and explicit
narrowing conversions are:
- in the default context, an `assert` that the value is in range (CSV1010);
- in a checked one, an `assume`: overflow throws, which ends the path;
- in an unchecked one, the value wrapped around (two's complement, as Euclidean `mod` of 2 to the type's bits).

`/` and `%` assert a divisor that isn't zero (CSV1009) and assume not `MinValue / -1`, which throws in .NET.

`Math.Max` and `Math.Min` of integers are `if`s; `Math.Abs(x)` is `x >= 0 ? x : checked(0 - x)`: `Abs(MinValue)`
throws, as checked negation does.

**Bitwise operators** (Boogie/Bits.cs): integer arithmetic over the two's
complement bits, which Boogie's Euclidean `div` and `mod` by a power of two read for negative values too
(bitvectors would make the solver convert between them and integers, which timed out on Base64's round trip).
- With one operand constant, each is exact and linear: `x >> k` is `x div 2^k`, `x << k` is `x * 2^k` wrapped into
  the type, `x & C` a sum of runs of `x`'s bits, `x | C` is `(x & ~C) + C`, `x ^ C` likewise, `~x` is `-1 - x` (or
  `2^w - 1 - x` unsigned). A shift's count is taken modulo the width; an unknown one is `$pow32(k mod 32)`.
- With neither constant, the result is `$bit.and32(x, y)` (or, xor; 64), of the type's range, with what is known of
  it: if one operand has no bits where the other may (a value shifted by k, and one below 2^k, as when a word is
  packed), their sum (or 0 for `&`); otherwise bit by bit, each bit of the result from the operands', and the value
  they add up to. In a specification it is translated only where it stands in a statement (`Spec.Assert`), whose
  facts are assumed just before it; not in a contract, nor of a quantifier's variable.
- Types narrower than `int` are computed as `int` and narrowed, as `x op= y` is.

**Arrays.** Dafny's encoding: an array is a `Ref`; `a.Length` is `len(a)`; `a[i]` is `$E.T[a][i]`. A read or a write
asserts `a != null` (CSV1013) and `0 <= i && i < len(a)` (CSV1003). `new T[n]` is a reference not allocated before (`havoc`, then
`assume !$Alloc[t]`), now allocated, of length `n`, its elements the default (or the initializer's). A non-nullable
array parameter is asserted not null at each call's argument (CSV1014), and assumed in the callee; a non-nullable
result is asserted where it's returned.

**Spans.** A `Span<T>` or `ReadOnlySpan<T>` of scalars is a value viewing memory: a base
array (`$sbase`), an offset into it (`$soff`) and a length (`len`). `s[i]` checks `0 <= i < len` (CSV1003) and is the
base's cell at offset + i, so what one span or the array writes, another sees. An array converted, `new Span<T>(a, start,
length)` and `a.AsSpan(...)` have the array as their base (a null one an empty span); `Slice` moves the offset, checked
within the span (CSV1001); `CopyTo` (the destination long enough, CSV1001), `TryCopyTo`, `Fill` and `Clear` write their
cells, as memmove does; `stackalloc` makes a new base. A span parameter's cells are some array's, within its length. A
library's static `[Pure]` stubs over spans (`BinaryPrimitives`' reads) are functions of their contracts.

**Rectangular arrays.** An `int[,]` (of any rank, of scalars) is a `Ref` as an array is, with a length per dimension
(`$dim(a, d)`, `GetLength(d)` for `0 <= d < rank`, CSV1003 otherwise) and its cells in its element type's map, cell
`[i, j]` at `$cell(i, j)` (`[i, j, k]` at `$cell($cell(i, j), k)`): an injective pairing, its inverses an axiom, so
two cells are the same exactly when their indices are, without `i * n + j`. Each
index is checked within its dimension (CSV1003, `index d in ...`), `Length` is the lengths' product, `new int[m, n]`
checks its sizes aren't negative (CSV1003) and fills its initializer's cells.

**Objects.** A class of the program whose objects are plain mutable state (not generic, not a record, derived from
`object`, with no virtual members or interfaces, and none of CsVerify's attributes: not `[Owned]`, no `[Invariant]`,
no locks or atomics) is a `Ref`, as an array is. Each of its fields and auto-properties is a map `$F.C.f: [Ref]T`
(Dafny's heap encoding); a static field is the map's value at `null`, the one object no reference aliases. An integer
field's map has a `where` clause keeping every value in range.
- `o.f` reads `$F.C.f[o]`, and `o.f = v` writes it, each asserting `o != null` first (CSV1013; `this` needs none).
- A field of non-nullable type is never null once its object is built: each write asserts it (CSV1014), each read
  assumes it (but `this`'s, in its constructor), and a constructor asserts at each return that it set it (CSV1014),
  as is a static one whose initializer makes an object, is a string literal or calls a method whose return type isn't
  nullable (a static one that starts null, `= null!`, promises nothing),
  unless it is `required`. A specification that reads one assumes it where it is evaluated.
- A local of non-nullable reference type has each write asserted not null (CSV1014).
- An instance method is a procedure with `this` (not null, allocated) first; `o.M(...)` asserts `o != null`.
  A virtual call is a call of the static target's contract, which overrides are checked against (see Inheritance).
- A constructor is a procedure on `this`, whose fields are their defaults at entry; it runs the field initializers,
  then its body. `new C(args)` allocates the object, sets its fields to their defaults and calls the constructor. An
  implicit constructor's initialized fields are unknown values at the call. A constructor that
  chains to `this(...)` skips the initializers and calls the other constructor on `this`, as `base(...)` is called
  (its arguments evaluated first, branching or not). `this` may escape (`a[0] = this`, a call with it): where the
  class has invariants or non-nullable fields, that's CSV1015, as the object isn't built yet. An object
  initializer's assignments are field stores on the new object (the control-flow graph spells them out).
- A method that runs alongside other code (`[RunsConcurrently]`, or started as a task or thread), or reads a field a
  lock guards, is checked for races (CSV1027, and warnings: `Lowering.Races`).

**Ownership.** An `[Owned]` class is in the subset too, with its `[Invariant]`s, as
[objects.md](objects.md#mutable-objects) describes it. A view `Own<C>` is the object it owns (a `Ref`); a procedure
keeps a local `perm: [Ref]bool`, the objects whose views it holds:
- at entry, `this` (in a method of the class that isn't `[Pure]`, and its constructor) and each view parameter, each
  not null, holding its invariant, and none another (views are linear);
- `Own.New(new C(...), out v)` proves the new object's invariant (CSV1015) and adds it; `Own.Drop(v)` removes it;
- writing an `[Owned]` object's field needs it in `perm` (CSV1016), as does calling a method of the class on it, which
  also proves its invariant (CSV1015) and assumes it after;
- a view handed to a call (by value or `ref`) is proved whole (CSV1016) and its invariant (CSV1015), and leaves
  `perm`; a `ref` or `out` view that comes back is in hand again, its invariant holding, and isn't one already in hand;
- at each return, a `ref` or `out` view given back, and `this`, hold their invariants again (CSV1015).

A call changes an `[Owned]` object's fields only where it holds the view: `this`, the views it gets, and objects it
makes. So a procedure that writes such a field ensures it unchanged at every other object allocated before:
`free ensures (forall o: Ref :: old($Alloc[o]) && o != this && o != p$v ==> $F.C.f[o] == old($F.C.f[o]))`. Its
preconditions are checked well-defined with the views' invariants assumed, as at entry. `v.Obj.Value` in a
specification is the view's object. `Own.ToAcc` and `Own.FromAcc` change nothing here: a view and `Spec.Acc` are one
permission.

**Ownership trees.** An `[Owns]` field of an `[Owned]` class holds an object whose view its container keeps
([objects.md](objects.md#mutable-objects)). Where the program has one, a global `$root: [Ref]Ref` maps each object to
its tree's root: an object whose view is in hand (made, received, given back) is its own root, and what an `[Owns]`
field holds is in its container's tree, and isn't its root.
- `Own.Take(ref c.F, out v)` needs c (CSV1016) and c.F not null (CSV1016); the object comes out with its view, its
  invariant holding, and c.F is null. c's tree splits: the object is a root now, and of the rest of c's tree, a havocked
  `split$` says what goes with it, never c and never what c's other `[Owns]` fields hold (those stay in c's tree, each
  a different object, and different from the one taken).
- `Own.Give(ref c.F, x, v)` needs c and x (CSV1016), c.F null, v x's view, x not c's root (a cycle, CSV1016), and x's
  invariant (CSV1015, "when it is given to its owner"); x's tree joins c's:
  `$root := (lambda y: Ref :: (if $root[y] == x then $root[c] else $root[y]))`.
- Any other write of an `[Owns]` field is CSV1016; a read of one in code assumes the tree fact of what it holds.
- `Own.Tree(x)` in a specification is the set of objects in x's tree.
- A call's frame is the trees it doesn't own: a procedure that writes `[Owned]` fields ensures each unchanged at every
  object allocated before whose root then wasn't the root of `this` or of a view it got (`old($root[o]) !=
  old($root[this])`), and `$root` unchanged there too; a constructor's `this` is new, so its frame stays `o != this`.
- Where a view's invariant is assumed, so is that its reference fields hold allocated objects, so a constructor called
  in between can't have changed them.

**Read shares.** Fractional permissions (a view is 1, each share ε): beside `perm`, a procedure keeps
`pk: [Ref]int`, the shares of each object in hand less those given away for good. A view is whole, so it may write,
hand itself to code that may, or be given to an owner, when it is in `perm` and `pk` isn't negative (CSV1016).
- A `Shared<C>` is its object (a `Ref`). `Own.Share(ref v, out s)` makes `s` of `v`: one share less with the view, one
  more in hand, so nothing changes. `Own.Unshare(ref v, s)` checks that `s` is of `v` (CSV1016), and again nothing changes.
- `Own.Drop(s)` and a share handed to a call by value give up a share: `pk[o]` goes down by one.
- A share parameter, or a view lent `in`, arrives with its invariant, as one share in hand: `pk[o] := 1`. It may
  alias other shares, but an `in` view isn't a view in hand. Handing either one to a call proves the invariant
  (CSV1015). A procedure's frame doesn't name them, so a call that gets only shares changes nothing of theirs.

**Packages.** A `[Linear]` positional `readonly record struct` is a data value (a datatype) whose views are its fields.
Beside `perm`, a procedure keeps `pkg: [Ref]bool`, the objects whose views are in packages it holds.
- Building one (`new P(v, o)`) proves each view's invariant (CSV1015, "when it is packed into P"), and moves it from
  `perm` to `pkg`. Deconstructing one (`var (v, o) = p;`) moves each view back to `perm`, its invariant holding.
- A package that arrives (a parameter, a call's result, a `ref` or `out` argument) brings its views into `pkg`. Each
  is different from the others and from every view in hand (`Receive` assumes a view isn't in `pkg` either).
- A call that gets a package (by value, or by `ref`) gets its views. Its procedure's frame names
  `$d.P.View(p$x$in)` as it names a view parameter.
- A struct is never null, and neither are its non-nullable references, which each construction checked. Each of
  them is allocated. A parameter's free requires and a result's free ensures say so.

A view moves from one variable to another (`view = back`) with its permission, which is its object's.

**Predicates.** Viper's, over the same permissions (as [objects.md](objects.md#mutable-objects) describes them, and as
Viper's Boogie backend, Carbon, encodes them). Instances are a type of their own, `Inst`, each `[Predicate]` an
injective constructor of its arguments (`i$Seg(from, to, n)`). Beside `perm`, a procedure keeps `pinst: [Inst]int`, how
many of each instance it holds, and `owner: [Ref]Inst`, which instance each folded object is in (`i#none`: none).
- A permission assertion (a precondition, a postcondition, an invariant, a predicate's body) is read left to right:
  `&&` and the branches of `?:` are followed, `Spec.Acc(o)` and instances are permissions under the condition they are
  in, and the rest are facts. In the assertion as Boogie sees it, the permissions read as `true`.
- Received (inhaled: a precondition at entry, a callee's postcondition after the call, an invariant at the loop head):
  `Spec.Acc(o)` is an object not null, not already in hand and folded nowhere, now in hand, its invariant holding; an
  instance's count goes up.
- Given up (exhaled: a callee's precondition at the call, a postcondition at a return, an invariant on the way into the
  loop's head): each must be in hand (CSV1016), an object's invariant holding (CSV1015).
- `Spec.Fold(P(args))` exhales the body (its facts must hold: CSV1019), and its objects, and what the instances in it
  own, are owned by the instance now. `Spec.Unfold` needs the instance (CSV1016) and inhales the body: its objects
  come back (they were owned by it), its facts hold, and the rest of its footprint goes to one of the instances in it.
- A call can change only what it was given. The caller snapshots, before the call, what it still holds (in hand, or
  folded into an instance it holds) and assumes it unchanged after: the `[Owned]` field maps the callee writes, and
  `owner`.
- A loop that exchanges permissions (folds, unfolds, or calls what gives or takes them) has its invariant's go round
  it: given up on the way in and on each back edge, received at the head with what was held outside it, and at each
  back edge nothing held outside it may have been used up (CSV1016).
- A predicate's body is checked where it is declared, as ghost code: read left to right, each field read needs a
  `Spec.Acc` to its left (CSV1016), and each read is checked not null under the conditions before it.
- As a condition elsewhere (`Spec.Assert(Seg(...))`), a permission means "in hand".
- A constructor exchanges permissions as any call does, about the new object.
- A field of an allocated object refers to an allocated object: assumed where one is read (Dafny's good heap).

**Array cells.** `Spec.Acc(a, lo, hi)` is permission to the cells `a[lo..hi)`, `Spec.Acc(a)` to all of them, and
`Spec.AccRead` a read share of them (Viper's quantified permissions over a range). A procedure that exchanges cells (its
contract names some, it folds or unfolds a predicate holding some, or it calls what takes some) keeps
`cells: [Ref][int]real` (1.0 whole, ε a share) and `cowner: [Ref][int]Inst`:
- one whose contract names cells holds none but those it is given; any other holds every cell, but those it gives;
- writing `a[i]` needs the whole cell (CSV1016); a new array's cells are all in hand;
- received cells are added (and, where it holds only what it is given, weren't whole already); given ones must be in
  hand (CSV1016); folded ones are owned by the instance, and unfolding splits them as objects are split;
- a call that takes cells changes only those it got, and those folded into the instances it got, unless they are still
  in hand, and arrays it allocates: every other cell keeps its value (`assume` against a snapshot taken before it);
- in a procedure that holds only what it is given, calling what may write any array without saying which cells is
  CSV1016;
- a predicate's body may read only cells it has a `Spec.Acc` for (CSV1016), and holds no `Spec.AccRead`.

`Spec.Fresh(r)` is `!old($Alloc[r])`.

**Single fields.** `Spec.Acc(o, nameof(C.F))` is permission to one field (Viper's `acc(o.f)`), of a sealed class
without an `[Invariant]`. Where the program uses them, a procedure keeps `fperm: [Ref][int]bool` and `fowner` (by
field id):
- writing `o.F` (and, in a predicate's body, reading it) needs the whole object or that field (CSV1016);
- giving one field of a whole object splits it: the other fields stay in hand, one by one; receiving the last of them
  makes it whole again; a whole object received holds none of its fields apart;
- a field is folded and unfolded as an object is, and a call keeps a field the caller holds, alone or folded.

**Functions over predicates.** A `[Pure]` or `[GhostFunction]` whose precondition holds one predicate instance (of
its parameters) reads that instance's footprint, and its value survives any change outside it (Viper's functions
over predicates). As Carbon does it, with snapshots: a procedure keeps `psnap: [Inst]int`, a snapshot of each
instance it holds, new where the instance is received or folded (unless a copy is in hand already, whose footprint is
then empty). Such a function is a Boogie function of the snapshot and its arguments, `f$Sum(psnap[i$Seg(from, to, n)],
from, to, n)`, with no definition of its own: at each fold and unfold of the instance, where its precondition holds,
its value for the instance's snapshot is its body, read then (nobody writes a folded footprint, so that is what it
was folded with). A snapshot is the procedure's own state, so a precondition or postcondition that names one is
checked and assumed in the body (at a call, at entry, after the call), not in Boogie's header; `old(...)` of it is of
the snapshots at entry (`psnap$entry`), or, in a caller, of those and of the memory just before the call. Its
postconditions that read no memory are axioms of every snapshot.

A function over a predicate may take more than the instance's parameters (`Key(t, i)` over `Table(t)`): at a fold or
unfold its value is defined for every value of the others. A snapshot has a state too (`$sst(s)`, of the memory's
maps, `$st.m($sst(s))`), in which the predicate's body's facts hold (they did when it was folded: assumed wherever a
snapshot is made or received), and a function over the predicate whose body reads no other snapshot is its body read
in that state: so `Contains(t, k)`, `Key(t, i)` and `Count(t)` of one snapshot agree, where nothing unfolds. One that unfolds its predicate in its body (`Spec.Unfold(Table(t));
return t.Count;`) ensures `result == Count(t)`, so its call in code tells what its uses in specifications read. A loop
head doesn't refresh a snapshot (the loop havocs those it changes, and Boogie assumes the invariants' facts of them),
and `old(...)` in an invariant is of the snapshots at entry, as in a postcondition. Where an instance is inhaled under
a guard that reads a snapshot (`r < Hedges(m) && Mesh(m)`), the guard is kept in a local before the snapshot changes.

A `[Pure]` method whose body is more than an expression is a function too: its body of local declarations, `if`s and
`return`s is one expression (each local a `let` over what follows), its
definition; a body of anything else leaves it a function of its contract alone (its procedure proves the contract,
and gives the function's value). One that reads nothing of the memory (scalar parameters, no field, no array, no call
but `Spec` and `Math`) takes no memory, so its value is the same before and after a write.

Not yet: a function over more than one instance, or over one not of its parameters; an ordinary function that calls one (its axioms are about every state).

**Floats.** `float` and `double` are IEEE 754 binary32 and binary64, Boogie's `float24e8` and `float53e11`
(Z3's floating point): `+ - * /` round to nearest (`$fp.add32` and the like, declared
`{:builtin "fp.add RNE"}`), `==` is IEEE's (`fp.eq`: NaN isn't itself, -0.0 is 0.0), `<` and the rest are false at
NaN, a literal is its bits (`$fp.bits32(1065353216bv32)`). An integer converts through the reals (`(_ to_fp 8 24) RNE`
of `real(i)`), a float to the other float type rounds; a float cast to an integer type truncates and must fit, not
NaN, infinite or out of range (CSV1010), its value then `int(fp.to_real(trunc(x)))`. `float.IsNaN` and the other tests
are Z3's, `Math.Abs`, `Sqrt`, `Floor`, `Ceiling`, `Truncate`, `Round` (to even), `FusedMultiplyAdd` exact, `Min` and
`Max` .NET's (NaN if either is; -0.0 below 0.0); `Sin`, `Exp` and the like are values not known. `%` is C's `fmod`: IEEE's
remainder (`fp.rem`) moved by `|y|` to `x`'s sign where it differs, which is exact. Fields, records and arrays of floats hold them as they are (`$E.Single`,
`$E.Double` where the program has float arrays), +0.0 by default.

**Tuples.** A tuple of the subset's values is a value whose elements are functions of it (`$tup.0.int(t)`): `(x, y)`
makes one (a literal at the type it's converted to too), `t.k` reads one, `var (a, b) = t` and `(a, b) = (b, a)` read
every element before assigning any. `t == u` of tuples of integers, enums, chars and bools evaluates the left's
elements, then the right's, and compares them element by element; `!=` is its negation.

**Structs.** A struct of the program whose instance fields (an auto-property's backing field too) are the subset's
values, no struct or tuple among them, is a value as a tuple is, its fields its elements in declaration order: `p.X`
reads one; `p.X = v` (of a local, a `ref` parameter, an array's cell, an object initializer's) makes a new value of the
others and `v` and writes it where `p` is (a struct in a class's field written in place is
refused, CSV1901), so a copy is a copy. `default(S)`, `new S()` and a new array's cells are the default value; a
constructor is a procedure giving the value it makes (`returns (this: Ref)`, the default to begin with). A member
that reads `this` is a procedure of it, a value never null. One that writes it (a member, `this` itself, or by calling
such a method on it) has `this` by reference, as C# does: in as `this$in`, out as `this`, `Spec.Old` of the value
in; a call writes the value out back to the receiver (a local, a parameter, an array's cell, a struct's member). A
struct value's integer fields are in their types' ranges.

**Enums.** An enum is an integer of its underlying type (any value of it, not only the named ones); conversions to
and from integers are the integers'. A switch expression no arm of which matches throws
`SwitchExpressionException`: CSV1022.

**Nullable values.** An `int?` (a `Nullable<T>` of an integer type or `bool`) is a reference: `null` where it has no
value, `$nmk.Int32(v)` where it has `v`, one reference per value (`$nmk` and `$nv`, its value, are each other's
inverse, `$nv` in the type's range), so the lifted `==` is the references'. Conversions wrap (`null` and `default` are
`null`), `(int)x` and `x.Value` unwrap (CSV1013 where it may be null), `HasValue` is `!= null`, `GetValueOrDefault` an
`if`, the lifted comparisons false where either is null, and patterns (`x is int k`, `x is null`, `x is > 0`) test the
value where there is one. Lifted arithmetic (`x + 1`) is `null` where an operand is, else the operation on the values.

**Strings, as values.** `a + b` of strings is as long as both and has their characters
(one too long throws OutOfMemoryException, a path not followed); `==` of strings in a specification gets the fact a
comparison in code does (of one length and different, they differ somewhere).

**LINQ.** LINQ to Objects is read member by member as its definitions (`Bcl/Linq.cs`) say
(Lowering.Linq): a source the verifier indexes (an array, a List, a list interface) is a sequence of a length and
elements, read where the call is (not null, CSV1013). `Select` maps it (with an index too), `Where` (with an index
too) and `Distinct` filter it (a running count `c` of the matches and each match's index `ix`, increasing), `Take` and
`Skip` keep the first `n` or the rest (`n` clamped to the length), `TakeLast` and `SkipLast` the last `n` or all
but them, `TakeWhile` and `SkipWhile` up to the first element the predicate rejects or from it on (its index a
fresh variable, of its definition), `Reverse` reads it backwards, `Append` and `Prepend` add one, `DefaultIfEmpty`
gives one default for an empty source, `Concat` puts one after the other and `Union` is the `Distinct` of that,
`Intersect` and `Except` keep the first source's first occurrences that the second has, or hasn't, `DistinctBy` the
elements whose key no earlier one has, `OrderBy` and `ThenBy`
permute it stably in their keys' order (a bijection `p` and its inverse; keys are ordered where they are integers or
chars), `Zip` pairs two, `SelectMany` flattens (running offsets, monotone, and each element's outer index), `Join`
filters the pairs of a flattening (a nullable key that is null matches nothing), `LeftJoin` adds each outer element
no inner one matches, with none; `Count`, `Any`, `All`, `Contains`, `First`, `Last` (and `OrDefault`), `Max`, `Min`,
`Sum` (every partial sum in range, CSV1001, as .NET adds them checked), `Average`, `MinBy` and `MaxBy` (the first
element whose integer key is least, or greatest) and `SequenceEqual` read it, their definitions' preconditions
CSV1001 (an empty sequence has no `First`); a List's `Find`, `FindIndex`, `Exists` and `TrueForAll` of a pure lambda
are its first match (or the default), the first match's index (or -1), `Any` and `All`; `Index` pairs each element with its
index; `ToDictionary` is a dictionary of the library's (what's in it unknown), its definition's precondition checked
(no key null or an earlier one's, CSV1001); `ToArray` and `ToList` copy it into a new object. A double
`Sum` adds in order from 0.0, rounding at each step. A `foreach` over a query reads it into a map where the loop
starts; `GroupBy` (with a result selector of the key and the group too) gives each key's first element's index, a
selector reading its `Key` and `Count()` (exact: a running count of the source's elements of that key; a database's
are bounds); over a `GroupBy`, each group is its key's first element's index, its `Key` that element's key, and a `foreach`
over it the source's elements of that key, as read when the groups were. Lambdas are inlined where they are pure
expressions (anonymous objects and tuples in them are tuples, made by a function of their parts); the running counts
and permutations are maps havocked where the call is, their definitions assumed, so a call in a loop gets new ones each
time round. Query syntax (`from s in xs let b = ... where ... select b`) is the calls it is. A `GroupJoin` looped over
(`from c in cs join o in os on k(c) equals k'(o) into g select new { c, g }`) is a row for each outer element, its
index, both sequences read where the loop starts; `row.c` is the outer element, and a loop over `row.g` runs over the
inner elements whose key is the row's. The members not named here are not translated (CSV1902).

**Entity Framework.** EF Core is read with a model of it (`EfModel`: entities, keys, unique indexes,
query filters, navigations, tokens; Lowering.Ef, Lowering.EfTracker):
- A query on a context's `DbSet` (or `Set<T>()`, through `AsNoTracking`, `IgnoreQueryFilters`, `AsTracking`, tags) is
  LINQ over the table as it is when the query runs (an `...Async` operator awaited where it's called is its operator,
  read after the await): a sequence in no order the database promises, of entities (`$isa`) not null, each a different
  object, no two with the same key or the same value of a unique index, each through the entity's query filters
  unless ignored. Its lambdas are the database's: strings compare by its collation (as having the same `$ckey`: an
  equivalence, which equal strings are in, with no axioms for the solver to go round) unless the only providers are
  ones that compare them exactly. `First` and `Last` keep a row by
  its place: unless the query is ordered by a key (or a unique index), at most one row may match (CSV1031). A `Join`
  on keys the database and .NET compare alike is LINQ's, in no order.
- Rows read without tracking are new objects (allocated where read); a reference navigation not included is null, a
  collection one as its initializer made it (a new empty `List`, or null), but where an Include path loads its type.
  An included reference is the row its foreign key names (or null, where the key can be), an included `List` (or
  `HashSet`) holds the rows whose foreign key is this row's key, each through its type's filters, new objects each, and so on down a `ThenInclude` path; a path that comes
  back to a type on it is CSV1032. An await leaves their columns as they were where no other code reaches them (the
  method lets none out: `EntitiesStayHere`).
- Rows read with tracking may be instances the context tracked already, as the program left them: what LINQ says of
  them (a filter's predicate, an order) holds only where the context tracked no entity of the type before
  (`Known`), and the count's bounds and the results' definitions whatever they hold. Their
  includes are as without tracking where the context tracked none of the types the paths load either. They are
  tracked from here on. `DbSet.Local` is what the context tracks of a type and doesn't delete, once each.
- The change tracker is state of the program's (`$F.$ef.State`: how each context tracks each object, `$F.$ef.Unsaved`,
  `$F.$ef.InTx`), which a call changes where its code does, and an await doesn't (a context is this code's alone while
  it runs, CSV1036); and the method's own record, none at entry: a failed save or rollback, a save outside a
  transaction, rows `ExecuteUpdate` changed behind the tracker, rows read without tracking and their tokens. `Add`,
  `Attach`, `Update`, `Remove`, `Entry(e).State =`, `SaveChanges`, `Find`, `Entry(e).Reload`, `Database.BeginTransaction`,
  `CurrentTransaction`, a transaction's `Commit`, `Rollback` and `Dispose`, `ChangeTracker.Clear`, `ExecuteUpdate` and
  `ExecuteDelete`, a write of an entity's column, and what a call of the program's may do (break a context, save, bulk
  update: read from its code) are checked (`Lowering.EfTracker`): CSV1033 (another tracked instance with the key,
  an `Update` of a graph, a context done with, a stale row written), CSV1034 (a token changed since read), CSV1035 (two
  saves outside a transaction, a transaction begun with one open, a commit with changes not saved).
- A database query's lambdas are checked translatable (CSV1032: a call of the
  program's, a property computed in C#); such a query throws where it runs, so what it gives isn't known. An operator
  that compares what the database and .NET don't compare alike (strings by collation, rows by every column), and
  `RightJoin`, say nothing of what they give, as a library call. `Distinct` and `Contains` of values
  compared alike are LINQ's (`Distinct` in no order); a join on nullable keys matches none that is null. With SQL's
  nulls (`UseRelationalNulls`), `==` and `!=` where a nullable value is null are unknown, for each comparison. A row
  version written is CSV1034 where it's written. CSV1036 is the static check's, as for every method Boogie verifies.
- A compiled query (`EF.CompileQuery`, a static readonly field of this file) of a value, called, is the query its
  lambda writes, on the arguments; of a sequence, a library call that says nothing of its rows.
- A call EF translates to SQL in a database query's lambda that the kernel has no function of (`c.Name.ToUpper()`)
  is the database's function of its arguments (`$db.`*member*), apart from C#'s: SQL's `UPPER` needn't be .NET's.
- With SQL's nulls (`UseRelationalNulls`), objects compared in a database query's lambda (`o.Customer == c`) are SQL's
  unknown where one that may be null is, as strings and nullable values are; against the literal null, `IS NULL`, exact.

**Opaque library values.** A `DateTime` is an `int` the kernel keeps but doesn't compute with: a field holds it, a
parameter takes it, a call gives it, and an EF concurrency token is compared by it. That int is its `Ticks`, so
`==`, `!=`, `<` and the rest of two `DateTime`s, or two `TimeSpan`s, compare it, as .NET's do, and `.Ticks` is it;
their other operators and members are not translated (CSV1902).

**Library nullness.** A library member's non-nullable result is not null, an out
parameter `[MaybeNullWhen(b)]` is not null where the member returns `!b` (in a collection stub's procedure too), a
`[NotNull]` argument is not null after the call, a `[NotNullWhen(b)]` one where it returns `b`, and an argument for a
parameter that isn't nullable is checked (CSV1014). A null check's message says where the null may come from (a
parameter declared nullable, a call that may return null, a call between a check of a field and its use).

**Library calls without a stub.** A library member with neither a stub nor sources is a library call: what it is
handed decides what it may change. It may write the arrays it's handed (any of the element maps, then) where the
Engine's analysis says it may write memory (`MayWriteHeap`), and anything where what it's handed may run
the program's code or reach a model (`WritesFieldsAt`: `$havoc`); nothing else. One handed a `Func` or an `Action`
(`Array.Exists(a, x => x > 0)`) may call it on anything: the lambda's body is verified for every argument, and what
it may change changes; one that runs it alongside (a task's, a timer's) isn't translated. Its `ref` and `out` arguments and its
result are values not known, not null where they're declared so; its receiver mustn't be null (CSV1013). A library
object (`Random`) is a reference, its `new` a new one; an argument boxed to `object` for it is evaluated as what it is.
Where exceptions are seen it may throw, once it has done what it does (a fork to the handlers). A collection's element
written with a value that branches (`d[k] = c ? a : b`) is its setter's call, of its receiver and index as they are
then. Not yet where cells are held (array mode, `Mem`'s views).

**Manual memory.** ATS's views of `Mem`'s cells: the cells are the element maps' rows at
`null` (`$E.Int32[null][a]`), and a view holds permissions to its cells as `Spec.Acc` holds an array's (array mode).
A `Ptr<T>`, `PointsTo<T>`, `ArrayView<T>`, `ArrayHole<T>` or `FreeGc<T>` of scalars is a value whose ghost properties
are functions of it (`$mem.Addr`, `$mem.Length`, `$mem.Index`, `$mem.Value.Int32`, `$mem.Elems.Int32`); a `Seq<T>` of
scalars is an `[int]` map. A view parameter holds its cells (`[Addr, Addr + Length)`, one for `PointsTo`, a hole's all
but its index): a `Spec.Acc` of them in its method's requires, and in its ensures where it's lent (`ref`, `in`) or
given (`out`, a result), so two views in hand are of different cells, and a call changes only the cells it gets. A view
that comes into hand (on entry, from a call, from `Mem`) says what its cells hold: its `Value` or `Elems` is the
memory there. `Mem`'s operations are its contracts, lowered at their instantiation: `Alloc` and `AllocArray` grant new
cells (not held before) and write them, `Read` and `Get` read the view, `Write` and `Set` write the view and the
memory, `Free` and `FreeArray` give the cells up, and `Split`, `Join`, `TakeOut`, `PutBack` (and `LengthIsNatural`)
trade views without touching memory; `p.Offset(k)` is `Addr + k`. Their preconditions are CSV1001. A new view's room is
said at the first cells of the views granted before it too (two intervals overlap only where one starts inside the
other). The cells live (`$live`) are those held on entry and those `Mem` grants, less those it frees: a view given
back (`ref`, `out`, a result) is of live cells. Linearity (a view used once, given back) is the analyzer's (CSV0001 and on); a call
that gives one variable by `ref` twice isn't translated.

**ref and out parameters.** A `ref` parameter comes in as `p$x$in` and goes out as `p$x` (a requires, and `old`, read
`p$x$in`); an `out` one only goes out. A `ref` or `out` argument is a local or a `ref`/`out` parameter, which the call
assigns, or an array's cell or a struct's member: a variable of the callee's, copied in and written back after the
call, which is what happens where the callee doesn't touch arrays itself (one that may is refused, CSV1901). Two arguments by reference that might be the same cell or variable are
CSV1020.

**Parameters the body assigns.** Boogie's parameters are constants, so a by-value parameter the body writes is a local
of the body, `p$x$v`, which starts as `p$x`. The contract is read of the parameter: a precondition, and `old(x)`, are
of its value at entry. A postcondition is checked at each return of the local (the
parameter's value then). Callers don't see that value, so a postcondition that names such a parameter (outside
`old`) isn't one they assume. A lambda that reads one reads its own input, the value when it runs (the parameter
isn't steady, so the lambda's postconditions don't name it); one a lambda or local function writes is, like a local
it writes, forgotten after each call that may run it.

**Strings.** As [the semantics](semantics.md#strings) says, a string is its value: a `Ref` (so that null is one), with
a length `slen(s)` and UTF-16 code units `sat(s, i)` in `0..65535`, functions of the value. A literal is a unique
constant of its own, not null, of its length and characters. `a + b` is `scat(a, b)`: not null, its characters `a`'s
then `b`'s (null counts as empty); a concatenation too long for a string throws, which ends the path. `==`, `!=` and
ordinal `Equals` compare values; where two strings are compared, two different ones of one length differ at some
index (`sdiff`), so a string is its characters. `s.Length` and `s[i]` are checked not null (CSV1013) and in bounds
(CSV1003). A `[Pure]` member of string with a stub contract (`Substring`, `IndexOf`, `Contains`, `StartsWith` with
`StringComparison.Ordinal`, ...) is a Boogie function of its arguments, its postconditions axioms where its
preconditions hold, its non-nullable result not null; a call checks its receiver (CSV1013) and its precondition
(CSV1001). A string as an object (`(object)s`, `ReferenceEquals`) is a reference whose contents are `$strOf(o)`:
the same object is the same string; equal strings may be different objects. Other library members of string, without a stub, aren't translated.

**Quantifiers in code.** A `Spec.Forall` or `Spec.Exists` in code (a `[Pure]` or ghost function's body) is
mathematics, read as the source has it; its body's checks (null, bounds, division, a function's precondition) are
asserted for every value in its range, under the conditions before them.

**Inheritance.** A class of the subset may derive from another, and have virtual, abstract and override methods (an
override only of the program's members, an abstract member's contract from its contract class), as
[objects.md](objects.md#object-oriented-code) says:
- a call is of the member as bound there: its procedure, whose contract every override keeps (behavioural
  subtyping); an abstract member is a procedure with no body;
- an override inherits its bases' contracts: their postconditions always (where it weakened the precondition,
  promised only where the base's held on entry: `old(requires) ==> ensures`), their precondition when it gives
  none; a base's contract names its parameters, which are the override's by position;
- in its `$wf` procedure, where its own precondition isn't assumed, an override's precondition follows from each
  base's, and its `Spec.Modifies` lies within theirs (CSV1018);
- a virtual member's procedure modifies what any of its overrides writes, and everything
  where it has no `Spec.Modifies` (an override not seen may write anything);
- `base(...)` in a constructor calls the base class's constructor on `this`; a new object's fields, inherited ones
  too, are their defaults; a constructor ensures the non-nullable fields it sets aren't null.

- interfaces of the program's (abstract members only, their contracts from a contract class; `[RunsConcurrently]` too)
  are references, as parameters, locals, fields and results; their members are procedures with no body, and an
  implementation inherits their contracts as an override does. A member that returns a task is awaited as an async
  method of the program is: a call of it, its contract of the task's result, other code running meanwhile (what the
  method doesn't hold is forgotten, its confined objects kept);
- a property with code (or an abstract or an interface one) is its accessors: a read calls its getter, a write its
  setter; a `[Pure]` one is a function; an abstract or virtual `[Pure]` member is a function of its contract alone (an
  override may answer the call), of every field the program names, with no definition;
- on `this`, a member whose override in this class (or a base) is sealed, or whose class is, is that override;
  a contract class's member is the member it specifies;
- `Spec.Reads(R)` of a `[Pure]` member is Dafny's frame axiom: two memories that agree on every object in `R` give it
  one value; its body reads only objects in `R` (CSV1017).

An immutable class (each instance field readonly) may have `[Invariant]`s, as a data type does. Each constructor
proves them at every return (CSV1015, "when the constructor of C returns"). They are assumed of every object of the
class that comes in: a parameter, `this` (except in an invariant, or what one calls), a field read, a call's result,
a new object. `object` is a reference type of the subset.

**Resolved by class.** A virtual `[Pure]` function called on a local that every write gives an object of one class
(`Shape s = new Square(3); s.Area()`: its declaration, assignments, `ref` and `out` too, each a `new Square(...)`) is
that class's implementation, whose body answers. A procedure called so is called by the
contract of the member as bound (the override's contract would prove more); a local
given objects of different classes, or one made elsewhere too, is not translated (CSV1902).

**Generic classes.** A class with type parameters (`Cell<T>`) is one class: its procedures and field maps are the
definition's, and a field of `T` holds a `Box`, as generic data's do. Where it's used at a type (`Cell<int>`), a read
of that field unboxes (`$unbox.int`), a write, an argument and a constructor's argument box, a result unboxes; the
arguments must be values that box (scalars, references, data, type parameters). A new object's field of `T` is the
default of a `T` the class doesn't know: a box nothing is known of, so a caller learns its value only from contracts.

**Constrained type parameters.** A type parameter constrained to references (`where T : class`, or to interfaces and
classes of the program's: `where T : IKeyed`) has references for values: `Ref`, not boxes; its members are its
constraints' (`a.Key()` calls `IKeyed.Key`). Its instantiations must be references (a call of a generic method with
others is not translated). A value of a type parameter may be null even under `where T : class`
(`K?` instantiates it), so dereferencing one is checked (CSV1013). Generic instance methods, not virtual, are
procedures as generic static ones are. A generic interface (`IKey<T>`) is one interface, as a generic class is one
class, its contract class `[ContractClassFor(typeof(IKey<>))]`. Well-formedness is coinductive: a constraint that
names its own parameter (`where T : IKey<T>`), or a class that instantiates an interface with itself
(`Kk : IKey<Kk>`), is checked assuming the type it is checking.

**Arrays of objects.** An array of references (`Shape[]`, `string[]`, `string?[]`, `object[]`, an interface's) has its
elements in one map, `$E.Object: [Ref][int]Ref`, beside the scalars' maps; a new one's elements are null. An element
read in code is allocated where it isn't null, as a field's value is, and of its class's invariant. An element may be
null whatever its type says (C# lets `new string[n]` hold nulls): a precondition rules nulls
out. Array covariance isn't checked (a `Square[]` passed as a `Shape[]` and given a `Rectangle`). A null pattern of a reference (`x is null`, `is not null`, `is { } y`, `is C y` of its own class) is
a null test.

A `[Pure]` member whose every override is `[Pure]` writes nothing when called, whichever override runs.

**Dynamic types.** Objects of the program's classes and interfaces (not generic, not `object`, a record, an exception
or a delegate) have the exceptions' `dtype` and `sub`: `o is C` is `o != null &&
sub(dtype(o), T#C)`; `new C(...)` is exactly a C (`dtype(o) == T#C`); in code, a value of a static type is an instance
of it where it's tested (a fact assumed there; in a specification none is needed). `sub` is C#'s derivation, base
types and interfaces; unrelated classes have no instance in common, nor have a sealed type and one not above it, and a
sealed type's instances are of it exactly. Type tests (`is C`, `is C x`, `is not C`, `switch` on them), `as` (`o`
where it's an instance, else null) and casts (`(C)o`: in code it throws unless `o` is null or an instance;
an upcast written as a cast, `(object)o`, is `o`). A `[Pure]` virtual or abstract member
called on another object is its function, which each `[Pure]` override defines for objects of exactly its class
(`dtype(this) == T#D ==> f$B(..) == f$D(..)`).

**Patterns.** Besides the null patterns: a class's property pattern (`p is { Age: >= 18 }`: not null, each field
read unchecked); an array's list pattern (`a is [1, .., 9]`, `[_, 0]`, `[>= 9, ..]`: not null, of the length,
each element as its pattern says, those after a slice counted from the end; in code, a slice with a pattern of its own
(`.. var rest`) matches a new array of the elements between, as C#'s `GetSubArray` makes, which in a specification
isn't translated; `a is [1, ..] b` binds `b` to the array); a string's constant pattern (`s is "a"`, a string's value).

**Frames.** `Spec.Modifies(W)`, Dafny's dynamic frames: `W` is an `ObjSet` (`ObjSet.Empty`, `ObjSet.Of(x)`, `.Add(x)`,
`.Union(s)`, `.Contains(x)`), a `[Ref]bool`. Its procedure writes a field or an array's cell only of an object in `W`
as it was on entry (`w$entry`), or allocated since (CSV1017; a constructor's own object counts as new); it calls only
what writes within that: a callee's frame inside ours, or none needed (a callee that may write fields or arrays without
one is CSV1017). It ensures every field and cell of an object allocated before the call, and not in `old(W)`, is as it
was. `[Owned]` classes are framed by their views instead.

A ghost `ObjSet` field (`Ghost<ObjSet> Repr`, the Dafny tutorial's representation set) is a field map of `[Ref]bool`
values, empty by default; `ObjSet`'s members and `==` are mathematics in ghost code too, and `Spec.Fresh(s)` says every
object in `s` is new since entry (a constructor's own object counts as new). A new object's reference fields are
allocated or null after its constructor, and its `ObjSet` fields hold allocated objects: a constructor could store
nothing else. A predicate's body's facts, and what a field read in a specification says (a reference allocated, a
non-nullable field set), are assumed where an instance is unfolded or inhaled.

`Own.Tree(x)` is `x`'s tree (`$tree`), or `{x}` where the program has no `[Owns]` fields; with `Spec.Modifies` a method
borrows it: it writes the tree's objects without their views, and can't fold them away (CSV1016); its caller lends
the tree only where the root's view is in hand. An `[Owns]` field's object is in its owner's tree (free at entry and
exit), an owned query (a `[Pure]` member of an owned receiver) reads its tree (CSV1017), and a call that keeps a
tree keeps what its owned queries say of it. An exclusive predicate is inhaled only where none of its instances is
held.

**Calls and frames.** A call of another translated method is a Boogie `call`. A procedure `modifies` the maps it
writes (an element map, a field map, or `$Alloc` when it allocates), and those of everything it calls; after a call,
what the callee modifies is unknown. Allocation
only grows: `free ensures (forall r: Ref :: old($Alloc[r]) ==> $Alloc[r])`. A field written only at objects allocated
since the call began (a constructor's own object, or a new one's defaults) is unchanged at every other:
`free ensures (forall o: Ref :: old($Alloc[o]) ==> $F.C.f[o] == old($F.C.f[o]))`: a constructor's writes to its own
object aren't the caller's. A method without `Spec.Modifies` that writes only arrays it
makes (`MayWriteHeap` infers it) leaves every array allocated before as it was (a free
postcondition), and so may be called under a caller's `Spec.Modifies`. Dafny's good heap: a reference in a field of an
allocated object is to an allocated object (`free requires`, and `free ensures` of the fields a procedure modifies), so
a new object is none of them.

**Methods whose bodies don't translate.** A method whose contract translates but whose body doesn't is a procedure of
its contract alone for its callers (as an abstract member is), so they are Boogie's still; it may write what the
effects analysis (`FieldEffects`) says it and its callees write (any field, where that says so), and every array
unless it writes none (`MayWriteHeap`). Its own body is not verified (CSV1902, saying why).

**Loops and arrays.** Boogie forgets at a loop head every map the loop modifies. A loop frame keeps the rest: only the
arrays the loop writes through a variable it doesn't change are forgotten (and all of them where it writes through
anything else, or calls what writes arrays). So the translation snapshots the maps on the way into the loop (`s$`*h*`$E.T`) and assumes at
its head that every array allocated then, other than those, is as it was. A confined local's object (one the method
made and never hands on) that the loop doesn't reassign is as it was on the way in, but for what the loop writes
through that local, even where the loop awaits or calls what may change anything (`c$`*h* snapshots of every map).

**Loop facts.** A `for`, `while` or `do` loop without invariants gets facts inferred for it
(Lowering.LoopFacts): from its condition (`i < n` suggests `i <= n` at the head) and, for each integer in it,
that it never goes below, or above, its value on entry (taken on each way in). Each is an assertion at the head, an
invariant to Boogie. One that fails (on entry, or at a back edge) is left out (its line is `assert true;`) and the
program verified again, until every fact assumed held; that run's failures
are what's reported. (Houdini's `/contractInfer` does the same, but which failures it reports varied from run to run.)

**Exceptions.** A method is verified for partial correctness on its exceptional paths too: they are checked only
where something sees them, a `catch` or a `Spec.EnsuresOnThrow`. Exceptions are references, of a type given by
`dtype(r): Ty`; each exception type named is a `const unique T#…: Ty`, `sub` is C#'s derivation between them (axioms
from Roslyn's base types, reflexive and transitive), and every type derives from `System.Exception` (every
exception type, where classes have dynamic types too: see "Dynamic types").
- `throw e` checks `e` isn't null (CSV1013), puts it in `ex$`, and jumps to the innermost handler; `new E(...)` of an
  exception type is a fresh reference with `dtype` `T#E` (its arguments evaluated, nothing else of it known).
- A `try` with catches is a dispatch: for each `catch (E)` in order, a block that assumes `sub(dtype(ex$), T#E)` and
  goes to the handler, and one that assumes it doesn't and goes on to the next; past the last, outward (the enclosing
  `try`'s dispatch, or the method's exit). `catch (Exception)` and `catch` take everything; `throw;` rethrows `ex$`.
- A call where an exception would be seen forks before it: one way, `call ex$ := P$throws(args)`, a twin procedure
  with the callee's inputs, its `modifies`, and only `free ensures (sub(dtype(ex), T#E) ==> cond)` of its
  `Spec.EnsuresOnThrow<E>(cond)` clauses (none of its postconditions), then the jump; the other, the call. Checked
  arithmetic out of range, and `int.MinValue / -1`, fork the same way with an `OverflowException`.
- The method's exit for exceptions (`x$exit`, where no handler catches) asserts each `Spec.EnsuresOnThrow<E>(cond)`
  as `sub(dtype(ex$), T#E) ==> cond`, with `Spec.Old` of the entry state (CSV1002).
- Where nothing sees an exception (no enclosing `catch`, no `EnsuresOnThrow`), a throw ends the path;
  proofs (lemmas, `[Pure]` and ghost code) never throw.

- A `finally` runs on every way out of its `try`: each edge that leaves it (a fall-through, a `return`, a `break`, a
  jump out of a loop) sets the finally's continuation `fin$`*n* to a number of its own and goes to the finally; the
  finally's end goes on, by that number, to where the edge was going (through the next finally out, for nested ones). A
  throw in the `try` runs it too, then goes on outward (to the handlers around it, the method's exit, or nowhere);
  inside a `try` with a `finally`, exceptions are seen, so calls and checked arithmetic fork as they do in a `try` with
  catches. A `return`'s value is kept before the finally runs.
- `using` is its `try`/`finally`: the resource disposed if it isn't null. A program class may implement `IDisposable`;
  its `Dispose` called through the interface, as `using` calls it, is code whose contract isn't known (its contract is
  partly the library interface's), so it may change anything (`$havoc`), as for a delegate.

- An exception filter (`catch (E e) when (cond)`): the handler's type is tested, then its filter runs; false, the
  exception goes on to the next handler (or outward) as if the type hadn't matched. An exception thrown inside a filter
  makes it false, as in .NET.

- A program's exception class is a class: its fields are on the heap, `new E(...)` runs its constructor (a library
  base's constructor, `base(message)`, keeps nothing), and it has `dtype` and `sub` like any class, so `catch`, `is`,
  `as` and casts test it. A library exception's members (`Message`) are unknown values (CSV1900).

**foreach.** A `foreach` over a one-dimensional array or a string is what C# compiles it to: the collection
evaluated once into `fe$`*n*`$a` (its length read, so a null one is CSV1013), an index `fe$`*n*`$i` from 0, the head's
`MoveNext()` the test `i < len(a)`, `Current` the element `a[i]` (widened to the iteration variable's type), and every
edge back to the head (the body's end, a `continue`) `i := i + 1`. The enumerator's `try`/`finally`, which disposes it,
isn't there: C# emits none for an array. `Spec.Index(x)` is the index: the number of elements gone through in the
loop's invariants, and `x`'s own in the body. The loop's first invariant is `0 <= i && i <= len(a)`, which holds by
itself.

A `foreach` over a collection: a `List<T>` whose loop changes no list (it calls only specifications, `[Pure]` members and lists'
`[Pure]` members) is the same loop over the list's model: the index up to `Size()`, each element `Items()[i]`, and
`Spec.Index` the index. A loop that may change a list, and one over any other collection, goes through the
enumerator, as C# does: `GetEnumerator()` keeps the collection's `Version()`, each `MoveNext()` checks the
collection's is still that (else it throws: CSV1001) and gives an unknown answer, and `Current` is unknown, but for a
dictionary's: a pair it has (`Domain[key]`, and `Entries[key]` its value; a `KeyValuePair`'s `Key` and `Value` are
functions of it, `$kvp.Key.`*K* and `$kvp.Value.`*V*). `Spec.Index` of such a loop is the number of edges back to
its head, as for an array, at most the `Count` the collection had where the loop began (`fe$`*n*`$c`): `MoveNext`
gives another only while fewer have gone, and, where the `Count` is still that, all of them (a dictionary's `Remove`
may go on while it's enumerated, so fewer may be given). A dictionary's `Keys` or `Values` are enumerated as the
dictionary is; a query's, or an interface's list's, elements are read where the loop starts; any other `IEnumerable<T>`
is an enumerator whose elements aren't known (see Iterators).

**Collections.** A `List<T>`, `Dictionary<K, V>`, `HashSet<T>`, `Stack<T>` or `Queue<T>` of the subset's values is an object whose contents
are CsVerify.Bcl's models: maps as fields are, `$F.$M.Size: [Ref]int` (never negative), `$F.$M.Version: [Ref]int`, and
per kind of value `$F.$M.Items.`*T*`: [Ref][int]`*T* (a list's, stack's or queue's), `$F.$M.Members.`*T*`: [Ref][T]bool`
(a set's), `$F.$M.Domain.`*K*`: [Ref][K]bool` and `$F.$M.Entries.`*K*`.`*V*`: [Ref][K]V` (a dictionary's), an integer
type's values in its range, so frames, modifies clauses and delegates' states take them in as they do fields. In
specifications the models read them, `Count` is `Size`, `l[i]` is `Items[l][i]` (well-defined where `0 <= i < Size`,
CSV1012), `d[k]` is `Entries[d][k]` (where `Domain[d][k]`), `d.ContainsKey(k)` is `Domain[d][k]`, and `s.Contains(x)`
is `Members[s][x]`. A `StringBuilder` is a collection of one model, its length (`Size`), and a `TextWriter` one of
none: their members are their stubs', as a list's are, and a stub without `Spec.Modifies` changes nothing (unless it
may run the program's code). `Array.Fill(a, v)` is its stub: `a`'s row a map that is `v`
everywhere, the rest as it was. A list stub's `T[]` (`ToArray`'s) is an array of the list's element type. A `Map<K, V>` is a Boogie map (`m[k]`, `Update`, `Map.Const`, `==`), and a `Ghost<T>`'s `Value`
the value.

A dictionary's string keys (a set's string members) index the models by reference, as every string is: a string is
its characters, so two of one content are one reference where the verifier knows it. A key given to a collection's
member, or read in a specification (`d[k]`, `d.ContainsKey(k)`, `s.Contains(x)`), is `$keyed(k)`: the string itself,
marked; any two marked keys get the fact assumed where two strings are compared (of one length and
different, they differ at some index), so `d["a"]` and `d[x]` where `x == "a"` are one entry, and only keys pay for it.

A `foreach` over a dictionary's `Keys` or `Values` enumerates the dictionary (its version checked at each `MoveNext`,
CSV1001): a key is one it has, never null; a value isn't known. `Keys.Count` and
`Values.Count` are its `Count`.

Through their interfaces (`IList<T>`, `IReadOnlyList<T>`, `ICollection<T>`, `IReadOnlyCollection<T>`), a collection is
a reference of one of three kinds: an array (`$arr`), a modeled collection (`$coll`: a `List`'s, or another's whose
`Count` is `Size`), or anything else; a conversion from an array or a collection says which. `Count` is
`if $arr(x) then len(x) else if $coll(x) then Size[x] else $ocount(x, $st(...))`, and `x[i]` the array's cell, the
list's `Items`, or `$oitem(x, i, $st(...))`: a value of the whole state, so the same until something changes (an
`l.Clear()` of a list that `x` may be changes `x.Count`). Where the program implements one of
these interfaces itself, each read through them is a new unknown. `x[i]` checks `0 <= i < Count` (CSV1003). Writes
through `IList`/`ICollection` (`Add`, `Insert`, `Remove`, `RemoveAt`, `Clear`, `x[i] = v`) branch on the three kinds: an
array's throw `NotSupportedException` (its indexer writes its cell), a `List`'s are its stub's, anything else's are
library calls that may change anything. Other members (`Contains`, `IndexOf`) and `foreach` over them are library
calls: values not known.

**Multisets.** A `Bag` is an `[int]int` map from value to count: `Bag.Empty` (`$bag.empty`), `Bag.Of(x)`, `Add`
(`$badd`), `Union` (`$bunion`), `Count(x)` (a read), `Contains(x)` (`0 <` its count), `==`. `Spec.Multiset(a, n)` of an
integer array is `$bag(ly, $E.T[a], n)`, well-defined where `a` isn't null and `0 <= n <= a.Length` (CSV1012; in ghost
code CSV1013 and CSV1003), with axioms: the empty prefix is the empty bag, and a write inside the
prefix trades the old element for the new one, outside it changes nothing. Each is triggered only by the multiset of
a written array. A use unfolds one element (`$LS($LZ)`, Dafny's fuel), and every element where `n` is a small
constant (a concrete array). So a swap keeps the multiset with no lemma, and the sorts prove they permute.

A `Seq<T>` is an `[int]` map:
`s[i]`, `s.Update(i, v)` (a store), `s.Drop(k)` and `s.Concat(k, t)` (lambdas), `Seq.Const(v)`, `==`; `Ghost.Of(x)`
is `x`, and `Spec.Equal` is `==`. In code every member of a collection is a call of a procedure of its stub contract
(`ListContracts<T>`, `DictionaryContracts<K, V>`, …, its `@this` the receiver, its type parameters the collection's
arguments), named for the collection's type: `Count`, the indexers (CSV1001 out of range or for a missing key), `Add`,
`TryGetValue`, `Remove`, `Push`, … modify only their own collection's models (their `Spec.Modifies`), and a
constructor returns a new collection. `Spec.Old` of a list's element is well-defined where it was in the old state.

**Delegates, with frames.** A lambda with `Spec.Reads` has its precondition, and, where it changes nothing and reads
only its frame, its postconditions and the value it returns (an expression, or specifications and a return), as
functions of any state (`$preS`, `$postS` over `$st.M(s)`), so a call after a write outside its frame still knows them.
A lambda that reads nothing gives its value too where its body is specifications and a return.

**Delegates.** A `Func` or an `Action` of the subset's values is a reference; what it accepts, gives and changes are
functions of it and the arguments, per signature (`Int32.Int32` for `Func<int, int>`), as Dafny's `f.requires` and
`f.ensures` of its `->` arrows, the same in every state:
- `Spec.Pre(f, x)` is `$pre.K(f, x)`, `Spec.Post(f, x, r)` is `$post.K(f, x, r)`, `Spec.Total(f)` is `$total.K(f)`
  (an axiom makes it `$pre.K(f, x)` for every `x`), and `Spec.ChangesNothing(f)` is `$nochange(f)`.
- A call `f(x)` checks `f` isn't null (CSV1013) and `$pre.K(f, x)` (CSV1001), then is `call r := $call.K(f, x)`: a
  procedure that may modify everything, ensures `$post.K(f, x, r)`, `r` in its type's range, and every map as it was
  where `$nochange(f)`. A method that calls one modifies everything (its callers' frames too), and a loop that does
  keeps no arrays.
- A lambda made one is a new reference (allocated, so no other delegate's facts are its) with, for every argument,
  `$pre` its `Spec.Requires` (or `true`), `$post` (with `$pre`) implying its postconditions and an expression's value,
  and `$nochange` if it writes no field, cell or object and calls only what's `[Pure]`. They count only as far as they
  depend on its parameters, constants, `this`, and variables never written after they're declared (the rest is left
  out); a precondition that depends on more is of the state it's made in where the lambda says what it reads
  (`Spec.Reads`, below), and CSV1029 where it doesn't. Its body is verified on its own.
- A method whose specifications speak of a parameter's `Spec.Pre`, `Spec.Post` or `Spec.Total` (and not of what it
  reads) takes it to be the same in every state: `$steady(p)` at entry, and each call of it asserts `$steady` of the
  argument (CSV1001). A lambda or method group that reads no state is steady.
- A state is `$st(`*every element and field map*`)`, of type `St`, with each map given back (`$st.$F.C.f(s)`). In a
  state, a delegate accepts `$preS.K(d, s, x)`, gives `$postS.K(d, s, x, r)` and reads `$readsS.K(d, s, x)` (a
  `[Ref]bool`); a steady one's are its `$pre` and `$post` and it reads nothing. Dafny's frame axiom: two states that
  agree on every field and cell of the objects it reads in the first give it the same `$preS`, `$postS` and reads
  (triggered on a pair of its terms). A call asserts `$preS` in the
  state it's made in, and ensures `$postS` of the state before it.
- `Spec.ReadsOf(f, x)` is `$readsS.K(f, now, x)`; `Spec.Reads(f, x => S)` is `forall x :: $readsS.K(f, now, x) ⊆ S`,
  and `Spec.Changes(f, x => S)` is `forall x :: $frame.K(f, x) ⊆ S`: a call keeps every field and cell of an object
  allocated before and not in `$frame.K(f, x)`, and `$nochange(f)` makes the frame empty. `ObjSet`'s `IsSubsetOf`
  and `IsDisjointFrom` are the set relations.
- A lambda whose precondition reads fields or cells says so with its own `Spec.Reads(R)`: its `$preS` in the state it's
  made in is its precondition, it reads within `R`, and each object its precondition reads must be in `R` (CSV1029).
  Without one, it is reported (CSV1029) and nothing is known of it. Its own `Spec.Modifies(S)` is its `$frame`.
- A method group of a static method gives its contract (precondition and postconditions, as far as they're steady),
  and changes nothing if it's `[Pure]`.
- A delegate type of the program with a contract (`[ContractClassFor]`): its `Invoke` is a procedure of the contract
  alone, as an interface member is, which modifies everything; a call of one is a call of it, and a lambda made one is
  a new reference (proved against the contract on its own).
- A local a lambda (or a local function) writes is forgotten after every call that may run it: any but a `[Pure]`
  function's or a lemma's.

A method group of an instance method (`a.Twice`) evaluates `a` where the delegate is made (CSV1013 if it may be null)
and is the method's contract with `this` that object; as for a static one, a precondition that reads state isn't
translated. A delegate called inside a `try` may throw, to its handlers.

Not yet: `Spec.Total` of a delegate that may read state, a method group of a generic method or one made a delegate
type with a contract, and delegates with permissions or method `Spec.Modifies`.

**Data types.** A data record (a closed hierarchy of positional records) is Dafny's
datatype. A value is a reference (null too) made by its case's constructor function `mk.`*C*`(fields)`: not null, its
tag (`$tag`, tested by `$is.`*C*) the case's, each field (a function `$d.`*R.f*, a base's field the argument the
record header gives it, as `Ind(Fact Prev) : Fact(Prev.N + 1, ...)`) what was given, and its rank (`$rank`, never
negative) above its data parts'. A value of a case is that case's constructor of its fields (triggered on `$is.`*C*),
so equal fields mean equal values, and a record's `==` (where its fields compare as values) is the references' `==`.
- A field of a data type is one of its cases (said by its tag, `$tag(f) == 3`: a test `$is.`*C*`(f)` would trigger
  the case's constructor of `f`'s fields, whose fields' cases would trigger more without end, a matching loop that a
  failing proof never saturates), and not null where its type says so (each construction checks its arguments,
  CSV1014); an integer one is in its type's range. A parameter, `this` and a result are of their type's
  cases.
- Type tests (`is`, `switch` statements and expressions) and patterns (declaration, type, constant, relational,
  `var`, discard, `not`, `and`, `or`, positional and property patterns) test tags and fields and bind their variables;
  a specification's `switch` is an `if`-chain. A cast to a case: in code, where it fails it throws; in a proof, CSV1011.
- `Spec.Decreases(d)` of a data value is its rank. A lemma or `[Pure]` function that may throw (a `switch` without
  a case) is CSV1011.
- Instance members of a data record are procedures (and functions) on `this`, a value.
- A record's `[Invariant]`s (of its fields, and of functions of values: static ones whose parameters are data or
  scalars, `Math.Max`, `Min` and `Abs`) hold of its values. Each construction checks them (CSV1015). A value that
  comes in (a parameter, `this`, a call's result, a field read in code, a constructed one, one a pattern binds) is
  `$valid.`*T*, which gives its invariants. Where a case is tested, it also gives its parts' validity, and a base
  type's validity is its cases' (`$valid.Ins(d) && $is.Viol(d) ==> $valid.Viol(d)`). The functions an invariant calls
  read no arrays, so its axiom names no memory. An invariant that reads mutable state is reported from its
  declaration by `StaticChecks` (CSV1015). A value's validity then says nothing of it,
  which is sound, and a construction still checks it.
- A record as an `object` is an object of its own: a reference not null, which no other is known to be, even when
  their values are equal (records have no identity CsVerify models).
- A closed base's constructor that does nothing (`private Avl() { }`) is a procedure of no statements.
- `Ghost<T>` is erased: `Ghost.Of(x)` and `g.Value` are the value.

**Generics.** A type parameter's values are boxes (`Box`); `$box.`*T* and `$unbox.`*T* (each the other's inverse)
take an integer, a boolean or a reference to a box and back where generic code meets code of a type argument: a
generic method's arguments and result, a generic data type's fields. A generic data type is one data type for all its
instantiations (`List<T>.Cons` of a `List<int>`), and a static generic method (of unconstrained type parameters) is one
procedure.

**Async.** An async method's contract is of its task's result (`T` of `Task<T>`, nothing of `Task`), its procedure's
`result`. `await F(...)` of an async method of the program is a call of it; `await Task.Yield()`, `Task.Delay(...)`
and `Task.CompletedTask` give nothing; `ConfigureAwait` is seen through. At every await other code may run: `call
$await(k)` may change every map but at the objects in `k`, the method's confined locals (each starts null, and only ever
holds a new object or array whose construction doesn't let it out, used only by its fields, cells, null tests,
specifications and `return`); and the locals lambdas write are forgotten. Where
exceptions are seen, a library's await may throw (a fork, as a call's). A call of an async method keeps the caller's
confined objects as they were (no code can reach them).
- **Tasks awaited later.** `var t = F(...)` checks `F`'s precondition there; its result is the task's, given by `await
  t`, `await Task.WhenAll(t, ...)` and, once awaited, `t.Result` (before: CSV1026, it blocks). A ghost `aw$`*n* says
  whether it has been awaited: each return asserts it (CSV1026, "might not be awaited on every path"), and while one
  isn't, every statement is followed by `call $awaitIf(running, k)`, which may change what the method doesn't hold.
- **`Task.Run` and threads.** `Task.Run(() => F(...))`, and `new Thread(() => F(...))` with its `Start()` and
  `Join()`, are tasks: of the call, proved where it starts (a callee of permissions, values
  that don't change), else of code verified on its own, whose result isn't known and which may reach anything (no
  object is kept in hand from then on). A thread needn't be joined.
- **Concurrent code** (`[RunsConcurrently]`, or started alongside) must hold what it uses (CSV1027): a field that may
  change and that no lock guards, or an array's cell, is used only on an object a confined local has, or the one its
  constructor is building.

**Tasks started here.** A task of an async method, of `Task.Run`'s code, or a thread runs alongside the method from
its start to its await or join. Until then the method's uses of fields and arrays must be held (CSV1027, as for code
that runs concurrently: a confined local's object, a new object's initializer, a lock), the locals its code writes are
unknown at each statement, and what the two may race on is a warning (see the race warnings). Every task (a
`Task.Run`'s too, but not a thread) is awaited on every path, through a `finally` too (CSV1026); one started in a loop
is awaited before the next round starts another (checked at each way back to the head). A `Task.Run` of code that
returns a non-nullable type, or a delegate's task, gives a value that isn't null.

**Locks.** `lock (_lock) { ... }` of a lock object (a readonly `object` field of this object, or a static one) is its
`Monitor.Enter` and its `finally`'s `Monitor.Exit`. Entering forgets what the lock guards (`[GuardedBy]`, at this
object: others have had it) and gives its `[LockInvariant]`s; leaving proves them (CSV1024), on every way out,
exceptions included; a constructor's end proves its object's, and a static constructor's its type's static ones
(CSV1024). A lock of anything else (`lock (_forks[i])`, a `new object()` being a new reference) guards nothing the
kernel knows of and changes no state; it mustn't be null (CSV1013), and two nested locks of one array's elements are
taken in increasing order of index (CSV1025: the outer index must not change under the
lock). Whether each use of guarded state is under its
lock (CSV1023), and the other checks made from the syntax (lock levels, concurrency marks, flags, atomics, a data
type's invariant's dependence), are `StaticChecks`', which run for every method.
A `SemaphoreSlim` of count 1 that guards state is a lock that can be held across awaits: `await g.WaitAsync()` (or
`g.Wait()`) takes it as entering a lock does, an await inside its `try` keeps what it guards (nobody else can have it),
and `g.Release()` proves its invariants (CSV1024); a static gate's state is kept as an instance's, and a
`[GuardedBy(nameof(g))]` method's awaits keep it too (its caller holds the gate all along). Starting such a method's
task without awaiting it there is CSV1023: it would run alongside its caller. A semaphore that guards nothing (of any
count) changes nothing the kernel knows of. Taking it while it's held is reported by the static checks (CSV1025).
A lock statement inside one of the same lock, on the same object, changes nothing (a monitor is reentrant); a call
under a lock of what may enter it again (code of the program's not `[GuardedBy]` that lock, or a library member that
may run the program's code) needs its invariants at the call (CSV1024), as does a call of such code from a
`[GuardedBy]` method.

**Lock levels.** Locks may be taken one inside another, and code may be called under them: in which order levels
are taken, what a call may take (through every call, override and callback), delegates, waits under a lock, and
`Monitor.Wait`, are `StaticChecks`' (CSV1025), from the lock-level analysis (`LockLevels`). Boogie proves the rest: two locks of one `OrderedBy` field or class, of two objects (a variable's, a parameter's, a readonly field's,
or this), are taken in increasing order of their id, where both are taken (`from.Id < to.Id` before `lock (from.Lock)
lock (to.Lock)`) and at a call that takes the second of an argument (CSV1025). A lock may be another object's lock
field, its guarded fields forgotten at that object, or an object of a class with a level. A call under a lock that
takes the same object's lock again is fine (a monitor is reentrant); where the order of two objects' locks can't be
told (a call of what takes the second of something that isn't a local, a parameter or a field), CSV1025.

`Monitor.Wait(o)` gives `o`'s lock back and takes it again: its invariants are proved at the call (CSV1024), what it
guards is forgotten, and its invariants are assumed again; with a timeout it says whether it was pulsed (unknown).
`Pulse` and `PulseAll` change nothing here. That the lock is held, and nothing else is, are the static checks
(CSV1023, CSV1025).

**Tasks one is given.** A `Task` or `Task<T>` parameter or local not started here is a reference: `await t` lets other
code run (what the method doesn't hold is forgotten) and gives a value nothing is known of; `t.Wait()` is a library
call that changes nothing here, and `t.Result` a value not known.

**Atomic fields.** An `[Atomic(Step = nameof(S))]` field's map is what this thread last saw or wrote there. A read in
code first lets the others take steps (a fresh value, the same or `S(last, now)`), and is then known; a plain write is
proved a step from what it overwrites, which the others may have moved too (CSV1030); `Volatile.Read`/`Write` and
`Interlocked`'s `Read`, `Exchange`, `CompareExchange` (a step where it compares equal), `Increment`, `Decrement` and
`Add` (wrapping, as at run time) are each one step after the others'. A plain read or write of one that isn't
`volatile` is CSV1030. Wherever the field is forgotten (a call, an await, `$havoc`, a delegate's call) it went by
steps (free postconditions, at every object allocated before and at the statics'), and at every loop head it went
by steps since the loop was entered (a snapshot of its maps taken on the way in): each change of it is a step, and steps are transitive (proved by the static checks,
CSV1030). An atomic field needs no lock in concurrent code.

**Try-locks.** An `int` or `bool` flag that guards state is a lock taken by `Interlocked.Exchange(ref f, 1)` (or
`CompareExchange(ref f, 1, 0)`), which gives back what it was (unknown): on the edge of the `if` where it was free,
what it guards is forgotten and its invariants hold, as a lock's on entering; `Volatile.Write(ref f, 0)` (or
`Interlocked.Exchange(ref f, 0)`) gives it back, proving them (CSV1024). Taken again by the thread that holds it, it
isn't free. Whether it's taken and given back in that form (CSV1023) is the static checks'.

**Tasks with permissions.** A started task's postcondition may read only what never changes and what it gives back,
to its left (CSV1016 at the start: by the await, others may have changed the rest); a
task can't be given views or its `[Owned]` receiver (CSV1901). Code that runs alongside other code reads only cells
it holds (CSV1016). A task or thread of a callee whose contract names permissions (`Spec.Acc`) runs in two
phases, as a fork and a join: its start (`Task.Run(() => F(...))`, `new Thread(...).Start()`, a call `Task.WhenAll`
awaits, `var t = F(...)`) checks its preconditions there and gives it the permissions they ask for, and nothing
returns (`Task.WhenAll` starts each of its tasks before it joins any); its join (`await t`, `Task.WhenAll`, `Join()`) calls its twin `F$started`, whose preconditions are free (they
were checked), and takes back what its postconditions give. In between the method holds only what it kept. An await,
and each statement while a task runs, keeps what the method's permissions cover too: the cells it holds (`cells`), the
fields of the objects whose views it holds (`perm`). A task that fails gives nothing back: its await goes to the
handlers with what it read forgotten, and so does a join, of what the postconditions read but don't give back.

**Well-definedness.** A specification is checked well-defined where it's evaluated, as Dafny's are (CSV1012): for the
preconditions, in a procedure of their own (`P$wf`, given the parameters but not the preconditions, which `P` itself
assumes at entry), each under those before it; at each return for the postconditions, at the loop head for an
invariant, where an assertion is. Well-defined means an array read is in bounds and of an array that isn't null, a
divisor isn't zero, and a function's precondition holds where it's called; each under what `&&`, `||` and `?:` make
hold there, and over a quantifier's range. The check is `assert {:subsumption 0}`: not assumed after it, so what an
ill-defined specification says stays unknown.

**Quantifiers.** `Spec.Forall(lo, hi, k => P)` is `(forall q$k: int :: lo <= q$k && q$k < hi ==> P)`, and
`Spec.Exists` is the `exists` of `lo <= q$k && q$k < hi && P`.

**Functions.** A `[Pure]` or `[GhostFunction]` method whose body is one expression is also a Boogie function, as
Dafny's functions are: on a layer, the memory it reads (as Dafny's take `$Heap`), `this` for an instance one, and its
parameters. The memory is the field maps it (or a function it calls) names, and the element maps; but a function that
reads arrays only through its own array parameters takes those arrays' elements instead (`$E.Int32[a]`), so writing
another array leaves its value as it was. Its definition is an
axiom: where its precondition holds, its value on layer `$LS(ly)` is its body, whose calls are on layer `ly`. Another
axiom makes every layer's value the same. A specification calls it on `$LS($LZ)`, so each use unfolds the definition
once; only a call back into its recursion group is on the layer below (Dafny's rule), any
other has a specification's fuel. Under a quantifier, of its variable, an application's definition is unfolded once
for every value in the quantifier's range (an assumption where the specification is read, and at a call for the
callee's preconditions); that equation applies again to the applications in its
body, so recursion over a range unfolds as far as it needs to. Its postcondition is an axiom of every value where its precondition holds, and a
run-time `[Pure]` function's value is in its type's range. The method stays a procedure, which verifies the body and
says its result is the function's value on `$LS($LZ)` (so a call in code knows its body too). A `[GhostFunction]`, and a lemma, is ghost code: its arithmetic is
mathematical.

**Termination.** Ordinary methods are verified for partial correctness, so only what
`Spec.Decreases` gives is checked:
- a call back into its own recursion group (the methods that call each other), of a method with a measure from one
  with a measure: the callee's at the arguments, in the state at the call, below the caller's at entry (`old`, as
  Dafny's), lexicographically (CSV1008);
- a `[Pure]` method or a lemma that recurses without a measure doesn't terminate, which would make its definition
  unsound: CSV1011;
- a loop's `Spec.Decreases`: its value at the head of each iteration, and at each edge back to the head, below it
  (CSV1007).

Below is Dafny's rule: the value before isn't negative, and the one after is less (it may be negative: McCarthy's 91
function's `101 - n`). The measure's check isn't assumed after it (`{:subsumption 0}`), so the loop's invariant is
checked on the same edge whether or not the measure went down.

## The subset

So far: static methods, and instance methods and constructors of [plain classes](#the-translation-construct-by-construct),
over the C# integer types, `char`, `bool`, one-dimensional arrays of them and objects of those classes (parameters,
locals, results, fields), with arithmetic, conversions, comparisons, `if`, loops with invariants and measures, array
reads, writes, lengths and allocation, fields, object creation, calls of each other (recursive too), `Spec.Assert` and
`Spec.Assume`; `[Pure]` and `[GhostFunction]` methods, lemmas, `Spec.Decreases`; and in specifications `Spec.Forall`,
`Spec.Exists`, `Spec.Old`, `Spec.Result` and calls of functions.

Also `ref` and `out` parameters, `[Owned]` classes with their views and invariants, `Spec.Acc` of objects, and
predicates with `Spec.Fold` and `Spec.Unfold`, functions over them, array-cell and single-field permissions.

Also strings and the string members with stub contracts, and quantifiers in code.

Also inheritance: base classes, virtual, abstract and override methods, interfaces, properties with code, and
`Spec.Reads`.

Also exceptions: `throw`, `try`/`catch` by type, rethrow, `finally`, `using`, caught checked overflow, `Spec.EnsuresOnThrow`.

**Lambdas and local functions** are units of their own: a procedure each
(`C.nested$<position>$<parameter types>`), which nothing calls; a call of the delegate is of its contract. What one
captures of the methods it's in, parameters and locals, comes in as an input of its own (`p$x$c`, `l$y$<n>$c`), so
its contract (`Spec.Requires`, `Spec.Ensures`, `Spec.Reads`) can name it. Each is some value of its type, since it
may run at any time: in range, allocated, not null where its type says so; a local with one value all along (a
`foreach`'s, or one assigned only where it's declared) that the compiler's flow analysis has as not null is not
null. A query clause's own parameter (the object its previous clause made, a group) is never null. The lambda
knows what its method requires of what never changes: that a delegate it captures is steady, and `Spec.Pre` and
`Spec.Total` of it. A captured variable the lambda writes is, in its precondition, its value at entry, and in its
postconditions its value at each return, as for a parameter the body assigns (callers don't assume those). An
exception in a lambda leaves it: the method's `try` and `finally` around it are not the lambda's. `this` is the
method's, where it has one. A local function is called as a procedure is: its captured inputs passed after its
arguments, as they are where it's called (the method's variables, or what a lambda calling it captures in turn); a
local it writes is forgotten after the call, as after any call that may run it. A variable passed by `ref` that
the flow graph captured before an argument after it branches (`Add(ref x, c ? 2 : 3)`, `Add(ref x, (x = 10) > 5 ?
...)`) is the variable itself, as it is at the call; an assignment as an expression is written, then its value.

**Library members with stubs.** A library member (not a collection's) whose stub contract the library gives, that
writes nothing and runs none of the program's code (no `Spec.Modifies`, nothing CsVerify's effects analysis says it
may write), not generic, of the subset's types (static, or a string's: `s.Trim()`, `s.ToUpperInvariant()`), is a
procedure of its contract, which its calls call: its preconditions checked, its postconditions assumed. A `[Pure]`
one is a function (as before), and so is any static one of the library's with a `[Pure]` stub (`Math.Clamp`,
`Math.Sign`): its precondition checked where it's called. A call in a body's assertion of what isn't `[Pure]` is
unknown there, with a warning (CSV1900), and so is a computed property's that isn't `[Pure]`. Each
stub a proof assumes is listed with the method. In a specification, `a ?? b` is `a`
where it isn't null (a nullable value's value), and `a?.m` null where `a` is, else `m` of it (a value made a
nullable one).

**Lifted arithmetic.** `+`, `-` and `*` of two nullable values of one integral type (`int? + int?`) are null where
either is, else the operation of their values, checked as code's arithmetic is (the values 0 where either is null,
which can't overflow). Static properties' getters and setters are methods, as instance ones are.

**Constructors' `this` as a value** (passed, stored) escapes before the object is built: where its class has an
object invariant or non-nullable fields, CSV1015; the object goes on as it is.
**Deconstruction** into array cells, fields and variables, `(a[i], a[j]) = (a[j], a[i])`, reads every value first,
then writes each target. In `Spec.Old`, a parameter the body assigns is the parameter as it came in.

**`in` parameters of values** (`in int x`) are by value: the callee can't change them.
An argument must be a local, a parameter or an array's cell (whose callee writes no array: else CSV1901, "the cell
and the parameter would disagree"); anything else is CSV1901 ("not supported"), and a struct's member isn't
translated.

Also the collections (`List`, `Dictionary`, `HashSet`, `Stack`, `Queue`) with their models and stub contracts, `Seq`
and `Map`, `foreach` over arrays, strings and collections, `Spec.Index`, and delegates: `Func` and `Action` values with `Spec.Pre`,
`Spec.Post`, `Spec.Total`, `Spec.ChangesNothing`, `Spec.Reads`, `Spec.ReadsOf`, `Spec.Changes`, calls of them,
lambdas and method groups; delegate types with contracts.

Also data records (Dafny's datatypes, with patterns, ranks, invariants), `Ghost<T>`, generic data types, generic
methods, generic classes and type parameters constrained to references; interfaces as parameters and fields.

Also arrays of objects and strings, and null patterns of references.

Also exception filters, `Spec.Multiset` and `Bag`, collections keyed by strings, a dictionary's `Keys` and `Values`,
and reading collections through their interfaces.

Also: delegates handed to library members (each element's precondition where the member calls it with the
elements, Parallel.For's indices, totality otherwise), ref locals, `await foreach` over library streams, library
awaits with and without stubs, tasks started inline in `Task.WhenAll` and in batches, library objects and tasks in
fields, classes with an `Equals` of their own (an unknown equivalence), collections' `[Pure]` members and stubs'
`[Model]`s as functions of the models, `Zip`, `GroupJoin`, `RightJoin`, lazy queries kept in a local, explicit
enumerators, the Spec library's trusted lemmas.

Also classes of the program that derive from a library class (`Collection<T>`, its virtual members overridden: a call
of the library's members on such an object may run them, so it forgets everything) or implement the library's
collection interfaces (read through them, they're unknown at each read).

Explicit interface implementations (`int ICounter.Next()`) are procedures like any other, held to the interface's
contract.

Iterators (`yield`): the body runs at the first `MoveNext`, after the call, so at its start, and after each `yield
return` (its value evaluated, with its checks), the caller's code may have changed anything; `yield break` returns,
and what the call gives isn't null. An iterator's postconditions would be of the enumerable, made before its body
runs: not translated. A `foreach` over any other `IEnumerable<T>` (an iterator's, a parameter's) evaluates it once (a
null one throws, CSV1013); each `MoveNext` may run the program's code, so may change anything, its answer unknown; each
element is a value of its type; `Spec.Index` counts the edges back to the head.

Not yet (such a method is not verified, CSV1902, with why): what the sweep's trace lists for a program (`CSVERIFY_TRACE_FILE`).

A filter (`Where`; and `Distinct`, `GroupBy`, `Union`, `Intersect`, `Except`, `DistinctBy` over each first
occurrence) is a count, `c[j + 1] == c[j] + (keep(j) ? 1 : 0)`, and the indices of its matches, `ix`, increasing:
that fact, `ix[i] < ix[i + 1]`, is triggered on the two indices together, as one alone would make the next and so on
without end. A first occurrence (no element before it the same) is a map of its own: where it is one, none before is
the same; where it isn't, `seen[j]`, one before, is. Not the `exists` itself inside the count's facts: each instance
of that made an element the solver hadn't, whose own instances made more, and a failing group query was undecided.
(A trigger on the count, `c[j + 1]`, was tried: it doesn't match `c[len(a)]`, so a count of a known length isn't
proved.) The group queries' failing assertions are decided whole, in seconds.

## How it's checked

`BoogieEngineTests` checks the diagnostics of every method of a corpus (one of each construct, a bug of each kind),
`samples/Good` and `samples/Buggy` against a snapshot (`tests/CsVerify.Tests/Expected/BoogieEngine.json`, written
with `CSVERIFY_RECORD=1`). The fuzz test checks that what verifies runs correctly.

Boogie verifies the procedures side by side (`/vcsCores`, a solver each). Each is first tried whole in a quarter of
the time limit (at least 10 s). One that times out is verified once more an assertion at a time
(`/vcsSplitOnEveryAssert`, for it alone, with the whole limit):
a long one that is hard as a whole is often easy split (Base64's encoder, decoder and round trip, Utf8's decoder). A
method split proves all of is verified. A failure split finds is not yet one: Boogie reports the solver's unknown,
where it gives up, as a failure, and split, without what it learned from the others, it gives up more (a correct loop
invariant over `3 * k`, say). So such a method is verified whole once more, with four times the time: a failure that
finds too is reported, one it proves is proved, and where the time runs out again the method is undecided (CSV1900);
what that whole run finds of its own (a counterexample split didn't get to) is reported too. Only a method the whole
didn't find failing (a correct one, maybe) is checked so: of one it did, split's failures are counterexamples as the
whole's are (the others' assertions assumed), and the whole, which stops looking after a few or at an unknown, may not
find them again. One that split doesn't decide all of is tried whole once more, with the whole limit, and if that
doesn't prove it either it is undecided: not verified (CSV1902), with the failures it did decide. A method is verified
only where Boogie said its procedure was correct.

At most two runs go at a time, sharing the cores, each on a thread pool of its own. A run that does nothing for five
time limits (five minutes at least) has lost a solver's answer and is ended; a run that a solver ended (Boogie's fatal
error, a dead solver, or Boogie's `TimeoutException` for an answer just past the limit) is run once more. Where the
second run fails too, its methods are not verified (CSV1902, with Boogie's reason). `CSVERIFY_TRACE=2` prints each run
and each failure Boogie reports.

A procedure that fails is verified once more split, too. Once Boogie has a counterexample it looks for more, and where
the solver then answers unknown it stops: the assertions it hadn't decided are reported neither failed nor undecided
(and it reports five at most). Split, each is decided on its own: the failures are the whole's and those of split's
the second whole run confirms (where split doesn't decide one, the method is undecided).

A kind of failure is reported once at a place (the first of the program's checks
there), however many checks and paths fail it.

A failure's diagnostic names the library calls it rests on (`Causes`, for `--library-report`): those whose results
the failing check reads, and those of the loops whose inferred facts it uses. A
check that something isn't assumed after a statement (`NotAssumedAfter`) is a side branch that ends there,
except in the leading statements of a loop head's block, where it would cut the loop.

The checks made from the syntax and the declarations alone (`StaticChecks`: locking, lock levels, atomics, flags,
concurrency marks, Entity Framework contexts, a data type's invariant's dependence, and the warnings they give) run
for every method, verified by Boogie or not, and their diagnostics are its. An [Atomic] field's step is proved
transitive in Boogie (CSV1030, an assertion in the step's procedure).

## Next

- Smoke tests (Boogie's `/smoke`), so that a contradiction in what a translation assumes is found as it is made.
