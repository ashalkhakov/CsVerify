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
2. **One program.** Each method goes through [the passes](#the-passes), and the methods translated are one Boogie
   program: [the prelude](#the-prelude), a function for each `[Pure]` or `[GhostFunction]` method, and a procedure
   for each method.
3. **Boogie verifies it,** in the same process (the `Boogie.ExecutionEngine` package), with the Z3 CsVerify uses.
4. **Back to C#.** Every check is an `assert` on a line of its own, and the translator keeps a table from line to the C#
   location and the CsVerify diagnostic it is; each failure Boogie reports is found there, so the diagnostics are the
   ones CsVerify's engine gives, at the same places (BoogieEngineTests checks that they are).

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
throws `NotTranslated`, and the method is verified by CsVerify's engine.

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
operations, then where it goes. A conditional branch's condition is evaluated once, into `g$`*n*, and goes through two
blocks of its own (`b`*n*`$then`, `$else`), each assuming it or its negation, so that the blocks the graph has stay plain: a loop's head, which a later block jumps back to,
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

**Objects.** A class of the program whose objects are plain mutable state (not generic, not a record, derived from
`object`, with no virtual members or interfaces, and none of CsVerify's attributes: not `[Owned]`, no `[Invariant]`,
no locks or atomics) is a `Ref`, as an array is. Each of its fields and auto-properties is a map `$F.C.f: [Ref]T`, as
in CsVerify's engine; a static field is the map's value at `null`, the one object no reference aliases. An integer
field's map has a `where` clause keeping every value in range.
- `o.f` reads `$F.C.f[o]`, and `o.f = v` writes it, each asserting `o != null` first (CSV1013; `this` needs none).
- A field of non-nullable type is never null once its object is built: each write asserts it (CSV1014), each read
  assumes it (but `this`'s, in its constructor), and a constructor asserts at each return that it set it (CSV1014),
  unless it is `required`. A specification that reads one assumes it where it is evaluated, as CsVerify's engine does.
- A local of non-nullable reference type has each write asserted not null (CSV1014).
- An instance method is a procedure with `this` (not null, allocated) first; `o.M(...)` asserts `o != null`.
  Virtual calls aren't translated.
- A constructor is a procedure on `this`, whose fields are their defaults at entry; it runs the field initializers,
  then its body. `new C(args)` allocates the object, sets its fields to their defaults and calls the constructor. An
  implicit constructor's initialized fields are unknown values at the call, as in CsVerify's engine. A constructor that
  chains to `this(...)`, or lets `this` escape, isn't translated yet.
- A method that runs alongside other code (`[RunsConcurrently]`, or started as a task or thread), or reads a field a
  lock guards, stays with CsVerify's engine, which checks races.

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
- A field of an allocated object refers to an allocated object: assumed where one is read, as CsVerify's engine does.

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

Not yet: a function over more than one instance, or over one not of its parameters; an ordinary function that calls one (its axioms are about every state), ownership trees (`[Owns]`, `Own.Take`, `Own.Give`, `Own.Tree`), read shares, `in` views, packages, and
`Spec.Modifies` lending trees.

**ref and out parameters.** A `ref` parameter comes in as `p$x$in` and goes out as `p$x` (a requires, and `old`, read
`p$x$in`); an `out` one only goes out. A `ref` or `out` argument is a local or a `ref`/`out` parameter, which the call
assigns.

**Strings.** As [the semantics](semantics.md#strings) says, a string is its value: a `Ref` (so that null is one), with
a length `slen(s)` and UTF-16 code units `sat(s, i)` in `0..65535`, functions of the value. A literal is a unique
constant of its own, not null, of its length and characters. `a + b` is `scat(a, b)`: not null, its characters `a`'s
then `b`'s (null counts as empty); a concatenation too long for a string throws, which ends the path. `==`, `!=` and
ordinal `Equals` compare values; where two strings are compared, two different ones of one length differ at some
index (`sdiff`), so a string is its characters. `s.Length` and `s[i]` are checked not null (CSV1013) and in bounds
(CSV1003). A `[Pure]` member of string with a stub contract (`Substring`, `IndexOf`, `Contains`, `StartsWith` with
`StringComparison.Ordinal`, ...) is a Boogie function of its arguments, its postconditions axioms where its
preconditions hold, its non-nullable result not null; a call checks its receiver (CSV1013) and its precondition
(CSV1001). Comparing strings as objects, and other library members, aren't translated yet.

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
- a virtual member's procedure modifies what any of its overrides writes, and, as in CsVerify's engine, everything
  where it has no `Spec.Modifies` (an override not seen may write anything);
- `base(...)` in a constructor calls the base class's constructor on `this`; a new object's fields, inherited ones
  too, are their defaults; a constructor ensures the non-nullable fields it sets aren't null.

- interfaces of the program's (abstract members only, their contracts from a contract class) are references; their
  members are procedures with no body, and an implementation inherits their contracts as an override does;
- a property with code (or an abstract or an interface one) is its accessors: a read calls its getter, a write its
  setter; a `[Pure]` one is a function; an abstract or virtual `[Pure]` member is a function of its contract alone (an
  override may answer the call), of every field the program names, with no definition;
- on `this`, a member whose override in this class (or a base) is sealed, or whose class is, is that override, as in
  CsVerify's engine; a contract class's member is the member it specifies;
- `Spec.Reads(R)` of a `[Pure]` member is Dafny's frame axiom: two memories that agree on every object in `R` give it
  one value; its body reads only objects in `R` (CSV1017).

Not yet: `this(...)`, type tests and casts, generic types, invariants of classes that aren't `[Owned]` (immutable
objects).

**Frames.** `Spec.Modifies(W)`, Dafny's dynamic frames: `W` is an `ObjSet` (`ObjSet.Empty`, `ObjSet.Of(x)`, `.Add(x)`,
`.Union(s)`, `.Contains(x)`), a `[Ref]bool`. Its procedure writes a field or an array's cell only of an object in `W`
as it was on entry (`w$entry`), or allocated since (CSV1017; a constructor's own object counts as new); it calls only
what writes within that: a callee's frame inside ours, or none needed (a callee that may write fields or arrays without
one is CSV1017). It ensures every field and cell of an object allocated before the call, and not in `old(W)`, is as it
was. `[Owned]` classes are framed by their views instead; `Spec.Reads` isn't translated yet.

**Calls and frames.** A call of another translated method is a Boogie `call`. A procedure `modifies` the maps it
writes (an element map, a field map, or `$Alloc` when it allocates), and those of everything it calls; after a call,
what the callee modifies is unknown, as CsVerify's engine forgets the arrays and fields a callee may write. Allocation
only grows: `free ensures (forall r: Ref :: old($Alloc[r]) ==> $Alloc[r])`. A field written only at objects allocated
since the call began (a constructor's own object, or a new one's defaults) is unchanged at every other:
`free ensures (forall o: Ref :: old($Alloc[o]) ==> $F.C.f[o] == old($F.C.f[o]))`, as CsVerify's engine doesn't count
a constructor's writes to its own object as the caller's.

**Loops and arrays.** Boogie forgets at a loop head every map the loop modifies. CsVerify's engine forgets only the
arrays the loop writes through a variable it doesn't change (and all of them where it writes through anything else, or
calls what writes arrays). So the translation snapshots the maps on the way into the loop (`s$`*h*`$E.T`) and assumes at
its head that every array allocated then, other than those, is as it was.

**Exceptions.** A method is verified for partial correctness on its exceptional paths too: they are checked only
where something sees them, a `catch` or a `Spec.EnsuresOnThrow`. Exceptions are references, of a type given by
`dtype(r): Ty`; each exception type named is a `const unique T#…: Ty`, `sub` is C#'s derivation between them (axioms
from Roslyn's base types, reflexive and transitive), and every type derives from `System.Exception`.
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
- Where nothing sees an exception (no enclosing `catch`, no `EnsuresOnThrow`), a throw ends the path, as in
  CsVerify's engine; proofs (lemmas, `[Pure]` and ghost code) never throw.

Not yet: `finally`, exception filters (`when`), `using`, `lock`, and reading an exception's members.

**foreach.** A `foreach` over a one-dimensional array or a string is what C# compiles it to: the collection
evaluated once into `fe$`*n*`$a` (its length read, so a null one is CSV1013), an index `fe$`*n*`$i` from 0, the head's
`MoveNext()` the test `i < len(a)`, `Current` the element `a[i]` (widened to the iteration variable's type), and every
edge back to the head (the body's end, a `continue`) `i := i + 1`. The enumerator's `try`/`finally`, which disposes it,
isn't there: C# emits none for an array. `Spec.Index(x)` is the index: the number of elements gone through in the
loop's invariants, and `x`'s own in the body. The loop's first invariant is `0 <= i && i <= len(a)`, which holds by
itself.

A `foreach` over a `List<T>` whose loop changes no list (it calls only specifications, `[Pure]` members and lists'
`[Pure]` members) is the same loop over the list's model: the index up to `Size()`, each element `Items()[i]`, and
`Spec.Index` the index. A loop that may change a list goes through the enumerator, as C# does: `GetEnumerator()` keeps
the list's `Version()`, each `MoveNext()` checks the list's is still that (else it throws: CSV1001) and gives an
unknown answer, and `Current` is unknown; `Spec.Index` of such a loop isn't translated. A `foreach` over anything else
(an interface's list, a query, an enumerable of the program's) isn't translated yet.

**Lists.** A `List<T>` of the subset's values is an object whose contents are CsVerify.Bcl's model: maps as fields
are, `$F.$M.Size: [Ref]int` (never negative), `$F.$M.Version: [Ref]int`, and per kind of element
`$F.$M.Items.`*K*`: [Ref][int]`*T* (an integer type's in its range), so frames, modifies clauses and delegates' states
take them in as they do fields. In specifications `l.Size()`, `l.Items()` and `l.Version()` read them, `l.Count` is
`Size`, and `l[i]` is `Items[l][i]`, well-defined where `0 <= i < Size` (CSV1012). A `Seq<T>` is an `[int]` map:
`s[i]`, `s.Update(i, v)` (a store), `s.Drop(k)` and `s.Concat(k, t)` (lambdas), `Seq.Const(v)`, `==`; `Ghost.Of(x)`
is `x`, and `Spec.Equal` is `==`. In code every member of a list is a call of a procedure of its stub contract
(`ListContracts<T>`, its `@this` the receiver), named for the list's kind: `Count`, the indexer (CSV1001 out of
range), `Add`, `RemoveAt`, `Insert`, `Contains`, … modify only their own list's model (their `Spec.Modifies`), and a
constructor returns a new list. `Spec.Old` of a list's element is well-defined where it was in the old state.

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
  out); a precondition that depends on more isn't translated. Its body is verified on its own.
- A method whose specifications speak of a parameter's `Spec.Pre`, `Spec.Post` or `Spec.Total` (and not of what it
  reads) takes it to be the same in every state: `$steady(p)` at entry, and each call of it asserts `$steady` of the
  argument (CSV1001). A lambda or method group that reads no state is steady.
- A state is `$st(`*every element and field map*`)`, of type `St`, with each map given back (`$st.$F.C.f(s)`). In a
  state, a delegate accepts `$preS.K(d, s, x)`, gives `$postS.K(d, s, x, r)` and reads `$readsS.K(d, s, x)` (a
  `[Ref]bool`); a steady one's are its `$pre` and `$post` and it reads nothing. Dafny's frame axiom: two states that
  agree on every field and cell of the objects it reads in the first give it the same `$preS`, `$postS` and reads
  (triggered on a pair of its terms, as CsVerify's engine relates its pairs of states). A call asserts `$preS` in the
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

Not yet: `Spec.Total` of a delegate that may read state, a method group of an instance or generic method or one made
a delegate type with a contract, delegates with permissions or method `Spec.Modifies`, and a delegate's call where
exceptions are seen.

**Well-definedness.** A specification is checked well-defined where it's evaluated, as Dafny's are (CSV1012): for the
preconditions, in a procedure of their own (`P$wf`, given the parameters but not the preconditions, which `P` itself
assumes at entry), each under those before it; at each return for the postconditions, at the loop head for an
invariant, where an assertion is. Well-defined means an array read is in bounds and of an array that isn't null, a
divisor isn't zero, and a function's precondition holds where it's called; each under what `&&`, `||` and `?:` make
hold there, and over a quantifier's range. The check is `assert {:subsumption 0}`: not assumed after it, so what an
ill-defined specification says stays unknown, as in CsVerify's engine.

**Quantifiers.** `Spec.Forall(lo, hi, k => P)` is `(forall q$k: int :: lo <= q$k && q$k < hi ==> P)`, and
`Spec.Exists` is the `exists` of `lo <= q$k && q$k < hi && P`.

**Functions.** A `[Pure]` or `[GhostFunction]` method whose body is one expression is also a Boogie function, as
Dafny's functions are: on a layer, the memory it reads (as Dafny's take `$Heap`), `this` for an instance one, and its
parameters. The memory is the field maps it (or a function it calls) names, and the element maps; but a function that
reads arrays only through its own array parameters takes those arrays' elements instead (`$E.Int32[a]`), so writing
another array leaves its value as it was, as in CsVerify's engine. Its definition is an
axiom: where its precondition holds, its value on layer `$LS(ly)` is its body, whose calls are on layer `ly`. Another
axiom makes every layer's value the same. A specification calls it on `$LS($LZ)`, so each use unfolds the definition
once, as CsVerify's engine does; only a call back into its recursion group is on the layer below (Dafny's rule), any
other has a specification's fuel. Under a quantifier, of its variable, an application's definition is unfolded once
for every value in the quantifier's range (an assumption where the specification is read, and at a call for the
callee's preconditions), as CsVerify's engine unfolds it; that equation applies again to the applications in its
body, so recursion over a range unfolds as far as it needs to. Its postcondition is an axiom of every value where its precondition holds, and a
run-time `[Pure]` function's value is in its type's range. The method stays a procedure, which verifies the body and
says its result is the function's value on `$LS($LZ)` (so a call in code knows its body too). A `[GhostFunction]`, and a lemma, is ghost code: its arithmetic is
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

Also exceptions: `throw`, `try`/`catch` by type, rethrow, caught checked overflow, `Spec.EnsuresOnThrow`.

Also `List<T>` with its model and stub contracts, `foreach` over arrays, strings and lists, `Spec.Index`, and delegates: `Func` and `Action` values with `Spec.Pre`,
`Spec.Post`, `Spec.Total`, `Spec.ChangesNothing`, `Spec.Reads`, `Spec.ReadsOf`, `Spec.Changes`, calls of them,
lambdas and method groups; delegate types with contracts.

Not yet (such a method is verified by CsVerify's engine): ownership trees, shares, records (data types), generics, string members without stubs, collections,
collections other than lists (dictionaries, sets, interfaces' lists, queries), `finally`, exception filters, `using`, a method that assigns a parameter, ghost types (`Seq`, `Map`, `Bag`), async, locks and threads, LINQ, and
library calls with stub contracts.

## How it's checked

On every method the Boogie engine verifies, it must report what CsVerify's engine reports: the same diagnostics, at
the same lines. `BoogieEngineTests` checks that on a corpus written for it (one of each construct, a bug of each kind),
on `samples/Good` and on `samples/Buggy`. `--engine boogie-only` verifies only what Boogie translates, to compare the
two quickly.

## What comes next

The subset grows a construct at a time, each under the same comparison, until CsVerify's engine is no longer needed:
1. the heap: objects, fields, constructors and allocation, instance methods, non-nullable references, as Dafny encodes
   them (done for plain classes, base classes, virtual methods, interfaces and properties; next: data records,
   immutable objects' invariants, object initializers, `this(...)`);
2. strings (done: values, literals, concatenation, comparison, the members with stub contracts) and the collections'
   models (done: `List` and `Seq`; next: `Dictionary`, `HashSet`, `Map`, `Bag`), and the ghost types;
3. `foreach`, lambdas and delegates (done: `foreach` over arrays and strings, delegates with their frames, lambdas,
   method groups, delegate types with contracts, `foreach` over lists; next: over dictionaries, sets, interfaces' lists);
4. exceptions (done: `throw`, `try`/`catch`, rethrow, `Spec.EnsuresOnThrow`; next: `finally`, filters, `using`);
5. frames (done: `Spec.Modifies`, `Spec.Reads`; next: ghost `ObjSet` fields), and the library's stub contracts
   (done for strings' `[Pure]` members);
6. views, permissions and ownership (done: `[Owned]` classes, views, `Own.New`, `Own.Drop`, invariants, `Spec.Acc` of
   objects, predicates, functions over them, array cells, single fields; next: trees, shares, packages,
   `Spec.Modifies`);
7. locks, async and threads;
8. LINQ and Entity Framework, their definitions and models as Boogie;
9. smoke tests (Boogie's `/smoke`), so that a contradiction in what a translation assumes is found as it is made.

Then the Boogie engine is the default, CsVerify's engine goes, and the rest of the documentation is revised to
describe the one engine there is.
