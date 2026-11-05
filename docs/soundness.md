# Soundness

This page says what "verified" claims, what that claim rests on, and why each part of the verifier keeps it. The
approach is reduction: each mechanism is an instance of a technique whose soundness is published, used inside the
conditions under which it was proved. Where CsVerify does something no paper covers, the page says so and gives the
argument, or the test, that stands in for a proof.

## The claim

**Theorem (informal).** Let a method M be reported verified, with no errors. Then every run of M that starts in a
state satisfying M's preconditions, under the assumptions A1–A9 below, has these properties:

1. **Safety.** No obligation the verifier checks is violated: no `Spec.Assert` fails; no array or span index is out
   of range; no divisor is zero; no null is dereferenced or passed where a non-null is required; no run-time integer
   arithmetic overflows outside `unchecked` (in `checked` code the overflow throws instead); no callee is called
   outside its precondition; no write is made without the permission, view or frame that allows it; no linear value
   is used twice or lost.
2. **Partial correctness.** If M returns normally, its postconditions hold; if it exits by throwing an `E`, its
   `EnsuresOnThrow<E>` clauses hold.
3. **Total correctness for proofs.** A lemma, `[Pure]` function or `[GhostFunction]` terminates on every input in its
   precondition and does not throw; ordinary methods terminate where they give `Spec.Decreases`.

The theorem is modular: it assumes every callee meets its own contract, which is what verifying the callee
establishes (or, for library code, what A5 assumes). Verifying every method of a program therefore gives the theorem
for the whole program, by induction on the call tree for terminating runs, and by the usual argument for partial
correctness (Hoare's rule for recursive procedures) otherwise.

"Not proved" is never "proved": a solver answer of `unknown` or a timeout is reported as a failure, as is a construct
the verifier cannot model (CSV1901) and a method that hits the path limit. Every gap below is therefore a gap in what
is assumed, never in what is reported.

## The assumptions (the trusted base)

- **A1. The solver.** Z3 answers `unsat` only for unsatisfiable queries.
- **A2. The front end.** Roslyn's `IOperation` trees and control-flow graphs mean what C# means (ECMA-334 and the
  compiler's own lowering). CsVerify symbolically executes Roslyn's lowering, so it inherits it. No formal semantics
  of C# exists to check this against; see N1.
- **A3. The runtime.** .NET runs the program as the C# and CLI specifications say. In particular `float` and
  `double` arithmetic is IEEE 754 binary32/binary64 with round-to-nearest-even and no extended intermediate
  precision. ECMA-335 permits extended precision; RyuJIT on x64 and arm64 does not use it.
- **A4. Threads.** No other thread writes the state a method uses while it runs (see
  [Async and concurrency](semantics.md#async-and-concurrency)).
- **A5. Library contracts.** `[ContractsFor]` stubs, LINQ's definitions (`Bcl/Linq.cs`), nullability annotations, and
  the stated facts about library code (it writes only what it is handed, and runs user code only through what it is
  handed) describe the library. They are checked against the real library by tests (`StubConformanceTests`,
  `QueryConformanceTests`), not proved. See N3.
- **A6. Explicit trust.** `[Trusted]` bodies, `Spec.Assume`, the `Ieee` lemmas, `[TakesOwnership]` and
  `Spec.HandOver` are axioms by definition.
- **A7. Options.** `--no-overflow` makes run-time integers mathematical, and a check profile (`--checks`) assumes the
  kinds of obligation it leaves out. Without either, nothing is assumed.
- **A8. The analyzers.** The linearity, ghost and purity analyzers enforce their rules; the verifier relies on them
  (a method with an analyzer error is not verified).
- **A9. Erasure.** The erased program (`-p:CsVerifyErase=true`) behaves as the original with its ghost code removed.
  Ghost code cannot write run-time state (purity analyzer), so removing it changes nothing observable.

Out of scope, as documented in [Limitations](limitations.md): running out of memory or stack, reflection, and
termination of ordinary methods without `Spec.Decreases`.

## Each mechanism and the result it instantiates

The table pairs what CsVerify does with the result that makes it sound, and the condition under which that result
holds, which CsVerify must (and does) meet.

| Mechanism | Sound because | Condition CsVerify meets |
|---|---|---|
| Verification conditions by forward symbolic execution of the CFG, path by path | Strongest postconditions, dual to weakest preconditions: Dijkstra 1975; for unstructured graphs, Barnett & Leino 2005 | Every path is explored or the method is rejected (path limit); every obligation is a query |
| Loops: cut at the head, havoc what the loop changes, assume the invariant | Hoare's while rule (1969), as desugared in Boogie (Barnett et al. 2005) | The havoc covers everything the loop may change: variables, fields, heap rows, handlers' and `finally` code, the calls the CFG makes |
| `goto` cycles | Natural loops of a reducible graph, cut at their heads (Barnett & Leino 2005) | Every cycle passes through a head; irreducible graphs are rejected |
| Inferred loop facts | Houdini (Flanagan & Leino 2001): the greatest fixpoint of candidates that hold on entry and are re-established is an inductive invariant | A run assumes only candidates it also proves at every back edge, else it is re-run without them |
| Termination (`Spec.Decreases`) | Well-founded ranking functions (Floyd 1967), lexicographic order | Each component non-negative where it decreases, and mutual recursion checked across the strongly connected component |
| Modular calls | Hoare's procedure rule; contracts as in ESC/Java, Spec# (Barnett, Leino & Schulte 2004), Dafny (Leino 2010) | The callee's precondition is proved, what it may change is havocked, its postcondition assumed |
| Virtual calls | Behavioural subtyping (Liskov & Wing 1994) by specification inheritance (Dhara & Leavens 1996) | Every override is checked to require no more, promise no less, and stay within its base's frame |
| Heap: one map per field; arrays as select/store | Burstall's component model, as in Bornat 2000; McCarthy's theory of arrays | Fields of different names never alias; a write updates one map |
| `Spec.Modifies` / `Spec.Reads`, `Spec.Fresh` | Dynamic frames (Kassios 2006), as in Dafny | Writes are checked against the frame on entry; a function's value is kept only across changes disjoint from its reads |
| `[Pure]` and `[GhostFunction]` definitions | Definitional extension: a function defined by a terminating recursion adds no theorems about old symbols (Shoenfield 1967). Unfolding one level per use is fuel (Amin, Leino & Rompf 2014), which loses completeness only | Every definition is proved total (CSV1011) and side-effect free (CSV0013), and is unfolded only within its precondition (CSV1012) |
| Data records | The theory of algebraic data types (Barrett, Shikanian & Tinelli 2007): constructors injective, tags disjoint, size well-founded | The hierarchy is closed within the compilation (see N4) |
| Permissions: `Spec.Acc`, single fields, array cells, predicates fold/unfold | Implicit dynamic frames (Smans, Jacobs & Piessens 2009) with fractional permissions (Boyland 2003), encoded as in Viper's Carbon (Müller, Schwerhoff & Summers 2016); abstract predicates (Parkinson & Bierman 2005) | Permission masks add up to at most one; predicate bodies self-frame (checked where declared); permissions are taken left to right |
| Read shares | Counting permissions (Bornat, Calcagno, O'Hearn & Parkinson 2005) | Every share is the same ε; a view is whole only with all shares back |
| Views, `Own<T>`, ownership trees, `Mem` | Stateful views (Zhu & Xi 2005) on linear logic; ownership as in Clarke, Potter & Noble 1998 | Views are linear (A8), so at most one exists per object; a call changes only the trees whose views it gets |
| State across `await` | The framing argument of concurrent separation logic (O'Hearn 2004): what a thread holds no one else can write. For confined locals, the same argument for unshared objects, as in confinement and uniqueness (Vitek & Bokowski 1999; Boyland 2001) | Everything not held by a view or a permission, nor in a confined local, is forgotten at each `await`; a confined local holds only objects made in the method, and no use of it hands its object on (base class library members are trusted not to keep their receiver) |
| Exceptions | Partial correctness with exceptional postconditions, as in JML and Spec# | Any call may throw; a throw leaves only `EnsuresOnThrow`; proofs may not throw |
| Raises merged at a handler | State merging (KeY's merge rule: Scheurer, Hähnle & Bubel 2016), as in Viper's Silicon | Each raise's facts since the `try` began are assumed under a fresh selector, and values differing between raises become `ite` terms on it, so the merged state is exactly the union of the raise states; a resource is kept only if every raise holds it; raises with different pending continuations are not merged |
| Bounded and mathematical integers | As in ACSL (Baudin et al.): run-time arithmetic checked against its type, specification arithmetic mathematical | Every run-time operation that can overflow is an obligation (CSV1010); values read from memory are in range |
| `float` and `double` | The SMT-LIB floating-point theory (Brain, Tinelli, Rümmer & Wahl 2015), an exact semantics of IEEE 754 | Operations round as .NET does (A3); the integer encoding in the heap is injective, so it has a model |
| Quantifiers by e-matching only | Instantiating a quantifier is a sound inference whatever the triggers (Detlefs, Nelson & Saxe 2005); triggers decide only what is found | `unknown` is a failure |
| Ghost sequences, multisets, maps | Theories with models: SMT arrays, and axioms each satisfied by the intended multiset | Each axiom is true of the intended interpretation |
| Rectangular arrays: `cv_cell` with inverses | An injection ℤ² → ℤ exists, so the axioms have a model | — |
| LINQ comprehensions, normalisation | The list monad's laws (Wadler 1990, 1992): for-yield is the unit law, for-for associativity, for-if and if-if the filter laws. Cheney, Lindley & Wadler 2013 normalise with these plus a union rule | Only rules valid for lists are used; the union rule, which reorders, is not |
| LINQ's encodings: filter counts, flattening offsets, sort permutations, running folds and seen-sets | Each is a fresh function symbol defined by primitive recursion on 0..n, or by a property of a function that exists (the actual permutation, the actual indices): a definitional extension | Each axiom is guarded by the condition under which its sequence is defined |
| Tuples, anonymous objects, groups | Free constructors with selectors (the same datatype theory) | The constructor term is a function of the parts, so of the element under a quantifier |
| `Spec.Equal` where `T`'s `Equals` is unknown | An uninterpreted relation: any relation is a model | Fixed within one contract (an epoch), fresh for each call |

Each row is sound only in its condition, and checking the conditions is where the verifier's work is. The table is
thus also a review checklist: a change to a mechanism must keep its condition.

## Where "nothing new" does not hold

The reduction above covers the logic. Four things are not covered by any one published result. For each, here is
the argument we have, and what would make it stronger.

**N1. The translation from C#.** The table assumes C# constructs become the right logical ones. There is no formal
semantics of C# to prove this against (A2). Our argument is per construct, and given where each is documented:
- `foreach` is the compiler's own lowering (arrays, `List<T>` over its model, the enumerator pattern otherwise);
- `ref` locals name a location fixed at binding; array cells by reference are copy-in/copy-out, sound under the
  stated restriction that the callee cannot see the cell any other way;
- mutable structs have value semantics: a write makes a new value and writes it back;
- spans are a base and an offset into the same heap rows as arrays.

What would make it stronger: a core calculus with a semantics, and a proof that each construct's lowering simulates
it. Short of that, testing (N5).

**N2. The combination of styles.** ATS views, dynamic frames, Viper permissions, ownership trees and `Mem` views share
one heap and one write rule ([One write rule](objects.md#mutable-objects)). Each is sound alone; no paper proves the
combination. Our argument: every style reduces to the same permission mask (object → fraction, plus cells), so a
write is allowed by exactly one of a held permission (views and `Spec.Acc` are permissions), a frame on entry, or
allocation in the method; and every call transfers permissions as implicit dynamic frames do. Lending
(`Spec.Modifies(Own.Tree(x))`) is the one bridge: the caller gives up the tree's permission for the call and gets it
back, which is the frame rule for a call. What would make it stronger: the mask encoding written out as one
calculus, with the styles as derived forms.

**N3. The library.** Contracts and LINQ's definitions are trusted (A5). Their conformance tests run each against the
real member on random inputs, including the edge cases that matter (NaN, -0.0, overflow, empty and repeated
values). Testing finds wrong definitions but cannot prove them right. Two choices keep the risk down: a definition
may be stronger than .NET where that only loses completeness (`MinBy` requires a non-empty source), and a member
whose behaviour depends on what .NET does internally (when a lambda runs) is not read at all.

**N4. Closed-world facts.** Data records' closedness, sealed overrides and "library code runs only what it is handed"
are facts about the program as compiled. They hold within the compilation verified, and fail only if other code is
linked in that breaks them (another assembly deriving from a record through its protected copy constructor, or
reflection).

**N5. The implementation.** A sound design can still have unsound code. The bugs found so far show where: an encoding
used outside its condition. One example, fixed: a tuple made in a lambda that a query applies to every element was a
fresh constant, one for all elements, so facts about different elements contradicted each other and false counts
were provable. The defences we have:
- every feature has negative tests (`Wrong…` methods, `samples/Buggy`), which must fail to verify;
- conformance tests for every library definition;
- the corpus and CsLemon runs, which catch proofs that change.

- **the verifier tested on random programs** (`tests/CsVerify.Tests/Fuzz`), after Irfan et al. (ISSTA 2022), who
  tested Dafny the same way. Random methods take integers, an array and two cells, `c` and `d`, where `d` may be
  null, `c` itself, or another cell. Their bodies have integer arithmetic, `Math`, array reads and writes, field reads
  and writes, new cells, data records and their equality, doubles (NaN, infinities, -0.0, `Sqrt`, casts back to
  `int`), `throw`, `try`/`catch`, `checked` arithmetic caught as `OverflowException`, ifs, `for` loops and LINQ.
  They call a library of helpers with real contracts: a `Spec.Modifies` frame that says how its cell changes, and
  one that does not; a writer of one array cell under `Spec.Acc`; a `[Pure]` function; and an `[Owned]` account with
  an invariant, made with `Own.New` and changed through its view (deposits, withdrawals, transfers between two);
  read shares of an account (`Own.Share`/`Unshare`); an ownership tree, a box owning the box inside it with an
  invariant one level down (`Own.Give`/`Take`); and a predicate holding two nodes' permissions and their order
  (`Own.ToAcc`, `Spec.Fold`/`Unfold`, sometimes of one node twice); a `[Pure]` recursive function and a lemma
  proving its closed form by induction; and a class with a virtual method and a `[Pure]` virtual query, and a
  sealed override, called through the base type; an interface whose contract is in a contract class, with two
  implementations; a Dafny-style object with a ghost `Repr` and `Valid()`, framed by `Spec.Modifies(Repr.Value)`;
  and `Mem` cells, allocated, written and read through their views and freed. Loops get `Spec.Invariant`s, checked at
  every head when run. The programs that run are the erased ones (the erasure pass, then the compiler), as users
  run them, so erasure is under the same oracle (A9).
  The helpers are verified in every batch, since the calls rely on their contracts.
  Each method is first run with every candidate assertion and postcondition recorded. Its *true variant* keeps those
  that held. Where it verifies, it is run again on fresh inputs with its specifications as run-time checks and
  overflow checked; a failed check, or an exception other than the program's own throw, is a soundness bug. Its
  *planted variant* adds one that failed on an input the precondition admits, and must not verify. An internal error
  (CSV1999) fails the test too. Pinned inputs (a precondition that fixes them) make the verifier all but exact, so
  many true variants verify and the test bites; their share is a measure of completeness. CI runs three seeds;
  `CSVERIFY_FUZZ_SEEDS=from..to`, `CSVERIFY_FUZZ_METHODS`, `CSVERIFY_FUZZ_SIZE` and `CSVERIFY_FUZZ_LOG` run a soak.

  Six soaks so far, 3,440 methods, found no soundness problem. In all, 1,913 true variants verified and passed
  their checks, and 2,601 of 2,601 planted ones were rejected. They found two other bugs:
  - **Division blow-up (robustness).** Division, remainder and absolute value were written out with their operands
    repeated, so nested ones grew exponentially. One method's term passed 2^31 characters and crashed the verifier,
    and others took minutes. Long operands now go through solver macros.
  - **By-ref arguments before a `?:` (completeness).** A call with a `?:` among its arguments has the flow graph
    capture the earlier arguments first, by-ref ones too. The verifier rejected the captured `ref` argument
    (CSV1901), and the linearity analyzer took capturing a view for consuming it (CSV0002), so correct code like
    `Transfer(a, ref va, b, ref vb, x > 0 ? 1 : 2)` did not verify.

**What the fuzzer covers.** Every feature the generator produces is one the oracle checks; the rest is tested only by
the hand-written tests and samples. By area:

| Area | Generated | Not yet generated |
|---|---|---|
| Integers | overflow obligations, `unchecked` (wraps), `checked` caught as `OverflowException`, division and remainder by zero, `Math`, `decimal` (unknown values) | |
| Floats | `double` (rounding, NaN, infinities, -0.0, `Sqrt`, `Floor`, casts to `int`), `float` | |
| Strings | literals, concatenation, interpolation, `Length`, `==`, `IsNullOrEmpty`, `Substring`, `StartsWith`, `Contains`, `IndexOf`, `Trim`, `ToUpperInvariant` | |
| Null | parameters that may be null, `int?` (`??`, `HasValue`, lifted `+`, `.Value`, relational patterns) | |
| Arrays and memory | reads and writes with bounds, rectangular arrays, spans, `ref` locals, struct members by `ref`, list patterns, `foreach` | |
| Control flow | `if`, `for` with and without invariants (inferred facts), termination measures, `while`, `do`, `switch` statements, `goto` loops, `foreach` | |
| Exceptions | `throw`, `try`/`catch`, filters, rethrow, `finally`, `EnsuresOnThrow`, failed downcasts | |
| Calls | helpers with contracts, `Spec.Modifies` frames, local functions, lambdas (also writing locals), calls between generated methods, async with `await` | |
| Objects | fields and aliasing, new objects, mutable structs, properties with code, constructors with contracts, static fields | |
| Data types | a closed record hierarchy and a generic one, `is`, `switch`, property and positional patterns, value equality, record and immutable-class invariants | |
| OOP | virtual methods and `[Pure]` virtual queries, interfaces and abstract classes with contract classes, a three-level hierarchy | |
| Ownership and permissions | views and transfers, ownership trees (`Give`/`Take`), read shares, predicates (also recursive), single-field and array-cell permissions, `Mem` cells and arrays (`Split`/`Join`, `TakeOut`/`PutBack`), dynamic frames (`Repr`/`Valid`, `Spec.Reads`, `Spec.Fresh` in the helpers), linear packages | deeper trees |
| Proofs and ghost state | `[Pure]` recursion, lemmas by induction (a closed form, monotonicity), `[GhostFunction]`s, multisets, sequences, maps, `Spec.Old` | lemma bodies generated at random |
| Library | LINQ, `List`, `Dictionary`, `HashSet`, `Stack`, `Queue`, `StringBuilder`, `MemoryStream`, `TextWriter`, `BinaryPrimitives`, disposables | the remaining stubs (`Stream` reads, `BinaryReader`/`Writer`) |
| Erasure | every program runs erased | |

Out of scope by design: `--no-overflow` and check profiles, which assume rather than check, and threads, which are
not supported.

## References

- Amin, Leino, Rompf. Computing with an SMT solver. TAP 2014.
- Barnett, Chang, DeLine, Jacobs, Leino. Boogie: a modular reusable verifier for object-oriented programs. FMCO 2005.
- Barnett, Leino. Weakest-precondition of unstructured programs. PASTE 2005.
- Barnett, Leino, Schulte. The Spec# programming system: an overview. CASSIS 2004.
- Barrett, Shikanian, Tinelli. An abstract decision procedure for satisfiability in the theory of recursive data types. ENTCS 174(8), 2007.
- Baudin et al. ACSL: ANSI/ISO C Specification Language.
- Bierman, Meijer, Torgersen. Lost in translation: formalizing proposed extensions to C#. OOPSLA 2007.
- Bornat. Proving pointer programs in Hoare logic. MPC 2000.
- Bornat, Calcagno, O'Hearn, Parkinson. Permission accounting in separation logic. POPL 2005.
- Boyland. Checking interference with fractional permissions. SAS 2003.
- Brain, Tinelli, Rümmer, Wahl. An automatable formal semantics for IEEE-754 floating-point arithmetic. ARITH 2015.
- Cheney, Lindley, Wadler. A practical theory of language-integrated query. ICFP 2013.
- Clarke, Potter, Noble. Ownership types for flexible alias protection. OOPSLA 1998.
- Detlefs, Nelson, Saxe. Simplify: a theorem prover for program checking. JACM 52(3), 2005.
- Dhara, Leavens. Forcing behavioral subtyping through specification inheritance. ICSE 1996.
- Dijkstra. Guarded commands, nondeterminacy and formal derivation of programs. CACM 18(8), 1975.
- Flanagan, Leino. Houdini, an annotation assistant for ESC/Java. FME 2001.
- Floyd. Assigning meanings to programs. 1967.
- Hoare. An axiomatic basis for computer programming. CACM 12(10), 1969.
- Irfan, Porncharoenwase, Rakamarić, Rungta, Torlak. Testing Dafny (experience paper). ISSTA 2022.
- Kassios. Dynamic frames: support for framing, dependencies and sharing without restrictions. FM 2006.
- Leino. Dafny: an automatic program verifier for functional correctness. LPAR 2010.
- Liskov, Wing. A behavioral notion of subtyping. TOPLAS 16(6), 1994.
- McCarthy. Towards a mathematical science of computation. IFIP 1962.
- Meijer, Beckman, Bierman. LINQ: reconciling object, relations and XML in the .NET framework. SIGMOD 2006.
- Müller, Schwerhoff, Summers. Viper: a verification infrastructure for permission-based reasoning. VMCAI 2016.
- O'Hearn. Resources, concurrency and local reasoning. CONCUR 2004.
- Parkinson, Bierman. Separation logic and abstraction. POPL 2005.
- Shoenfield. Mathematical Logic. 1967.
- Smans, Jacobs, Piessens. Implicit dynamic frames: combining dynamic frames and separation logic. ECOOP 2009.
- Wadler. Comprehending monads. LFP 1990.
- Wadler. The essence of functional programming. POPL 1992.
- Zhu, Xi. Safe programming with pointers through stateful views. PADL 2005.
