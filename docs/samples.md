# Samples

`samples/Good` (verifies completely, no analyzer diagnostics):
- `Arrays.Sum`: safe array sum against a recursive `[Pure]` definition.
- `Arrays.BinarySearch`: binary search with invariants and the full functional spec.
- `Arrays.Append`: length and contents postcondition.
- `Arrays.Last`: a ghost static index.
- `Lemmas.TriFormula`: `2·Tri(n) = n(n+1)` by induction, used by `TriFast`.
- `Lemmas.Power2`: recursion termination.
- `Memory.*`: alloc / read / write / free with linear `PointsTo` views, including a function that borrows a view and gives it back.
- `ArrayViews.Fill`: divide-and-conquer fill. It splits `array_v(n, l)` into `array_v(n/2, l) * array_v(n - n/2, l + n/2)`, recurses on each half through its own pointer, and joins them back.
- `DataTypes.cs` (lists after ATS and Dafny, expressions after Dafny's tutorial, FACT from INT2PROGINATS):
  - `Length`, `Append` and `Reverse` on a generic `List<T>`, with `AppendLength` and `ReverseLength` proved by structural induction. `Countdown` builds a `List<int>` whose length is proved, and `ReversedCount` applies the generic lemma to it.
  - `Eval` and constant folding `Fold` on expressions, with `FoldPreservesEval`.
  - The dataprop `FACT` as a closed record (`Bas`, `Ind`), with its `nat` index as an invariant. `FactIsFunctional` is ATS's `fact_isfun`, by induction on one proof and case analysis on the other. `Factorial` returns `r` together with a `Ghost<Fact>` proof of `FACT(n, r)` built in its loop; the erased program never builds it.
  - `Interval`, a record with the invariant `Lo <= Hi`, and `Widen`, which keeps it.
- `Trees.cs`, after ATS's verified AVL and red-black trees. ATS indexes the types, `avltree(h)` and `rbtree(color, bh, violation)`, so an unbalanced tree does not type-check. Here those indices are invariants of the node records, so no unbalanced node can be built:
  - **AVL:** `Node`, both rotations (single and double), and `Insert`, proved to raise the height by at most one.
  - **Red-black, after Okasaki:** `BalanceL` and `BalanceR` handle the four rotation cases as nested C# patterns, such as `Ins.Viol(Rb.T { Red: true } a, var y, var c)`. `Ins` keeps the black height. `Insert` raises it by at most one. ATS's violation index becomes a type of its own, `Ins = Fine(Rb) | Viol(l, k, r)`: an intermediate tree that may have a red-red violation at its root cannot be an `Rb`.
  - **Hints and dead branches:** `Spec.Assert(Bh(a) == Bh(a.L))` hints play the part of ATS's `prval` steps, because definitions unfold one level per use. Unreachable branches carry a `Spec.Assert(false)` that the verifier checks.
- `DynamicFrames.cs`: Dafny's `Valid()`/`Repr` idiom. A `Pair` of two cells has a ghost representation set, a ghost `Valid()` that reads only it, and `IncA`/`Swap` that modify only it. `Demo` builds two pairs, updates one, and proves the other unchanged and still valid.
- `LibraryContracts.cs`: code over `List<T>`, `Dictionary<K, V>` and `string` with CsVerify's BCL contracts ([Contracts for code without sources](library-contracts.md)). `Squares` builds a list with a loop invariant over its elements, `Max` finds a list's largest element, `MoveLast` changes two lists within its `Spec.Modifies`, `Histogram` counts with a dictionary, `Sum` adds up a list with `foreach`, `Zeroes` shows `Array.Fill` writing only its own array, and `WriteList` builds a line with a `StringBuilder` and writes it to a `TextWriter`. `Samples/Buggy/LibraryContractBugs.cs` has the bugs they catch.
- `Linq.cs`: LINQ over Lists and arrays ([Contracts for code without sources](library-contracts.md), "LINQ"). `Passing` filters scores with `Where` and specifies all of what it keeps, `Best` is `Max`, `Total` a `Sum` that cannot overflow, `Above` an exact `Count` with a predicate, `Lowest` and `Sorted` sort with `OrderBy`, `Customers` counts with `Distinct`, `Busiest` loops over `GroupBy`'s groups and each group's orders, `FirstItem` flattens with `SelectMany`, `LastEven` uses `Select` with an index, `Agree` compares two arrays with `Zip`, `Matched` joins customers to their orders, `ByTens` sorts with `OrderBy` then `ThenBy`, `Curved` is query syntax with a `let`, `Mean` an `Average` of doubles, `Classes` counts `Distinct` tuples, and `OrdersOf` loops over a `join ... into`'s matches. `Samples/Buggy/LinqBugs.cs` has the bugs they catch: a `Sum` that may overflow, `Max` and `First` of what may be empty, the wrong sort order, repeated values `Distinct` drops, a group's members taken to equal its key, `Zip` taken to be as long as its first source, the `First` of a join that may match nothing, `ThenByDescending` taken for `ThenBy`, the `Average` of what may be empty, a `let` that selects the wrong variable, and `==` taken to compare anonymous objects by value.
- `AcslByExample.cs`, from *ACSL by Example* (Fraunhofer FOKUS, MIT licence), the C++ standard algorithms specified in ACSL for Frama-C/WP, with their contracts carried over:
  - **Non-mutating:** `find` (its *some*/*none* behaviors), `mismatch`, `equal`, `adjacent_find`, and `count` against the logic function `Count`.
  - **Min/max and search:** `max_element`, `clamp`, and `lower_bound`, `upper_bound` and `binary_search` on sorted arrays.
  - **Mutating:** `fill`, `copy`, `swap_ranges`, `replace`, `remove_copy` and `reverse`, each with ACSL's `assigns` and `Unchanged` as explicit postconditions.
  - **Numeric:** `iota`, `accumulate` and `partial_sum` against the logic function `Accumulate`, and `is_sorted`.
  - **Sorting:** `selection_sort`, `bubble_sort` and `insertion_sort` (with adjacent swaps; the book's version uses `rotate`), each proved to sort and to permute: `MultisetReorder` becomes `Spec.Multiset(a, n) == Spec.Old(...)`.
  - **The translation:** `\valid_read(a + (0..n-1))` becomes `n <= a.Length`, `\separated` becomes `a != b`, `Unchanged{Old,Here}` becomes `Spec.Old` under a `Forall`, and logic functions become recursive `[Pure]` definitions.
  - **Not ported:** the heap chapter, the `rotate`-based insertion sort, and the stack (an ADT with axioms).
  - **Overflow:** as in ACSL, logic functions (`Count`, `Accumulate`) are mathematical. `accumulate` and `partial_sum` carry ACSL's `AccumulateBounds` precondition, and `iota` requires `v + n` to fit.
- `AtsViewtypes.cs`, from INT2PROGINATS part IV ("Programming with Views and Viewtypes"):
  - **Linear lists `list_vt(a, n)` (ch. 15):** `insord` and an insertion sort that only relinks nodes. The length index is preserved, and sortedness is proved too, which the book's version does not prove.
  - **Linear binary search trees `bstree_vt(a, n)` (ch. 15):** leaf insertion, proved to grow the size index by one and keep each node ordered with its children.
  - **The circular buffer `cbufObj(a, m, n)` (ch. 16):** the book skips its proofs as "too costly". Here capacity and size bounds are the object's invariant, and every index is checked.
  - **The stopwatch `timer` (ch. 16):** a simple linear object, made by `Own.New`, borrowed by its operations, and freed by `Own.Drop`.
- `OwnedList.cs`: a sorted linked list whose nodes own the rest of the list. A ghost length `Len`, ATS's index, also measures the recursion. `InsertAfter` unfolds, inserts and folds back, and the list is proved sorted because every node is. `Independent` shows that inserting into one list leaves another's whole tree as it was.
- `Oop.cs`:
  - **Shapes.** Immutable classes with invariants, and an abstract `[Pure]` `Area()` specified by a contract class. `TotalArea` works for any shapes; `Nine` computes a square's area through a `Shape` reference.
  - **Accounts.** A `BankAccount` hierarchy whose abstract members have contracts and frames (`Spec.Modifies(ObjSet.Of(this))`). `Overdraft` is built with `base(...)` and overrides to allow more withdrawals. `Transfer` keeps the sum of two accounts of any kinds.
- `Owned.cs`: an `[Owned]` bank `Account` whose invariant (never overdrawn) travels with its view. `Bank.Transfer` takes two accounts with their views, and `Demo` calls unknown `IAudit` code between updates and still knows both balances.
- `Nulls.*`: nullable parameters checked before use, `??`, a `string[]` whose elements a precondition proves non-null, and a caller that proves it.
- `StaticFields.cs`: a counter in static fields; a call forgets only the static fields its callee writes.
- `ArrayViews.SwapEnds`: exchanges the first and last cells through two disjoint views. The postcondition is an exact sequence equation: `Elems == Old.Update(0, Old[n-1]).Update(n-1, Old[0])`.

## Ported from ATS and Dafny

- `DafnyLemon.cs`, from github.com/ashalkhakov/dafny-lemon (2024), a Dafny translation of Lemon's data structures, ported and cleaned up:
  - **The hash table.** dafny-lemon's `hashset.dfy` and `hashmap.dfy`, near-copies as Lemon's x1..x4 are, build the table from linked node objects with ghost lists and sets, and leave resize commented out (`assume false` in `resize_aux`, and a FIXME that keeping the count timed out). Here one table goes back to Lemon's own layout: entries in an array in arrival order, bucket heads and next links as indices, so chains run to smaller indices. The invariant is a few quantifiers over arrays. Find is complete (not found means absent), and insert grows the table by doubling, keeping every entry at its index, so Nth and arrayof are stable.
  - **The rest.** `struct.dfy`'s two tables (their disjointness, asserted by hand in Dafny, now holds by construction), `set.dfy`'s sets, and `option.dfy`'s ISOPT.

Rewritten in C#, not copied. Each program names its source in its doc comment.
- `AtsIntro.cs`, from Xi's *Introduction to Programming in ATS* (INT2PROGINATS) and the Stateful Views paper:
  - `FactIter` and `FibIter` against `[Pure]` versions of the FACT and FIB dataprops.
  - `Mul` by repeated addition (the MUL relation) and the inductive lemma `MulSucc`.
  - Euclid's `GcdIter`.
  - `Swap` of two cells through two borrowed `T @ l` views.
  - `Ackermann`, with the lexicographic metric `(m, n)`.
  - `IsEven`/`IsOdd`, mutually recursive, with metrics `2n` and `2n + 1`.
- Strings and bits:
  - `Strings.cs`: a palindrome check, substring search, digit parsing, and cut and split round trips.
  - `StringConversions.cs` (after Dafny's standard library): numbers to strings and back in any base up to 16.
  - `StringEscaping.cs` (the escaping after the same library): unescaping undoes escaping, and a comparison proved to be lexicographic order.
  - `Kmp.cs`: Knuth-Morris-Pratt. ATS's `kmp.dats` proves memory safety and termination; this proves that the table holds the longest borders and that the search returns the first occurrence.
  - `Utf8.cs` (after Dafny's standard library): a scalar value to bytes and back, written with shifts and masks and specified by arithmetic. `Decode` accepts exactly the encodings: no overlong form, surrogate or value past U+10FFFF.
  - `Base64.cs` (after the same library): a byte array to text and back, padded. `Decode` refuses exactly what isn't canonical. The tests also run it against `Convert.ToBase64String`, and `Utf8.cs` against `Encoding.UTF8`.
- Concurrency:
  - `Locks.cs`: a counter, an account, a stack, a lazily built table and statistics, shared between threads under locks with invariants. The tests also run them on real threads.
  - `AsyncService.cs`: a cache with a semaphore held across its load, a rate limiter, a worker on a channel with cancellation, fetching several at once, and retries, written for this repository rather than taken from a real program. It has one contract, a loop invariant: no null dereferences, overflows or unguarded uses. A first version had two bugs the verifier found.
  - `Callbacks.cs`: callbacks with specifications, written for this repository: a price map over an array whose function says what it accepts and gives and that it changes nothing, a discount that mustn't change the prices it is summing, an approval rule that reads only its order (its frame, as Dafny's `f.reads`), a pricing delegate type with a contract, and a retry helper. Writing it found that lambdas in field initializers and property bodies were never verified.
  - `ParallelWork.cs`: an array copied in two parts by tasks, by `Task.Run` and by threads, each with its part of the target and a share of the source, and a lock class around a semaphore, held across an await, written for this repository.
  - `TicketLock.cs` (after K. R. M. Leino, *Modeling Concurrency in Dafny*): the algorithm as atomic events. No two processes eat at once in any interleaving, and under a schedule fair within w steps the display advances at least once in every 3w. Leino's scheduler is fair eventually; this bound is a stronger assumption.
  - `DiningPhilosophers.cs`: a model where taking the lower-numbered fork first means someone can always move, with a verified run in which taking the left fork first reaches a state where no one can. Then a real table of fork locks, in the order `CSV1025` checks. The tests run it on real threads.
- `AtsMatrixAndTakeOut.cs`, from INT2PROGINATS and `matrixSub` in Xi's ICFP'05 paper:
  - `IncrementAt`, which takes cell i out of an array view as a plain `int @ (l + i)`, updates it with the single-cell `Read`/`Write`, and puts it back.
  - `MatGet` and `FillRows`, which index an m × n matrix in row-major order. The nonlinear bound `i·n + j < m·n` comes from the lemma `RowMajorInBounds`, which is built on an inductive `MulMonotone`.
- From the author's own ATS repositories (github.com/ashalkhakov), using permissions and predicates:
  - `AtsDlSeg.cs`, from ats-miscellanea/dlseg (2010): doubly-linked list segments with forward and backward views (`dlseg_v`, `rdlseg_v`), the four proof functions as recursive lemmas (two appends, two direction conversions), cons, uncons, snoc, length, concat (through the backward view of the first list), and the zipper `dllst_v_zipper` (make first, move right/left, write the focus, back to a list).
  - `AtsCircList.cs`, from ats-miscellanea/hacks/circlist.dats (2011): a circular list as a head node and a segment back round to it; `printcirc`'s walk once round shows the segment is empty when the head comes back, because the head's permission is in hand.
  - `AtsQueue.cs`, from tfc's `queue_sllist2` (Hongwei Xi's "Effective ATS" amortized queue): a front list and a reversed rear list, with `f + r = n`.
  - `AtsDynArray.cs`, from libatsc's `dynarray` (with Hongwei Xi, 2019): a growable array whose header and buffer cells form a predicate (`myprop`'s 0 < m, n <= m inside). It has get, set, insert-at (shifting right), append, takeout-at (shifting left), takeout-last, growth by doubling (`frealloc`), and reset-capacity. Each operation states what the contents become, through a `[Pure] Buf(d, n)` that unfolds the predicate (Viper's `unfolding` in a function).
  - `AtsHalfEdge.cs`, from ATS-playground/half-edge-mesh (2014-2015): half-edge collapse and split. In ATS the mesh is a region whose pointers may alias freely, and that they point into the region was taken on trust. Here the region is a predicate over a structure-of-arrays mesh, and "no dangling region pointers" is part of it: every next, prev, twin, vertex and face index is in range. Collapse and split are proved to keep it. Collapse deactivates the half-edge's face, split activates it again, and a two-triangle demo checks both.
  - `AtsStrBuf.cs`, from libatsc's `strbuf`: a C string in a buffer. `strbuf_v(m, n, l)` becomes a predicate over a `char[]`: n non-NUL chars, then a NUL, n < m. The shape facts ATS gives as axioms (`strbuf_v_null`/`cons`/`uncons`/`split`), and the `__trustme` in the copy, become what each operation proves: copying a substring, getting and setting a char, `test_char_at`, and strlen and strchr scans.
  - `AtsSList.cs`, from libatsc's `slist`: an intrusive singly-linked list (`slseg_v`, `slist_v`). It has cons, `foreach`, `iforeach`, `all`, and `insert_before` (the recursive aux keeps the node before the place in hand), with the template hooks fixed. `search_takeout` duplicates the found node's view with a `__trustme`. Here the takeout is honest: the list comes back split around the node, and the lemma `Restore` joins it again.
  - `AtsHeapArray.cs`, from tfc's `heaparray`: the same heap as an object (`HEAPNODE`), with the view `heap(T, m, n, l)` as a predicate that also carries the heap order. Push, pop and front unfold it and reuse `AtsBinHeap`'s proved array algorithms. Init, is-not-full, resize (copying in order) and term are new.
  - `AtsDList.cs`, from ATS-playground's `dlist` (after Hongwei Xi's libats/ngc dlist): forward and backward doubly-linked segments and the circular list. `dlist.sats` leaves `dlfseg_lemma3` "unproven, because to show this, we'd have to always assume and check that at-proofs don't alias". As stated, the lemma is false: `Lemma3Counterexample` builds a one-node segment that breaks it. The form the walks need holds, and is proved from that non-aliasing: with the head's permission in hand, a walk back at the head has nothing left. It covers make-single, insert-after-head, length, free, and a sum standing in for print.
  - `AtsBvh.cs`, from ats-miscellanea/rtrace's BVH (2011). The geometry is integral, so ray tracing becomes a box query. `part` partitions the id array in place. `bvh_mk` builds each half with only that half's array cells, and the tree has k leaves and k − 1 inner nodes: the 2n − 1 bound the source leaves as "TODO: prove this result". Every node's box contains its points. The source's `split` "doesn't know if this terminates for all inputs", and it doesn't when points coincide, so here a split that separates nothing halves the range. The query returns exactly what a brute-force pass over the leaves would: skipping a box the query misses loses nothing.
  - `AtsBinHeap.cs`, from ATS-playground/binheap.dats: a binary max-heap over `Spec.Acc(a)` cells. The original proves memory safety with the index arithmetic taken on trust. Here the arithmetic is checked and the heap order is proved too: push and pop keep it, a pushed value is in the heap, and the root is the maximum.
- `AtsArrays.cs`:
  - DML's `DotProd`: only bounds, the point of the PLDI'98 paper.
  - A view-based `Copy`: `!array_v` × 2, element-wise postcondition.
  - `InsertionSort`, sortedness only.
- `DafnyClassics.cs`, from the Dafny tutorial and the Dafny test suite:
  - `FindMax`, `Find`, `Reverse` in place (uses `Spec.Old` inside the loop invariant), `Sqrt`.
  - `FastPow`, exponentiation by squaring, with the inductive lemma `PowAdd`.
  - `DutchFlag`, sortedness only.
  - `McCarthy91`, whose nested recursion terminates only thanks to the inner call's postcondition.
  - `FindZero`, which skips ahead justified by a lemma containing a loop.
- `DafnyMore.cs`, from Dafny's test suite:
  - `MaxSegSum`, Kadane's algorithm. It returns the optimal segment `(k, m)` as a tuple and proves it beats every segment, with doubly quantified invariants over a `[Pure] Sum`.
  - `Cubes`, which fills `a[i] = i³` with additions only.
  - `SumOfCubes`, through Nicomachus' theorem `Σ i³ = (Σ i)²`, which uses two inductive lemmas.
  - `AdditiveFactorial`, nested loops of additions.

`samples/Buggy/PortBugs.cs` holds the same programs with planted bugs:
- a wrong initial accumulator;
- a mirror index off by one;
- squaring without the lemma;
- a wrong termination metric;
- a Dutch flag that forgets `mid++`;
- Ackermann with only `m` as its metric;
- `Even`/`Odd` both measured by `n`.

`samples/Buggy/PortBugs2.cs` does the same for the second batch:
- a taken-out cell written through the wrong pointer;
- a matrix stride by rows instead of columns;
- Kadane without the restart;
- a wrong finite difference in `Cubes`;
- sum of cubes without the Nicomachus lemma.

**What the ports could not say yet:**
- **Permutation.** Sorts and partitions don't prove that the output is a permutation of the input. ATS proves it with a dataprop over lists, Dafny with `multiset`.
- **Dataviews.** Singly-linked list segments (`slseg`, PADL'05) need views defined by cases over mutable memory. That is stage 2: mutable objects, owned through views.
- **Proofs returned by lemmas.** ATS's `fact_istot` returns a proof. A lemma is a `[Conditional]` void method, which can't have `out` parameters, so only run-time functions can return a `Ghost<T>` proof (`Factorial`).
- **Sets and cardinalities.** Pigeonhole proofs like Dafny's TwoDuplicates need them.

Of the surveyed programs, the ones that remain need the features above. One exception: Dafny's `MinWindowMax` is feasible but heavy.

Sources and licences:
- The ATS-CodeBook is MIT licensed (its only relevant recipe is binary search, already covered by `Arrays.BinarySearch`).
- The INT2PROGINATS code carries an MIT-style notice, © Hongwei Xi.
- Dafny is MIT licensed, © Microsoft.
- The papers' programs are re-implemented, not copied.

`samples/Buggy` holds deliberate errors:
- `Bugs.cs` has one verifier error per method.
- `FrameBugs.cs`: a `Valid()`-style function reading outside its `Spec.Reads`, a write outside `Spec.Modifies`, and two objects whose constructor promises no freshness, so updating one says nothing about the other.
- `AcslBugs.cs`: a `lower_bound` comparing with `<=` (so it is really `upper_bound`), a `find` that returns the last match, a `copy` whose contract lets the ranges overlap, and a selection sort that copies the minimum instead of swapping (sorted, but not a permutation).
- `ViewtypeBugs.cs`: a ring buffer that forgets to wrap around, one that can go below empty, and a tree that adds a leaf but not to its size.
- `TreeOwnershipBugs.cs`: appending a smaller node to a sorted list, writing an owned node in place, setting an `[Owns]` field directly, a node made to own itself, and assuming an inner node unchanged after the list was handed to a method.
- `OopBugs.cs`:
  - **Subtyping:** an override that requires more (CSV1018), one that breaks the inherited postcondition, and one that writes outside the inherited frame.
  - **Construction:** a bad `base(...)` argument, a constructor that breaks an immutable class's invariant, and one that lets `this` escape.
  - **Casts:** a `[Pure]` function with an unproved cast.
- `OwnedBugs.cs`: a method that leaves the object breaking its invariant, a write without the view, a forged second view, reading the invariant without the view, and a write after `Drop`.
- `TreeBugs.cs`: an AVL insert that never rotates, a single rotation where a double one is needed, and a red-black rebalance that leaves a red node over a red child.
- `DataBugs.cs`: a switch missing a case, recursion on the same tree instead of a subtree, a constant folder that breaks its correctness lemma, a FACT proof step that does not match the computation, an interval built the wrong way round, an assertion that two equal values are the same object, and a record invariant that reads a mutable `Gauge`, which anyone holding it could change after the record is built.
- `NullBugs.cs`: an unchecked `T?`, `null!` passed and returned, an element of `new string[2]`, and a precondition that reads `a.Length` before checking `a`.
- `ArrayViewBugs.cs`: a wrong pointer offset, halves never joined back, and a read one past the end of a view.
- `Linearity.cs` has leak, double free, use-after-free, forging and run-time ghost reads. Its analyzer errors are downgraded to warnings in that project's `.editorconfig` so the solution still builds.
- `ProofBugs.cs` holds proofs that would be unsound if accepted:
  - a circular lemma that "proves" `n != n` (CSV1011);
  - an inconsistent definition `f(x) = f(x) + 1` (CSV1011);
  - a lemma that writes an array (CSV0013);
  - one view passed as two `ref` arguments, so the contract says +1 while the cell gets +2 (CSV0007).
