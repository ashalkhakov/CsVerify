# Data types and objects

## Data types and object invariants

A **data record** is a record class whose whole state is its positional properties. A hierarchy of them is **closed** when the abstract root can't be extended from outside: its constructors are private (cases nested inside it), or the type isn't visible outside the assembly. The verifier then treats it as an algebraic data type:
- **Construction** `new Cons(h, t)` is the term `Cons(h, t)`. Its fields read back, it is not null, its tag is `Cons`'s, and its size is one more than its parts'. A case's base fields are computed from its header (`Ind(Prev) : Fact(Prev.N + 1, ...)` gives `N == Prev.N + 1`).
- **Downcasts.** `(Cons)xs` throws unless `xs` is a `Cons`. Ordinary code that goes on may assume it was. A lemma, a `[Pure]` function or a specification may not throw, so there the cast must be proved (CSV1011, or CSV1012 in a specification).
- **Case analysis.** `is`, `switch` statements and switch expressions test the tag. A value of a closed type is one of its cases, and on each branch it is that case's constructor applied to its own fields. A switch that misses a case throws, which a `[Pure]` function or lemma may not do (CSV1011), and a specification may not do either (CSV1012).
- **Equality.** The synthesized record `==` is equality of values, as long as every field compares the way the verifier models it (integers, booleans, arrays by reference, data records).
- **No identity.** A data value is its contents, so reference identity (`ReferenceEquals`, or `==` at type `object` or an interface) is not modeled. Only comparisons with `null` are known.
- **Structural recursion.** `Spec.Decreases(xs)` measures the value's size, so recursion on a sub-value terminates, and a lemma recursing that way is a proof by structural induction.
- **Fields keep their nullability.** A positional field of a non-nullable type is not null, because the constructor's argument was proved not null.
- **Generic records** (`List<T>`, `Option<T>` with cases `Some<T>`, `None<T>`) are one data type for all instantiations. Tags, constructors and fields are those of the definition, so the `List<int>` a caller builds is what a generic `Length<T>` and its lemmas take apart. Two limits follow from that:
  - **Nullability.** A field of type `T` is maybe-null even in a `List<string>`, because generic code with an unconstrained `T` can build a `List<string>` holding null.
  - **Equality.** `==` is value equality when the type arguments compare as modeled: `List<int>` does, `List<string>` doesn't. In that case the result is unknown, with a warning.

An **object invariant** is a `[Pure]` parameterless `bool` method marked `[Invariant]` on a data record or its base. It is proved at every `new` (CSV1015) and assumed of every object of the type, since the fields never change afterwards. While verifying the invariant itself, or anything it calls, it is not assumed: otherwise a helper could be "proved" from the very invariant it defines. Invariants may read fields and their lengths but not array contents, which can change. Nor may they read any mutable state: an invariant is assumed of objects nobody re-checks, so whatever it reads must be unable to change behind its back (CSV1015 on the invariant). For a data record that means only positional fields and functions of them. For an `[Owned]` class it means only its own owned fields, read through `this` (and its `[Owns]` children's, one level down). That rules out static helpers, other objects, and array elements, since anyone holding the array can write it; array lengths are fine.

**Constructors** of other classes are calls: `new C(args)` checks the constructor's `Spec.Requires` and assumes its `Spec.Ensures`, about the new object as `this`.

## Mutable objects

**Heap fields.** An instance field or auto-property of a class in the sources is a map from object to value, and so is a mutable static field (a field of one statics object, which no reference aliases):
- **Reads, writes and aliasing.** `o.F` reads the map and `o.F = v` updates it, so two references to the same object see each other's writes, and different objects don't.
- **Calls.** A call forgets only the fields its callee, or anything it reaches, may write: an inferred frame condition per field. A virtual or interface call forgets only what its declared member's `Spec.Modifies` allows, which every override is checked against. Without one, any field may have changed, as after a library call that can run user code (see [Calls are modular](how-it-works.md#layer-2-the-verifier-z3-separate-process)). Building a data value writes nothing.
- **Loops** forget only the fields they write.
- **`[Pure]` functions** take the field maps they read as arguments, so their value is never stale after a write. The same goes for arrays: a function that reads array elements only through its own array parameters depends on those arrays' contents, so writing another array leaves it as it was. A function that reaches arrays any other way (through a field, say) depends on the whole array heap.
- **Constructors.**
  - Verifying one: the new object's fields start at their defaults and the field initializers run.
  - At `new C(...)`: the constructor's preconditions are checked and its postconditions assumed about the new object. That object is distinct from every reference in scope, and its fields are their defaults unless the constructor or an initializer sets them.
- **Nullability.** A field of non-nullable type is never null once its object is built. Every write proves it (CSV1014); a constructor must set it before returning, except a `required` one, which every object initializer sets; and `this` may not escape a constructor of such a class (CSV1015). A static field is not null when its initializer makes an object.

**Owned objects (ATS style).** A class marked `[Owned]` is written only through its object's **view**, `Own<C>`. That is a zero-size `[Linear]` token, so the linearity analyzer ensures at most one exists per object. Views erase like the other proof types.
- **Making a view.** `Own.New(new C(...), out var view)` takes ownership of a new object, and only a new one (CSV1016).
- **Writing.** Writing an owned field needs a live view of the object in hand (CSV1016): a local, a `ref` parameter (an `in` parameter is read-only), or `this` inside the class's own methods. Calling a method of the class needs the receiver's view.
- **Exact frames for free.** A call can change an owned object only if its view goes in (by `ref` or by value), comes out, or the object is the receiver. So even unknown code, such as an interface call, leaves every other owned object as it was, with no frame annotations.
- **Distinctness.** Two views in hand own two different objects, so `(a, ref va, b, ref vb)` needs no `a != b` precondition.
- **The class's `[Invariant]` travels with the view.** It is assumed where a view is received (a parameter, a call's result, and `this` at entry to the class's methods). It is proved where the view is handed over or given back (CSV1015): a call's `ref` or by-value argument, a `ref`/`out` parameter or `this` at return, and `Own.New`. In between, the holder may break it temporarily. Without the view nothing is assumed, because whoever holds it may be mid-update.
- **Reads need no view.** Objects are garbage-collected, and while a method runs nobody else holds a view it lent.
- **Giving up.** `Own.Drop(view)` gives the object up for good.
- **The ATS idiom.** Methods take the object and its view side by side, `Transfer(Account from, ref Own<Account> fromView, ...)`, tied by `Spec.Requires(fromView.Obj.Value == from)`.

**Ownership trees (ATS's nested views).** A field of an `[Owned]` class marked `[Owns]` owns the object it refers to: that object's view is inside the container.
- **Unfold and fold.** To work on an owned object, take it out with `Own.Take(ref c.F, out var view)`, which leaves the field null. Give it back with `Own.Give(ref c.F, x, view)`. Both need the container's view and are real run-time helpers; erasure keeps them without the view argument.
- **What is rejected (CSV1016):** writing an owned object in place, setting an `[Owns]` field directly, giving into a field that still owns something, and giving an object to its own descendant (a cycle).
- **Children's invariants.** An owned child's own invariant is known only once it is taken out, so a container's invariant must state what it relies on about its children (`Head.Len >= 1`).
- **Invariants.** An owned object at rest can't change, so its invariant held when it went in still holds when it comes out. The container's invariant may read its children's fields, one level down. A sorted list is then every node's `Next == null || Val <= Next.Val`.
- **Frames.** The verifier tracks each object's tree root, a ghost map maintained exactly by `Own.New`, `Take` and `Give`. A call that gets a root's view may change that root's whole tree and nothing else, so two lists stay independent. For classes no `[Owns]` field can hold, every object is its own root and only the objects whose views go in change.

**Owned objects and the frame rule.** An ownership tree is a footprint: the root and everything it owns, transitively.
- **`Own.Tree(x)`** is that footprint as a ghost `ObjSet`, for Dafny-style specifications such as `Spec.Reads(Own.Tree(list))` on a static query.
- **Queries read their tree.** A `[Pure]` method or property of an `[Owned]` class without its own `Spec.Reads` reads its tree. Its body is checked to read nothing outside the tree (CSV1017); invariants keep their stricter rule.
- **The frame rule applies.** Every owned change knows its footprint:
  - a field write: one object;
  - `Own.Take`/`Own.Give`: the container's tree;
  - a call: the trees of the views it gets, plus the callee's `Spec.Modifies`.
  
  So a query on one list keeps its value across any change to another list. `Spec.Reads` may be given on owned classes; `Spec.Modifies` may not, since writes go through views.

**Permissions and lending (the permission core).** Internally, write access to owned objects is a permission mask: object → fraction, where 1 lets the holder write. It's granted by:
- a view in hand;
- `this` in the class's own methods;
- a tree lent through a frame.

It's revoked when the view goes: consumed, moved, dropped, or lent by `ref`. Writes check it (CSV1016).
- **Lending.** A Dafny-style method with `Spec.Modifies(Own.Tree(x))` borrows `x`'s whole ownership tree for the call. Its caller must hold that tree (its root's view), the method may then write any object in it without a view, and afterwards the caller knows that tree, and nothing else, may have changed. That bridges ATS-style ownership and Dafny-style frames: framed code works on owned data without threading views through its signature.
- **What stays.** This is the Carbon-style encoding of permissions (Viper's VC-generating backend): the heap stays a map per field, so reads remain free, and the ownership `Root` map and the frame links stay. Predicates build on the same mask (below).

**Packages of views.** A `[Linear]` positional `readonly record struct` keeps views together with ordinary values, as ATS pairs a view with its pointer: `[Linear] readonly record struct OwnedTally(Own<Tally> View, Tally Obj)`.
- **Building one** with `new` hands its views over: their invariants are proved, and the variables no longer hold them.
- **Deconstructing it** (`var (view, t) = tally;`) gives them back, alive, with their invariants and permissions. Reading a view out of a package that still holds it (`tally.View`) would copy it, and is rejected (CSV0004).
- **A package's own invariant** can tie its parts together: `[Invariant, GhostFunction] bool Valid() => View.Obj.Value == Obj`. It is proved where the package is built and known wherever it is read.
- **Calls.** A call that gets a package may change only the objects whose views are in it. The views in a package that arrives (a parameter, a call's result, a `ref` argument) are distinct from each other and from the views in hand. See samples/Good/Packages.cs.
- **Erasure.** It removes the proof parts: the package keeps its run-time fields, and a deconstruction keeps only those.

**Read shares (fractions).** `Own.Share(ref v, out Shared<T> s)` splits a read share off a view, and `Own.Unshare(ref v, s)` joins it back. This is the fractional permission of ATS's early prototype, in its counting form: every share holds the same small fraction ε, so a view with k shares out holds 1 − kε and is whole again only when all k are back.
- **Holding a share.** A `Shared<T>` is linear: it is passed, returned or dropped (`Own.Drop(s)`), never copied. Its holder relies on the object's invariant, which is proved when the share is handed over, and on nobody writing the object while the share is out. It cannot write the object itself.
- **The view while shares are out.** It cannot write the object, hand it to code that may (by `ref` or by value), or give it to an owner (`Own.Give`). A share given away for good leaves the object read-only for good.
- **Aliasing.** Shares may alias: two shares of one object are fine, as in `Within(in s1, g, in s2, g)` (samples/Good/Shares.cs).
- **`in Own<T>`.** A view lent `in` is a share for the call. Two `in` views may be the same view, and the invariant is proved when it is lent. Both used to be assumed, which was unsound.

**Predicates (Viper style; ATS's dataviews).** `Spec.Acc(o)` is write permission to an [Owned] object. A `[Predicate]` is a static bool method whose one-expression body describes permissions and facts. Permissions are `Spec.Acc` or other predicates, joined by `&&` or in the branches of `?:`. Predicates may be recursive. ATS's list segment `slseg_v` becomes:

```csharp
[Predicate]
public static bool Seg(SNode? from, SNode? to, int n) =>
    n == 0 ? from == to : n > 0 && from != null && Spec.Acc(from) && Seg(from.Next, to, n - 1);
```

- **Instances.** An instance `Seg(a, b, n)` is held like a view. `Spec.Fold(Seg(a, b, n))` puts the body's permissions into it, and its facts must hold (CSV1019). `Spec.Unfold` takes them out again, and the facts hold. Nobody can write a folded footprint.
- **Self-framing.** A predicate's body may read only objects it has `Spec.Acc` for, to its left (CSV1016, checked where it is declared). So what a held instance says cannot change behind its back.
- **Left to right.** Permissions in a body, precondition or invariant are taken in order, as in Viper: a fact that needs one (a read, or a function over a predicate, like `Buf(h, n).Length`) must come after it. Write `Heap(h, n) && n < Buf(h, n).Length`, not the other way round.
- **Contracts.** Permissions in `Spec.Requires` and `Spec.Ensures` are given by the caller and received by the callee, then back. A call changes only the footprints it gets. In a loop invariant, permissions go round the loop. The loop body may not use up permissions held outside it (CSV1016). Lemmas exchange permissions too (ATS's `slseg_v_extend` is a recursive lemma).
- **As a condition.** Elsewhere, `Spec.Acc(o)` and `Seg(a, b, n)` mean "in hand".
- **Functions over predicates.** A `[Pure]` or `[GhostFunction]` with a predicate in its precondition may `Spec.Unfold` it in its body, and it reads exactly that footprint. Its value then survives any change outside the footprint (the frame rule). For example, `Sum(keep, null, n)` is unchanged by reversing another list.
- **Views and `Spec.Acc`.** `Own.ToAcc(view)` turns a view into a plain permission, for folding. `Own.FromAcc(o, out view)` turns it back.
- **The sample.** samples/Good/ListSegments.cs has cons, length (walking with a segment from the head to the cursor), in-place reverse, and a ghost sum.
- **Limits.** Two copies of one instance are allowed only when its footprint is empty. A `[Pure]` callee must hold the predicates its precondition names (it is given nothing).

**Single fields.** `Spec.Acc(o, nameof(C.F))` is permission to write one field of an [Owned] object (Viper's `acc(o.f)`). Different code may hold different fields of one object.
- **Writing `o.F`** needs the whole object (a view, `Spec.Acc(o)`) or that field.
- **Split and rejoin.** Giving a field out of a whole object splits it: the other fields stay in hand, one by one. With every field in hand again, the object is whole, and its view can be handed over again.
- **Calls and predicates.** A call that gets a field changes only that field, so the rest of the object stays known. Fields can be folded into predicates like objects (samples/Good/FieldPermissions.cs).
- **Limits.** Only for sealed classes without an `[Invariant]`, and not `[Owns]` fields: invariants and ownership trees are about whole objects.

**Array cells.** `Spec.Acc(a, from, to)` is permission to write the cells `a[from..to)`, and `Spec.Acc(a)` is the whole array (Viper's quantified permissions over a range). Array permissions are opt-in per method: they apply in a method whose contract mentions them.
- **Such a method writes only cells in hand** (CSV1016). Its permissions come from its preconditions and from arrays it creates.
- **Calls to it change only the cells it gets,** plus arrays it allocates. Every other array keeps its contents, so `Halves` in samples/Good/ArrayPermissions.cs fills `a` twice and still knows `other` and the first half.
- **Disjointness.** Two permissions to one cell cannot both be in hand. So `SwapCells(a, i, j)`, given `Spec.Acc(a, i, i + 1) && Spec.Acc(a, j, j + 1)`, knows `i != j`, and `SwapCells(a, 1, 1)` is rejected at the call.
- **Calls from it.** It may not call a method that could write any array without saying which cells.
- **Methods without array permissions** hold every cell and hand cells out at calls. Their writes are checked too, but only cells they gave away (to a callee, or folded into a predicate) are missing.
- **In predicates.** A predicate's body may hold cells: ATS's viewtypes whose view includes an `array_v`. `CellStacks.Stack(s, n)` in samples/Good/CellStacks.cs holds the stack object and its array's cells. Folding gives the cells up into the instance, so nobody writes them while folded. A body may read only cells it has permission to. A call that gets the instance changes only its cells. A method that folds, unfolds or receives such a predicate starts with no cells but those it is given.
- **Constructors** exchange permissions like any call, so `new` can hand back the cells of an array it creates.
- **Limits.** Only C# arrays and `Mem` memory: a method with array permissions cannot write through a `Span` (whose base may be any array's cells), and reads through one are unknown values.

**Mem memory, on the same model.** ATS's manual memory (`Mem`, `Ptr<T>`) and its views (`PointsTo<T>` is `T @ l`, `ArrayView<T>` is `array_v`, `ArrayHole<T>`) are cells of the same heap as C# arrays, a row of its own, under the same cell permissions.
- **A view in hand holds its cells.** Two non-empty views in hand are of different cells, and a cell in hand is none of an array view's (samples/Good/MemoryModel.cs). ATS gets this from linearity, unstated; here it is a fact the solver can use.
- **Contents.** A view's contents (`Elems`, `Value`) are its own ghost value, as in ATS, tied to its cells whenever it comes into hand. Nobody changes cells that are held, so the tie stays true.
- **Calls.** A call changes only the cells whose views it gets, plus memory it allocates or frees; every view still in hand keeps its contents. `Split`, `Join`, `TakeOut`, `PutBack`, `Get` and `Read` change nothing. `Mem` writes no C# array, so memory code and array code frame each other: copying a view into an array with `Spec.Acc(target)` leaves the view's contents, and the array's other cells, known.
- **The API is unchanged**, and so are the samples that use it.

**One write rule.** A write of `o.F` is allowed if:
- `o` is `[Owned]` and its view is in hand (a live view, or `this` in its class's methods) — a `Spec.Modifies` frame does not count, since the view's holder relies on its invariant;
- or `o` is in the method's `Spec.Modifies` frame;
- or `o` was allocated in the method.

The styles mix: a method can have a `Spec.Modifies` frame and hold views, and an `[Owned]` class's methods can call framed methods.

## Object-oriented code

Verification is modular, with behavioural subtyping (Liskov), as in Dafny, Spec# and JML. A call through a base type is checked against the base's contract, and every override is checked against that contract too.
- **Contracts of abstract and interface members.** They have no body, so their `Spec` statements go in a *contract class*, the .NET Code Contracts pattern: `[ContractClassFor(typeof(IShape))] internal abstract class ShapeContract : IShape { ... }`. Its methods carry only specifications. It is not verified or run, and inside it a member's name means the member it specifies. For types without sources (the BCL, other assemblies) use a `[ContractsFor]` stub instead (see [Contracts for code without sources](library-contracts.md)).
- **Overrides inherit.** An override or implementation inherits its base's postconditions and frame, and its precondition unless it states its own.
  - **Preconditions:** it may require less, not more (CSV1018). If it weakens the precondition, the inherited postconditions are promised only where the base's precondition held.
  - **Postconditions:** it may promise more.
  - **Frames:** its `Spec.Modifies` must lie within the base's (CSV1018).
- **Virtual `[Pure]` queries** (`Area()`, an abstract `[Pure]` property `Balance`):
  - **One function.** A query and all its overrides are one function, named after the root declaration, so `s.Area()` means the same whatever the static type of `s`.
  - **Overrides are queries too.** An override of a `[Pure]` member is `[Pure]` itself, and the analyzer checks its body.
  - **Postconditions.** An override's extra postconditions hold for instances of its class.
  - **Bodies.** Its body defines the query only where it is the one that runs, a `sealed` override, for instances of its class. So after `Shape s = new Square(3)`, `s.Area() == 9` is provable.
- **Dynamic types.**
  - **What is known.** A value of a static type is an instance of it and its supertypes, and an object made by `new C()` is exactly a `C`.
  - **Disjointness.** Unrelated classes share no instances (single inheritance), and neither do a sealed class and anything not above it.
  - **Tests and casts.** `is`, `as`, patterns and casts use this. A downcast is assumed in ordinary code (a failed cast throws) and must be proved in proofs (CSV1011).
  - **Generics.** Generic types are not modelled.
- **Constructors.** `base(...)` and `this(...)` are checked calls on the object being built: preconditions checked, postconditions assumed. Field initializers run before `base(...)`, and not with `this(...)`.
- **Properties with code** are methods. A getter or setter with a body is verified and called with its contract, and so is an abstract, virtual or interface accessor. A `[Pure]` property is a function usable in specifications.
- **Invariants of immutable classes.** In a class whose instance fields are all `readonly`, an `[Invariant]`:
  - is proved where each constructor returns, and assumed wherever fields are read;
  - may not be relied on early: `this` may not escape a constructor before the invariant holds (CSV1015).

An `[Invariant]` on a mutable class gets a warning and is not used. Use the immutable, `[Owned]` or Dafny `Valid()` style for those.

**Dafny-style objects (dynamic frames).** For ordinary mutable classes, Dafny's `Valid()`/`Repr` idiom is available:
- **The pieces.** An object keeps a ghost set of the objects it is made of, `Ghost<ObjSet> Repr`, which is erased like every ghost. `ObjSet` has `Empty`, `Of`, `Add`, `Union`, `Contains`, `IsSubsetOf` and `IsDisjointFrom`. A ghost `[GhostFunction] bool Valid()` states the object's invariant over `Repr`.
- **`Spec.Modifies(W)`:** the method writes fields only of objects in `W` (as on entry) or of objects it allocates (CSV1017). A callee that writes fields but has no frame, or a wider one, is reported there too. A call to such a method changes nothing outside `W`: every other object's fields stay as they were, and only the callee's own Modifies is needed, not inferred effects.
- **`Spec.Reads(R)`:** a `[Pure]` or `[GhostFunction]` reads fields only of objects in `R` (CSV1017), and calls only functions whose `Reads` are within `R`. Its value then survives any change of fields that touches nothing in `R`. The verifier follows each change back (a field write touches one object, a call touches its `Modifies` and what it allocates) and keeps the old value whenever the change is disjoint from `R`. So `q.Valid()` survives `p.Swap()` when their representations are disjoint.
- **`Spec.Fresh(x)` / `Spec.Fresh(set)`** in a postcondition: allocated by the method, as Dafny's `fresh`. A constructor that ensures `Spec.Fresh(Repr.Value)` lets clients know two new objects have disjoint representations.
- **Allocation is tracked** (which objects exist), in programs that use dynamic frames or `[Owned]` classes. A new object is then none of the objects reachable through fields.
- **Arrays are outside dynamic frames.** Their contents are the array heap, as before, and any change to it ends the frame reasoning for `[Pure]` functions.
- **One style per class.** An `[Owned]` class is framed by its views; `Spec.Modifies`/`Spec.Reads` on its methods is an error (CSV1017).
