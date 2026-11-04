# Contracts for code without sources

The verifier reads contracts from source code. The BCL and third-party assemblies have none, so without help a call
into them gets no contract: a result of its declared type, its nullability annotations, and a fixed frame rule
(see [How it works](how-it-works.md#layer-2-the-verifier-z3-separate-process)). *Stubs* give such members contracts,
and *model functions* give their objects ghost state to state them over.

CsVerify ships stubs for part of the BCL (`List<T>`, `Dictionary<K, V>`, `string`, `int.Parse`, `Math`). They work
without any setup. To use their model functions in specifications, add `using CsVerify.Bcl;`.

```csharp
using System.Collections.Generic;
using CsVerify;
using CsVerify.Bcl;

public static List<int> Squares(int n)
{
    Spec.Requires(0 <= n && n <= 1000);
    Spec.Modifies(ObjSet.Empty);                       // changes no list the caller has
    Spec.Ensures<List<int>>(r => r.Count == n);
    Spec.Ensures<List<int>>(r => Spec.Forall(0, n, i => r[i] == i * i));
    var squares = new List<int>(n);
    for (int i = 0; i < n; i++)
    {
        Spec.Invariant(0 <= i && i <= n && squares.Count == i);
        Spec.Invariant(Spec.Forall(0, i, j => squares[j] == j * j));
        squares.Add(i * i);
    }
    return squares;
}
```

`samples/Good/LibraryContracts.cs` has more, and `samples/Buggy/LibraryContractBugs.cs` has what the contracts catch:
an index or a key that may be missing, `Substring` past the end, a list changed outside the caller's frame.

## Stubs: `[ContractsFor]`

A stub is a class marked `[ContractsFor(typeof(X))]`. Its methods match X's members by signature, and each
method's leading `Spec.Requires`/`Ensures`/`EnsuresOnThrow`/`Modifies` statements become that member's contract.

| X's member | the stub's method |
|---|---|
| static method `M(p…)` | `static R M(p…)` |
| instance method `M(p…)` | `static R M(X @this, p…)`: `@this` is the receiver |
| property getter / setter | `get_P(X @this)` / `set_P(X @this, T value)`, or a getter named `P` |
| indexer | `get_Item(X @this, int index)`, `set_Item(X @this, int index, T value)` |
| constructor `X(p…)` | `static X @new(p…)` |

A generic type's stub has its type parameters, in order. A generic method's stub has the method's.

```csharp
[ContractsFor(typeof(List<>))]
public static class ListContracts<T>
{
    [Pure]
    public static T get_Item(List<T> @this, int index)
    {
        Spec.Requires(0 <= index && index < @this.Size());
        Spec.Ensures<T>(r => Ghost.Of(r) == @this.Items()[index]);
        throw null!;
    }

    public static void Add(List<T> @this, T item)
    {
        Spec.Modifies(ObjSet.Of(@this));
        Spec.Ensures(@this.Size() == Spec.Old(@this.Size()) + 1);
        Spec.Ensures(@this.Items() == Spec.Old(@this.Items()).Update(Spec.Old(@this.Size()), Ghost.Of(item)));
        throw null!;
    }
}
```

- **Preconditions are proved** at every call (CSV1001), like any callee's.
- **Postconditions are assumed, never proved.** A stub's contract is trusted, like `[Trusted]`. A wrong stub makes
  wrong things provable (`StubTests.StubContracts_AreTrusted_AndCounted` shows one). CsVerify's own stubs are tested
  against the real BCL instead ([below](#conformance-tests)). Every run counts the stubbed
  members its proofs used: the summary line ends with `, N library contract(s) assumed`, and `-v` lists them
  (`assumed System.Collections.Generic.List<T>.Add(T)`).
- **Frames.** A stub's `Spec.Modifies` says which objects' model state the member may change, as for source methods:
  only the model functions of its own type (a list's for `List<T>`'s stub). Without one, the member changes no model
  state, except that a constructor sets up the new object's. A caller with `Spec.Modifies` must cover what the stubbed
  callee changes (CSV1017).
- **Arrays.** A stubbed member that may write arrays (one it is handed) writes only the arrays its `Spec.Modifies`
  names: `Array.Fill(a, 0)` leaves every other array as it was. A library method without a stub, handed an array, may
  still write any array.
- **Virtual members.** A stub may specify a virtual or abstract member (`TextWriter.Write`). A call through it gets the
  stub's contract and effects, plus whatever the overrides in your sources may do (a `TextWriter` subclass of yours
  that writes a field). Your overrides inherit the stub's contract, and are checked against it like any override
  ([Object-oriented code](objects.md#object-oriented-code)). The library's own overrides (`StreamWriter.Write`) keep
  the contract of the member they override: trusted, like the rest.
- **Async stubs.** A stub declared `async` (`public static async Task<int> ReadAsync(Stream @this, ...)`) specifies
  what awaiting the member gives: `Spec.Ensures<int>(r => r <= count)` is of the awaited value. A call of the member
  that is not awaited at once gets no contract. The conformance tests wait for the task.
- **Fresh results.** A postcondition `Spec.Fresh(r)` makes a returned array a new one, distinct from every array in
  scope (`list.ToArray()`).
- **`[Pure]` stubs** may be used in specifications (`l.Count`, `l[i]`, `d.ContainsKey(k)`, `string.IsNullOrEmpty(s)`).
  If one has a postcondition `r == E`, or `Ghost.Of(r) == E`, its value is E itself. So `l[i]` is the model's element,
  and a quantified fact about `l[j]` carries across a change to another element. A `[Pure]` stub has no effects
  (trusted).
- **Bodies** are never run or verified. Write `throw null!`, assigning `out` parameters first if a postcondition names
  them (C#'s definite assignment applies under `CSVERIFY_SPEC`).
- **Precedence.** A stub in your sources wins over CsVerify's for the same member.
- **Mistakes are errors.** A stub method that matches no member (a typo, a wrong parameter type, a missing `@this`) is
  reported as CSV1021, so it can't leave a member silently unspecified.
- A stub generalises `[ContractClassFor]` ([Object-oriented code](objects.md#object-oriented-code)), which specifies the
  interfaces and abstract classes of your own sources.

## Model functions: `[Model]`

A library object's state is hidden. A model function names some of it as ghost state:

```csharp
[Model] public static Seq<T> Items<T>(this List<T> list) => throw null!;
[Model]
public static int Size<T>(this List<T> list) { Spec.Ensures<int>(r => r >= 0); throw null!; }
```

A model function is static. Its first parameter is the object, of a reference type. It may take a second parameter, a
key (a value at each index or key), and then it may not return a ghost collection. To the verifier it is a ghost field
of the object, which stubs read and change and specifications read. Like a field, it changes only through calls that
may write it: a stubbed member within its `Spec.Modifies`, or a library method without a stub that is handed something
that may lead to the object (CsVerify cannot know what such a method does). Its own `Spec.Ensures` hold of every value
it has (trusted). Model functions are ghost: calls to them are specification only, and erased.

Without model functions, a library property was a new unknown value at each read in code, and could not appear in a
specification (CSV1900, CSV1901). With a `[Pure]` stub defined by a model, `l.Count` is a function of the list's state.

## CsVerify's BCL contracts (`CsVerify.Bcl`)

The stubs are in [`src/CsVerify.Spec/Bcl`](../src/CsVerify.Spec/Bcl). They are part of the `CsVerify` package (so a
normal build, and the analyzers, see the model functions), and the verifier compiles them in from source.

| type | models | members |
|---|---|---|
| `List<T>` | `Items()`: `Seq<T>`, `Size()` | constructors, `Count`, the indexer (get and set), `Add`, `Insert`, `AddRange` (keeps the elements, grows), `RemoveAt`, `RemoveRange`, `Clear`, `Reverse`, `Sort` (frame and count), `ToArray`, `GetRange`, `IndexOf`, `Contains`, `Remove(T)` (by `Spec.Equal`: below), `GetEnumerator`; `foreach` (below) |
| `Array` | the arrays' contents (built in) | `Empty`, `Fill` (whole and a range), `Reverse<T>`, `Copy` (bounds, the frame, and the destination's other elements), `Resize` (the new length), `IndexOf<T>` (its range), `Sort<T>` (the frame) |
| `Dictionary<K, V>` | `Domain()`: `Map<K, bool>`, `Entries()`: `Map<K, V>`, `Size()` | constructors (with a capacity too), `Count`, `ContainsKey`, the indexer (get and set), `Add`, `TryAdd`, `Remove` (and with the value out), `TryGetValue`: keys compare as the dictionary does (below) |
| `IReadOnlyList<T>`, `IList<T>`, `IReadOnlyCollection<T>`, `ICollection<T>` | a `List`'s, an array's (built in) | `Count`, the indexer (get and set), `Contains`, `IndexOf`, `Add`, `Insert`, `RemoveAt`, `Remove`, `Clear`, and `foreach`: by what the object is (below) |
| `HashSet<T>` | `Members()`: `Map<T, bool>`, `Size()` | constructor, `Count`, `Contains`, `Add`, `Remove` (their results), `Clear` |
| `Stack<T>` | `Items()` from the bottom, `Size()` | constructor, `Count`, `Push`, `Pop`, `Peek` (not empty: a precondition), `Clear` |
| `Queue<T>` | `Items()` from the head, `Size()` | constructor, `Count`, `Enqueue`, `Dequeue`, `Peek` (not empty: a precondition), `Clear` |
| `StringBuilder` | `Size()` (its `Length`; the characters are not modeled) | constructors, `Length` (get and set), the indexer (its range), `Append` (`char`, a repeated `char`, `string`, part of a `string`, `StringBuilder`, `int`, `long`, `object`), `AppendLine`, `Insert(int, string)`, `Remove`, `Clear`, `ToString` (whole and a range): each `Append` returns the builder |
| `TextWriter` | | `Write`, `WriteLine` (for `string`, `char`, `int`, `long`, `bool`, `object`, format strings, a `char[]` range) and `Flush`: they change nothing modeled |
| `Stream` | | `Read(byte[], int, int)` and `ReadAsync(byte[], int, int)` (an async stub): the range is in the buffer, only the buffer changes, at most `count` bytes are read |
| `ArgumentException` | | `ThrowIfNullOrEmpty`, `ThrowIfNullOrWhiteSpace`: the argument is not null and not empty when they return |
| `MemoryExtensions` | spans (built in) | `IndexOf`, `LastIndexOf`, `IndexOfAny` (their ranges), `SequenceEqual` (equal lengths when true), `StartsWith` (the prefix fits): what they say of elements would depend on `T`'s `Equals` |
| `BinaryPrimitives` | | `Read{Int16,UInt16,Int32,UInt32,Int64}{Big,Little}Endian`: the span holds the bytes |
| `string` | its `Length` (built in) | `IsNullOrEmpty`, `Substring`, `Concat(string, string)`, `StartsWith`, `EndsWith`, `Contains`, `IndexOf(char)`, `LastIndexOf(char)`, `Trim`, `ToUpperInvariant`, `ToLowerInvariant` |
| `int` | | `Parse(string)`, `TryParse(string, out int)` |
| `Math` | | `Clamp` and `Sign` for `int` and `long` |

`Seq.Contents(a)` is an array's elements whatever its type, for contracts over `System.Array`, whose elements C# cannot
index. Compare them with each other, not with typed values. `Array.Copy` says nothing of the elements it copies,
because it converts between element types (`int[]` to `long[]` or `object[]`), and the converted values are not the ones
stored.

**A collection changed while it is enumerated.** `List`, `Dictionary`, `HashSet`, `Stack` and `Queue` each have a
`Version()` model, which a change of the collection (within its stub's `Spec.Modifies`) may change. An enumerator
remembers its collection and the version from `GetEnumerator`, and each `MoveNext` requires the version to be the same
still. Otherwise it would throw `InvalidOperationException` ("Collection was modified"), and that is reported (CSV1001):

```csharp
foreach (var x in list) { if (x > 0) list.Add(x); }   // reported: the next MoveNext throws
```

In a `foreach`, "the version is still the enumerator's" is inferred as a loop fact. It holds where the loop changes
another collection (one shown to be different), or changes this one and leaves at once (`break`): the next `MoveNext`
is what fails, and it never runs. `Dictionary.Remove`, and overwriting an existing key's value (`d[k] = v`), keep the
version, since both are allowed during enumeration from .NET Core 3.0 on. The conformance tests check that against
the collections' own `_version`.

A dictionary's `Keys` and `Values` are views of it: their enumerators check the dictionary's version, and their
`Count` is its `Count`. In a `foreach` over a dictionary, the current pair is one the dictionary has
(`d.ContainsKey(kv.Key)`, `d[kv.Key] == kv.Value`); over its `Keys`, the current key is one of them. So
`foreach (var kv in d) d[kv.Key] = 0;` is fine, and `foreach (var k in d.Keys) d[k + 1] = 0;` is reported.

**Lists through their interfaces.** `Count` and the indexer of `IReadOnlyList<T>`, `IList<T>`,
`IReadOnlyCollection<T>` and `ICollection<T>` read what the object is. For a `List<T>` they read its models, so a list
passed as an `IReadOnlyList<T>` keeps its facts, and a change made through the list is seen through the interface.
For an array they read its length and cells. For anything else (a library wrapper, a collection the verifier does not
model) they read a function of the heap and the model state, which is the same between two reads and changes whenever
those might. The indexer's range is checked as the list's (CSV1003). If a class of the program implements one of these
interfaces, that last case is an unknown value at each read, since the program's own list could change in ways no
model follows.

`Contains` and `IndexOf` search as `Spec.Equal` compares, over the same reads. Writes (the indexer, `Add`, `Insert`,
`RemoveAt`, `Remove`, `Clear`) change, by what the object is:
- a `List`'s models, as its own contracts say;
- an array's cells for the indexer. The other writes throw `NotSupportedException`, since arrays are fixed-size.
- anything at all for another collection, as a library call without a contract may.

A `foreach` over an `IReadOnlyList<T>` or `IList<T>` whose loop changes no state (and when the program implements no
list of its own) runs over `Count` and the indexer, like a foreach over an array: `Spec.Index(x)` is its index, it ends
by itself, and its enumerator's `Dispose` is taken to do nothing. Library collections are trusted to enumerate as they
index.

**LINQ.** Over a `List`, an array, an `IReadOnlyList<T>` or an `IList<T>` (read as above), `Count`, `Any`, `All`,
`Contains`, `First`, `FirstOrDefault`, `Last`, `LastOrDefault`, `ElementAt`, `ToList` and `ToArray`, and `List`'s `Find`,
`FindIndex`, `Exists` and `TrueForAll`, are exact. A predicate that is a pure lambda (an expression with no assignments,
calling only `[Pure]` members: `x => x > k`, `s => s.Length == 3`) is inlined as a condition on each element, so
`a.First(x => x > 5)` is the first element above 5 and `a.All(x => x > 0)` a quantifier. What would throw (`First` of a
sequence with no match, `ElementAt` past the end) is reported (CSV1001). The lambda's own obligations are checked where
it is verified, as a unit of its own. With another lambda, or another source, the call is a library call as before.

**Lazy LINQ.** `Select`, `Where`, `Take` and `Skip` (with pure lambdas, over what the verifier reads or over each
other) make views. A view is read when it is enumerated: by the eager methods above, `ToList`, `ToArray`, or a
`foreach`. It reads its source as it is then, and runs its lambda then, on what it captures as it is then. So
`var q = list.Select(x => x); list.Add(5); q.First()` is 5. A `Select`'s elements are its selector's values. A
`Where`'s elements are the matching ones, in order and all of them: `a.Where(x => x > 5).Count()` is exact. A
`foreach` over such a chain, whose loop changes no state, runs over the view like a foreach over an array. A view
kept in a variable is known in its own method only.

**Equality.** `Spec.Equal(a, b)` is what `EqualityComparer<T>.Default.Equals(a, b)` gives, for `T` as the call
instantiates it. It is exact where the verifier knows `T`'s `Equals`: numbers, chars, bools, enums, strings (their
contents), classes that do not override `Equals` (references), and data records. For other types (a class with its own
`Equals`, a struct, `double`, whose `NaN.Equals(NaN)` is true) it is a relation the verifier knows nothing of, fixed
within one call's contract. So `List<int>.IndexOf(7)` is exact, and `List<Customer>.Contains(c)`, with
`Customer.Equals` overridden, says nothing it should not. A `Map`'s keys compare the same way: by value where `T`'s
equality is known, and otherwise through a key function, which is sound as long as a key does not change while it is
one (which .NET's dictionaries and sets require too). A dictionary or set built with a custom comparer is not modeled
apart from this. `Sort` gives the frame and the count only.

**`foreach` over a `List<T>`** runs like a `foreach` over an array, over the list's model: the iteration variable is
`Items()[i]` for `i` from 0 to `Size()`, `Spec.Index(x)` is `i`, and the loop ends by itself. That holds only if the loop
changes no list. In .NET, changing the list makes the next `MoveNext` throw. So if the loop may change any model state,
it goes through the enumerator instead: `GetEnumerator`, `MoveNext` and `Current` are calls, and the elements are
unknown values (CSV1900). Either way the enumerator's `Dispose`, which does nothing for a list, is left out.

`Map<K, V>` is a ghost total map, like `Seq<T>` but indexed by keys: `m[k]`, `m.Update(k, v)`, `Map.Const<K, V>(v)`, `==`.

`Math.Min`, `Max` and `Abs` stay built into the verifier. Their definitions are needed inside the definitions of
`[Pure]` functions, which unfold only one level, and `Abs(int.MinValue)` throws `OverflowException`, which is not a
precondition. The floating-point functions are built in too (see [Floating point](semantics.md#floating-point)).

## Conformance tests

Every stub in `CsVerify.Bcl` is run against the real BCL on random inputs (`StubConformanceTests`). For each stub
method the test generates a checker and compiles it:
1. it assumes the preconditions, skipping inputs that break them;
2. it copies the arguments, for `Spec.Old`;
3. it calls the real member;
4. it checks the postconditions, and that only the objects `Spec.Modifies` names changed their models.

The model functions get their run-time meanings: `Items()` is the list's elements, `Size()` its `Count`, `Domain()`
its keys. Where a model means nothing (`Items()` past `Size()`, `Entries()` at a missing key) its value is
undetermined, and matches anything.

A `[Pure]` stub's member must not throw where its preconditions hold, because the verifier assumes it returns. Any
other member may throw, since every call may in CsVerify's model; then its `EnsuresOnThrow` and its frame are checked.
Type parameters are `int`, and `string` for a dictionary's keys. `WrongStubs_AreCaught` checks that the checkers
catch wrong stubs: a wrong count, a write outside the frame, a `[Pure]` member that throws, a wrong `Spec.Old` under a
quantifier. A stub added to `CsVerify.Bcl` is tested the same way, with no test to write, as long as its parameter
types have random inputs in the test.

Where the contracts are weaker than the library, or trusted for more than they say, see
[Limitations](limitations.md).
