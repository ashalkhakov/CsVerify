# CsVerify

An applied type system for C#, written entirely in C#.

CsVerify brings the ideas of ATS (Hongwei Xi's *Applied Type System*) to C#. In the imperative style of Xanadu, ATS's C-like sibling, it gives you:

- static indices,
- dependent refinements,
- loop invariants,
- termination metrics,
- proof functions,
- linear *views* of memory.

It adds **no syntax**. There is no preprocessor, desugaring step or compiler fork. Every file you write is ordinary C#: it compiles with the normal compiler and gets full IDE support. The extensions are:

- a small specification library (`CsVerify.Spec`). Its statements are erased from normal builds.
- Roslyn analyzers that check linearity and ghost hygiene as you type.
- a verifier that turns specifications into verification conditions and proves them with Z3.
- an optional proof-erasure pass (`dotnet csverify erase`, or `-p:CsVerifyErase=true`). It builds the program with every proof removed and checks that what is left compiles. This is not a language layer: the sources stay plain C#, and a normal build of them is the reference meaning, which erasure must and does preserve.

CsVerify is the proving counterpart of [Tarp](https://github.com/ashalkhakov/Tarp). Tarp measures, by running your tests, which conditions and decisions were exercised (MC/DC). CsVerify proves statically that index bounds, contracts, invariants and termination hold on *every* path. Both work on the same plain C# sources.

```csharp
public static int BinarySearch(int[] a, int key)
{
    Spec.Requires(Spec.Forall(0, a.Length, i => Spec.Forall(i, a.Length, j => a[i] <= a[j])));
    Spec.Ensures<int>(r => -1 <= r && r < a.Length);
    Spec.Ensures<int>(r => r < 0 || a[r] == key);
    Spec.Ensures<int>(r => r >= 0 || Spec.Forall(0, a.Length, i => a[i] != key));
    int lo = 0, hi = a.Length;
    while (lo < hi)
    {
        Spec.Invariant(0 <= lo && lo <= hi && hi <= a.Length);
        Spec.Invariant(Spec.Forall(0, lo, i => a[i] < key));
        Spec.Invariant(Spec.Forall(hi, a.Length, i => a[i] > key));
        Spec.Decreases(hi - lo);
        int mid = lo + (hi - lo) / 2;          // every a[...] below is proved in bounds
        if (a[mid] < key) lo = mid + 1;
        else if (a[mid] > key) hi = mid;
        else return mid;
    }
    return -1;
}
```

## What it does

- **Proves your C# correct, with no new syntax.** Preconditions, postconditions, loop invariants, termination
  measures, lemmas and ghost values are calls to `Spec.*` that a normal build compiles away. The verifier turns them
  into verification conditions and proves them with Z3, method by method.
- **Rules out run-time errors.** Array and string indexes are in bounds, nothing null is dereferenced (C#'s nullable
  annotations become contracts, `null!` included), nothing divides by zero, and integer arithmetic does not overflow
  silently (it is bounded, as at run time).
- **Linear views of memory and objects, as in ATS.** Pointers with `PointsTo` views, array views that split and join,
  owned objects, predicates over linked structures, fractional permissions. Roslyn analyzers check that linear values
  are used exactly once, in the IDE as you type.
- **Objects too.** Data types with closed hierarchies, object invariants, heap fields with inferred frames, dynamic
  frames (`Spec.Modifies`, `Spec.Reads`), virtual members with contracts, exceptions, floating point as IEEE 754.
- **Proofs erased, and checked to be.** `-p:CsVerifyErase=true` builds the program with every proof removed, and
  checks that what runs never depended on one.
- **Static proof, then dynamic coverage.** With [Tarp](https://github.com/ashalkhakov/Tarp): verify, erase, and run
  the tests under Tarp's MC/DC instrumentation, on the program that runs.
- **Used on real code.** [CsLemon](#cslemon), SQLite's parser generator ported to C#, verifies completely (and the
  proof found a bug in the C original); the [samples](#samples) port proofs from ATS, Dafny and *ACSL by Example*.

What it does not prove, and why, is listed in [Limitations](docs/limitations.md).

## Using it in your project

You need the .NET 10 SDK and [Z3](https://github.com/Z3Prover/z3) on `PATH` (`brew install z3`, `apt install z3`,
`winget install z3`), or `CSVERIFY_Z3=/path/to/z3`.

Reference the `CsVerify` package (the `Spec` library, the analyzers, and the MSBuild targets) and install the
verifier, the `dotnet-csverify` tool:

```sh
dotnet add package CsVerify
dotnet new tool-manifest            # once per repository
dotnet tool install dotnet-csverify
```

Write specifications (see [Writing specifications](docs/specifications.md)), then verify:

```sh
dotnet build -p:CsVerifyEnabled=true     # verifies each project after it builds; failures are build errors
dotnet csverify src/MyProject            # or from the command line (files, directories, .csproj)
```

```
src/MyProject/Orders.cs(12,24): error CSV1003: index in 'a[i]' might be out of range
csverify: 4 of 5 methods verified, 42/43 obligations proved
```

Test projects are not verified (set `CsVerifyExclude` to leave out others). A normal build is unaffected: the
specifications compile away. To build the program with the proofs removed, and test it with Tarp's MC/DC coverage:

```sh
dotnet build -p:CsVerifyErase=true
dotnet tool install dotnet-tarp
dotnet tarp test -p:CsVerifyErase=true
```

[Running the verifier](docs/running.md) has the options and diagnostics; [CI](docs/ci.md) shows it in GitHub
Actions and Azure DevOps, with Tarp. Until the packages are on nuget.org, take them from a
[GitHub release](https://github.com/ashalkhakov/CsVerify/releases) (`--add-source <directory>`), or build them
(below).

## Building from source

```sh
dotnet build                 # everything
dotnet test                  # the tests (they need Z3)
dotnet run --project src/CsVerify.Verifier -- -v samples/Good
bash samples/e2e.sh          # the packages end to end: verify, erase and test with Tarp a copy of samples/Shop
```

```
src/CsVerify.Spec        Spec, Ghost<T>, attributes, Ptr<T>/PointsTo<T>/Mem    (net10.0, package "CsVerify")
src/CsVerify.Analyzers   LinearityAnalyzer, GhostAnalyzer, PurityAnalyzer      (netstandard2.0)
src/CsVerify.Verifier    the verifier: contracts, CFG symbolic execution, SMT-LIB/Z3, erasure, MSBuild targets
                         (net10.0, tool "dotnet-csverify")
tests/CsVerify.Tests     xUnit: analyzer rules, erasure, verifier proved/refuted per feature, samples
samples/Good, samples/Buggy, samples/Shop
docs                     the documentation
lemon/CsLemon            cslemon: Lemon ported to C# and verified
lemon/CsLemon.Runtime    the verified LR interpreter and validators, the run time of its C# parsers
lemon/tests              differential tests against C Lemon and its parsers, grammars
```

`dotnet pack src/CsVerify.Spec` and `dotnet pack src/CsVerify.Verifier` make the two packages. CI and releases are
in [CI](docs/ci.md#building-and-releasing-csverify).

## Samples

- **`samples/Good`** verifies completely, with no analyzer diagnostics: arrays and searches with full functional
  specifications, lemmas by induction, ghost indices, data types and their proofs, mutable and owned objects, dynamic
  frames, views of memory and arrays, exceptions, floating point, null references. Many are ports: from ATS (the
  INT2PROGINATS book, libatsc, ATS-playground, rtrace), Dafny's tutorial and test suite, *ACSL by Example*, and
  dafny-lemon.
- **`samples/Buggy`** has a planted bug in each method, which the verifier or the analyzers must report: off-by-one
  indexes, wrong invariants, leaks and double frees, unsound proofs.
- **`samples/Shop`** is a small solution using CsVerify from its package, as you would: `samples/e2e.sh` verifies
  it, erases it and runs its tests through Tarp.
- **`lemon/`** is CsLemon (below).

[Samples](docs/samples.md) describes each one.

## CsLemon

`lemon/` holds a larger example: the LEMON LALR(1) parser generator (SQLite's), ported from C to C# and verified
completely (no unexpected exceptions or silent overflow, non-null fields, invariants of its data structures; proving
one found an out-of-bounds write in C Lemon). Its output is byte-identical to C Lemon's on SQLite's grammar and the
others tested. It comes with an LR(1) interpreter proved sound, and validators for safety and completeness after
Jourdan, Pottier and Leroy's *Validating LR(1) Parsers*, and can generate C# parsers that run the verified
interpreter. See [lemon/README.md](lemon/README.md).

## Documentation

- [Writing specifications](docs/specifications.md): ATS concepts in C#, the specification library, the rules.
- [How it works](docs/how-it-works.md): the analyzers, and how the verifier turns code into verification conditions.
- [Data types and objects](docs/objects.md): data types and invariants, mutable and owned objects, predicates,
  dynamic frames, object-oriented code.
- [Integers, exceptions, floating point and null](docs/semantics.md).
- [Contracts for code without sources](docs/library-contracts.md): `[ContractsFor]` stubs and `[Model]` functions for
  the BCL and other assemblies, and the BCL contracts CsVerify ships.
- [Proof erasure](docs/erasure.md).
- [Running the verifier](docs/running.md): the command line, MSBuild, diagnostics.
- [CI](docs/ci.md): GitHub Actions, Azure DevOps, with Tarp; building and releasing CsVerify.
- [Samples](docs/samples.md).
- [Limitations](docs/limitations.md).

## Licence

MIT: see [LICENSE](LICENSE). The ported samples are rewritten, not copied, from the sources named under Samples. Those that carry a licence are MIT or MIT-style (Dafny, *ACSL by Example*, the INT2PROGINATS code, the ATS-CodeBook), and the rest are the author's own ATS repositories.

## References

- H. Xi, *Applied Type System* (extended abstract), TYPES 2003.
- H. Xi, *Applied Type System: An Approach to Practical Programming with Theorem-Proving*, arXiv:1703.08683.
- D. Zhu, H. Xi, *Safe Programming with Pointers through Stateful Views*, PADL 2005.
- H. Xi, *Imperative Programming with Dependent Types* (Xanadu), LICS 2000.
- H. Xi, F. Pfenning, *Eliminating Array Bound Checking Through Dependent Types*, PLDI 1998.
- H. Xi, *Introduction to Programming in ATS*, https://ats-lang.github.io (INT2PROGINATS).
- K. R. M. Leino et al., Dafny tutorial and test suite, https://github.com/dafny-lang/dafny.
