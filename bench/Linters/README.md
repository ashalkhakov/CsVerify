# The linter benchmark

Can CsVerify catch what linters catch ([#20](https://github.com/ashalkhakov/CsVerify/issues/20))? These cases are the
bugs that C# linters have rules for, and the bugs CsVerify checks for, each written three ways:

- **Direct:** the bug as the linter's documentation shows it.
- **Hidden:** the same bug behind an alias, a helper, or a value that is only sometimes bad.
- **Harmless:** code that looks like the bug but cannot go wrong. A tool that reports it raises a false alarm.

The cases are in [`Cases.cs`](Cases.cs), one `#region case <name> bug|ok` each, with no specifications: this is code as
people write it. The project builds them with the linters as analyzers:
- [SharpSource](https://github.com/Vannevelj/SharpSource);
- [Meziantou.Analyzer](https://github.com/meziantou/Meziantou.Analyzer);
- [Roslynator](https://github.com/dotnet/roslynator);
- [StyleCop](https://github.com/DotNetAnalyzers/StyleCopAnalyzers);
- the .NET SDK's own analyzers (`CA`, with `AnalysisMode` `All`);
- the compiler's warnings, nullable ones included.

Then CsVerify verifies them.

```bash
bash bench/linters.sh
```

prints the table below. CI runs it too: the `linter-bench` job puts it in the job's summary. `LinterBenchTests` pins
CsVerify's column.

[DevSkim](https://github.com/microsoft/DevSkim) is not here. Its C# rules are security patterns (weak cryptography,
hard-coded secrets, insecure TLS settings) that neither kind of tool here looks for. StyleCop is here only to show
that a style checker reports none of these bugs.

## Results (2026-11-05)

A cell lists the rules that reported the case. Only rules that speak of the case's bug count (`bench/score.py` lists
them). Every other warning a tool raised on the cases is in the last row: style, naming, culture, and argument
validation.

| case | bug? | compiler | SDK (CA) | SharpSource | Meziantou | Roslynator | StyleCop | CsVerify |
|---|---|---|---|---|---|---|---|---|
| ThrowNull.Direct | bug | · | · | SS006 | · | · | · | CSV1013 |
| ThrowNull.Hidden | bug | · | · | · | · | · | · | CSV1013 |
| ThrowNull.Harmless | no | · | · | · | · | · | · | · |
| ModifiedWhileEnumerated.Direct | bug | · | · | SS057 | · | · | · | CSV1001 |
| ModifiedWhileEnumerated.HiddenAlias | bug | · | · | · | · | · | · | CSV1001 |
| ModifiedWhileEnumerated.HiddenCall | bug | · | · | · | · | · | · | CSV1001 |
| ModifiedWhileEnumerated.Harmless | no | · | · | · | · | · | · | · |
| Unobserved.Direct | bug | CS4014 | · | · | · | · | · | CSV1901 |
| Unobserved.Hidden | bug | · | · | · | · | · | · | CSV1901 |
| Unobserved.Harmless | no | · | · | · | · | · | · | CSV1901 |
| Disposal.LeakDirect | bug | · | CA2000 | · | · | · | · | CSV0020 |
| Disposal.LeakHidden | bug | · | CA2000 | · | · | · | · | CSV0020 |
| Disposal.UseAfterDispose | bug | · | · | · | · | · | · | CSV0021 |
| Disposal.Harmless | no | · | · | · | · | · | · | · |
| DisposableField.Direct | bug | · | · | SS066 | · | · | · | · |
| DisposableField.Harmless | no | · | · | · | · | · | · | · |
| FormatArguments.Direct | bug | · | CA2241 | SS014 | · | · | · | · |
| FormatArguments.Hidden | bug | · | CA2241 | SS014 | · | · | · | · |
| FormatArguments.Harmless | no | · | · | · | · | · | · | · |
| EnumSwitch.Direct | bug | CS8509 | · | SS018 | · | · | · | · |
| EnumSwitch.Harmless | no | CS8509 | · | SS018 | · | · | · | · |
| NaNComparison.Direct | bug | · | CA2242 | · | MA0082 | RCS1215 | · | · |
| NaNComparison.Harmless | no | · | · | · | · | · | · | · |
| UnusedResult.Direct | bug | · | CA1806 | SS040 | MA0060 | · | · | · |
| OrderByTwice.Direct | bug | · | · | SS055 | MA0030 | · | · | · |
| TimeSpanTicks.Direct | bug | · | · | SS068 | · | · | · | · |
| BlockingResult.Direct | bug | · | · | SS034 | · | · | · | · |
| IdenticalBranches.Direct | bug | · | · | · | MA0140 | RCS1211 | · | · |
| Null.Direct | bug | · | · | · | · | · | · | CSV1013 |
| Null.Hidden | bug | · | · | · | · | · | · | CSV1013 |
| Null.Harmless | no | · | · | · | · | · | · | · |
| Bounds.Direct | bug | · | · | · | · | · | · | CSV1003 |
| Bounds.Hidden | bug | · | · | · | · | · | · | CSV1003 |
| Bounds.Harmless | no | · | · | · | · | · | · | · |
| Overflow.Direct | bug | · | · | · | · | · | · | CSV1010 |
| Overflow.Harmless | no | · | · | · | · | · | · | · |
| DivideByZero.Direct | bug | · | · | · | · | · | · | CSV1009 |
| DivideByZero.Harmless | no | · | · | · | · | · | · | · |
| **bugs reported** | 26 | 2 | 6 | 10 | 4 | 2 | 0 | 16 |
| **harmless code reported** | 12 | 1 | 0 | 1 | 0 | 0 | 0 | 1 |
| **other warnings** (noise) | | 0 | 25 | 8 | 26 | 40 | 101 | 0 |

Bugs reported by some tool: 26 of 26.

## What it shows

- **The tools mostly catch different bugs.** Of the 26 bugs:
  - the linters together report 15, and CsVerify 16;
  - both report 5: throwing null, changing a list in its own `foreach`, a dropped task, and a stream never disposed
    (two cases).
- **What only CsVerify reports: bugs that depend on values or on paths** (11 bugs).
  - **The hidden variants.** CsVerify reports 7 of the 8. The linters report 2, and only where the pattern stays
    visible: a constant format string, and a leak with an early return. The linters match a syntactic pattern:
    - `throw e!` where `e` may be null;
    - a list changed through an alias or a helper;
    - a task kept in a variable and never awaited;
    - a stream used after `Dispose`.
  - **The bug families no linter has a rule for:** null dereferences hidden by `!`, an index out of range, the
    midpoint overflow `(lo + hi) / 2`, and division by zero.
- **What only the linters report: bugs about intent, and some CsVerify could check but does not** (10 bugs).
  - **Intent:** `d == double.NaN`, a discarded `Trim()`, `OrderBy` twice, `new TimeSpan(5)`, blocking on `.Result`,
    identical branches. Each of these runs without failing, but does something other than what was meant. CsVerify
    would report them only against a specification that says what was meant.
  - **Real gaps:**
    - A format string with too few arguments. It throws `FormatException`, and a precondition on `string.Format`
      could say so.
    - A switch expression that misses an enum value. Its `SwitchExpressionException` counts as an exception the
      method may throw.
    - A disposable field its owner never disposes.
- **False alarms.** One each from the compiler, SharpSource and CsVerify:
  - **The compiler and SharpSource** report a switch that misses `Blue` even after `Blue` was handled earlier.
  - **CsVerify** rejects a task that is stored and awaited later. That is not supported yet: it would run
    interleaved with the method.
- **Noise.** The linters raised 200 other warnings on these 38 cases, StyleCop 101 of them. CsVerify raised none:
  it reports only what may go wrong at run time.

The cases were chosen from the linters' bug rules (style, naming and API-preference rules left out), plus four bug
families that CsVerify checks and the linters do not. That choice favours bugs over style, but not CsVerify: ten of the
bugs are ones only the linters report.
