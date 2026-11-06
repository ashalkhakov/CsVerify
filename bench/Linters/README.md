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

[InferSharp](https://github.com/microsoft/infersharp) (Facebook's Infer for .NET) runs on the compiled cases, in its
Docker image; without Docker its column stays empty. Then CsVerify verifies them.

```bash
bash bench/linters.sh
```

prints the table below. CI runs it too: the `linter-bench` job puts it in the job's summary. `LinterBenchTests` pins
CsVerify's column.

[DevSkim](https://github.com/microsoft/DevSkim) is not here. Its C# rules are security patterns (weak cryptography,
hard-coded secrets, insecure TLS settings) that neither kind of tool here looks for. StyleCop is here only to show
that a style checker reports none of these bugs.

## Results (2026-11-06)

A cell lists the rules that reported the case. Only rules that speak of the case's bug count (`bench/score.py` lists
them). Every other warning a tool raised on the cases is in the last row: style, naming, culture, and argument
validation.

| case | bug? | compiler | SDK (CA) | SharpSource | Meziantou | Roslynator | StyleCop | InferSharp | CsVerify |
|---|---|---|---|---|---|---|---|---|---|
| ThrowNull.Direct | bug | · | · | SS006 | · | · | · | · | CSV1013 |
| ThrowNull.Hidden | bug | · | · | · | · | · | · | · | CSV1013 |
| ThrowNull.Harmless | no | · | · | · | · | · | · | · | · |
| ModifiedWhileEnumerated.Direct | bug | · | · | SS057 | · | · | · | · | CSV1001 |
| ModifiedWhileEnumerated.HiddenAlias | bug | · | · | · | · | · | · | · | CSV1001 |
| ModifiedWhileEnumerated.HiddenCall | bug | · | · | · | · | · | · | · | CSV1001 |
| ModifiedWhileEnumerated.Harmless | no | · | · | · | · | · | · | · | · |
| Unobserved.Direct | bug | CS4014 | · | · | · | · | · | · | CSV1901 |
| Unobserved.Hidden | bug | · | · | · | · | · | · | · | CSV1901 |
| Unobserved.Harmless | no | · | · | · | · | · | · | · | CSV1901 |
| Disposal.LeakDirect | bug | · | CA2000 | · | · | · | · | · | CSV0020 |
| Disposal.LeakHidden | bug | · | CA2000 | · | · | · | · | · | CSV0020 |
| Disposal.LeakWriter | bug | · | CA2000 | · | · | · | · | PULSE_RESOURCE_LEAK | CSV0020 |
| Disposal.UseAfterDispose | bug | · | · | · | · | · | · | · | CSV0021 |
| Disposal.Harmless | no | · | · | · | · | · | · | · | · |
| DisposableField.Direct | bug | · | CA2213 | SS066 | · | · | · | · | CSV0022 |
| DisposableField.Harmless | no | · | · | · | · | · | · | · | · |
| FormatArguments.Direct | bug | · | CA2241 | SS014 | · | · | · | · | CSV1001 |
| FormatArguments.Hidden | bug | · | CA2241 | SS014 | · | · | · | · | CSV1001 |
| FormatArguments.Harmless | no | · | · | · | · | · | · | · | · |
| SwitchExpression.Direct | bug | CS8509 | · | SS018 | · | · | · | · | CSV1022 |
| SwitchExpression.Hidden | bug | CS8524 | · | · | · | · | · | · | CSV1022 |
| SwitchExpression.Harmless | no | CS8509 | · | · | · | · | · | · | · |
| Race.Direct | bug | · | · | · | · | · | · | THREAD_SAFETY_VIOLATION | CSV1023 |
| Race.Hidden | bug | · | · | · | · | · | · | THREAD_SAFETY_VIOLATION | CSV1023 |
| Race.Harmless | no | · | · | · | · | · | · | · | · |
| NaNComparison.Direct | bug | · | CA2242 | · | MA0082 | RCS1215 | · | · | · |
| NaNComparison.Harmless | no | · | · | · | · | · | · | · | · |
| UnusedResult.Direct | bug | · | CA1806 | SS040 | MA0060 | · | · | · | · |
| OrderByTwice.Direct | bug | · | · | SS055 | MA0030 | · | · | · | · |
| TimeSpanTicks.Direct | bug | · | · | SS068 | · | · | · | · | · |
| BlockingResult.Direct | bug | · | · | SS034 | · | · | · | · | · |
| IdenticalBranches.Direct | bug | · | · | · | MA0140 | RCS1211 | · | · | · |
| Null.Direct | bug | · | · | · | · | · | · | · | CSV1013 |
| Null.Definite | bug | · | · | · | · | · | · | NULLPTR_DEREFERENCE | CSV1013 |
| Null.DefiniteHelper | bug | · | · | · | · | · | · | NULLPTR_DEREFERENCE | CSV1013 |
| Null.Hidden | bug | · | · | · | · | · | · | · | CSV1013 |
| Null.Harmless | no | · | · | · | · | · | · | · | · |
| Bounds.Direct | bug | · | · | · | · | · | · | · | CSV1003 |
| Bounds.Hidden | bug | · | · | · | · | · | · | · | CSV1003 |
| Bounds.Harmless | no | · | · | · | · | · | · | · | · |
| Overflow.Direct | bug | · | · | · | · | · | · | · | CSV1010 |
| Overflow.Harmless | no | · | · | · | · | · | · | · | · |
| DivideByZero.Direct | bug | · | · | · | · | · | · | · | CSV1009 |
| DivideByZero.Harmless | no | · | · | · | · | · | · | · | · |
| StringIndex.Direct | bug | · | · | · | · | · | · | · | CSV1003 |
| StringIndex.Hidden | bug | · | · | · | · | · | · | · | CSV1003 |
| StringIndex.Harmless | no | · | · | · | · | · | · | · | · |
| Substring.Direct | bug | · | · | · | · | · | · | · | CSV1001 |
| Substring.Hidden | bug | · | · | · | · | · | · | · | CSV1001 |
| Substring.Harmless | no | · | · | · | · | · | · | · | · |
| MaskedIndex.Direct | bug | · | · | · | · | · | · | · | CSV1003 |
| MaskedIndex.Hidden | bug | · | · | · | · | · | · | · | CSV1003 |
| MaskedIndex.Harmless | no | · | · | · | · | · | · | · | · |
| Truncation.Direct | bug | · | · | · | · | · | · | · | CSV1010 |
| Truncation.Hidden | bug | · | · | · | · | · | · | · | CSV1010 |
| Truncation.Harmless | no | · | · | · | · | · | · | · | · |
| **bugs reported** | 40 | 3 | 8 | 10 | 4 | 2 | 0 | 5 | 34 |
| **harmless code reported** | 17 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 |
| **other warnings** (noise) | | 0 | 35 | 9 | 36 | 60 | 171 | 0 | 0 |

## What it shows

- **CsVerify reports 34 of the 40 bugs. The other tools together report 21, and 15 are reported by both.**
- **What only CsVerify reports: bugs that depend on values or on paths** (19 bugs).
  - **The hidden variants.** CsVerify reports all 14. The linters report 3, and only where the pattern stays
    visible: a constant format string, a leak with an early return, and an enum switch that names every member. The
    linters match a syntactic pattern:
    - `throw e!` where `e` may be null;
    - a list changed through an alias or a helper;
    - a task kept in a variable and never awaited;
    - a stream used after `Dispose`;
    - `s[s.IndexOf(':') + 1]` and `s.Substring(0, s.IndexOf('='))`, where `IndexOf` may say -1;
    - `table[hash >> 28]`, where a negative hash stays negative;
    - `(byte)(x & 0x1FF)`, a mask one bit too wide.
  - **The bug families no linter has a rule for:** null dereferences hidden by `!`, an index out of range, the
    midpoint overflow `(lo + hi) / 2`, division by zero, and the string and bit bugs above.
- **InferSharp reports what it can be sure of** (5 bugs, no false alarms, no other warnings).
  - **It finds** a value that is always null, also through a helper, a leaked `StreamWriter`, and races: a field written
    under a lock in one method and without it in another. CsVerify reports those too (CSV1023).
  - **It misses** a null that depends on an input (`Find(key)!.Length`, where `Find` may return null), and a leaked
    `File.OpenRead` or `FileStream`. It runs on a debug build here: on an optimized one it misses `Null.Definite` too.
- **What only the linters report: bugs about intent** (6 bugs): `d == double.NaN`, a discarded `Trim()`, `OrderBy`
  twice, `new TimeSpan(5)`, blocking on `.Result`, identical branches. Each of these runs without failing, but does
  something other than what was meant. CsVerify is about functional correctness: it reports such a bug only against a
  specification that says what was meant.
- **Harmless code that needs a proof.** `table[hash & 15] + table[hash >>> 28]` is in bounds for any `hash`, and
  `(byte)((x >> 8) & 0xFF)` always fits. CsVerify proves both.
- **False alarms.** One each from the compiler and CsVerify.
  - **The compiler** reports a switch whose missing value was returned for earlier.
  - **CsVerify** rejects a task that is stored and awaited later. That is not supported yet: it would run
    interleaved with the method.
- **Noise.** The linters raised 311 other warnings on these 57 cases, StyleCop 171 of them. InferSharp and CsVerify
  raised none.
