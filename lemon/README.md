# CsLemon

The [LEMON](https://sqlite.org/lemon.html) LALR(1) parser generator (SQLite's), ported from C to C# and checked by
CsVerify. It is a port of lemon-grove's sliced sources (SQLite check-in f2f279b2, 2021); `CsLemon/lempar.c` is the
parser template of the same version. Lemon is in the public domain.

The C function and struct field names are kept, so each file reads side by side with its C original:

| C | C# |
|---|---|
| struct.h | Struct.cs |
| set.c, plink.c, error.c, msort.c, table.c | Support.cs |
| main.c, option.c | Program.cs |
| parse.c | Parser.cs |
| build.c | Build.cs |
| configlist.c | ConfigList.cs |
| action.c | Actions.cs |
| report.c | Report.cs |

## Usage

```
dotnet run --project lemon/CsLemon -- [options] grammar.y
```

The options are Lemon's (`-x` for the version, `-g` to reprint the grammar, `-s` for statistics, `-D` for `%ifdef`
macros, and so on). It writes `grammar.c`, `grammar.h` and the report `grammar.out` as Lemon does.

## Testing

`tests/difftest.sh <C lemon>` runs CsLemon and the C lemon it was ported from on every grammar in `tests/grammars`
(Lemon's calculator examples, SQLite 3.37.0's `parse.y`, and grammars for conflicts, directives, errors and empty
rules), with each of 14 option sets, and compares every output file, stdout, stderr and the exit code byte for byte.
The C lemon is built from lemon-grove's `lemon.c`: `cc -o lemon lemon.c`.

## Verification

```
dotnet run --project src/CsVerify.Verifier -- lemon/CsLemon
```

verifies every method (173 of 173). What that proves, beyond what C# already guarantees (no memory corruption):

- **No unexpected exceptions.** Every array and string index is in range, nothing null is dereferenced, nothing is
  divided by zero, and every call's precondition holds.
- **No silent overflow.** C# integers wrap by default; every arithmetic operation is proved not to overflow, or is
  `checked` (counters such as line numbers and error counts: they throw rather than wrap).
- **Non-null means non-null.** Fields, locals and parameters of non-nullable type never hold null (`null!` is not
  trusted); the fields C always sets are `required`.
- **Some invariants of Lemon's own data structures**: the action table under construction (`Actions.Wf`: its tables
  are distinct and as long as their allocations, lookaheads are symbols, every slot from `nAction` on is empty), the
  grammar file parser's state (`Parser.Wf`), sets (elements below the set size), the merge sorts' bins.

Proving `Actions.Wf` found a bug in C Lemon: `acttab_insert` reserves `nsymbol + 1` slots, but placing a transaction
can need `mnLookahead + mxLookahead + 2`; then the search for a hole stops short and C writes past the table. CsLemon
reserves `2 * nsymbol + 1`, which is enough (a hole is found by `nAction + mnLookahead + 1`); only the size changes.

It does **not** prove that the generated parser is right (that the states, follow sets, conflict resolution and table
compression implement the grammar's LALR(1) automaton). The differential test is the evidence for that.

### Run-time checks

Some facts hold across the whole grammar graph (linked lists of rules, configurations and actions), where the
verifier is not shown them. They are checked at run time with `Checks.That` (Support.cs), which throws instead of
running into undefined behaviour as C would; the verifier assumes them after. Each is a bug in Lemon if it fails:

| Where | Checked |
|---|---|
| `Rule.Rhs(i)`, `Symbol.Sub(k)` | a rule's right-hand side holds `nrhs` symbols; a multiterminal's `subsym` holds `nsubsym` |
| `Symbol.FirstSet()`, `Config.Fws()` | first sets exist once computed; a configuration's follow set until it is freed |
| `LemonAction.Rp()`, `Report.Stp` | a reduce action has its rule, a shift its state |
| `Lemon.Sym(i)`, `Lemon.Sorted(i)`, `Lemon.StartRule()` | the symbol and state tables are full; the grammar has rules |
| `Sets.SetAdd`, `Sets.SetFind` | set elements are terminals, below the set size |
| Parser.cs | the pstate's first `nrhs` symbols are set; `nsubsym` is never negative |
| Report.cs | counts are non-negative and consistent; a rule has `nrhs` aliases; lookaheads are symbols; C's `assert`s in `acttab_insert` and `CompressTables`; the sorts permute full tables |
| Program.cs | the option table is full; `argv` holds strings |

Run `grep -n Checks.That lemon/CsLemon/*.cs` for each one with its reason.

### Changes made for the verifier

The output stays byte-identical to C Lemon's (the differential test). The code changed where the verifier needed it:
comparisons return the sign of C's difference (which could overflow); long functions (`translate_code`,
`ReportTable`, `preprocess_input`) are split into helpers, in C's order; a few library calls the verifier treats as
able to change anything are avoided (integer formatting is written out, the action tables are copied before output);
list heads are returned instead of written through `ref`.
