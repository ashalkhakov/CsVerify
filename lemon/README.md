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

### C# parsers

`cslemon -C grammar.y` writes `grammar.cs` instead of `grammar.c` and `grammar.h`: a parser that runs the verified LR
interpreter (`CsLemon.Runtime`, which it references) on the automaton CsLemon built, once that passes the safety
validator. The grammar's actions are C#: each rule's code runs with its aliases as variables of their symbols'
`%type`s (`%token_type` for terminals); `%include` goes at the top of the file, `%code` into the parser class,
`%extra_argument` becomes a parameter, and `%syntax_error`, `%parse_accept`, `%parse_failure` run as in Lemon. The
parser class is `<%name>Parser` (`ParseParser` by default), with the token codes Lemon's header has as constants, and
`Parse(int[] tokens, object?[] values[, extra])`. The actions run after the interpreter has parsed the input, on the
parse tree, in the order an LR parser reduces; on a syntax error, those of the reductions made before it run first,
as in Lemon's C parsers. Unlike them, it does not recover from an error inside the input (by dropping tokens): the
error is reported and parsing stops.

## Testing

`tests/difftest.sh <C lemon>` runs CsLemon and the C lemon it was ported from on every grammar in `tests/grammars`
(Lemon's calculator examples, SQLite 3.37.0's `parse.y`, and grammars for conflicts, directives, errors, empty
rules and unambiguous ones), with each of 14 option sets, and compares every output file, stdout, stderr and the
exit code byte for byte.
The C lemon is built from lemon-grove's `lemon.c`: `cc -o lemon lemon.c`.

`tests/parsertest.sh <C lemon>` compares the parsers themselves: each grammar in `tests/parsers` is there twice, with
C actions (built by the C lemon and cc) and with C# actions (built by `cslemon -C` and dotnet), and both parsers run
on the same token files and must print the same. `tests/lrtest.sh` runs the interpreter and the validators on the
test grammars (below).

## Verification

```
dotnet run --project src/CsVerify.Verifier -- lemon/CsLemon lemon/CsLemon.Runtime
```

verifies every method (310 of 310, the validated parser of the next section included). What that proves, beyond what C# already guarantees (no memory corruption):

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

That the generated parser is right is checked per grammar, by validation (next section); the table compression
(`yy_action`, `yy_lookahead`) is not yet covered, and the differential test is the evidence for it.

## A validated LR(1) parser

Following Jourdan, Pottier and Leroy, *Validating LR(1) Parsers* (ESOP 2012), written from the paper (see
`Lr/DESIGN.md`), `CsLemon.Runtime` has an LR interpreter and two validators, all verified:

- **Soundness** (`Interpreter.cs`): for any automaton, what the interpreter accepts comes with a parse tree of the
  start symbol whose leaves are exactly the input consumed.
- **Safety** (`Safety.cs`): if the safety validator accepts the automaton (with annotations CsLemon computes), the
  interpreter never reaches an internal error (a reduction finds its cells, every goto exists).
- **Completeness** (`Completeness.cs`): if the completeness validator accepts the automaton with its items (Lemon's
  configurations and follow sets, first sets, nullability), every sentence of the grammar is accepted, with its parse
  tree given back exactly (`ParseAccepts`); so the grammar is unambiguous.

`CSLEMON_VALIDATE=1 cslemon grammar.y` runs both validators on the automaton Lemon built (after conflict resolution,
before compression); `CSLEMON_PARSE=tokens cslemon grammar.y` parses a file of terminal names with the verified
interpreter. Every test grammar's automaton passes the safety validator, SQLite's included. Completeness holds only
for conflict-free grammars (`tests/grammars/expr.y`, `decls.y`): precedence declarations resolve the conflicts of an
ambiguous grammar, and the parser deliberately rejects some of its parse trees. `tests/lrtest.sh` checks parses,
both validators, and that corrupted automata are rejected.

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
