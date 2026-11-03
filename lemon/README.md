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
