#!/bin/sh
# Differential test: CsLemon against the C lemon it was ported from, on every grammar in grammars/, with several
# option sets. Usage: difftest.sh <path to C lemon> [cslemon dll]
# The C lemon must be built from the same Lemon version (lemon-grove's lemon.c, SQLite check-in f2f279b2).
set -u
REF="$1"
HERE="$(cd "$(dirname "$0")" && pwd)"
CS="${2:-$HERE/../CsLemon/bin/Debug/net10.0/cslemon.dll}"
TPL="$HERE/../CsLemon/lempar.c"
WORK="${TMPDIR:-/tmp}/cslemon-difftest.$$"
pass=0; fail=0
for g in "$HERE"/grammars/*.y; do
  for opts in "" "-g" "-s" "-l" "-c" "-r" "-b" "-m" "-p" "-S" "-E" "-DWITH_PLUS" "-DWITH_TIMES -DWITH_PLUS" "-DWITH_ALL -E"; do
    name="$(basename "$g" .y)"
    rm -rf "$WORK"; mkdir -p "$WORK/c" "$WORK/cs"
    for side in c cs; do cp "$g" "$WORK/$side/"; cp "$TPL" "$WORK/$side/"; done
    (cd "$WORK/c" && "$REF" $opts "$name.y" > stdout 2> stderr; echo $? > exit)
    (cd "$WORK/cs" && dotnet "$CS" $opts "$name.y" > stdout 2> stderr; echo $? > exit)
    if diff -r "$WORK/c" "$WORK/cs" > "$WORK/diff" 2>&1; then
      pass=$((pass + 1))
    else
      fail=$((fail + 1))
      echo "FAIL: $name $opts"; head -20 "$WORK/diff"
    fi
  done
done
rm -rf "$WORK"
echo "difftest: $pass passed, $fail failed"
[ "$fail" -eq 0 ]
