#!/bin/sh
# The verified LR interpreter (lemon/CsLemon/Lr) on Lemon's automata: each tests/lr/<grammar>.<name>.tok is a
# sequence of terminals; "ok" files must be accepted whole, "bad" ones rejected (never an internal error).
# Usage: lrtest.sh [cslemon dll]
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
CS="${1:-$HERE/../CsLemon/bin/Debug/net10.0/cslemon.dll}"
WORK="${TMPDIR:-/tmp}/cslemon-lrtest.$$"
pass=0; fail=0
for t in "$HERE"/lr/*.tok; do
  base="$(basename "$t" .tok)"; g="${base%%.*}"; kind="${base#*.}"
  rm -rf "$WORK"; mkdir -p "$WORK"; cp "$HERE/grammars/$g.y" "$HERE/../CsLemon/lempar.c" "$t" "$WORK/"
  out="$(cd "$WORK" && CSLEMON_PARSE="$base.tok" dotnet "$CS" -q "$g.y" 2>&1)"
  n="$(wc -w < "$t" | tr -d ' ')"
  case "$kind" in
    ok*) expect="accepted $n of $n:" ;;
    *) expect="rejected at" ;;
  esac
  case "$out" in
    "$expect"*) pass=$((pass + 1)) ;;
    *) fail=$((fail + 1)); echo "FAIL: $base: $out" | cut -c1-200 ;;
  esac
done
rm -rf "$WORK"
echo "lrtest: $pass passed, $fail failed"
[ "$fail" -eq 0 ]
