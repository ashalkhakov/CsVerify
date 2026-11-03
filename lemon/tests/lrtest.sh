#!/bin/sh
# The verified LR interpreter (lemon/CsLemon/Lr) on Lemon's automata: each tests/lr/<grammar>.<name>.tok is a
# sequence of terminals; "ok" files must be accepted whole, "bad" ones rejected (never an internal error); and the
# safety validator must accept each grammar's automaton and reject corruptions of it (not all: some keep it safe);
# the completeness validator must accept the unambiguous grammars' (expr, decls) and reject every dropped action.
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
    ok*) expect="(safe) accepted $n of $n:" ;;
    *) expect="(safe) rejected at" ;;
  esac
  case "$out" in
    "$expect"*) pass=$((pass + 1)) ;;
    *) fail=$((fail + 1)); echo "FAIL: $base: $out" | cut -c1-200 ;;
  esac
done
# the safety validator accepts every grammar's automaton, and rejects corrupted ones
for g in "$HERE"/grammars/*.y; do
  name="$(basename "$g" .y)"; [ "$name" = errors ] && continue
  rm -rf "$WORK"; mkdir -p "$WORK"; cp "$g" "$HERE/../CsLemon/lempar.c" "$WORK/"
  out="$(cd "$WORK" && CSLEMON_VALIDATE=mutate dotnet "$CS" -q "$name.y" 2>/dev/null | grep -E '^(safety|mutations|completeness)')"
  case "$name" in expr|decls) complete=yes ;; *) complete=no ;; esac
  if echo "$out" | grep -q '^safety: validated' && echo "$out" | grep -Eq '^mutations rejected: [1-9]' &&
     { [ $complete = no ] || { echo "$out" | grep -q '^completeness: validated' &&
                               echo "$out" | grep -Eq '^completeness mutations rejected: ([0-9]+) of \1$'; }; }; then
    pass=$((pass + 1))
  else
    fail=$((fail + 1)); echo "FAIL: $name: $out"
  fi
done
rm -rf "$WORK"
echo "lrtest: $pass passed, $fail failed"
[ "$fail" -eq 0 ]
