#!/bin/sh
# Lemon's C parsers against CsLemon's C# parsers (cslemon -C, the verified LR interpreter), on the same inputs. Each
# tests/parsers/<name> has the grammar twice, c/<name>.y with C actions (and c/driver.c) and cs/<name>.y with C#
# actions (and cs/Driver.cs), and inputs/*.tok, one token per line: its name and its value. The C parser is built by
# the C lemon and cc, the C# one by cslemon -C and dotnet; both run on each input and must print the same.
# (Inputs end where errors are: on an error inside the input, Lemon's C parsers recover by dropping tokens, which the
# interpreter does not do.) Usage: parsertest.sh <C lemon> [cslemon dll]
set -u
REF="$1"
HERE="$(cd "$(dirname "$0")" && pwd)"
CS="${2:-$HERE/../CsLemon/bin/Debug/net10.0/cslemon.dll}"
RUNTIME="$HERE/../CsLemon.Runtime/CsLemon.Runtime.csproj"
WORK="${TMPDIR:-/tmp}/cslemon-parsertest.$$"
pass=0; fail=0
for d in "$HERE"/parsers/*/; do
  name="$(basename "$d")"
  rm -rf "$WORK"; mkdir -p "$WORK/c" "$WORK/cs"
  cp "$d"/c/* "$HERE/../CsLemon/lempar.c" "$WORK/c/"
  if ! (cd "$WORK/c" && "$REF" -q "$name.y" && cc -w -o parser "$name.c" driver.c); then
    fail=$((fail + 1)); echo "FAIL: $name: the C parser does not build"; continue
  fi
  cp "$d"/cs/* "$WORK/cs/"
  cat > "$WORK/cs/parser.csproj" <<PROJ
<Project Sdk="Microsoft.NET.Sdk">
  <PropertyGroup>
    <OutputType>Exe</OutputType>
    <TargetFramework>net10.0</TargetFramework>
    <Nullable>enable</Nullable>
  </PropertyGroup>
  <ItemGroup>
    <Compile Remove="$name.y" />
    <ProjectReference Include="$RUNTIME" />
  </ItemGroup>
</Project>
PROJ
  if ! (cd "$WORK/cs" && dotnet "$CS" -C -q "$name.y" && dotnet build -v q -nologo -o out > build.log 2>&1); then
    fail=$((fail + 1)); echo "FAIL: $name: the C# parser does not build"; tail -5 "$WORK/cs/build.log" 2>/dev/null; continue
  fi
  for t in "$d"/inputs/*.tok; do
    input="$(basename "$t" .tok)"
    # names to codes, by the C parser's header (CsLemon numbers the tokens as Lemon does)
    awk 'NR == FNR { if ($1 == "#define") code[$2] = $3; next } NF > 0 { print code[$1], ($2 == "" ? 0 : $2) }' \
      "$WORK/c/$name.h" "$t" > "$WORK/in"
    "$WORK/c/parser" "$WORK/in" > "$WORK/c.out" 2>&1
    dotnet "$WORK/cs/out/parser.dll" "$WORK/in" > "$WORK/cs.out" 2>&1
    [ -n "${SHOW:-}" ] && { echo "== $name $input"; cat "$WORK/cs.out"; }
    if cmp -s "$WORK/c.out" "$WORK/cs.out"; then
      pass=$((pass + 1))
    else
      fail=$((fail + 1)); echo "FAIL: $name $input"; diff "$WORK/c.out" "$WORK/cs.out" | head -10
    fi
  done
done
[ -n "${KEEP:-}" ] || rm -rf "$WORK"
echo "parsertest: $pass passed, $fail failed"
[ "$fail" -eq 0 ]
