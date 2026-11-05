#!/usr/bin/env bash
# The linter benchmark (see bench/Linters/README.md): builds the cases with the linters as analyzers, verifies them
# with CsVerify, and prints which tool reports which case. Exits 0 whatever it finds; fails only if a tool cannot run.
set -euo pipefail
cd "$(dirname "$0")/.."
dotnet build src/CsVerify.Verifier -c Release -v q -nologo > /dev/null
lint=$(dotnet build bench/Linters -c Release -v q -nologo --no-incremental 2>&1 | grep -E '\): (warning|error) ' || true)
set +e
verify=$(dotnet src/CsVerify.Verifier/bin/Release/net10.0/csverify.dll bench/Linters 2>&1)
code=$?
set -e
if [ "$code" -gt 1 ]; then echo "$verify"; exit "$code"; fi
printf '%s\n%s\n' "$lint" "$verify" | python3 -I bench/score.py bench/Linters/Cases.cs
