#!/usr/bin/env bash
# The library report on the whole corpus (see corpus/README.md): the parsers here, the samples, and CsLemon, each
# verified as a program of its own, with what their failures come from ranked. The corpus is not expected to verify
# (the parsers have no specifications), so this exits 0 whatever it finds; it fails only if the verifier cannot run.
# Extra arguments go to the verifier (e.g. --timeout 5000).
set -euo pipefail
cd "$(dirname "$0")/.."
dotnet build src/CsVerify.Verifier -c Release -v q -nologo > /dev/null
set +e
out=$(dotnet src/CsVerify.Verifier/bin/Release/net10.0/csverify.dll --each --library-report "$@" \
  corpus samples/Good lemon/CsLemon,lemon/CsLemon.Runtime)
code=$?
set -e
if [ "$code" -gt 1 ]; then echo "$out"; exit "$code"; fi
# the summary line, then the report (the diagnostics themselves are in a plain run)
echo "$out" | grep '^csverify:'
echo "$out" | sed -n '/^library report$/,$p'
