#!/usr/bin/env bash
# Runs InferSharp (in its Docker image) on the benchmark's compiled cases, and prints what it reports on them as
# diagnostics for score.py. It analyzes binaries, so it comes after the build. Prints nothing if Docker can't run it.
set -euo pipefail
cd "$(dirname "$0")/.."
image=mcr.microsoft.com/infersharp:v1.5
docker info > /dev/null 2>&1 || { echo "InferSharp not run: no Docker" >&2; exit 0; }
work=$(mktemp -d)
# (only the cases: the Spec library they reference is not what is being measured)
# (a debug build: optimizing hides some of what it would report)
dotnet build bench/Linters -c Debug -v q -nologo > /dev/null 2>&1
cp bench/Linters/bin/Debug/net10.0/CsVerify.Bench.Linters.dll bench/Linters/bin/Debug/net10.0/CsVerify.Bench.Linters.pdb "$work"
docker run --rm --platform linux/amd64 -v "$work:/infersharp/binary_path" "$image" /bin/bash -c \
  "./run_infersharp.sh binary_path; cp infer-out/report.json /infersharp/binary_path/report.json" > /dev/null 2>&1 ||
  { echo "InferSharp failed" >&2; exit 0; }
python3 -I -c '
import json, sys
for x in json.load(open(sys.argv[1])):
    print("Cases.cs(%d,1): warning %s: %s" % (x["line"], x["bug_type"], x["qualifier"].splitlines()[0]))
' "$work/report.json"
