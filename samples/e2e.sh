#!/usr/bin/env bash
# End-to-end check of CsVerify as users get it: packs the CsVerify package and the dotnet-csverify tool, uses them
# in a copy of samples/Shop (the package by PackageReference, the tool as a local tool), verifies it, checks that a
# planted bug fails the build, erases the proofs, and runs the tests through Tarp (dotnet-tarp, from nuget.org) on
# the erased program.
#
#   samples/e2e.sh [nupkg directory]   (default: pack the working tree)
set -euo pipefail

repo=$(cd "$(dirname "$0")/.." && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
tarp_version=0.7.0

if [ $# -ge 1 ]; then
    nupkg=$(cd "$1" && pwd)
else
    nupkg="$work/nupkg"
    # a version of its own: NuGet would use a package of the same version from its cache
    version=0.0.0-e2e.$(date +%s)
    dotnet pack "$repo/src/CsVerify.Spec" -c Release -o "$nupkg" -p:Version=$version
    dotnet pack "$repo/src/CsVerify.Verifier" -c Release -o "$nupkg" -p:Version=$version
fi
version=$(ls "$nupkg" | sed -n 's/^dotnet-csverify\.\(.*\)\.nupkg$/\1/p' | head -1)

cp -R "$repo/samples/Shop" "$work/Shop"
cd "$work/Shop"
cat > NuGet.config <<CONFIG
<?xml version="1.0" encoding="utf-8"?>
<configuration>
  <packageSources>
    <add key="csverify" value="$nupkg" />
    <add key="nuget.org" value="https://api.nuget.org/v3/index.json" />
  </packageSources>
</configuration>
CONFIG
echo "<Project><PropertyGroup><CsVerifyVersion>$version</CsVerifyVersion></PropertyGroup></Project>" > Directory.Build.props

dotnet new tool-manifest
dotnet tool install dotnet-csverify --version "$version"
dotnet tool install dotnet-tarp --version "$tarp_version"

# verify, in the build: the library is proved, the test project is not looked at
dotnet build -p:CsVerifyEnabled=true | tee build.txt
grep -F "csverify: 5 of 5 methods verified, 51/51 obligations proved" build.txt

# and from the command line
dotnet csverify Shop.Core | tee verify.txt
grep -F "csverify: 5 of 5 methods verified" verify.txt

# a bug fails the build, with the verifier's diagnostic as a build error at its line
printf 'namespace Shop.Core;\npublic static class Planted\n{\n    public static int First(int[] a) => a[0];\n}\n' > Shop.Core/Planted.cs
if dotnet build -p:CsVerifyEnabled=true > bug.txt 2>&1; then
    echo "error: the build passed with a planted out-of-bounds read" >&2
    exit 1
fi
grep -E "Planted\.cs\(4,[0-9]+\): error CSV1003: index in 'a\[0\]' might be out of range" bug.txt
rm Shop.Core/Planted.cs

# erasure: the program without its proofs, compiled without the CsVerify assembly
dotnet build -p:CsVerifyErase=true
erased=Shop.Core/obj/csverify-erased/Debug/net10.0
ls "$erased"/*Orders.cs
if grep -q "Spec\." "$erased"/*Orders.cs; then
    echo "error: the erased sources still have specifications" >&2
    exit 1
fi
# (Orders.Last's ghost parameter is CsVerify's Ghost<int>: gone, so nothing refers to CsVerify, nor do the tests)
for dll in Shop.Core/bin/Debug/net10.0/Shop.Core.dll Shop.Core.Tests/bin/Debug/net10.0/Shop.Core.Tests.dll; do
    if grep -a -q "CsVerify.Spec" "$dll"; then
        echo "error: the erased $dll still refers to CsVerify" >&2
        exit 1
    fi
done

# Tarp on the erased program: the decisions are the code's (5), not the specifications', and all of them run
dotnet tarp test -p:CsVerifyErase=true --tarp-report report.txt
cat report.txt
grep -E "^  Lines +11/11 " report.txt
grep -F "Summary: 5 decisions (0 never executed), 4/8 conditions shown (50.0%), 0 decisions not instrumented" report.txt
grep -F "c1 total >= 100: NOT shown, missing false" report.txt

# a normal build afterwards compiles the original sources again, against CsVerify (Ghost<int>)
dotnet build
grep -a -q "CsVerify.Spec" Shop.Core/bin/Debug/net10.0/Shop.Core.dll

echo "e2e: OK"
