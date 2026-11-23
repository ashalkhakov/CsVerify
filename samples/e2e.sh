#!/usr/bin/env bash
# End-to-end check of CsVerify as users get it: packs the CsVerify package and the dotnet-csverify tool, uses them
# in a copy of samples/Shop (the package by PackageReference, the tool as a local tool), verifies it, checks that a
# planted bug fails the build, erases the proofs, and runs the tests through Tarp (dotnet-tarp, from nuget.org) on
# the erased program; then verifies samples/Layered, a solution of several projects.
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
# NuGet.config needs a path dotnet can read: on Windows (Git Bash), /tmp/... is not one
if command -v cygpath > /dev/null; then nupkg=$(cygpath -m "$nupkg"); fi
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
grep -F "csverify: 5 of 5 methods verified, 43/43 obligations proved" build.txt

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

# generated code: the SDK's global usings and a source generator's output reach the verifier and erasure, compiled
# with the program, not verified
printf 'using System.Text.RegularExpressions;\nnamespace Shop.Core;\npublic static partial class Codes\n{\n    [GeneratedRegex("^[A-Z]{3}$")]\n    public static partial Regex ThreeLetters();\n    public static int Count(List<int> xs) => xs.Count;\n}\n' > Shop.Core/Codes.cs
dotnet build -p:CsVerifyEnabled=true -p:ImplicitUsings=enable | tee generated.txt
grep -F "csverify: 6 of 6 methods verified" generated.txt
dotnet build -p:CsVerifyErase=true -p:ImplicitUsings=enable
rm Shop.Core/Codes.cs

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

# a project that uses Shop.Core's internals (InternalsVisibleTo) and ASP.NET Core's logging: the verifier compiles it
# under its assembly name, with the shared frameworks' references other than Microsoft.NETCore.App's
printf '[assembly: System.Runtime.CompilerServices.InternalsVisibleTo("Shop.Rows")]\nnamespace Shop.Core;\npublic sealed class Row\n{\n    internal long Id { get; set; }\n}\n' > Shop.Core/Row.cs
mkdir Shop.Rows
cat > Shop.Rows/Shop.Rows.csproj <<'PROJECT'
<Project Sdk="Microsoft.NET.Sdk">
  <PropertyGroup><TargetFramework>net10.0</TargetFramework><Nullable>enable</Nullable></PropertyGroup>
  <ItemGroup>
    <FrameworkReference Include="Microsoft.AspNetCore.App" />
    <ProjectReference Include="../Shop.Core/Shop.Core.csproj" />
    <PackageReference Include="CsVerify" Version="$(CsVerifyVersion)" />
  </ItemGroup>
</Project>
PROJECT
printf 'using Microsoft.Extensions.Logging;\nusing Shop.Core;\nnamespace Shop.Rows;\npublic static class Rows\n{\n    public static long RowOf(Row r) => r.Id;\n    public static bool Loud(LogLevel level) => level >= LogLevel.Warning;\n}\n' > Shop.Rows/Rows.cs
dotnet build Shop.Rows -p:CsVerifyEnabled=true | tee rows.txt
grep -F "csverify: 2 of 2 methods verified" rows.txt
# (Shop.Core's implementation assembly, not its reference assembly, which has no backing fields: #86)
# (Windows' paths have backslashes: as slashes)
tr '\\' '/' < Shop.Rows/obj/Debug/net10.0/csverify.rsp > rsp.txt
grep -E "Shop\.Core/bin/Debug/net10\.0/Shop\.Core\.dll" rsp.txt
if grep -E "/ref/Shop\.Core\.dll" rsp.txt; then
    echo "error: the verifier was given Shop.Core's reference assembly" >&2
    exit 1
fi
dotnet build Shop.Rows -p:CsVerifyErase=true

# a layered solution (samples/Layered): a domain project and a data project, excluded, and the application, verified,
# with the others as projects of their own that its compilation references. Every method of it verifies. (Under
# Shop, for its NuGet.config, its CsVerify version and its tools)
cp -R "$repo/samples/Layered" Layered
dotnet build Layered/Layered.App -p:CsVerifyEnabled=true 2>&1 | tee layered.txt
grep -F "csverify: 18 of 18 methods verified" layered.txt
# (App alone, the others built before: their descriptions as complete, Model's InternalsVisibleTo among them, #116)
rm Layered/Layered.App/obj/Debug/net10.0/csverify.stamp
dotnet build Layered/Layered.App --no-restore --no-dependencies -p:CsVerifyEnabled=true -p:CsVerifyCache=false 2>&1 | tee layered-alone.txt
grep -F "csverify: 18 of 18 methods verified" layered-alone.txt
grep -F "AssemblyInfo.cs" Layered/Layered.Model/obj/Debug/net10.0/csverify.project.rsp
tr '\\' '/' < Layered/Layered.App/obj/Debug/net10.0/csverify.rsp > layered-rsp.txt
grep -E -- "--project-reference .*Layered\.Model/obj/Debug/net10\.0/csverify\.project\.rsp" layered-rsp.txt
grep -E -- "--project-reference .*Layered\.Data/obj/Debug/net10\.0/csverify\.project\.rsp" layered-rsp.txt
grep -F -- "--nullable enable" Layered/Layered.Model/obj/Debug/net10.0/csverify.project.rsp

echo "e2e: OK"
