# CI

CsVerify runs anywhere the .NET 10 SDK and Z3 do. A pipeline has three steps: verify the program, erase the
proofs, and test what is left (here with [Tarp](https://github.com/ashalkhakov/Tarp)'s MC/DC coverage).

The examples assume a tool manifest (`.config/dotnet-tools.json`) with `dotnet-csverify` and `dotnet-tarp`:

```sh
dotnet new tool-manifest
dotnet tool install dotnet-csverify
dotnet tool install dotnet-tarp
```

Without one, `dotnet tool install -g dotnet-csverify` (and `dotnet-tarp`) does the same on the agent.

## Z3

The verifier finds `z3` on `PATH`, or takes `CSVERIFY_Z3=/path/to/z3`. Linux agents have it from the package
manager (`sudo apt-get install -y z3`); the [Z3 releases](https://github.com/Z3Prover/z3/releases) have builds for
every agent. This repository's own CI takes 5.3.3 from there: see
[`.github/actions/setup-z3`](../.github/actions/setup-z3/action.yml), which can be copied as it is.

## With Tarp

The proofs are checked statically, so the tests don't need them: Tarp tests the program as it runs, with the
proofs taken out.

1. **Verify.** `dotnet build -p:CsVerifyEnabled=true` verifies each project after it builds (test projects and
   those with `CsVerifyExclude` are left out). Every obligation not proved is a build error, so the step fails.
2. **Erase.** `-p:CsVerifyErase=true` compiles each project from erased copies of its sources, in
   `obj/csverify-erased/<configuration>/<framework>/`, with the CsVerify assembly replaced by a small runtime (see
   [Erasure](erasure.md)). Erasure runs before `BeforeCompile`, so whatever instruments the sources then (Tarp
   does it after `BeforeCompile`) sees the erased ones.
3. **Test.** `dotnet tarp test -p:CsVerifyErase=true` passes the property on to the build, so the tests run
   against the erased program, instrumented for MC/DC.

```sh
dotnet build -p:CsVerifyEnabled=true
dotnet tarp test -p:CsVerifyErase=true --tarp-report coverage.txt
```

The erased copies keep the original line numbers (`#line` directives), so lines, decisions and conditions are
where they are in your sources; Tarp names the files by the erased copies' paths, e.g.
`Shop.Core/obj/csverify-erased/Debug/net10.0/000_Orders.cs`. Tarp's exclusion lists take those paths too.

The erased build is a build of its own: run a normal `dotnet build` afterwards to get the program with the `Spec`
library back. [`samples/e2e.sh`](../samples/e2e.sh) does all of this on [`samples/Shop`](../samples/Shop).

## In GitHub Actions

```yaml
jobs:
  verify-and-test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-dotnet@v4
        with:
          dotnet-version: 10.0.x
      - run: sudo apt-get install -y z3
      - run: dotnet tool restore
      - name: Verify
        run: dotnet build -p:CsVerifyEnabled=true
      - name: Test the erased program with coverage
        run: >
          dotnet tarp test -p:CsVerifyErase=true
          --tarp-markdown coverage/coverage.md --tarp-html coverage/index.html
      - name: Coverage summary
        if: always()
        run: cat coverage/coverage.md >> "$GITHUB_STEP_SUMMARY"
      - uses: actions/upload-artifact@v4
        if: always()
        with:
          name: coverage
          path: coverage
```

The verifier's diagnostics have the compiler's format, so GitHub shows them on the pull request's files.

## In Azure DevOps

```yaml
steps:
- task: UseDotNet@2
  inputs:
    version: 10.0.x
- script: sudo apt-get install -y z3
  displayName: Z3
- script: dotnet tool restore
- script: dotnet build -p:CsVerifyEnabled=true
  displayName: Verify
- script: >
    dotnet tarp test -p:CsVerifyErase=true
    --logger trx --results-directory $(Agent.TempDirectory)/tests
    --tarp-cobertura $(Agent.TempDirectory)/coverage/cobertura.xml
    --tarp-markdown $(Agent.TempDirectory)/coverage/coverage.md
    --tarp-html $(Agent.TempDirectory)/coverage/index.html
    --tarp-fail-under-mcdc 100 --tarp-fail-under-branches 100
  displayName: Test the erased program with coverage
- task: PublishTestResults@2
  condition: succeededOrFailed()
  inputs:
    testResultsFormat: VSTest
    testResultsFiles: $(Agent.TempDirectory)/tests/*.trx
- task: PublishCodeCoverageResults@2
  condition: succeededOrFailed()
  inputs:
    summaryFileLocation: $(Agent.TempDirectory)/coverage/cobertura.xml
- script: echo "##vso[task.uploadsummary]$(Agent.TempDirectory)/coverage/coverage.md"
  condition: succeededOrFailed()
  displayName: Coverage and MC/DC summary
- publish: $(Agent.TempDirectory)/coverage
  artifact: coverage
  condition: succeededOrFailed()
```

On a Windows agent, install Z3 with `winget` or from its release zip, and add its `bin` to the path
(`##vso[task.prependpath]...`), or set `CSVERIFY_Z3`.

The **Verify** step fails the run on an obligation not proved; the errors appear in the run's summary with their
files and lines. Then, as in Tarp's own instructions: the **Tests** tab has the test results, **Code Coverage**
the lines and branches, **Extensions** the Markdown report with MC/DC, and the `coverage` artifact the HTML report.
The coverage gate (`--tarp-fail-under-...`) fails the test step, and the steps after it publish the results anyway.

To verify without building first, e.g. a single project in its own step:
`dotnet csverify src/MyProject` (it exits with 1 when something is not verified).

## Building and releasing CsVerify

This repository's workflows, in [`.github/workflows`](../.github/workflows):

- **CI** (`ci.yml`), on pushes to `master` and on pull requests:
  - `test`: builds the solution and runs the unit tests, on Linux and Windows;
  - `e2e`: packs both packages and runs [`samples/e2e.sh`](../samples/e2e.sh) on them, on Linux and Windows:
    verify `samples/Shop` (with the build and with `dotnet csverify`), check that a planted bug fails the build,
    erase it, and test it with Tarp;
  - `lemon`: verifies CsLemon and checks it against the C lemon (see [CsLemon](../lemon/README.md)).
- **Release** (`release.yml`), on a `v*` tag: the version is the tag's (`v0.2.0` → `0.2.0`). It runs the tests,
  packs `CsVerify` and `dotnet-csverify`, runs `e2e.sh` on those packages, creates the GitHub release with them,
  and pushes them to nuget.org.

To release:

```sh
git tag v0.2.0
git push origin v0.2.0
```

Between releases, the packages are versioned `0.1.0-dev` (`Directory.Build.props`); nothing in the sources is
changed per release.

**nuget.org** uses [trusted publishing](https://learn.microsoft.com/nuget/nuget-org/trusted-publishing): no API
key is stored. Once, on nuget.org, add a trusted publishing policy for the owner `ashalkhakov`, repository
`CsVerify`, workflow `release.yml`; and in the repository's secrets, set `NUGET_USER` to the nuget.org profile
name. Without `NUGET_USER` the release still goes to GitHub, and nuget.org is skipped. To publish a release made
before that, run the Release workflow by hand with its tag: it pushes the packages already attached to the GitHub
release.
