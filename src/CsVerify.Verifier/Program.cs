using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;

namespace CsVerify.Verifier
{
    public static class Program
    {
        private const string Usage = @"usage: csverify [options] <file.cs | directory | project.csproj | @paths.rsp>...

Verifies CsVerify specifications (Spec.Requires/Ensures/Invariant/Decreases/Assert, lemmas, views) with Z3.
Directories are searched recursively for .cs files (bin/ and obj/ are skipped); a .csproj means its directory.

options:
  --no-overflow       treat every integer as mathematical (unsound where code can overflow); by default
                      run-time arithmetic is C#'s: overflow is reported unless checked (throws) or
                      unchecked (wraps on purpose)
  --nullable <ctx>    nullable context: enable (default), disable, annotations, warnings; only
                      non-nullable reference types are known not to be null
  --timeout <ms>      per-query Z3 timeout (default 10000)
  --method-budget <ms> the most one method may take (all rounds); past it, the rest is not verified (default: none)
  --z3 <path>         Z3 executable (default: CSVERIFY_Z3, then PATH)
  --engine <name>     csverify (the default; CSVERIFY_ENGINE sets it): CsVerify's own engine;
                      boogie: each method with Boogie (docs/boogie.md), CsVerify's own engine where it
                      isn't translated or can't be decided; boogie-only: Boogie alone
  --boogie-out <file> write the Boogie program it verifies
  -d <SYMBOL>         extra preprocessor symbol (CSVERIFY_SPEC is always defined)
  -r <assembly.dll>   extra metadata reference
  --smt-log <file>    write the SMT-LIB2 conversation with Z3
  --only <text>       verify only the methods whose name (Type.Method) contains the text (repeatable)
  -v                  list every method with its proved obligations, and the library contracts
                      ([ContractsFor] stubs, trusted) the proofs assumed
  --checks <kinds>    prove only these kinds of obligation, a comma-separated list of null, linear,
                      bounds, overflow, contracts (or all); the others are assumed, and counted.
                      Within a profile an unsupported construct is a warning, its value unknown
  --each              verify each argument as a program of its own (a comma joins paths into one), and
                      combine the results: for programs that cannot be compiled together
  --library-report    after the results, rank what the failures come from: library members without
                      contracts (by the failures they cause, and their calls), methods without
                      postconditions, loops without invariants; and the failures by kind, the
                      unsupported constructs and the unknown values
  -h, --help          this text

       csverify erase --out <dir> ...   writes the program with every proof erased (csverify erase -h)";

        public static int Main(string[] args)
        {
            if (args.Length > 0 && args[0] == "erase") return Erase(ExpandResponseFiles(args.Skip(1)).ToList());
            // @file.rsp: a path, or an option and its value, per line (what the MSBuild target passes)
            args = ExpandResponseFiles(args).ToArray();
            var options = new VerifierOptions();
            var inputs = new List<string>();
            bool verbose = false;
            bool libraryReport = false;
            bool each = false;
            string smtLog = null;
            try
            {
                for (int i = 0; i < args.Length; i++)
                {
                    switch (args[i])
                    {
                        case "--overflow": options.CheckOverflow = true; break; // the default
                        case "--no-overflow": options.CheckOverflow = false; break;
                        case "--nullable":
                            options.Nullable = (Microsoft.CodeAnalysis.NullableContextOptions)Enum.Parse(typeof(Microsoft.CodeAnalysis.NullableContextOptions), args[++i], ignoreCase: true);
                            break;
                        case "--timeout": options.TimeoutMs = int.Parse(args[++i]); break;
                        case "--method-budget": options.MethodBudgetMs = int.Parse(args[++i]); break;
                        case "--z3": options.Z3Path = args[++i]; break;
                        case "--engine": options.Engine = args[++i]; break;
                        case "--boogie-out": options.BoogieOut = args[++i]; break;
                        case "-d": options.Defines.Add(args[++i]); break;
                        case "-r": options.References.Add(args[++i]); break;
                        case "--smt-log": smtLog = args[++i]; options.SmtLog = new System.Text.StringBuilder(); break;
                        case "--only": options.Only.Add(args[++i]); break;
                        case "-v": verbose = true; break;
                        case "--library-report": libraryReport = true; break;
                        case "--each": each = true; break;
                        case "--checks": options.CheckKinds = Checks.Parse(args[++i]); break;
                        case "-h": case "--help": Console.WriteLine(Usage); return 0;
                        default:
                            if (args[i].StartsWith("-")) throw new ArgumentException("unknown option " + args[i]);
                            inputs.Add(args[i]);
                            break;
                    }
                }
                if (inputs.Count == 0) { Console.Error.WriteLine(Usage); return 2; }

                var programs = each
                    ? inputs.Select(i => i.Split(',', StringSplitOptions.RemoveEmptyEntries)).ToList()
                    : new List<string[]> { inputs.ToArray() };
                var result = VerificationResult.Combine(programs.Select(p => Engine.VerifyFiles(p.SelectMany(Expand).Distinct().ToList(), options)).ToList());
                if (smtLog != null) File.WriteAllText(smtLog, options.SmtLog.ToString());

                foreach (var d in result.Diagnostics) Console.WriteLine(d);
                if (verbose)
                    foreach (var m in result.Methods)
                        Console.WriteLine($"  {(m.Verified ? "ok  " : "FAIL")} {m.Name}: {m.Proved}/{m.Obligations} obligations proved");
                // the stub contracts the proofs relied on: trusted, not proved
                if (verbose)
                    foreach (var a in result.Assumptions) Console.WriteLine($"  assumed {a}");
                int failed = result.Methods.Count(m => !m.Verified);
                Console.WriteLine(result.CompilationErrors.Count > 0
                    ? $"csverify: {result.CompilationErrors.Count} compilation error(s); nothing verified"
                    : $"csverify: {result.Methods.Count - failed} of {result.Methods.Count} methods verified, " +
                      $"{result.Methods.Sum(m => m.Proved)}/{result.Methods.Sum(m => m.Obligations)} obligations proved" +
                      (result.Assumptions.Count > 0 ? $", {result.Assumptions.Count} library contract(s) assumed" : "") +
                      (options.Boogie ? $"; {result.Methods.Count(m => m.Engine == "boogie")} by Boogie" : "") +
                      (options.CheckKinds != null ? $"; checks: {string.Join(",", Checks.All.Where(options.CheckKinds.Contains))}" +
                                                    $", {result.Methods.Sum(m => m.AssumedObligations)} obligation(s) outside them assumed" +
                                                    $", {result.Methods.Sum(m => m.Unmodeled)} construct(s) not modeled" : ""));
                if (libraryReport && result.CompilationErrors.Count == 0)
                {
                    Console.WriteLine();
                    Console.Write(LibraryReport.Render(result));
                }
                return result.Success ? 0 : 1;
            }
            catch (Exception e) when (e is ArgumentException || e is FileNotFoundException || e is DirectoryNotFoundException || e is FormatException)
            {
                Console.Error.WriteLine("csverify: " + (Environment.GetEnvironmentVariable("CSVERIFY_TRACE") != null ? e.ToString() : e.Message));
                return 2;
            }
        }

        /// <summary>@file.rsp: one argument per line; a line "-r path" is an option and its value.</summary>
        private static IEnumerable<string> ExpandResponseFiles(IEnumerable<string> args)
        {
            foreach (var a in args)
            {
                if (!a.StartsWith("@")) { yield return a; continue; }
                foreach (var line in File.ReadAllLines(a.Substring(1)).Select(l => l.Trim()).Where(l => l.Length > 0))
                {
                    int space = line.IndexOf(' ');
                    if (line.StartsWith("-") && space > 0) { yield return line.Substring(0, space); yield return line.Substring(space + 1).Trim(); }
                    else yield return line;
                }
            }
        }

        private const string EraseUsage = @"usage: csverify erase --out <dir> [--checked] [-r <reference.dll>]... [-d <symbol>]... <file.cs | directory | @paths.rsp>...

Writes the program with all proofs erased (specifications, lemmas, ghost parameters, views) to <dir>, plus the
erased CsVerify runtime under <dir>/CsVerify.Runtime, and checks that it compiles without CsVerify: if it does
not, run-time code depends on ghost code (CSV2001). With -r, those references (minus the CsVerify assembly) are
used for the check; without, the shared framework.

--checked   a checked build: the specifications that can run are kept as run-time checks (preconditions,
            postconditions, assertions, loop invariants, lock invariants, [Atomic] steps, lock levels), which
            throw SpecificationFailedException, or do what CsVerify.Checked.Failed says (docs/erasure.md).";

        private static int Erase(List<string> args)
        {
            string outDir = null;
            var references = new List<string>();
            var defines = new List<string>();
            var inputs = new List<string>();
            bool checkedBuild = false;
            try
            {
                for (int i = 0; i < args.Count; i++)
                {
                    switch (args[i])
                    {
                        case "--out": outDir = args[++i]; break;
                        case "--checked": checkedBuild = true; break;
                        case "-r": references.Add(args[++i]); break;
                        case "-d": defines.Add(args[++i]); break;
                        case "-h": case "--help": Console.WriteLine(EraseUsage); return 0;
                        default:
                            if (args[i].StartsWith("-")) throw new ArgumentException("unknown option " + args[i]);
                            inputs.Add(args[i]);
                            break;
                    }
                }
                if (outDir == null || inputs.Count == 0) { Console.Error.WriteLine(EraseUsage); return 2; }
                var files = inputs.SelectMany(Expand).Distinct().ToList();
                var result = Erasure.Erase(files.Select(f => (f, File.ReadAllText(f))), references, defines, checkedBuild);
                if (Directory.Exists(outDir)) Directory.Delete(outDir, recursive: true);
                foreach (var f in result.Files)
                {
                    var path = Path.Combine(outDir, f.OutputName);
                    Directory.CreateDirectory(Path.GetDirectoryName(path));
                    File.WriteAllText(path, f.Text);
                }
                foreach (var d in result.Errors) Console.WriteLine(d);
                Console.WriteLine(result.Success
                    ? $"csverify erase: {result.Files.Count} files written to {outDir}; the {(checkedBuild ? "checked" : "erased")} program compiles"
                    : $"csverify erase: {result.Errors.Count} error(s)");
                return result.Success ? 0 : 1;
            }
            catch (Exception e) when (e is ArgumentException || e is FileNotFoundException || e is DirectoryNotFoundException || e is IOException)
            {
                Console.Error.WriteLine("csverify: " + e.Message);
                return 2;
            }
        }

        private static IEnumerable<string> Expand(string input)
        {
            if (input.EndsWith(".csproj", StringComparison.OrdinalIgnoreCase)) input = Path.GetDirectoryName(Path.GetFullPath(input));
            if (File.Exists(input)) return new[] { Path.GetFullPath(input) };
            if (!Directory.Exists(input)) throw new FileNotFoundException("no such file or directory: " + input);
            var sep = Path.DirectorySeparatorChar;
            return Directory.EnumerateFiles(Path.GetFullPath(input), "*.cs", SearchOption.AllDirectories)
                .Where(p => !p.Contains($"{sep}bin{sep}") && !p.Contains($"{sep}obj{sep}"))
                .OrderBy(p => p, StringComparer.Ordinal);
        }
    }
}
