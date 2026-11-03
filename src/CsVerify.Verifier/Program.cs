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
  --overflow          also prove that integer arithmetic does not overflow
  --timeout <ms>      per-query Z3 timeout (default 10000)
  --z3 <path>         Z3 executable (default: CSVERIFY_Z3, then PATH)
  -d <SYMBOL>         extra preprocessor symbol (CSVERIFY_SPEC is always defined)
  -r <assembly.dll>   extra metadata reference
  --smt-log <file>    write the SMT-LIB2 conversation with Z3
  -v                  list every method with its proved obligations
  -h, --help          this text

       csverify erase --out <dir> ...   writes the program with every proof erased (csverify erase -h)";

        public static int Main(string[] args)
        {
            if (args.Length > 0 && args[0] == "erase") return Erase(ExpandResponseFiles(args.Skip(1)).ToList());
            var options = new VerifierOptions();
            var inputs = new List<string>();
            bool verbose = false;
            string smtLog = null;
            try
            {
                for (int i = 0; i < args.Length; i++)
                {
                    switch (args[i])
                    {
                        case "--overflow": options.CheckOverflow = true; break;
                        case "--timeout": options.TimeoutMs = int.Parse(args[++i]); break;
                        case "--z3": options.Z3Path = args[++i]; break;
                        case "-d": options.Defines.Add(args[++i]); break;
                        case "-r": options.References.Add(args[++i]); break;
                        case "--smt-log": smtLog = args[++i]; options.SmtLog = new System.Text.StringBuilder(); break;
                        case "-v": verbose = true; break;
                        case "-h": case "--help": Console.WriteLine(Usage); return 0;
                        default:
                            if (args[i].StartsWith("-")) throw new ArgumentException("unknown option " + args[i]);
                            inputs.Add(args[i]);
                            break;
                    }
                }
                if (inputs.Count == 0) { Console.Error.WriteLine(Usage); return 2; }

                // @file.rsp: one path per line (what the MSBuild target passes).
                inputs = inputs.SelectMany(i => i.StartsWith("@") ? File.ReadAllLines(i.Substring(1)).Where(l => l.Trim().Length > 0) : new[] { i }).ToList();
                var files = inputs.SelectMany(Expand).Distinct().ToList();
                var result = Engine.VerifyFiles(files, options);
                if (smtLog != null) File.WriteAllText(smtLog, options.SmtLog.ToString());

                foreach (var d in result.Diagnostics) Console.WriteLine(d);
                if (verbose)
                    foreach (var m in result.Methods)
                        Console.WriteLine($"  {(m.Verified ? "ok  " : "FAIL")} {m.Name}: {m.Proved}/{m.Obligations} obligations proved");
                int failed = result.Methods.Count(m => !m.Verified);
                Console.WriteLine(result.CompilationErrors.Count > 0
                    ? $"csverify: {result.CompilationErrors.Count} compilation error(s); nothing verified"
                    : $"csverify: {result.Methods.Count - failed} of {result.Methods.Count} methods verified, " +
                      $"{result.Methods.Sum(m => m.Proved)}/{result.Methods.Sum(m => m.Obligations)} obligations proved");
                return result.Success ? 0 : 1;
            }
            catch (Exception e) when (e is ArgumentException || e is FileNotFoundException || e is DirectoryNotFoundException || e is FormatException)
            {
                Console.Error.WriteLine("csverify: " + e.Message);
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

        private const string EraseUsage = @"usage: csverify erase --out <dir> [-r <reference.dll>]... [-d <symbol>]... <file.cs | directory | @paths.rsp>...

Writes the program with all proofs erased (specifications, lemmas, ghost parameters, views) to <dir>, plus the
erased CsVerify runtime under <dir>/CsVerify.Runtime, and checks that it compiles without CsVerify: if it does
not, run-time code depends on ghost code (CSV2001). With -r, those references (minus the CsVerify assembly) are
used for the check; without, the shared framework.";

        private static int Erase(List<string> args)
        {
            string outDir = null;
            var references = new List<string>();
            var defines = new List<string>();
            var inputs = new List<string>();
            try
            {
                for (int i = 0; i < args.Count; i++)
                {
                    switch (args[i])
                    {
                        case "--out": outDir = args[++i]; break;
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
                var result = Erasure.Erase(files.Select(f => (f, File.ReadAllText(f))), references, defines);
                if (Directory.Exists(outDir)) Directory.Delete(outDir, recursive: true);
                foreach (var f in result.Files)
                {
                    var path = Path.Combine(outDir, f.OutputName);
                    Directory.CreateDirectory(Path.GetDirectoryName(path));
                    File.WriteAllText(path, f.Text);
                }
                foreach (var d in result.Errors) Console.WriteLine(d);
                Console.WriteLine(result.Success
                    ? $"csverify erase: {result.Files.Count} files written to {outDir}; the erased program compiles"
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
