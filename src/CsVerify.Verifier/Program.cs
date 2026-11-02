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
  -h, --help          this text";

        public static int Main(string[] args)
        {
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
