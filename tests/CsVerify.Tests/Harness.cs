using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.IO;
using System.Linq;
using CsVerify.Analyzers;
using CsVerify.Verifier;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.Diagnostics;

namespace CsVerify.Tests
{
    internal static class Harness
    {
        private const string Usings = "using System; using System.Diagnostics; using CsVerify;\n";

        // (one set for the whole run: each test reading them again held a copy of the framework's metadata)
        private static readonly Lazy<List<MetadataReference>> _references = new Lazy<List<MetadataReference>>(() =>
        {
            var frameworkDir = Path.GetDirectoryName(typeof(object).Assembly.Location);
            var tpa = ((string)AppContext.GetData("TRUSTED_PLATFORM_ASSEMBLIES")).Split(Path.PathSeparator);
            return tpa.Where(p => Path.GetDirectoryName(p) == frameworkDir)
                .Append(typeof(CsVerify.Spec).Assembly.Location)
                .Select(p => (MetadataReference)MetadataReference.CreateFromFile(p)).ToList();
        });

        public static IEnumerable<MetadataReference> References() => _references.Value;

        public static CSharpCompilation Compile(string source, params string[] defines)
        {
            var tree = CSharpSyntaxTree.ParseText(Usings + source, new CSharpParseOptions(LanguageVersion.Latest, preprocessorSymbols: defines), "Test.cs");
            return CSharpCompilation.Create("Test", new[] { tree }, References(),
                new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary));
        }

        /// <summary>Runs both analyzers, as an IDE would on a normal build (CSVERIFY_SPEC not defined).</summary>
        public static string[] Analyze(string source)
        {
            var compilation = Compile(source);
            var errors = compilation.GetDiagnostics().Where(d => d.Severity == DiagnosticSeverity.Error).ToList();
            if (errors.Count > 0) throw new InvalidOperationException("test source does not compile: " + string.Join("\n", errors));
            var analyzers = ImmutableArray.Create<DiagnosticAnalyzer>(new LinearityAnalyzer(), new GhostAnalyzer(), new PurityAnalyzer(), new DisposalAnalyzer());
            return compilation.WithAnalyzers(analyzers).GetAnalyzerDiagnosticsAsync().Result
                .Select(d => d.Id).OrderBy(x => x).ToArray();
        }

        private const string EfUsings = "using System.Collections.Generic; using System.Linq; using System.Threading; using System.Threading.Tasks; using Microsoft.EntityFrameworkCore;\n";

        /// <summary>EF Core's assemblies (and what they build on), as a project referencing it passes them.</summary>
        public static List<string> EfReferences() => Directory.EnumerateFiles(AppContext.BaseDirectory, "*.dll")
            .Where(p => Path.GetFileName(p).StartsWith("Microsoft.EntityFrameworkCore") || Path.GetFileName(p).StartsWith("Microsoft.Extensions."))
            .Where(p => !Path.GetFileName(p).Contains("Sqlite") && !Path.GetFileName(p).Contains("Design")).ToList();

        /// <summary>A program using Entity Framework Core.</summary>
        public static VerificationResult VerifyEf(string source, bool overflow = true)
        {
            var options = new VerifierOptions { CheckOverflow = overflow };
            options.References.AddRange(EfReferences());
            var result = Engine.VerifySources(new[] { ("Test.cs", Usings + EfUsings + source) }, options);
            Xunit.Assert.True(result.CompilationErrors.Count == 0, string.Join("\n", result.CompilationErrors));
            return result;
        }

        public static VerificationResult Verify(string source, bool overflow = true)
        {
            var result = Engine.VerifySources(new[] { ("Test.cs", Usings + source) }, new VerifierOptions { CheckOverflow = overflow });
            Xunit.Assert.True(result.CompilationErrors.Count == 0, string.Join("\n", result.CompilationErrors));
            return result;
        }

        /// <summary>Error ids reported for one method (warnings excluded). The name must match one method only: which of
        /// several came first would depend on the order of the files, which differs between platforms.</summary>
        public static string[] Errors(this VerificationResult r, string method)
        {
            var matches = r.Methods.Where(m => m.Name == method || m.Name.EndsWith("." + method)).ToList();
            if (matches.Count == 0) throw new ArgumentException("no method " + method);
            if (matches.Count > 1) throw new ArgumentException($"'{method}' is ambiguous: " + string.Join(", ", matches.Select(m => m.Name)));
            return matches[0].Diagnostics.Where(d => d.IsError).Select(d => d.Id).OrderBy(x => x).ToArray();
        }

        /// <summary>One method's errors with their messages, for an assertion's failure message.</summary>
        public static string Explain(this VerificationResult r, string method) =>
            method + ": " + string.Join("; ", r.Methods.Where(m => m.Name == method || m.Name.EndsWith("." + method))
                .SelectMany(m => m.Diagnostics.Where(d => d.IsError)).Select(d => d.Id + " " + d.Message));

        public static string RepoRoot()
        {
            var dir = AppContext.BaseDirectory;
            while (dir != null && !File.Exists(Path.Combine(dir, "global.json"))) dir = Path.GetDirectoryName(dir);
            return dir ?? throw new DirectoryNotFoundException("repository root (global.json) not found above " + AppContext.BaseDirectory);
        }
    }
}
