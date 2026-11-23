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
        internal const string Usings = "using System; using System.Diagnostics; using CsVerify;\n";

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
            var analyzers = ImmutableArray.Create<DiagnosticAnalyzer>(new LinearityAnalyzer(), new GhostAnalyzer(), new PurityAnalyzer(), new DisposalAnalyzer(), new TaintAnalyzer());
            return compilation.WithAnalyzers(analyzers).GetAnalyzerDiagnosticsAsync().Result
                .Select(d => d.Id).OrderBy(x => x).ToArray();
        }

        public static VerificationResult Verify(string source, bool overflow = true)
        {
            var result = Engine.VerifySources(new[] { ("Test.cs", Usings + source) }, new VerifierOptions { CheckOverflow = overflow });
            Xunit.Assert.True(result.CompilationErrors.Count == 0, string.Join("\n", result.CompilationErrors));
            return result;
        }

        /// <summary>
        /// Verifies the source against a library compiled from another source (a referenced project's assembly); with
        /// sources, given that project too (--project-reference), as the build targets give it.
        /// </summary>
        public static VerificationResult VerifyWithLibrary(string library, string source, bool sources = false)
        {
            var name = "CsVerifyLibrary" + Guid.NewGuid().ToString("N");
            var dir = Path.Combine(Path.GetTempPath(), name);
            Directory.CreateDirectory(dir);
            var file = Path.Combine(dir, "Library.cs");
            File.WriteAllText(file, library);
            var lib = CSharpCompilation.Create(name, new[] { CSharpSyntaxTree.ParseText(library, path: file) }, Engine.FrameworkReferences().Append(MetadataReference.CreateFromFile(typeof(CsVerify.Spec).Assembly.Location)),
                new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary, nullableContextOptions: NullableContextOptions.Enable));
            var path = Path.Combine(dir, name + ".dll");
            var emit = lib.Emit(path);
            Xunit.Assert.True(emit.Success, string.Join("\n", emit.Diagnostics));
            try
            {
                var options = new VerifierOptions { CheckOverflow = true };
                options.References.Add(path);
                if (sources)
                {
                    var project = new ProjectReference { AssemblyName = name, Nullable = NullableContextOptions.Enable };
                    project.Sources.Add(file);
                    options.ProjectReferences.Add(project);
                }
                var result = Engine.VerifySources(new[] { ("Test.cs", Usings + source) }, options);
                Xunit.Assert.True(result.CompilationErrors.Count == 0, string.Join("\n", result.CompilationErrors));
                return result;
            }
            finally { try { Directory.Delete(dir, true); } catch (IOException) { } }
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
