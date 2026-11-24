using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using CsVerify.Verifier;
using Microsoft.CodeAnalysis;

namespace CsVerify.Tests
{
    /// <summary>Programs that use Entity Framework Core, verified with its assemblies as a project referencing it passes them.</summary>
    internal static class EfHarness
    {
        private const string Usings = "using System; using System.Diagnostics; using CsVerify; using System.Collections.Generic; using System.Linq; " +
                                      "using System.Threading; using System.Threading.Tasks; using Microsoft.EntityFrameworkCore;\n";

        /// <summary>EF Core's assemblies, and what they build on (not a provider's), and ASP.NET Core Identity's stores.</summary>
        public static List<string> EfReferences(bool sqlite = false) => Directory.EnumerateFiles(AppContext.BaseDirectory, "*.dll")
            .Where(p => Path.GetFileName(p).StartsWith("Microsoft.EntityFrameworkCore") || Path.GetFileName(p).StartsWith("Microsoft.Extensions.") ||
                        Path.GetFileName(p).StartsWith("Microsoft.AspNetCore.Identity") ||
                        sqlite && Path.GetFileName(p).StartsWith("Microsoft.Data.Sqlite"))
            .Where(p => sqlite || !Path.GetFileName(p).Contains("Sqlite"))
            .Where(p => !Path.GetFileName(p).Contains("SqlServer") && !Path.GetFileName(p).Contains("Design")).ToList();

        /// <summary>The options: EF Core's assemblies, and SQLite's provider if asked for (a program that names it).</summary>
        public static VerifierOptions Options(bool overflow = true, bool sqlite = false)
        {
            var options = new VerifierOptions { CheckOverflow = overflow };
            options.References.AddRange(EfReferences(sqlite));
            return options;
        }

        /// <summary>
        /// A library compiled to an assembly of its own (a domain project the program references), with its
        /// InternalsVisibleTo granting the program's assembly, "App"; the program is verified under that name.
        /// </summary>
        public static VerificationResult VerifyEfWithLibrary(string library, string source, bool referenceAssembly = false)
        {
            var path = Path.Combine(Path.GetTempPath(), "CsVerifyEfLib" + Guid.NewGuid().ToString("N") + ".dll");
            var lib = Microsoft.CodeAnalysis.CSharp.CSharpCompilation.Create(Path.GetFileNameWithoutExtension(path),
                new[] { Microsoft.CodeAnalysis.CSharp.CSharpSyntaxTree.ParseText("[assembly: System.Runtime.CompilerServices.InternalsVisibleTo(\"App\")]\n" + library) },
                Engine.FrameworkReferences(), new Microsoft.CodeAnalysis.CSharp.CSharpCompilationOptions(Microsoft.CodeAnalysis.OutputKind.DynamicallyLinkedLibrary,
                    nullableContextOptions: Microsoft.CodeAnalysis.NullableContextOptions.Enable));
            // (a reference assembly, as a targeting pack's: no private members, its backing fields among them)
            Microsoft.CodeAnalysis.Emit.EmitResult emit;
            if (referenceAssembly)
            {
                using var file = File.Create(path);
                emit = lib.Emit(file, options: new Microsoft.CodeAnalysis.Emit.EmitOptions(metadataOnly: true, includePrivateMembers: false));
            }
            else
            {
                emit = lib.Emit(path);
            }
            Xunit.Assert.True(emit.Success, string.Join("\n", emit.Diagnostics));
            try
            {
                var options = Options();
                options.AssemblyName = "App";
                options.References.Add(path);
                var result = Engine.VerifySources(new[] { ("Test.cs", Usings + source) }, options);
                Xunit.Assert.True(result.CompilationErrors.Count == 0, string.Join("\n", result.CompilationErrors));
                return result;
            }
            finally { try { File.Delete(path); } catch (IOException) { } }
        }

        /// <summary>
        /// A library of its own that uses EF Core (a project with the context and its configuration), compiled to an
        /// assembly the program references, and described as the MSBuild target describes it (--project-reference).
        /// </summary>
        public static VerificationResult VerifyEfWithContextLibrary(string library, string source, bool sources = true)
        {
            var name = "CsVerifyEfContext" + Guid.NewGuid().ToString("N");
            var dir = Path.Combine(Path.GetTempPath(), name);
            Directory.CreateDirectory(dir);
            var file = Path.Combine(dir, "Context.cs");
            File.WriteAllText(file, Usings.Replace("using CsVerify; ", "") + library);
            var lib = Microsoft.CodeAnalysis.CSharp.CSharpCompilation.Create(name,
                new[] { Microsoft.CodeAnalysis.CSharp.CSharpSyntaxTree.ParseText(File.ReadAllText(file), path: file) },
                Engine.FrameworkReferences().Concat(EfReferences().Select(r => MetadataReference.CreateFromFile(r))),
                new Microsoft.CodeAnalysis.CSharp.CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary, nullableContextOptions: NullableContextOptions.Enable));
            var path = Path.Combine(dir, name + ".dll");
            var emit = lib.Emit(path);
            Xunit.Assert.True(emit.Success, string.Join("\n", emit.Diagnostics));
            try
            {
                var options = Options();
                options.References.Add(path);
                // (without: a library's, read from its assembly alone)
                if (sources)
                {
                    var project = new ProjectReference { AssemblyName = name, Nullable = NullableContextOptions.Enable };
                    project.Sources.Add(file);
                    project.References.AddRange(EfReferences());
                    options.ProjectReferences.Add(project);
                }
                var result = Engine.VerifySources(new[] { ("Test.cs", Usings + source) }, options);
                Xunit.Assert.True(result.CompilationErrors.Count == 0, string.Join("\n", result.CompilationErrors));
                return result;
            }
            finally { try { Directory.Delete(dir, true); } catch (IOException) { } }
        }

        /// <summary>A project the program references: its name, its source, the projects it references, and whether it references EF Core.</summary>
        public sealed record Project(string Name, string Source, string[] Projects, bool Ef = true);

        /// <summary>
        /// Projects the program references, each compiled to an assembly of its own (in order: a project's references
        /// first) and described as the MSBuild target describes it; the program references them all and EF Core.
        /// </summary>
        public static VerificationResult VerifyEfWithProjects(string source, params Project[] projects) => VerifyEfWithProjects(source, _ => { }, projects);

        public static VerificationResult VerifyEfWithProjects(string source, Action<VerifierOptions> set, params Project[] projects)
        {
            var dir = Path.Combine(Path.GetTempPath(), "CsVerifyEfProjects" + Guid.NewGuid().ToString("N"));
            Directory.CreateDirectory(dir);
            try
            {
                var options = Options();
                options.AssemblyName = "App";
                var dlls = new Dictionary<string, string>();
                var described = new Dictionary<string, ProjectReference>();
                foreach (var p in projects)
                {
                    var file = Path.Combine(dir, p.Name + ".cs");
                    File.WriteAllText(file, (p.Ef ? Usings.Replace("using CsVerify; ", "") : "using System; using System.Collections.Generic;\n") + p.Source);
                    var files = (p.Ef ? EfReferences() : new List<string>()).Concat(p.Projects.Select(r => dlls[r])).ToList();
                    var lib = Microsoft.CodeAnalysis.CSharp.CSharpCompilation.Create(p.Name,
                        new[] { Microsoft.CodeAnalysis.CSharp.CSharpSyntaxTree.ParseText(File.ReadAllText(file), path: file) },
                        Engine.FrameworkReferences().Concat(files.Select(r => MetadataReference.CreateFromFile(r))),
                        new Microsoft.CodeAnalysis.CSharp.CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary, nullableContextOptions: NullableContextOptions.Enable));
                    var path = Path.Combine(dir, p.Name + ".dll");
                    var emit = lib.Emit(path);
                    Xunit.Assert.True(emit.Success, string.Join("\n", emit.Diagnostics));
                    dlls[p.Name] = path;
                    var project = new ProjectReference { AssemblyName = p.Name, Nullable = NullableContextOptions.Enable };
                    project.Sources.Add(file);
                    project.References.AddRange(files);
                    // (a project's references include what the projects it references reference, as the build's do)
                    project.References.AddRange(p.Projects.SelectMany(r => described[r].References));
                    described[p.Name] = project;
                    options.ProjectReferences.Add(project);
                    options.References.Add(path);
                }
                set(options);
                var result = Engine.VerifySources(new[] { ("Test.cs", Usings + source) }, options);
                Xunit.Assert.True(result.CompilationErrors.Count == 0, string.Join("\n", result.CompilationErrors));
                return result;
            }
            finally { try { Directory.Delete(dir, true); } catch (IOException) { } }
        }

        public static VerificationResult VerifyEf(string source, bool overflow = true, bool sqlite = false)
        {
            var result = Engine.VerifySources(new[] { ("Test.cs", Usings + source) }, Options(overflow, sqlite));
            Xunit.Assert.True(result.CompilationErrors.Count == 0, string.Join("\n", result.CompilationErrors));
            return result;
        }
    }
}
