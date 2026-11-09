using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using CsVerify.Verifier;

namespace CsVerify.Tests
{
    /// <summary>Programs that use Entity Framework Core, verified with its assemblies as a project referencing it passes them.</summary>
    internal static class EfHarness
    {
        private const string Usings = "using System; using System.Diagnostics; using CsVerify; using System.Collections.Generic; using System.Linq; " +
                                      "using System.Threading; using System.Threading.Tasks; using Microsoft.EntityFrameworkCore;\n";

        /// <summary>EF Core's assemblies, and what they build on (not a provider's).</summary>
        public static List<string> EfReferences(bool sqlite = false) => Directory.EnumerateFiles(AppContext.BaseDirectory, "*.dll")
            .Where(p => Path.GetFileName(p).StartsWith("Microsoft.EntityFrameworkCore") || Path.GetFileName(p).StartsWith("Microsoft.Extensions.") ||
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

        public static VerificationResult VerifyEf(string source, bool overflow = true, bool sqlite = false)
        {
            var result = Engine.VerifySources(new[] { ("Test.cs", Usings + source) }, Options(overflow, sqlite));
            Xunit.Assert.True(result.CompilationErrors.Count == 0, string.Join("\n", result.CompilationErrors));
            return result;
        }
    }
}
