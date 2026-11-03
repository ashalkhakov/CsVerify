using System;
using System.IO;
using System.Linq;
using System.Reflection;
using CsVerify.Verifier;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Xunit;

namespace CsVerify.Tests
{
    /// <summary>
    /// The erasure pass: the program with every proof removed still compiles, carries no ghost types, and computes
    /// what the proofs say it computes.
    /// </summary>
    public class ErasurePassTests
    {
        private static ErasureResult EraseSamples() =>
            Erasure.Erase(Directory.GetFiles(Path.Combine(Harness.RepoRoot(), "samples", "Good"), "*.cs")
                .Select(p => (p, File.ReadAllText(p))), Array.Empty<string>(), Array.Empty<string>());

        private static Assembly Load(ErasureResult erased)
        {
            var compilation = CSharpCompilation.Create("Erased",
                erased.Files.Select(f => CSharpSyntaxTree.ParseText(f.Text, new CSharpParseOptions(LanguageVersion.Latest), f.OutputName)),
                Engine.FrameworkReferences(), new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary));
            using var ms = new MemoryStream();
            var emit = compilation.Emit(ms);
            Assert.True(emit.Success, string.Join("\n", emit.Diagnostics));
            return Assembly.Load(ms.ToArray());
        }

        private static object Run(Assembly asm, string type, string method, params object[] args) =>
            asm.GetType("Samples." + type).GetMethod(method).Invoke(null, args);

        [Fact]
        public void ErasedSamples_ComputeWhatTheProofsSay()
        {
            var erased = EraseSamples();
            Assert.True(erased.Success, string.Join("\n", erased.Errors));
            var asm = Load(erased);
            // each expected value is a verified postcondition of the method
            Assert.Equal(9 + 7, Run(asm, "ArrayViews", "Demo"));
            Assert.Equal(42, Run(asm, "Memory", "Counter"));
            Assert.Equal(2, Run(asm, "Memory", "Twice"));
            Assert.Equal(2 * 10 + 1, Run(asm, "AtsIntro", "SwapDemo"));
            Assert.Equal(5, Run(asm, "AtsArrays", "CopyDemo"));
            Assert.Equal(4 + 3, Run(asm, "AtsMatrixAndTakeOut", "TakeOutDemo"));
            Assert.Equal(3, Run(asm, "Arrays", "LastOfThree"));
            Assert.Equal(55, Run(asm, "AtsIntro", "FibIter", 10));
            Assert.Equal(9, Run(asm, "AtsIntro", "Ackermann", 2, 3));
            Assert.Equal(55, Run(asm, "Lemmas", "TriFast", 10));
            Assert.Equal((2, 5), Run(asm, "DafnyMore", "MaxSegSum", new[] { 1, -3, 4, -1, 2, -9, 3 }));
            Assert.Equal(7 + 2, Run(asm, "Nulls", "Demo"));
            Assert.Equal(3 + 4 + 7 + 6, Run(asm, "DataTypes", "Demo")); // a proof-carrying factorial: its Ghost<Fact> is gone
            Assert.Equal(10 * 3 + 3, Run(asm, "Trees", "Demo")); // 1..7 inserted: AVL height 3, black height 3
            Assert.Equal(30 + 20, Run(asm, "Bank", "Demo", Activator.CreateInstance(asm.GetType("Samples.NullAudit")))); // owned accounts: views gone
            Assert.Equal(10, Run(asm, "DynamicFrames", "Demo")); // Dafny-style pairs: Repr and Valid() gone
            Assert.Equal(5431, Run(asm, "OwnedList", "Demo")); // 1, 5, 3, 4 inserted: 1 3 4 5, last digit first; Take/Give run
            // INT2PROGINATS ch. 15-16: 3 1 4 1 5 sorted (54311), buffer 7 then 8, timer 40 ticks, tree of size 4
            Assert.Equal(54311L * 10000 + 78 * 100 + 40 + 4 * 1000, Run(asm, "AtsViewtypes", "Demo"));
            // ACSL by Example on 1 3 3 5 8: find 5 at 3, lower/upper bound of 3 at 1/3, two 3s, three kept, sum 20
            Assert.Equal(20 * 100000 + 3 * 10000 + 1 * 1000 + 3 * 100 + 2 * 10 + 3, Run(asm, "AcslByExample", "Demo"));
            Assert.Equal(123123123, Run(asm, "AcslByExample", "SortDemo")); // selection, bubble and insertion sort
            // OOP: area 9 + 10, checking 100 + 30, first transfer allowed, second refused, a square's area via Shape
            Assert.Equal(9L * 100000000 + 19 * 10000 + 130 * 10 + 1, Run(asm, "Oop", "Demo"));
        }

        [Fact]
        public void ErasedSamples_CarryNoProofs()
        {
            var asm = Load(EraseSamples());
            var types = asm.GetTypes();
            // no ghost or view type survives, in the runtime or in any signature
            Assert.DoesNotContain(types, t => new[] { "Ghost`1", "Seq`1", "PointsTo`1", "ArrayView`1", "ArrayHole`1", "FreeGc`1", "Own`1", "ObjSet", "Spec" }.Contains(t.Name));
            var signatures = types.SelectMany(t => t.GetMethods(BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Static | BindingFlags.Instance | BindingFlags.DeclaredOnly));
            Assert.DoesNotContain(signatures, m => m.GetParameters().Any(p => p.ParameterType.Name.StartsWith("Ghost") || p.ParameterType.Name.Contains("View")));
            // lemmas, ghost functions and proof-only view functions are gone
            Assert.Null(asm.GetType("Samples.Lemmas").GetMethod("TriFormula", BindingFlags.Public | BindingFlags.Static));
            Assert.Null(asm.GetType("Samples.ArrayViews").GetMethod("AllEqual", BindingFlags.Public | BindingFlags.Static));
            Assert.Null(asm.GetType("CsVerify.Mem").GetMethod("Split"));
            // ATS's erased signatures: fill(p, n, x), last(A)
            Assert.Equal(new[] { "Ptr`1", "Int32", "Int32" }, asm.GetType("Samples.ArrayViews").GetMethod("Fill").GetParameters().Select(p => p.ParameterType.Name));
            Assert.Single(asm.GetType("Samples.Arrays").GetMethod("Last").GetParameters());
            Assert.DoesNotContain(asm.GetReferencedAssemblies(), a => a.Name.StartsWith("CsVerify"));
        }

        [Fact]
        public void ErasedFiles_KeepTheirLineNumbers()
        {
            foreach (var f in EraseSamples().Files.Where(f => !f.OutputName.StartsWith(Erasure.RuntimeFolder)))
                Assert.Equal(File.ReadAllText(f.OriginalPath).Split('\n').Length + 1, f.Text.Split('\n').Length);
        }

        private static ErasureResult Erase(string source) =>
            Erasure.Erase(new[] { ("Test.cs", "using System; using CsVerify;\n" + source) }, Array.Empty<string>(), Array.Empty<string>());

        [Fact]
        public void GhostLeakingIntoRunTimeCode_IsReported()
        {
            // a view hidden in a tuple, a ghost value boxed: neither can be erased
            var tuple = Erase("public static class C { public static (Ptr<int>, PointsTo<int>) M() { var p = Mem.Alloc(1, out var v); return (p, v); } }");
            Assert.Contains(tuple.Errors, d => d.Id == "CSV2001");
            var boxed = Erase("public static class C {\n public static object M() {\n object o = Ghost.Of(1);\n return o; } }");
            var error = Assert.Single(boxed.Errors, d => d.Id == "CSV2001");
            Assert.Equal(("Test.cs", 3), (error.Span.Path, error.Span.StartLinePosition.Line)); // reported where it is written
        }

        [Fact]
        public void EmbeddedSpecStatement_LeavesAnEmptyBlock()
        {
            var erased = Erase("public static class C { public static int M(int x) { if (x > 0) Spec.Assert(x != 0); return x; } }");
            Assert.True(erased.Success, string.Join("\n", erased.Errors));
            Assert.Contains("if (x > 0) { }", erased.Files[0].Text);
        }
    }
}
