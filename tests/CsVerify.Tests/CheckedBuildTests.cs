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
    /// The checked build (csverify erase --checked): the specifications that can run are run-time checks, which throw
    /// when the program breaks them, and stay quiet when it doesn't.
    /// </summary>
    public class CheckedBuildTests
    {
        private static ErasureResult Checked(string source) =>
            Erasure.Erase(new[] { ("Test.cs", "using System; using System.Threading; using CsVerify;\n" + source) }, Array.Empty<string>(), Array.Empty<string>(), checkedBuild: true);

        private static Assembly Load(ErasureResult built)
        {
            Assert.True(built.Success, string.Join("\n", built.Errors));
            var compilation = CSharpCompilation.Create("Checked" + Guid.NewGuid().ToString("N"),
                built.Files.Select(f => CSharpSyntaxTree.ParseText(f.Text, new CSharpParseOptions(LanguageVersion.Latest), f.OutputName)),
                Engine.FrameworkReferences(), new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary));
            using var ms = new MemoryStream();
            var emit = compilation.Emit(ms);
            Assert.True(emit.Success, string.Join("\n", emit.Diagnostics));
            return Assembly.Load(ms.ToArray());
        }

        /// <summary>Calls C.method (a new C for an instance method); the message of the specification that failed, or null.</summary>
        private static string Fails(string source, string method, params object[] args)
        {
            var c = Load(Checked(source)).GetType("C");
            var m = c.GetMethod(method);
            try
            {
                m.Invoke(m.IsStatic ? null : Activator.CreateInstance(c), args);
                return null;
            }
            catch (TargetInvocationException e) when (e.InnerException?.GetType().Name == "SpecificationFailedException")
            {
                return e.InnerException.Message;
            }
        }

        [Fact]
        public void CheckedSamples_ComputeWhatTheProofsSay_AndKeepTheirLineNumbers()
        {
            var built = Erasure.Erase(Directory.GetFiles(Path.Combine(Harness.RepoRoot(), "samples", "Good"), "*.cs").Select(p => (p, File.ReadAllText(p))),
                Array.Empty<string>(), Array.Empty<string>(), checkedBuild: true);
            // verified code breaks none of its checks
            ErasurePassTests.ComputeWhatTheProofsSay(Load(built));
            foreach (var f in built.Files.Where(f => !f.OutputName.StartsWith(Erasure.RuntimeFolder)))
                Assert.Equal(File.ReadAllText(f.OriginalPath).Split('\n').Length + 2, f.Text.Split('\n').Length); // (#pragma and #line)
            Assert.Contains(built.Files, f => f.Text.Contains("global::CsVerify.Checked.Requires"));
        }

        [Fact]
        public void Precondition_IsChecked()
        {
            const string source = "public static class C { public static int M(int x) { Spec.Requires(x > 0); return x; } }";
            Assert.Null(Fails(source, "M", 1));
            Assert.Contains("precondition failed: x > 0 (Test.cs:2)", Fails(source, "M", 0));
        }

        [Fact]
        public void Postcondition_IsCheckedAtEachReturn_WithOldValues()
        {
            const string source = "public sealed class C { private int _n;\n" +
                "public int Next(int x) { Spec.Ensures<int>(r => r > x); if (x == 5) return x; return x + 1; }\n" +
                "public void Add(int k) { Spec.Ensures(_n == Spec.Old(_n) + k); if (k == 0) return; _n += k == 3 ? 4 : k; } }";
            Assert.Null(Fails(source, "Next", 1));
            Assert.Contains("postcondition failed: r => r > x", Fails(source, "Next", 5));
            Assert.Null(Fails(source, "Add", 0));
            Assert.Null(Fails(source, "Add", 2));
            Assert.Contains("postcondition failed: _n == Spec.Old(_n) + k", Fails(source, "Add", 3)); // (at the end of the body)
        }

        [Fact]
        public void AssertionsAndForall_Run()
        {
            const string source = "public static class C { public static void M(int[] a) { Spec.Assert(Spec.Forall(0, a.Length, i => a[i] >= 0)); } }";
            Assert.Null(Fails(source, "M", new[] { 1, 2 }));
            Assert.Contains("assertion failed", Fails(source, "M", new[] { 1, -2 }));
        }

        [Fact]
        public void LockInvariant_IsCheckedWhereTheLockIsGivenBack()
        {
            const string source = "public sealed class C { private readonly object _lock = new object(); [GuardedBy(nameof(_lock))] private int _n;\n" +
                "[LockInvariant(nameof(_lock)), Pure] private bool Valid() => _n >= 0;\n" +
                "public void M(int k) { lock (_lock) { _n -= k; if (k == 2) _n += k; } } }";
            Assert.Null(Fails(source, "M", 2));
            Assert.Contains("lock invariant failed: Valid() (_lock)", Fails(source, "M", 1));
        }

        [Fact]
        public void AtomicWrite_IsCheckedAsAStep()
        {
            const string source = "public sealed class C { [Atomic(Step = nameof(Grows))] private volatile int _n = 5;\n" +
                "[Pure] private static bool Grows(int old, int now) => old <= now;\n" +
                "public void Set(int v) { _n = v; }\n" +
                "public void Cas(int v) { Interlocked.CompareExchange(ref _n, v, 5); } }";
            Assert.Null(Fails(source, "Set", 7));
            Assert.Contains("step failed: _n = v", Fails(source, "Set", 4));
            Assert.Contains("step failed: Interlocked.CompareExchange", Fails(source, "Cas", 4));
        }

        [Fact]
        public void LockLevel_IsCheckedWhereALockIsTaken()
        {
            const string source = "public sealed class C { [LockLevel(1)] private readonly object _low = new object(); [LockLevel(2)] private readonly object _high = new object();\n" +
                "public void InOrder() { lock (_low) lock (_high) { } }\n" +
                "public void Reversed() { lock (_high) lock (_low) { } } }";
            Assert.Null(Fails(source, "InOrder"));
            Assert.Contains("lock level failed: _low (level 1) taken while holding _high (level 2)", Fails(source, "Reversed"));
            Assert.Null(Fails(source, "InOrder")); // (and the lock given back is no longer held)
        }

        [Fact]
        public void WhatCantRun_OrMayChangeMeanwhile_IsLeftOut()
        {
            // ghost state; an [Atomic] field another thread may step; a guarded field outside its lock
            const string source = "public sealed class C { [Atomic] private volatile int _a; private readonly object _lock = new object(); [GuardedBy(nameof(_lock))] private int _g;\n" +
                "public int M(Seq<int> s) { Spec.Requires(s.Count == 1); Spec.Ensures<int>(r => r == _a); Spec.Assert(_g == 1); return 3; } }";
            var built = Checked(source);
            Assert.DoesNotContain("Checked.", built.Files[0].Text);
            Load(built);
        }
    }
}
