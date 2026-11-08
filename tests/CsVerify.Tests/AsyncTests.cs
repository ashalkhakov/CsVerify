using System;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Threading.Tasks;
using CsVerify.Verifier;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Xunit;

namespace CsVerify.Tests
{
    /// <summary>
    /// async and await: an async method's contract speaks of its task's result, awaiting it is a call, and at each
    /// await everything the method does not hold may change.
    /// </summary>
    public class AsyncTests
    {
        private const string Usings = "using System.Threading.Tasks; ";

        private static string[] Errors(string method, string source) =>
            Harness.Verify(Usings + "public static class C { " + source + " }", overflow: false).Errors(method);

        private const string Twice =
            "static async Task<int> Twice(int x) { Spec.Requires(-1000 < x && x < 1000); Spec.Ensures<int>(r => r == 2 * x); await Task.Yield(); return 2 * x; } ";

        // ---- async methods and awaited calls -------------------------------------------------------------------

        [Fact]
        public void AsyncMethod_ContractOfItsResult() => Assert.Empty(Errors("Twice", Twice));

        [Fact]
        public void AsyncMethod_PostconditionChecked() => Assert.Equal(new[] { "CSV1002" }, Errors("M",
            "static async Task<int> M() { Spec.Ensures<int>(r => r > 0); await Task.Yield(); return 0; }"));

        [Fact]
        public void AsyncMethod_NonNullResult() => Assert.Equal(new[] { "CSV1014" }, Errors("M",
            "static async Task<string> M(string? s) { await Task.Yield(); return s; }"));

        [Fact]
        public void Await_GivesTheCalleesPostcondition() => Assert.Empty(Errors("M", Twice +
            "static async Task<int> M() { var r = await Twice(3); Spec.Assert(r == 6); return r; }"));

        [Fact]
        public void Await_GivesTheCalleesPostcondition_Refuted() => Assert.Equal(new[] { "CSV1004" }, Errors("M", Twice +
            "static async Task<int> M() { var r = await Twice(3); Spec.Assert(r == 7); return r; }"));

        [Fact]
        public void Await_ChecksTheCalleesPrecondition() => Assert.Equal(new[] { "CSV1001" }, Errors("M", Twice +
            "static async Task<int> M() { return await Twice(5000); }"));

        [Fact]
        public void Await_ThroughConfigureAwait() => Assert.Empty(Errors("M", Twice +
            "static async Task<int> M() { var r = await Twice(3).ConfigureAwait(false); Spec.Assert(r == 6); return r; }"));

        [Fact]
        public void Await_OfATask() => Assert.Empty(Errors("M",
            "static async Task Log(int x) { Spec.Requires(x >= 0); await Task.Yield(); } static async Task M() { await Log(1); }"));

        [Fact]
        public void LibraryTask_ResultAsDeclared() => Assert.Empty(Errors("M",
            "static async Task<string> M(string path) { var s = await System.IO.File.ReadAllTextAsync(path); return s; }"));

        [Fact]
        public void DelegateTask_ResultAsItsTypeSays()
        {
            Assert.Empty(Errors("M", "static async Task<string> M(System.Func<Task<string>> c) { Spec.Requires(Spec.Pre(c)); return await c(); }"));
            Assert.Equal(new[] { "CSV1014" }, Errors("M", "static async Task<string> M(System.Func<Task<string?>> c) { Spec.Requires(Spec.Pre(c)); return await c(); }"));
        }

        [Fact]
        public void LibraryTask_ResultUnknown() => Assert.Equal(new[] { "CSV1004" }, Errors("M",
            "static async Task M() { var n = await Task.FromResult(1); Spec.Assert(n == 1); }"));

        [Fact]
        public void AsyncLemma_IsRejected() => Assert.Contains("CSV1901", Errors("L",
            "[Lemma, System.Diagnostics.Conditional(\"CSVERIFY_SPEC\")] static async void L() { await Task.Yield(); }"));

        // ---- what an await forgets, and what it keeps ----------------------------------------------------------

        [Fact]
        public void Await_ForgetsFields() => Assert.Equal(new[] { "CSV1004" }, Harness.Verify(Usings +
            "public sealed class Counter { public int N; } public static class C { static async Task M(Counter c) { c.N = 1; await Task.Yield(); Spec.Assert(c.N == 1); } }",
            overflow: false).Errors("M"));

        [Fact]
        public void Await_ForgetsArrays() => Assert.Equal(new[] { "CSV1004" }, Errors("M",
            "static async Task M(int[] a) { Spec.Requires(a.Length > 0); a[0] = 1; await Task.Yield(); Spec.Assert(a[0] == 1); }"));

        // ---- confined objects: made by the method and never handed out, so no other code can reach them ------

        private const string CounterType = "public sealed class Counter { public int N; } " +
            "public sealed class Leaky { public static Leaky Last; public int N; public Leaky() { Last = this; } } " +
            "public class Registering : System.Collections.ObjectModel.Collection<int> { public int N; protected override void InsertItem(int i, int x) { Holder.Last = this; base.InsertItem(i, x); } } " +
            "public sealed class Disposing : System.IDisposable { public int N; public void Dispose() { Holder.Last = this; } } " +
            "public static class Holder { public static object Last; public static Counter Kept; public static void Keep(Counter c) { Kept = c; } } ";

        private static string[] Confined(string body) =>
            Harness.Verify(Usings + CounterType + "public static class C { static async Task M() { " + body + " } }", overflow: false).Errors("M");

        [Fact]
        public void Await_KeepsAConfinedObject() => Assert.Empty(Confined("var c = new Counter(); c.N = 1; await Task.Yield(); Spec.Assert(c.N == 1);"));

        [Fact]
        public void Await_KeepsAConfinedArray() => Assert.Empty(Confined("var a = new int[3]; a[0] = 1; await Task.Yield(); Spec.Assert(a[0] == 1 && a.Length == 3);"));

        [Fact]
        public void Await_KeepsAConfinedList() => Assert.Empty(Confined(
            "var l = new System.Collections.Generic.List<int>(); l.Add(4); await Task.Yield(); Spec.Assert(l.Count == 1 && l[0] == 4);"));

        [Fact]
        public void Await_KeepsAConfinedObject_ReassignedFresh() => Assert.Empty(Confined(
            "var c = new Counter(); c.N = 1; await Task.Yield(); c = new Counter(); c.N = 2; await Task.Yield(); Spec.Assert(c.N == 2);"));

        [Fact]
        public void Await_ForgetsAnObjectStoredInAField() => Assert.Equal(new[] { "CSV1004" }, Confined(
            "var c = new Counter(); Holder.Kept = c; c.N = 1; await Task.Yield(); Spec.Assert(c.N == 1);"));

        [Fact]
        public void Await_ForgetsAnObjectPassedToACall() => Assert.Equal(new[] { "CSV1004" }, Confined(
            "var c = new Counter(); Holder.Keep(c); c.N = 1; await Task.Yield(); Spec.Assert(c.N == 1);"));

        [Fact]
        public void Await_ForgetsAnObjectItsConstructorHandsOut() => Assert.Equal(new[] { "CSV1004" }, Confined(
            "var c = new Leaky(); c.N = 1; await Task.Yield(); Spec.Assert(c.N == 1);"));

        [Fact]
        public void Await_ForgetsAnObjectALibraryBaseMayHandOut() => Assert.Equal(new[] { "CSV1004" }, Confined(
            "var c = new Registering(); c.Add(3); c.N = 1; await Task.Yield(); Spec.Assert(c.N == 1);"));

        [Fact]
        public void Await_ForgetsAnObjectItsDisposeMayHandOut() => Assert.Equal(new[] { "CSV1004" }, Confined(
            "var d = new Disposing(); using (d) { } d.N = 1; await Task.Yield(); Spec.Assert(d.N == 1);"));

        [Fact]
        public void Await_ForgetsACapturedObject() => Assert.Equal(new[] { "CSV1004" }, Confined(
            "var c = new Counter(); System.Action a = () => c.N = 2; c.N = 1; await Task.Yield(); Spec.Assert(c.N == 1);"));

        [Fact]
        public void Await_ForgetsAnAliasedObject() => Assert.Equal(new[] { "CSV1004" }, Confined(
            "var c = new Counter(); var d = c; Holder.Kept = d; c.N = 1; await Task.Yield(); Spec.Assert(c.N == 1);"));

        [Fact]
        public void Await_ForgetsAnObjectFromElsewhere() => Assert.Equal(new[] { "CSV1004" }, Confined(
            "var c = Holder.Kept; Spec.Assume(c != null); c.N = 1; await Task.Yield(); Spec.Assert(c.N == 1);"));

        [Fact]
        public void Await_InALoop_KeepsAConfinedObject() => Assert.Empty(Confined(
            "var c = new Counter(); c.N = 1; for (int i = 0; i < 3; i++) { await Task.Yield(); } Spec.Assert(c.N == 1);"));

        [Fact]
        public void Await_InALoop_ForgetsWhatTheLoopWrites() => Assert.Equal(new[] { "CSV1004" }, Confined(
            "var c = new Counter(); c.N = 1; for (int i = 0; i < 3; i++) { await Task.Yield(); c.N = 2; } Spec.Assert(c.N == 1);"));

        [Fact]
        public void Await_InALoop_KeepsAConfinedArray() => Assert.Empty(Confined(
            "var a = new int[2]; var b = new int[2]; a[0] = 7; for (int i = 0; i < 3; i++) { await Task.Yield(); b[1] = i; } Spec.Assert(a[0] == 7);"));

        [Fact]
        public void Await_KeepsLocals() => Assert.Empty(Errors("M",
            "static async Task M(int x) { int k = x + 1; await Task.Yield(); Spec.Assert(k == x + 1); }"));

        [Fact]
        public void Await_ForgetsLocalsALambdaWrites() => Assert.Equal(new[] { "CSV1004" }, Errors("M",
            "static async Task M() { int s = 0; System.Action a = () => s = 1; await Task.Yield(); Spec.Assert(s == 0); }"));

        [Fact]
        public void Await_KeepsHeldCells() => Assert.Empty(Errors("M",
            "static async Task M(int[] a) { Spec.Requires(a.Length > 1 && Spec.Acc(a)); Spec.Ensures(Spec.Acc(a)); a[0] = 1; await Task.Yield(); Spec.Assert(a[0] == 1); }"));

        [Fact]
        public void Await_ForgetsCellsNotHeld() => Assert.Equal(new[] { "CSV1004" }, Errors("M",
            "static async Task M(int[] a, int[] b) { Spec.Requires(a.Length > 0 && b.Length > 0 && Spec.Acc(a)); Spec.Ensures(Spec.Acc(a)); " +
            "var x = b[0]; await Task.Yield(); Spec.Assert(b[0] == x); }"));

        private const string Account = "[Owned] public sealed class Account { public int Balance; [Invariant, Pure] public bool Valid() => Balance >= 0; " +
            "public Account(int initial) { Spec.Requires(initial >= 0); Spec.Ensures(Balance == initial); Balance = initial; } } ";

        [Fact]
        public void Await_KeepsObjectsWhoseViewIsHeld() => Assert.Empty(Harness.Verify(Usings + Account +
            "public static class C { static async Task M() { var a = Own.New(new Account(5), out var v); await Task.Yield(); Spec.Assert(a.Balance == 5); Own.Drop(v); } }",
            overflow: false).Errors("M"));

        [Fact]
        public void Await_ForgetsObjectsWhoseViewIsElsewhere() => Assert.Equal(new[] { "CSV1004" }, Harness.Verify(Usings + Account +
            "public static class C { static async Task M(Account a) { var b = a.Balance; await Task.Yield(); Spec.Assert(a.Balance == b); } }",
            overflow: false).Errors("M"));

        [Fact]
        public void Await_InALoop() => Assert.Empty(Errors("M",
            "static async Task M(int n) { Spec.Requires(n >= 0); int i = 0; while (i < n) { Spec.Invariant(i <= n); await Task.Yield(); i++; } Spec.Assert(i == n); }"));

        [Fact]
        public void Await_InALoop_ForgetsArrays() => Assert.Equal(new[] { "CSV1004" }, Errors("M",
            "static async Task M(int[] a, int n) { Spec.Requires(a.Length > 0); a[0] = 1; for (int i = 0; i < n; i++) { await Task.Yield(); } Spec.Assert(a[0] == 1); }"));

        // ---- lambdas and local functions that write the method's locals -----------------------------------------

        [Fact]
        public void LambdaWrites_AreSeenAfterACall() => Assert.Equal(new[] { "CSV1004" }, Errors("M",
            "static void M(System.Collections.Generic.List<int> l) { int s = 0; l.ForEach(x => s += x); Spec.Assert(s == 0); }"));

        [Fact]
        public void LambdaWrites_AreSeenAfterInvokingIt() => Assert.Equal(new[] { "CSV1004" }, Errors("M",
            "static void M() { int s = 0; System.Action a = () => s = 1; a(); Spec.Assert(s == 0); }"));

        [Fact]
        public void LocalFunctionWrites_AreSeenAfterCallingIt() => Assert.Equal(new[] { "CSV1004" }, Errors("M",
            "static void M() { int s = 0; void Set() { s = 1; } Set(); Spec.Assert(s == 0); }"));

        [Fact]
        public void LambdaWrites_InALoopWithACall() => Assert.Equal(new[] { "CSV1004" }, Errors("M",
            "static void M(System.Collections.Generic.List<int> l) { int s = 0; for (int i = 0; i < 2; i++) { l.ForEach(x => s = 1); } Spec.Assert(s == 0); }"));

        [Fact]
        public void LocalsNoLambdaWrites_AreKeptAcrossCalls() => Assert.Empty(Errors("M",
            "static void M(System.Collections.Generic.List<int> l) { int s = 0; int k = 2; l.ForEach(x => s += x + k); Spec.Assert(k == 2); }"));

        // ---- erasure ---------------------------------------------------------------------------------------------

        [Fact]
        public async Task Erased_Async_Runs()
        {
            const string source = "using System.Diagnostics; using System.Threading.Tasks; using CsVerify;\nnamespace Samples { public static class Async {\n" + Twice +
                "public static async Task<int> Demo() { Spec.Ensures<int>(r => r == 6 + 8); var a = await Twice(3); var b = await Twice(4).ConfigureAwait(false); return a + b; }\n} }";
            Assert.DoesNotContain(Harness.Verify(source, overflow: false).Methods.SelectMany(m => m.Diagnostics), d => d.IsError);
            var erased = Erasure.Erase(new[] { ("Async.cs", source) }, Array.Empty<string>(), Array.Empty<string>());
            Assert.True(erased.Success, string.Join("\n", erased.Errors));
            var compilation = CSharpCompilation.Create("Erased",
                erased.Files.Select(f => CSharpSyntaxTree.ParseText(f.Text, new CSharpParseOptions(LanguageVersion.Latest), f.OutputName)),
                Engine.FrameworkReferences(), new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary));
            using var ms = new MemoryStream();
            var emit = compilation.Emit(ms);
            Assert.True(emit.Success, string.Join("\n", emit.Diagnostics));
            var task = (Task<int>)Assembly.Load(ms.ToArray()).GetType("Samples.Async").GetMethod("Demo").Invoke(null, null);
            Assert.Equal(6 + 8, await task);
        }
    }
}
