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
    /// <summary>Loops that are not while/for/do: foreach (over arrays, and over anything else), and goto cycles.</summary>
    public class LoopTests
    {
        private static string[] Errors(string method, string source, bool overflow = false) =>
            Harness.Verify("public static class C { " + source + " }", overflow).Errors(method);

        private static string[] Warnings(string method, string source) =>
            Harness.Verify("public static class C { " + source + " }", overflow: false)[method].Diagnostics.Where(d => !d.IsError).Select(d => d.Id).ToArray();

        private const string Sum =
            "[Pure] static int Sum(int[] a, int n) { Spec.Requires(0 <= n && n <= a.Length); Spec.Decreases(n); return n == 0 ? 0 : Sum(a, n - 1) + a[n - 1]; } ";

        // ---- foreach over an array: an index from 0 to the length ---------------------------------------------

        [Fact]
        public void ForEachArray_Sum_Proved() => Assert.Empty(Errors("M", Sum +
            "static int M(int[] a) { Spec.Ensures<int>(r => r == Sum(a, a.Length)); int s = 0; " +
            "foreach (var x in a) { Spec.Invariant(s == Sum(a, Spec.Index(x))); s += x; } return s; }"));

        [Fact]
        public void ForEachArray_Count_Proved() => Assert.Empty(Errors("M",
            "static int M(int[] a) { Spec.Ensures<int>(r => r == a.Length); int n = 0; foreach (var x in a) { Spec.Invariant(n == Spec.Index(x)); n++; } return n; }"));

        [Fact]
        public void ForEachArray_Count_Refuted() => Assert.Equal(new[] { "CSV1002" }, Errors("M",
            "static int M(int[] a) { Spec.Ensures<int>(r => r == a.Length + 1); int n = 0; foreach (var x in a) { Spec.Invariant(n == Spec.Index(x)); n++; } return n; }"));

        [Fact]
        public void ForEachArray_InvariantNotOnEntry() => Assert.Equal(new[] { "CSV1005" }, Errors("M",
            "static void M(int[] a) { int n = 1; foreach (var x in a) { Spec.Invariant(n == Spec.Index(x)); n++; } }"));

        [Fact]
        public void ForEachArray_InvariantNotMaintained() => Assert.Equal(new[] { "CSV1006" }, Errors("M",
            "static void M(int[] a) { int n = 0; foreach (var x in a) { Spec.Invariant(n == Spec.Index(x)); n += 2; } }"));

        [Fact]
        public void ForEachArray_ElementIsTheCellAtTheIndex() =>
            Assert.Empty(Errors("M", "static void M(int[] a) { foreach (var x in a) { Spec.Assert(0 <= Spec.Index(x) && Spec.Index(x) < a.Length && x == a[Spec.Index(x)]); } }"));

        [Fact]
        public void ForEachArray_IndexIsNotAlwaysZero() => Assert.Equal(new[] { "CSV1004" }, Errors("M",
            "static void M(int[] a) { foreach (var x in a) { Spec.Assert(Spec.Index(x) == 0); } }"));

        [Fact]
        public void ForEachArray_WithoutInvariant_ForgetsWhatTheLoopChanges() => Assert.Equal(new[] { "CSV1004" }, Errors("M",
            "static void M(int[] a) { int n = 0; foreach (var x in a) { n++; } Spec.Assert(n == a.Length); }"));

        // the element is read when the iteration reaches it: a write ahead of the loop is seen
        private const string WriteAhead =
            "static void M(int[] a) { Spec.Requires(a.Length == 2); int n = 0; " +
            "foreach (var x in a) { Spec.Invariant(n == Spec.Index(x) && (n == 0 || a[1] == 9)); if (n == 1) Spec.Assert(x == EXPECTED); a[1] = 9; n++; } }";

        [Fact]
        public void ForEachArray_ReadsTheCurrentContents() => Assert.Empty(Errors("M", WriteAhead.Replace("EXPECTED", "9")));

        [Fact]
        public void ForEachArray_ReadsTheCurrentContents_Refuted() => Assert.Equal(new[] { "CSV1004" }, Errors("M", WriteAhead.Replace("EXPECTED", "0")));

        // the array is evaluated once: assigning the variable does not change what is enumerated
        private const string Reassigned =
            "static void M(int[] a) { Spec.Requires(a.Length == 2); int n = 0; " +
            "foreach (var x in a) { Spec.Invariant(n == Spec.Index(x)); a = new int[5]; n++; } Spec.Assert(n == EXPECTED); }";

        [Fact]
        public void ForEachArray_EvaluatesTheArrayOnce() => Assert.Empty(Errors("M", Reassigned.Replace("EXPECTED", "2")));

        [Fact]
        public void ForEachArray_EvaluatesTheArrayOnce_Refuted() => Assert.Equal(new[] { "CSV1004" }, Errors("M", Reassigned.Replace("EXPECTED", "5")));

        [Fact]
        public void ForEachArray_ReturnFromTheBody() => Assert.Empty(Errors("M",
            "static int M(int[] a) { Spec.Ensures<int>(r => r == -1 || (0 <= r && r < a.Length && a[r] == 7)); int i = 0; " +
            "foreach (var x in a) { Spec.Invariant(i == Spec.Index(x)); if (x == 7) return i; i++; } return -1; }"));

        [Fact]
        public void ForEachArray_ReturnFromTheBody_Refuted() => Assert.Equal(new[] { "CSV1002" }, Errors("M",
            "static int M(int[] a) { Spec.Ensures<int>(r => r == -1 || (0 <= r && r < a.Length && a[r] == 7)); int i = 0; " +
            "foreach (var x in a) { Spec.Invariant(i == Spec.Index(x)); if (x == 7) return i + 1; i++; } return -1; }"));

        [Fact]
        public void ForEachArray_ContinueGoesToTheNextElement() => Assert.Empty(Errors("M",
            "static int M(int[] a) { Spec.Ensures<int>(r => 0 <= r && r <= a.Length); int n = 0; " +
            "foreach (var x in a) { Spec.Invariant(0 <= n && n <= Spec.Index(x)); if (x == 0) continue; n++; } return n; }"));

        [Fact]
        public void ForEachArray_WritesThroughTheIndex() => Assert.Empty(Errors("M",
            "static void M(int[] a) { Spec.Ensures(Spec.Forall(0, a.Length, k => a[k] == 0)); int i = 0; " +
            "foreach (var x in a) { Spec.Invariant(i == Spec.Index(x) && Spec.Forall(0, i, k => a[k] == 0)); a[i] = 0; i++; } }"));

        [Fact]
        public void ForEachArray_NullArray_IsReported() => Assert.Equal(new[] { "CSV1013" }, Errors("M",
            "static void M(int[]? a) { foreach (var x in a) { } }"));

        [Fact]
        public void ForEachArray_WidenedElements() => Assert.Empty(Errors("M",
            "static void M(int[] a) { foreach (long v in a) { Spec.Assert(-2147483648L <= v && v <= 2147483647L); } }", overflow: true));

        [Fact]
        public void ForEachArray_ExceptionLeavesTheLoop() => Assert.Empty(Errors("M",
            "static int M(int[] a) { Spec.Ensures<int>(r => r == 0 || r == 1); " +
            "try { foreach (var x in a) { if (x < 0) throw new ArgumentException(); } return 0; } catch (ArgumentException) { return 1; } }"));

        [Fact]
        public void ForEachArray_InALemma_TerminatesByItself()
        {
            const string lemma = "[Lemma, Conditional(\"CSVERIFY_SPEC\")] static void L(int[] a) { Spec.Ensures(true); int n = 0; foreach (var x in a) { n++; } }";
            Assert.Empty(Errors("L", lemma));
        }

        // ---- foreach over anything else: the enumerator's calls -----------------------------------------------

        private const string List = "System.Collections.Generic.List<int>";

        [Fact]
        public void ForEachList_IsVerified() =>
            Assert.Empty(Errors("M", $"static int M({List} l) {{ int n = 0; foreach (var x in l) {{ Spec.Invariant(n >= 0); if (n < 100) n++; }} return n; }}"));

        [Fact]
        public void ForEachList_HavocsWhatTheLoopChanges() => Assert.Equal(new[] { "CSV1004" }, Errors("M",
            $"static void M({List} l) {{ int n = 0; foreach (var x in l) {{ n = 1; }} Spec.Assert(n == 0); }}"));

        [Fact]
        public void ForEachList_HasAnIndex_UnlessItsLoopChangesAList()
        {
            // over the list's model (CsVerify.Bcl, see StubTests): an index from 0 to Count
            Assert.Empty(Errors("M", "static void M(System.Collections.Generic.List<int> l) { foreach (var x in l) { Spec.Assert(0 <= Spec.Index(x) && Spec.Index(x) < l.Count); } }"));
            // a loop that may change a list goes through the enumerator: no index
            const string source = "static void M(System.Collections.Generic.List<int> l, System.Collections.Generic.List<int> o) { Spec.Requires(l != o); foreach (var x in l) { o.Add(x); Spec.Assert(Spec.Index(x) >= 0); } }";
            Assert.Equal(new[] { "CSV1004" }, Errors("M", source));
            Assert.Contains("CSV1900", Warnings("M", source));
        }

        [Fact]
        public void ForEachString_IsVerified() =>
            Assert.Empty(Errors("M", "static int M(string s) { int n = 0; foreach (var c in s) { Spec.Invariant(n >= 0); if (n < 100) n++; } return n; }"));

        [Fact]
        public void SpecIndex_IsGhost() =>
            Assert.Contains("CSV0010", Harness.Analyze("public static class C { static int M(int[] a) { foreach (var x in a) return Spec.Index(x); return 0; } }"));

        // ---- goto cycles: cut at the label ---------------------------------------------------------------------

        [Fact]
        public void Goto_WithInvariant_Proved() => Assert.Empty(Errors("M",
            "static int M(int x) { Spec.Requires(x < 3); Spec.Ensures<int>(r => r == 3); again: Spec.Invariant(x < 3); x++; if (x < 3) goto again; return x; }"));

        [Fact]
        public void Goto_WithoutInvariant_ForgetsWhatTheLoopChanges() => Assert.Equal(new[] { "CSV1004" }, Errors("M",
            "static void M() { int y = 0; again: y++; if (y < 10) goto again; Spec.Assert(y == 10); }"));

        [Fact]
        public void Goto_InvariantNotOnEntry() => Assert.Equal(new[] { "CSV1005" }, Errors("M",
            "static int M(int x) { Spec.Requires(x <= 3); again: Spec.Invariant(x <= 2); x++; if (x < 3) goto again; return x; }"));

        [Fact]
        public void Goto_InvariantNotMaintained() => Assert.Equal(new[] { "CSV1006" }, Errors("M",
            "static int M(int x) { Spec.Requires(x == 0); again: Spec.Invariant(x == 0); x++; if (x < 3) goto again; return x; }"));

        [Fact]
        public void Goto_MeasureMustDecrease() => Assert.Equal(new[] { "CSV1007" }, Errors("M",
            "static void M(int x) { again: Spec.Decreases(x); x++; if (x > 0) goto again; }"));

        [Fact]
        public void Goto_InALemma_NeedsAMeasure()
        {
            const string attrs = "[Lemma, Conditional(\"CSVERIFY_SPEC\")] ";
            Assert.Equal(new[] { "CSV1011" }, Errors("L", attrs + "static void L(int x) { again: x++; if (x < 3) goto again; }"));
            Assert.Empty(Errors("L", attrs + "static void L(int x) { Spec.Requires(x <= 3); again: Spec.Invariant(x <= 3); Spec.Decreases(3 - x); x++; if (x < 3) goto again; }"));
        }

        [Fact]
        public void Goto_BackToALoop_ChecksItsInvariant() => Assert.Equal(new[] { "CSV1006" }, Errors("M",
            "static void M() { int k = 0; int i = 0; again: while (i < 3) { Spec.Invariant(k == 0); i++; } k++; if (k < 2) goto again; }"));

        [Fact]
        public void Goto_BackToALoop_HavocsWhatTheGotoPathChanges() => Assert.Equal(new[] { "CSV1004" }, Errors("M",
            "static void M() { int k = 0; int i = 0; again: while (i < 3) { i++; } k++; if (k < 2) goto again; Spec.Assert(k == 1); }"));

        [Fact]
        public void Goto_WithATryInTheCycle_HavocsTheFinally() => Assert.Equal(new[] { "CSV1004" }, Errors("M",
            "static void M(int x) { int k = 0; again: try { x++; } finally { k++; } if (x < 3) goto again; Spec.Assert(k == 1); }"));

        [Fact]
        public void Goto_OutOfATryAndBack_HavocsTheFinally() => Assert.Equal(new[] { "CSV1004" }, Errors("M",
            "static void M(int x) { int k = 0; again: try { x++; if (x < 3) goto again; } finally { k++; } Spec.Assert(k == 1); }"));

        [Fact]
        public void Goto_InsideATry_KeepsWhatComesBefore() => Assert.Empty(Errors("M",
            "static void M(int x) { try { int n = 5; again: Spec.Invariant(true); x++; if (x < 3) goto again; Spec.Assert(n == 5); } " +
            "catch (InvalidOperationException) { } }"));

        [Fact]
        public void Goto_IntoALoop_IsRejected() => Assert.Contains("CSV1901", Errors("M",
            "static void M(int x, bool c) { if (c) goto inside; again: x++; inside: x++; if (x < 5) goto again; }"));

        // ---- erasure --------------------------------------------------------------------------------------------

        [Fact]
        public void Erased_ForEachAndGoto_ComputeWhatTheProofsSay()
        {
            const string source = "using System.Diagnostics; using CsVerify;\nnamespace Samples { public static class Loops {\n" + Sum +
                "public static int Total(int[] a) { Spec.Ensures<int>(r => r == Sum(a, a.Length)); int s = 0; " +
                "foreach (var x in a) { Spec.Invariant(s == Sum(a, Spec.Index(x))); s += x; } return s; }\n" +
                "public static int UpTo(int x) { Spec.Requires(x < 3); Spec.Ensures<int>(r => r == 3); again: Spec.Invariant(x < 3); x++; if (x < 3) goto again; return x; }\n" +
                "} }";
            Assert.DoesNotContain(Harness.Verify(source, overflow: false).Methods.SelectMany(m => m.Diagnostics), d => d.IsError);
            var erased = Erasure.Erase(new[] { ("Loops.cs", source) }, Array.Empty<string>(), Array.Empty<string>());
            Assert.True(erased.Success, string.Join("\n", erased.Errors));
            Assert.DoesNotContain(erased.Files.Where(f => f.OriginalPath == "Loops.cs"), f => f.Text.Contains("Spec."));
            var compilation = CSharpCompilation.Create("Erased",
                erased.Files.Select(f => CSharpSyntaxTree.ParseText(f.Text, new CSharpParseOptions(LanguageVersion.Latest), f.OutputName)),
                Engine.FrameworkReferences(), new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary));
            using var ms = new MemoryStream();
            var emit = compilation.Emit(ms);
            Assert.True(emit.Success, string.Join("\n", emit.Diagnostics));
            var loops = Assembly.Load(ms.ToArray()).GetType("Samples.Loops");
            Assert.Equal(1 + 2 + 3, loops.GetMethod("Total").Invoke(null, new object[] { new[] { 1, 2, 3 } }));
            Assert.Equal(3, loops.GetMethod("UpTo").Invoke(null, new object[] { -5 }));
        }
    }
}
