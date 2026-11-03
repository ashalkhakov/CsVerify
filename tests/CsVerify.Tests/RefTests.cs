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
    /// <summary>Array cells passed by reference, ref locals, and mutable struct members.</summary>
    public class RefTests
    {
        private static string[] Errors(string method, string source, bool overflow = false) =>
            Harness.Verify("public static class C { " + source + " }", overflow).Errors(method);

        private const string Swap = "static void Swap(ref int x, ref int y) { Spec.Ensures(x == Spec.Old(y) && y == Spec.Old(x)); var t = x; x = y; y = t; } ";

        // ---- array cells passed by reference: copied in and out ------------------------------------------------

        [Fact]
        public void RefCell_Swap_Proved() => Assert.Empty(Errors("M", Swap +
            "static void M(int[] a, int i, int j) { Spec.Requires(0 <= i && i < a.Length && 0 <= j && j < a.Length && i != j); " +
            "var ai = a[i]; var aj = a[j]; Swap(ref a[i], ref a[j]); Spec.Assert(a[i] == aj && a[j] == ai); }"));

        [Fact]
        public void RefCell_Swap_Refuted() => Assert.Equal(new[] { "CSV1004" }, Errors("M", Swap +
            "static void M(int[] a) { Spec.Requires(a.Length > 1 && a[0] != a[1]); var a0 = a[0]; Swap(ref a[0], ref a[1]); Spec.Assert(a[0] == a0); }"));

        [Fact]
        public void RefCell_OtherCellsKept() => Assert.Empty(Errors("M", Swap +
            "static void M(int[] a) { Spec.Requires(a.Length > 2); a[2] = 9; Swap(ref a[0], ref a[1]); Spec.Assert(a[2] == 9); }"));

        [Fact]
        public void RefCell_SameCellTwice_IsReported() => Assert.Equal(new[] { "CSV1020" }, Errors("M", Swap +
            "static void M(int[] a, int i, int j) { Spec.Requires(0 <= i && i < a.Length && 0 <= j && j < a.Length); Swap(ref a[i], ref a[j]); }"));

        [Fact]
        public void RefVariable_Twice_IsReported() => Assert.Equal(new[] { "CSV1020" }, Errors("M", Swap + "static void M(int x) { Swap(ref x, ref x); }"));

        [Fact]
        public void RefCell_IndexChecked() => Assert.Equal(new[] { "CSV1003", "CSV1003" }, Errors("M", Swap + "static void M(int[] a) { Swap(ref a[0], ref a[1]); }"));

        [Fact]
        public void RefCell_CalleeTouchingArrays_IsRejected() => Assert.Equal(new[] { "CSV1901" }, Errors("M",
            "static void Peek(int[] b, ref int x) { Spec.Requires(b.Length > 0); x = b[0]; } " +
            "static void M(int[] a) { Spec.Requires(a.Length > 1); Peek(a, ref a[1]); }"));

        [Fact]
        public void RefCell_CalleeTouchingArraysIndirectly_IsRejected() => Assert.Equal(new[] { "CSV1901" }, Errors("M",
            "static int First(int[] b) { Spec.Requires(b.Length > 0); return b[0]; } " +
            "static void Peek(int[] b, ref int x) { Spec.Requires(b.Length > 0); x = First(b); } " +
            "static void M(int[] a) { Spec.Requires(a.Length > 1); Peek(a, ref a[1]); }"));

        [Fact]
        public void InCell_CalleeMayReadArrays() => Assert.Empty(Errors("M",
            "static int Add(int[] b, in int x) { Spec.Requires(b.Length > 0); Spec.Ensures(Spec.Result<int>() == b[0] + x); return b[0] + x; } " +
            "static void M(int[] a) { Spec.Requires(a.Length > 1 && a[0] == 1 && a[1] == 2); var r = Add(a, in a[1]); Spec.Assert(r == 3); }"));

        [Fact]
        public void InCell_CalleeWritingArrays_IsRejected() => Assert.Equal(new[] { "CSV1901" }, Errors("M",
            "static int Bump(int[] b, in int x) { Spec.Requires(b.Length > 0); b[0] = 5; return x; } " +
            "static void M(int[] a) { Spec.Requires(a.Length > 1); Bump(a, in a[0]); }"));

        [Fact]
        public void OutCell_LibraryCallee() => Assert.Empty(Errors("M",
            "static void M(int[] a, string s) { Spec.Requires(a.Length > 1); a[1] = 4; int.TryParse(s, out a[0]); Spec.Assert(a[1] == 4); }"));

        [Fact]
        public void OutCell_LibraryCallee_ValueUnknown() => Assert.Equal(new[] { "CSV1004" }, Errors("M",
            "static void M(int[] a, string s) { Spec.Requires(a.Length > 1); a[0] = 4; int.TryParse(s, out a[0]); Spec.Assert(a[0] == 4); }"));

        // ---- ref locals: a name for a variable or a cell ---------------------------------------------------------

        private const string RefCell =
            "static void M(int[] a) { Spec.Requires(a.Length > 2); ref int r = ref a[1]; r = 7; Spec.Assert(a[1] == 7); a[1] = 8; Spec.Assert(r == 8); " +
            "a = new int[1]; Spec.Assert(r == EXPECTED); }";

        [Fact]
        public void RefLocal_NamesItsCell() => Assert.Empty(Errors("M", RefCell.Replace("EXPECTED", "8")));

        [Fact]
        public void RefLocal_NamesItsCell_Refuted() => Assert.Equal(new[] { "CSV1004" }, Errors("M", RefCell.Replace("EXPECTED", "0")));

        [Fact]
        public void RefLocal_NamesItsVariable() => Assert.Empty(Errors("M",
            "static void M() { int x = 1; ref int r = ref x; r = 5; Spec.Assert(x == 5); x = 6; Spec.Assert(r == 6); }"));

        [Fact]
        public void RefLocal_NamesItsVariable_Refuted() => Assert.Equal(new[] { "CSV1004" }, Errors("M",
            "static void M() { int x = 1; int y = 1; ref int r = ref x; r = 5; Spec.Assert(y == 5); }"));

        [Fact]
        public void RefLocal_WrittenInALoop_HavocsItsVariable() => Assert.Equal(new[] { "CSV1004" }, Errors("M",
            "static void M() { int x = 0; ref int r = ref x; for (int i = 0; i < 3; i++) { r = 1; } Spec.Assert(x == 0); }"));

        [Fact]
        public void RefLocal_WrittenInALoop_WithInvariant() => Assert.Empty(Errors("M",
            "static void M() { int x = 0; ref int r = ref x; for (int i = 0; i < 3; i++) { Spec.Invariant(0 <= x && x <= 1); r = 1; } Spec.Assert(x <= 1); }"));

        [Fact]
        public void RefLocal_ReboundInALoop_IsRejected() => Assert.Contains("CSV1901", Errors("M",
            "static void M(int[] a, int[] b) { Spec.Requires(a.Length > 0 && b.Length > 0); ref int r = ref a[0]; for (int i = 0; i < 3; i++) { r = ref b[0]; } r = 1; }"));

        [Fact]
        public void RefLocal_PassedByRef_SameCell_IsReported() => Assert.Equal(new[] { "CSV1020" }, Errors("M", Swap +
            "static void M(int[] a) { Spec.Requires(a.Length > 0); ref int r = ref a[0]; ref int s = ref a[0]; Swap(ref r, ref s); }"));

        [Fact]
        public void RefLocal_ToAField_IsRejected() => Assert.Contains("CSV1901", Harness.Verify(
            "public sealed class Cell { public int V; } public static class C { static void M(Cell c) { ref int r = ref c.V; r = 1; } }").Errors("M"));

        // ---- mutable struct members: values updated in place ---------------------------------------------------

        private const string Pt = "public struct Pt { public int X; public int Y; public int Z { get; set; } " +
            "public Pt(int x, int y) { Spec.Ensures(X == x && Y == y && Z == 0); X = x; Y = y; Z = 0; } } ";

        private static string[] StructErrors(string method, string source) =>
            Harness.Verify(Pt + "public sealed class Box { public Pt P; } public static class C { " + source + " }", overflow: false).Errors(method);

        [Fact]
        public void Struct_MemberWrite_KeepsTheOthers() => Assert.Empty(StructErrors("M",
            "static void M() { var p = new Pt(1, 2); p.X = 5; Spec.Assert(p.X == 5 && p.Y == 2 && p.Z == 0); p.Z = 9; Spec.Assert(p.X == 5 && p.Z == 9); }"));

        [Fact]
        public void Struct_MemberWrite_Refuted() => Assert.Equal(new[] { "CSV1004" }, StructErrors("M",
            "static void M() { var p = new Pt(1, 2); p.X = 5; Spec.Assert(p.Y == 5); }"));

        [Fact]
        public void Struct_IsCopied() => Assert.Empty(StructErrors("M",
            "static void M() { var p = new Pt(1, 2); var q = p; q.X = 7; Spec.Assert(p.X == 1 && q.X == 7); }"));

        [Fact]
        public void Struct_IsCopied_Refuted() => Assert.Equal(new[] { "CSV1004" }, StructErrors("M",
            "static void M() { var p = new Pt(1, 2); var q = p; q.X = 7; Spec.Assert(p.X == 7); }"));

        [Fact]
        public void Struct_ByRefParameter() => Assert.Empty(StructErrors("M",
            "static void SetX(ref Pt p) { Spec.Ensures(p.X == 3 && p.Y == Spec.Old(p.Y)); p.X = 3; } " +
            "static void M() { var p = new Pt(1, 2); SetX(ref p); Spec.Assert(p.X == 3 && p.Y == 2); }"));

        [Fact]
        public void Struct_InAnArrayCell() => Assert.Empty(StructErrors("M",
            "static void M(Pt[] a) { Spec.Requires(a.Length > 1); var y = a[1].X; a[0].X = 4; Spec.Assert(a[0].X == 4 && a[1].X == y); }"));

        [Fact]
        public void Struct_InAnArrayCell_IsAHeapWriteForCallers() => Assert.Equal(new[] { "CSV1004" }, StructErrors("M",
            "static void Set(Pt[] a) { Spec.Requires(a.Length > 0); a[0].X = 4; } " +
            "static void M(Pt[] a) { Spec.Requires(a.Length > 1); a[1].Y = 1; Set(a); Spec.Assert(a[1].Y == 1); }"));

        [Fact]
        public void Struct_ObjectInitializer() => Assert.Empty(StructErrors("M",
            "static void M() { var p = new Pt { X = 3, Y = 4 }; Spec.Assert(p.X == 3 && p.Y == 4); }"));

        [Fact]
        public void Struct_WrittenInALoop() => Assert.Empty(StructErrors("M",
            "static void M() { var p = new Pt(0, 0); for (int i = 0; i < 3; i++) { Spec.Invariant(p.Y == 0); p.X = i; } Spec.Assert(p.Y == 0); }"));

        [Fact]
        public void Struct_WrittenInALoop_IsHavocked() => Assert.Equal(new[] { "CSV1004" }, StructErrors("M",
            "static void M() { var p = new Pt(0, 0); for (int i = 0; i < 3; i++) { p.X = i; } Spec.Assert(p.X == 0); }"));

        [Fact]
        public void Struct_InAClassField_IsRejected() => Assert.Equal(new[] { "CSV1901" }, StructErrors("M", "static void M(Box b) { b.P.X = 3; }"));

        [Fact]
        public void Struct_MethodWritingThis_IsRejected() => Assert.Equal(new[] { "CSV1901" },
            Harness.Verify("public struct S { public int X; public void Move(int d) { X = d; } }", overflow: false).Errors("Move"));

        // ---- erasure ---------------------------------------------------------------------------------------------

        [Fact]
        public void Erased_RefsAndStructs_Run()
        {
            const string source = "using System.Diagnostics; using CsVerify;\nnamespace Samples {\n" + Pt + "public static class Refs {\n" + Swap +
                "public static int Demo() { Spec.Ensures<int>(r => r == 2 * 100 + 1 * 10 + 7); var a = new[] { 1, 2 }; Swap(ref a[0], ref a[1]); " +
                "ref int r = ref a[1]; r = r * 10; var p = new Pt(3, 4); p.X = 7; return a[0] * 100 + a[1] + p.X; }\n} }";
            Assert.DoesNotContain(Harness.Verify(source, overflow: false).Methods.SelectMany(m => m.Diagnostics), d => d.IsError);
            var erased = Erasure.Erase(new[] { ("Refs.cs", source) }, Array.Empty<string>(), Array.Empty<string>());
            Assert.True(erased.Success, string.Join("\n", erased.Errors));
            var compilation = CSharpCompilation.Create("Erased",
                erased.Files.Select(f => CSharpSyntaxTree.ParseText(f.Text, new CSharpParseOptions(LanguageVersion.Latest), f.OutputName)),
                Engine.FrameworkReferences(), new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary));
            using var ms = new MemoryStream();
            var emit = compilation.Emit(ms);
            Assert.True(emit.Success, string.Join("\n", emit.Diagnostics));
            Assert.Equal(2 * 100 + 1 * 10 + 7, Assembly.Load(ms.ToArray()).GetType("Samples.Refs").GetMethod("Demo").Invoke(null, null));
        }
    }
}
