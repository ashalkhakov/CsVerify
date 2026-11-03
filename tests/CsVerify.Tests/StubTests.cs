using System;
using System.Linq;
using CsVerify.Verifier;
using Xunit;

namespace CsVerify.Tests
{
    /// <summary>
    /// Contracts for code without sources: [ContractsFor] stubs and [Model] functions, the user's and CsVerify.Bcl's.
    /// Stub contracts are trusted: assumed at calls, counted, never proved.
    /// </summary>
    public class StubTests
    {
        private const string Usings = "using System.Collections.Generic; using CsVerify.Bcl; ";

        private static VerificationResult Verify(string source) => Harness.Verify(Usings + source);

        private static string[] Errors(string method, string body) => Verify("public static class C { " + body + " }").Errors(method);

        [Fact]
        public void Lists_FollowTheirModel()
        {
            Assert.Empty(Errors("M", "static void M() { var l = new List<int>(); l.Add(3); l.Add(4); Spec.Assert(l.Count == 2 && l[0] == 3 && l[1] == 4); l[0] = 7; Spec.Assert(l[0] == 7 && l[1] == 4); }"));
            Assert.Empty(Errors("M", "static int M(List<int> l) { Spec.Requires(l.Count > 0); return l[0]; }"));
            Assert.Empty(Errors("M", "static void M(List<int> l, int x) { Spec.Modifies(ObjSet.Of(l)); Spec.Ensures(l.Count == Spec.Old(l.Count) + 1 && l[l.Count - 1] == x); l.Add(x); }"));
            // the model in specifications, and through a loop
            Assert.Empty(Errors("M", "static void M(List<int> l) { Spec.Modifies(ObjSet.Of(l)); Spec.Requires(l.Size() == 0); Spec.Ensures(l.Items()[0].Value == 5); l.Add(5); }"));
            Assert.Empty(Errors("M", "static void M(List<int> l, int n) { Spec.Requires(0 <= n && n < 1000 && l.Count == 0); Spec.Modifies(ObjSet.Of(l)); Spec.Ensures(l.Count == n); " +
                                     "for (int i = 0; i < n; i++) { Spec.Invariant(0 <= i && i <= n && l.Count == i); l.Add(i); } }"));
            // refuted: an index that may be out of range, a wrong claim about the contents
            Assert.Equal(new[] { "CSV1001" }, Errors("M", "static int M(List<int> l) => l[0];"));
            Assert.Equal(new[] { "CSV1004" }, Errors("M", "static void M(List<int> l) { Spec.Modifies(ObjSet.Of(l)); l.Add(1); Spec.Assert(l[0] == 1); }"));
            Assert.Equal(new[] { "CSV1001" }, Errors("M", "static void M(List<int> l) { Spec.Modifies(ObjSet.Of(l)); l.RemoveAt(0); }"));
        }

        [Fact]
        public void StubFrames_KeepOtherObjects()
        {
            // List.Add changes its own list only (Spec.Modifies in its stub); a new list changes no other
            Assert.Empty(Errors("M", "static void M(List<int> a, List<int> b) { Spec.Requires(a != b && a.Count == 1); Spec.Modifies(ObjSet.Of(b)); b.Add(5); Spec.Assert(a.Count == 1); }"));
            Assert.Empty(Errors("M", "static void M(List<int> a) { Spec.Requires(a.Count == 1); var b = new List<int>(); Spec.Assert(a.Count == 1 && b.Count == 0); }"));
            Assert.Equal(new[] { "CSV1004" }, Errors("M", "static void M(List<int> a, List<int> b) { Spec.Requires(a.Count == 1); Spec.Modifies(ObjSet.Of(b)); b.Add(5); Spec.Assert(a.Count == 1); }"));
            // a stubbed call is checked against the caller's frame
            Assert.Equal(new[] { "CSV1017" }, Errors("M", "static void M(List<int> a, List<int> b) { Spec.Modifies(ObjSet.Of(a)); b.Add(5); }"));
            // a library method without a stub that is handed the list may change it
            Assert.Equal(new[] { "CSV1004" }, Errors("M", "static void M(List<int> a) { Spec.Requires(a.Count == 1); a.Reverse(); Spec.Assert(a.Count == 1); }"));
        }

        [Fact]
        public void Dictionaries_StringsAndParsing()
        {
            Assert.Empty(Errors("M", "static int M(int x) { Spec.Requires(x < 100); var d = new Dictionary<int, int>(); d[x] = 10; d[x + 1] = 20; Spec.Assert(d.ContainsKey(x) && d.Count == 2 && d[x + 1] == 20); " +
                                     "if (d.TryGetValue(x, out var v)) { Spec.Assert(v == 10); return v; } Spec.Assert(false); return 0; }"));
            Assert.Equal(new[] { "CSV1001" }, Errors("M", "static int M(Dictionary<int, int> d) => d[1];"));
            Assert.Empty(Errors("M", "static int M(Dictionary<int, int> d) => d.ContainsKey(1) ? d[1] : 0;"));
            Assert.Empty(Errors("M", "static string M(string s) { Spec.Requires(s.Length >= 3); var t = s.Substring(1, 2); Spec.Assert(t.Length == 2); return t; }"));
            Assert.Equal(new[] { "CSV1001" }, Errors("M", "static string M(string s) => s.Substring(1, 2);"));
            Assert.Empty(Errors("M", "static int M(string s) { if (string.IsNullOrEmpty(s)) return 0; return s[0]; }"));
            Assert.Empty(Errors("M", "static int M(string s) { if (int.TryParse(s, out int n)) { Spec.Assert(s.Length > 0); return n; } Spec.Assert(n == 0); return n; }"));
            Assert.Equal(new[] { "CSV1001" }, Errors("M", "static int M(int x) => System.Math.Clamp(x, 1, 0);"));
            Assert.Empty(Errors("M", "static void M(int x) { Spec.Assert(System.Math.Clamp(x, 0, 9) <= 9); }"));
        }

        private const string Builder = @"
[ContractsFor(typeof(System.Text.StringBuilder))]
public static class BuilderContracts
{
    [Model] public static int Len(System.Text.StringBuilder b) => throw null!;
    [Model] public static char At(System.Text.StringBuilder b, int i) => throw null!;
    public static System.Text.StringBuilder @new() { Spec.Ensures<System.Text.StringBuilder>(r => Len(r) == 0); throw null!; }
    [Pure] public static int get_Length(System.Text.StringBuilder @this) { Spec.Ensures<int>(r => r == Len(@this)); throw null!; }
    [Pure] public static char get_Chars(System.Text.StringBuilder @this, int index)
    {
        Spec.Requires(0 <= index && index < Len(@this));
        Spec.Ensures<char>(r => r == At(@this, index));
        throw null!;
    }
    public static System.Text.StringBuilder Append(System.Text.StringBuilder @this, char value)
    {
        Spec.Modifies(ObjSet.Of(@this));
        Spec.Ensures<System.Text.StringBuilder>(r => r == @this && Len(@this) == Spec.Old(Len(@this)) + 1 && At(@this, Spec.Old(Len(@this))) == value);
        Spec.Ensures(Spec.Forall(0, Spec.Old(Len(@this)), i => At(@this, i) == Spec.Old(At(@this, i))));
        throw null!;
    }
}
";

        [Fact]
        public void UserStubs_SpecifyALibraryType()
        {
            // a model with a key (the character at each index), a constructor, an indexer, a method returning its receiver
            var r = Verify(Builder + "public static class C { static char M() { var b = new System.Text.StringBuilder(); b.Append('a').Append('b'); Spec.Assert(b.Length == 2); return b[1]; } " +
                                     "static char N() { var b = new System.Text.StringBuilder(); b.Append('a'); b.Append('b'); Spec.Assert(b[0] == 'a' && b[1] == 'b'); return b[0]; } " +
                                     "static char Bad(System.Text.StringBuilder b) => b[0]; }");
            Assert.Empty(r.Errors("M"));
            Assert.Empty(r.Errors("N"));
            Assert.Equal(new[] { "CSV1001" }, r.Errors("Bad"));
            Assert.Contains("System.Text.StringBuilder.Append(char)", r.Assumptions);
            Assert.Contains("System.Text.StringBuilder.this[int].get", r.Assumptions);
        }

        [Fact]
        public void StubContracts_AreTrusted_AndCounted()
        {
            // a wrong stub makes a false claim provable: its contract is assumed, never checked against the library
            const string wrong = "[ContractsFor(typeof(System.Math))] public static class WrongMath { [Pure] public static long BigMul(int a, int b) { Spec.Ensures<long>(r => r == 0); throw null!; } } ";
            var r = Verify(wrong + "public static class C { static void M() { Spec.Assert(System.Math.BigMul(2, 3) == 0); } static void N() { } }");
            Assert.Empty(r.Errors("M"));
            Assert.Equal(new[] { "System.Math.BigMul(int, int)" }, r.Assumptions.ToArray());
            Assert.Contains("System.Math.BigMul(int, int)", r["M"].Assumptions);
            Assert.Empty(r["N"].Assumptions);
            // the user's stub wins over CsVerify.Bcl's for the same member
            var mine = Verify("[ContractsFor(typeof(System.Math))] public static class MyMath { [Pure] public static int Sign(int value) { Spec.Ensures<int>(r => r == 7); throw null!; } } " +
                              "public static class C { static void M() { Spec.Assert(System.Math.Sign(-1) == 7); } }");
            Assert.Empty(mine.Errors("M"));
            // the stub's body is never verified
            Assert.Null(r["WrongMath.BigMul"]);
        }

        [Fact]
        public void IllFormedStubs_AreReported()
        {
            var r = Verify("[ContractsFor(typeof(System.Math))] public static class Typo { [Pure] public static int Maxx(int a, int b) { throw null!; } } " +
                           "[ContractsFor(typeof(List<>))] public static class NoReceiver<T> { public static void Add(T item) { throw null!; } } " +
                           "public static class Models2 { [Model] public static int Bad(int x) => 0; } public static class C { static void M() { } }");
            Assert.False(r.Success);
            Assert.Equal(3, r.AnalyzerErrors.Count(d => d.Id == "CSV1021"));
            Assert.Contains(r.AnalyzerErrors, d => d.Message.Contains("'Maxx' matches no member of System.Math"));
        }

        [Fact]
        public void Analyzer_AcceptsPureStubbedMembers_InSpecifications()
        {
            // in a normal build the BCL stubs come from the CsVerify assembly's metadata
            Assert.Empty(Harness.Analyze("public static class C { static void M(string s) { Spec.Requires(!string.IsNullOrEmpty(s)); } }"));
            Assert.Equal(new[] { "CSV0013" }, Harness.Analyze("public static class C { static void M(string s) { Spec.Requires(s.Normalize() == s); } }"));
        }

        [Fact]
        public void Erasure_RemovesStubsAndModels()
        {
            var source = Usings + "using System; using CsVerify; " + Builder +
                         "public static class C { public static int M(List<int> l) { Spec.Requires(l.Size() > 0); Spec.Ensures<int>(r => r == l.Items()[0].Value); return l[0]; } }";
            var erased = Erasure.Erase(new[] { ("Test.cs", source) }, Array.Empty<string>(), Array.Empty<string>());
            Assert.True(erased.Success, string.Join("\n", erased.Errors));
            var program = erased.Files.Single(f => f.OriginalPath == "Test.cs").Text;
            Assert.DoesNotContain("BuilderContracts", program);
            Assert.DoesNotContain("Len(", program);
            Assert.Contains("return l[0];", program);
            // and the runtime keeps no stubs either
            Assert.DoesNotContain(erased.Files.Where(f => f.OutputName.StartsWith(Erasure.RuntimeFolder)), f => f.Text.Contains("public static class ListContracts"));
        }
    }
}
