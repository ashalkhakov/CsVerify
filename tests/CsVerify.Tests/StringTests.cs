using System;
using System.IO;
using System.Linq;
using CsVerify.Verifier;
using Xunit;

namespace CsVerify.Tests
{
    /// <summary>Strings' characters: what can be proved of them, and what must not be.</summary>
    public class StringTests
    {
        private const string Rejected = "CSV1004";

        private static string[] Errors(string body) =>
            Harness.Verify("using CsVerify; using System; public static class C { " + body + " }", overflow: false).Errors("M");

        [Theory]
        [InlineData("var s = \"abc\"; Spec.Assert(s[1] == 'b' && s.Length == 3);")]
        [InlineData("Spec.Assert(\"a\" + \"b\" == \"ab\");")]
        public void Literals_AreKnown(string body) => Assert.Empty(Errors($"static void M() {{ {body} }}"));

        [Theory]
        [InlineData("var s = \"abc\"; Spec.Assert(s[1] == 'c');")]
        [InlineData("Spec.Assert(\"a\" + \"b\" == \"ba\");")]
        public void Literals_WrongClaims_AreRejected(string body) => Assert.Equal(new[] { Rejected }, Errors($"static void M() {{ {body} }}"));

        [Fact]
        public void Concat_HasBothStrings_InOrder() => Assert.Empty(Errors(
            "static void M(string a, string b) { Spec.Requires(a.Length > 0 && b.Length > 0); var c = a + b; " +
            "Spec.Assert(c[0] == a[0]); Spec.Assert(c[a.Length] == b[0]); }"));

        [Fact]
        public void Concat_WrongOrder_IsRejected() => Assert.Equal(new[] { Rejected }, Errors(
            "static void M(string a, string b) { Spec.Requires(a.Length > 0 && b.Length > 0); var c = a + b; Spec.Assert(c[0] == b[0]); }"));

        [Fact]
        public void Concat_IsAssociative() => Assert.Empty(Errors(
            "static void M(string a, string b, string c) { Spec.Assert((a + b) + c == a + (b + c)); }"));

        [Fact]
        public void Concat_IsNotCommutative() => Assert.Equal(new[] { Rejected }, Errors(
            "static void M(string a, string b) { Spec.Assert(a + b == b + a); }"));

        [Fact]
        public void Concat_NullIsEmpty() => Assert.Empty(Errors(
            "static void M(string? a, string b) { Spec.Requires(a == null); Spec.Assert(a + b == b); }"));

        [Fact]
        public void Substring_PiecesRebuildTheString() => Assert.Empty(Errors(
            "static void M(string s, int n) { Spec.Requires(0 <= n && n <= s.Length); Spec.Assert(s.Substring(0, n) + s.Substring(n) == s); }"));

        [Fact]
        public void Substring_PiecesSwapped_IsRejected() => Assert.Equal(new[] { Rejected }, Errors(
            "static void M(string s, int n) { Spec.Requires(0 <= n && n <= s.Length); Spec.Assert(s.Substring(n) + s.Substring(0, n) == s); }"));

        [Fact]
        public void SameCharacters_SameString() => Assert.Empty(Errors(
            "static void M(string a, string b) { Spec.Requires(a.Length == b.Length && Spec.Forall(0, a.Length, i => a[i] == b[i])); Spec.Assert(a == b); }"));

        [Fact]
        public void SameCharacters_OfAPrefix_AreNotEnough() => Assert.Equal(new[] { Rejected }, Errors(
            "static void M(string a, string b) { Spec.Requires(a.Length == b.Length && a.Length > 0 && Spec.Forall(1, a.Length, i => a[i] == b[i])); Spec.Assert(a == b); }"));

        [Fact]
        public void Null_IsNotTheEmptyString() => Assert.Equal(new[] { Rejected }, Errors(
            "static void M(string? a) { Spec.Requires(a == null); string e = \"\"; Spec.Assert(a == e); }"));

        [Fact]
        public void Arrays_WithTheSameContents_AreStillDifferentObjects() => Assert.Equal(new[] { Rejected }, Errors(
            "static void M(int[] a, int[] b) { Spec.Requires(a.Length == b.Length && Spec.Forall(0, a.Length, i => a[i] == b[i])); Spec.Assert(a == b); }"));

        [Fact]
        public void IndexOf_FoundOrNot() => Assert.Empty(Errors(
            "static void M(string s) { var k = s.IndexOf('x'); if (k >= 0) Spec.Assert(s[k] == 'x'); else if (s.Length > 0) Spec.Assert(s[0] != 'x'); }"));

        [Fact]
        public void StartsWith_Ordinal_SaysWhatTheCharactersAre() => Assert.Empty(Errors(
            "static void M(string s) { if (s.StartsWith(\"ab\", StringComparison.Ordinal)) Spec.Assert(s[1] == 'b'); }"));

        /// <summary>"a".StartsWith("a­") is true under the current culture: the prefix need not even fit.</summary>
        [Fact]
        public void StartsWith_CultureSensitive_PromisesNothing() => Assert.Equal(new[] { Rejected }, Errors(
            "static void M(string s, string v) { if (s.StartsWith(v)) Spec.Assert(v.Length <= s.Length); }"));

        [Fact]
        public void Loop_ProvesWhatItChecked() => Assert.Empty(Errors(
            "static bool M(string s) { Spec.Ensures<bool>(r => !r || Spec.Forall(0, s.Length, j => '0' <= s[j] && s[j] <= '9')); " +
            "for (int i = 0; i < s.Length; i++) { Spec.Invariant(0 <= i && i <= s.Length && Spec.Forall(0, i, j => '0' <= s[j] && s[j] <= '9')); " +
            "if (s[i] < '0' || s[i] > '9') return false; } return true; }"));

        [Fact]
        public void Characters_AreCodeUnits() => Assert.Empty(Harness.Verify(
            "using CsVerify; public static class C { static void M(string s, int i) { Spec.Requires(0 <= i && i < s.Length); Spec.Assert(0 <= s[i] && s[i] <= 65535); } }").Errors("M"));

        // ---- foreach ----------------------------------------------------------------------------------------------

        [Fact]
        public void Foreach_ReadsTheCharacters() => Assert.Empty(Errors(
            "static bool M(string s) { Spec.Ensures<bool>(r => !r || Spec.Forall(0, s.Length, j => '0' <= s[j] && s[j] <= '9')); " +
            "foreach (char c in s) { Spec.Invariant(Spec.Forall(0, Spec.Index(c), j => '0' <= s[j] && s[j] <= '9')); " +
            "if (c < '0' || c > '9') return false; } return true; }"));

        [Fact]
        public void Foreach_TheElementIsTheCharacterAtTheIndex() => Assert.Empty(Errors(
            "static void M(string s) { foreach (char c in s) { Spec.Assert(c == s[Spec.Index(c)]); } }"));

        [Fact]
        public void Foreach_TheWrongCharacter_IsRejected() => Assert.Equal(new[] { Rejected }, Errors(
            "static void M(string s) { Spec.Requires(s.Length > 1); foreach (char c in s) { Spec.Assert(c == s[0]); } }"));

        [Fact]
        public void Foreach_OverALiteral_IsKnown() => Assert.Empty(Errors(
            "static void M() { foreach (char c in \"aa\") { Spec.Assert(c == 'a'); } }"));

        [Fact]
        public void Foreach_ToInt_KeepsTheCode() => Assert.Empty(Errors(
            "static void M() { foreach (int c in \"a\") { Spec.Assert(c == 97); } }"));

        [Fact]
        public void Foreach_CountsWithoutAMeasure() => Assert.Empty(Errors(
            "static int M(string s) { Spec.Ensures<int>(r => r == s.Length); int n = 0; " +
            "foreach (char c in s) { Spec.Invariant(n == Spec.Index(c)); n = n + 1; } return n; }"));

        [Fact]
        public void Foreach_OverNull_IsReported() => Assert.NotEmpty(Errors(
            "static void M(string? s) { foreach (char c in s!) { } }"));

        // (the same object is the same string; equal strings may be different objects)
        [Theory]
        [InlineData("static bool M(string a, string b) { Spec.Ensures((bool r) => !r || a == b); return (object)a == (object)b; }", true)]
        [InlineData("static bool M(string a, string b) { Spec.Ensures((bool r) => !r || a == b); return ReferenceEquals(a, b); }", true)]
        [InlineData("static bool M(string a, string b) { Spec.Ensures((bool r) => r == (a == b)); return ReferenceEquals(a, b); }", false)]
        public void ComparedAsObjects(string body, bool verifies) => Assert.Equal(verifies, Errors(body).Length == 0);
    }
}
