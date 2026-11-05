using CsVerify.Verifier;
using Xunit;

namespace CsVerify.Tests
{
    /// <summary>
    /// Failures the program did not write: a composite format naming an argument that is not there (FormatException),
    /// and a switch expression no arm of which matches (SwitchExpressionException).
    /// </summary>
    public class FormatAndSwitchTests
    {
        private const string Types = "public enum Color { Red, Green, Blue } ";

        private static string[] Errors(string method, string source) =>
            Harness.Verify(Types + "public static class C { " + source + " }", overflow: false).Errors(method);

        // ---- format strings -------------------------------------------------------------------------------------

        [Theory]
        [InlineData("plain", 0)]
        [InlineData("{0}", 1)]
        [InlineData("{1} {0}", 2)]
        [InlineData("{0,5} {1,-3:x2} {2:yyyy-MM-dd}", 3)]
        [InlineData("{{0}} {0}", 1)]
        [InlineData("}}{{", 0)]
        [InlineData("{0 , 4 }", 1)]
        [InlineData("{", -1)]
        [InlineData("}", -1)]
        [InlineData("{a}", -1)]
        [InlineData("{0", -1)]
        [InlineData("{0:x{y}", -1)]
        [InlineData("{,3}", -1)]
        public void FormatArity_AsDotNetParsesIt(string format, int arity) => Assert.Equal(arity, FormatStrings.Arity(format));

        [Fact]
        public void Format_TooFewArguments_IsReported() => Assert.Equal(new[] { "CSV1001" }, Errors("M",
            "static string M(int a) => string.Format(\"{0} and {1}\", a);"));

        [Fact]
        public void Format_EnoughArguments_Verifies() => Assert.Empty(Errors("M",
            "static string M(int a, int b) => string.Format(\"{1} and {0}, {0}\", a, b);"));

        [Fact]
        public void Format_FourArguments_AParamsSpan_Verifies() => Assert.Empty(Errors("M",
            "static string M(int a) => string.Format(\"{0}{1}{2}{3}\", a, a, a, a);"));

        [Fact]
        public void Format_NotWellFormed_IsReported() => Assert.Equal(new[] { "CSV1001" }, Errors("M",
            "static string M(int a) => string.Format(\"{0} {\", a);"));

        [Fact]
        public void Format_AConstant_IsChecked() => Assert.Equal(new[] { "CSV1001" }, Errors("M",
            "const string Pair = \"{0}/{1}\"; static string M(int a) => string.Format(Pair, a);"));

        [Fact]
        public void Format_ConsoleAndStringBuilderAndTextWriter_AreChecked()
        {
            Assert.Equal(new[] { "CSV1001" }, Errors("M1", "static void M1(int a) => System.Console.WriteLine(\"{0} {1}\", a);"));
            Assert.Equal(new[] { "CSV1001" }, Errors("M2", "static void M2(System.Text.StringBuilder sb, int a) => sb.AppendFormat(\"{1}\", a);"));
            Assert.Equal(new[] { "CSV1001" }, Errors("M3", "static void M3(System.IO.TextWriter w, int a) => w.Write(\"{2}\", a, a);"));
        }

        [Fact]
        public void Format_WriteLineOfAString_IsNotAFormat() => Assert.Empty(Errors("M",
            "static void M() => System.Console.WriteLine(\"{not a format}\");"));

        [Fact]
        public void Format_OnlyOnPathsThatReachIt() => Assert.Empty(Errors("M",
            "static string M(int a) { if (a > 0 && a < 0) return string.Format(\"{0} {1}\", a); return \"\"; }"));

        // ---- switch expressions ---------------------------------------------------------------------------------

        [Fact]
        public void Switch_MissingAMember_IsReported() => Assert.Equal(new[] { "CSV1022" }, Errors("M",
            "static int M(Color c) => c switch { Color.Red => 1, Color.Green => 2 };"));

        [Fact]
        public void Switch_OverAnEnum_MayGetAnUnnamedValue() => Assert.Equal(new[] { "CSV1022" }, Errors("M",
            "static int M(Color c) => c switch { Color.Red => 1, Color.Green => 2, Color.Blue => 3 };"));

        [Fact]
        public void Switch_WithADiscard_Verifies() => Assert.Empty(Errors("M",
            "static int M(Color c) => c switch { Color.Red => 1, _ => 2 };"));

        [Fact]
        public void Switch_ThatCoversWhatItCanGet_Verifies() => Assert.Empty(Errors("M",
            "static int M(int x) { if (x == 0) return 0; return x switch { > 0 => 1, < 0 => -1 }; }"));

        [Fact]
        public void Switch_CoveredByThePrecondition_Verifies() => Assert.Empty(Errors("M",
            "static int M(int x) { Spec.Requires(x != 0); return x switch { > 0 => 1, < 0 => -1 }; }"));

        [Fact]
        public void Switch_OverABool_Verifies() => Assert.Empty(Errors("M",
            "static int M(bool b) => b switch { true => 1, false => 0 };"));
    }
}
