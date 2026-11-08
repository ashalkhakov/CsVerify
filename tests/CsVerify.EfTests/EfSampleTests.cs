using System.IO;
using System.Linq;
using CsVerify.Verifier;
using Xunit;

namespace CsVerify.Tests
{
    /// <summary>samples/EntityFramework: the good one verifies, and each planted bug of the buggy one is reported.</summary>
    public class EfSampleTests
    {
        private static VerificationResult VerifySamples(string dir)
        {
            var root = Path.Combine(Harness.RepoRoot(), "samples", "EntityFramework", dir);
            var sep = Path.DirectorySeparatorChar;
            var files = Directory.EnumerateFiles(root, "*.cs", SearchOption.AllDirectories)
                .Where(f => !f.Contains($"{sep}obj{sep}") && !f.Contains($"{sep}bin{sep}"));
            return Engine.VerifyFiles(files, EfHarness.Options());
        }

        [Fact]
        public void GoodSample_Verifies()
        {
            var r = VerifySamples("Good");
            Assert.True(r.Success, string.Join("\n", r.Diagnostics));
            Assert.Empty(r.Diagnostics);
        }

        [Fact]
        public void BuggySample_IsFlagged()
        {
            var r = VerifySamples("Buggy");
            Assert.Equal(new[] { "CSV1031" }, r.Errors("AnyLowStock"));
            Assert.Equal(new[] { "CSV1001" }, r.Errors("ByName"));
            Assert.Equal(new[] { "CSV1032" }, r.Errors("CountScarce"));
            Assert.Equal(new[] { "CSV1032" }, r.Errors("CountLabelled"));
            Assert.Equal(new[] { "CSV1033" }, r.Errors("Restock"));
            Assert.Equal(new[] { "CSV1033" }, r.Errors("AttachTwice"));
            Assert.Equal(new[] { "CSV1033" }, r.Errors("Retry"));
            Assert.Equal(new[] { "CSV1033" }, r.Errors("Zero"));
            Assert.Equal(new[] { "CSV1034" }, r.Errors("Bump"));
            Assert.Equal(new[] { "CSV1035" }, r.Errors("Split"));
            Assert.Equal(new[] { "CSV1035" }, r.Errors("Nested"));
            Assert.Equal(new[] { "CSV1036", "CSV1036" }, r.Errors("Both"));
            Assert.Equal(new[] { "CSV1036" }, r.Errors("Background"));
        }
    }
}
