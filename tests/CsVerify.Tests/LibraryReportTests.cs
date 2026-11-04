using System.Linq;
using CsVerify.Verifier;
using Xunit;

namespace CsVerify.Tests
{
    /// <summary>The library report charges each failed obligation to where its unknown values come from.</summary>
    public class LibraryReportTests
    {
        private const string Program = @"
public static class P
{
    // a library member without a contract: its result is unknown
    public static int Library(string s, int[] a)
    {
        int i = s.IndexOf(""x"", StringComparison.Ordinal);
        return a[i];
    }

    // a method of the program without postconditions: callers know only its type
    private static int Next(int i) => i / 2;
    public static int Source(int[] a)
    {
        Spec.Requires(a.Length > 1);
        return a[Next(0)];
    }

    // a loop without invariants: what it changes is unknown at its head
    public static int Loop(int[] a)
    {
        int s = 0;
        for (int i = 0; i < a.Length; i++) s = a[i];
        return s;
    }

    // the code's own values: none of these
    public static int Own(int[] a) => a[0];

    // a library call with no effect on any failure
    public static int Quiet(string s) => s.GetHashCode();
}";

        [Fact]
        public void Failures_AreChargedToWhatMadeTheirValuesUnknown()
        {
            var r = Harness.Verify(Program);
            string Cause(string method) => string.Join(" ", r[method].Diagnostics.Where(d => d.IsError).SelectMany(d => d.Causes));
            Assert.Equal("library string.IndexOf(string, System.StringComparison)", Cause("Library"));
            Assert.Equal("source P.Next(int)", Cause("Source"));
            Assert.Equal("a loop without invariants", Cause("Loop"));
            Assert.Equal("", Cause("Own"));
            Assert.Contains(r["Own"].Diagnostics, d => d.Id == "CSV1003");

            var report = LibraryReport.Render(r);
            Assert.Contains("6 methods: 2 verified, 4 with failed obligations, 0 not verified", report.Replace("\r", ""));
            Assert.Matches(@"\n\s+1\s+1\s+string\.IndexOf\(string, System\.StringComparison\)\r?\n", report);
            Assert.Matches(@"\n\s+0\s+1\s+string\.GetHashCode\(\)\r?\n", report);
            Assert.Matches(@"\n\s+1\s+P\.Next\(int\)\r?\n", report);
            Assert.Matches(@"\n\s+1\s+a loop without invariants\r?\n", report);
            Assert.Matches(@"\n\s+1\s+none of these \(the code's own values\)\r?\n", report);
            Assert.Matches(@"\n\s+4\s+CSV1003\s+index out of range\r?\n", report);
        }

        [Fact]
        public void Results_OfSeparatePrograms_Combine()
        {
            var a = Harness.Verify("public static class A { public static int F(int[] a) => a[0]; }");
            var b = Harness.Verify("public static class B { public static int G(int x) => x; }");
            var both = VerificationResult.Combine(new[] { a, b });
            Assert.Equal(2, both.Methods.Count);
            Assert.False(both.Success);
            Assert.Contains("2 methods: 1 verified, 1 with failed obligations", LibraryReport.Render(both));
        }
    }
}
