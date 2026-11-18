using System;
using System.IO;
using System.Linq;
using CsVerify.Verifier;
using Xunit;

namespace CsVerify.Tests
{
    /// <summary>
    /// A solver that dies during a run (#58): what it was checking is not verified, the rest goes on, and the run ends.
    /// Before, Boogie waited for ever on a dead solver's answer, and once every solver's slot was lost so, the run hung.
    /// </summary>
    public class SolverDeathTests
    {
        private const string Methods = @"public static class Sums
{
    public static int A(int a) { Spec.Requires(a > 0 && a < 1000); Spec.Ensures(Spec.Result<int>() == a); var s = 0; for (var k = 0; k < a; k++) { Spec.Invariant(s == k && k <= a); s += 1; } return s; }
    public static int B(int a) { Spec.Requires(a > 0 && a < 1000); Spec.Ensures(Spec.Result<int>() == a + 1); var s = 1; for (var k = 0; k < a; k++) { Spec.Invariant(s == k + 1 && k <= a); s += 1; } return s; }
    public static int C(int a, int b) { Spec.Requires(a >= 0 && a < 1000 && b >= 0 && b < 1000); Spec.Ensures(Spec.Result<int>() >= a); return b > a ? b : a; }
}";

        /// <summary>Z3, through a proxy that passes on this many lines of its output, then kills it and ends.</summary>
        private static string DyingZ3(int lines)
        {
            var z3 = Z3.Find(null);
            var path = Path.Combine(Path.GetTempPath(), $"csverify-dying-z3-{lines}-{Guid.NewGuid():N}.pl");
            File.WriteAllText(path, $@"#!/usr/bin/perl
use IPC::Open2;
my $pid = open2(my $out, my $in, '{z3}', @ARGV);
if (fork() == 0) {{ close STDOUT; close $out; $SIG{{PIPE}} = sub {{ exit }}; while (<STDIN>) {{ print $in $_; $in->flush; }} exit; }}
close $in; $| = 1; my $n = 0;
while (<$out>) {{ print; last if ++$n >= {lines}; }}
kill 9, $pid; exit;
");
            File.SetUnixFileMode(path, UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
            return path;
        }

        private static VerificationResult Run(int lines) =>
            Engine.VerifySources(new[] { ("Test.cs", Harness.Usings + Methods) }, new VerifierOptions { Z3Path = DyingZ3(lines), Cores = 2 });

        [Fact]
        public void ASolverThatDies_LeavesItsChecksNotVerified_AndTheRunEnds()
        {
            if (OperatingSystem.IsWindows())
            {
                return;
            }
            var r = Run(3);
            foreach (var m in new[] { "A", "B", "C" })
            {
                Assert.Equal(new[] { "CSV1902" }, r.Errors(m));
                Assert.DoesNotContain("Boogie failed", r.Explain(m));
            }
        }

        [Fact]
        public void ASolverThatDies_IsStartedAgain()
        {
            if (OperatingSystem.IsWindows())
            {
                return;
            }
            var r = Run(20);
            foreach (var m in new[] { "A", "B", "C" })
            {
                Assert.True(r.Errors(m).Length == 0, r.Explain(m));
            }
        }
    }
}
