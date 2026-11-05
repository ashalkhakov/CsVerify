using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text.RegularExpressions;
using CsVerify.Verifier;
using Xunit;

namespace CsVerify.Tests
{
    /// <summary>
    /// The linter benchmark's CsVerify column (bench/Linters, scored with the linters by bench/linters.sh): which cases
    /// CsVerify reports. A change here is a change to the benchmark's table: update its README with it.
    /// </summary>
    public class LinterBenchTests
    {
        private static readonly string[] Reported =
        {
            "ThrowNull.Direct", "ThrowNull.Hidden",
            "ModifiedWhileEnumerated.Direct", "ModifiedWhileEnumerated.HiddenAlias", "ModifiedWhileEnumerated.HiddenCall",
            "Unobserved.Direct", "Unobserved.Hidden", "Unobserved.Harmless", // (a task awaited later is not supported)
            "Disposal.LeakDirect", "Disposal.LeakHidden", "Disposal.UseAfterDispose",
            "DisposableField.Direct",
            "FormatArguments.Direct", "FormatArguments.Hidden",
            "SwitchExpression.Direct", "SwitchExpression.Hidden",
            "Null.Direct", "Null.Hidden",
            "Bounds.Direct", "Bounds.Hidden",
            "Overflow.Direct",
            "DivideByZero.Direct",
        };

        [Fact]
        public void CsVerify_ReportsTheseCases()
        {
            var file = Path.Combine(Harness.RepoRoot(), "bench", "Linters", "Cases.cs");
            var cases = new List<(string name, int from, int to)>();
            var lines = File.ReadAllLines(file);
            (string name, int from)? open = null;
            for (int i = 0; i < lines.Length; i++)
            {
                var m = Regex.Match(lines[i], @"^\s*#region case (\S+) (bug|ok)");
                if (m.Success) open = (m.Groups[1].Value, i + 1);
                else if (open != null && lines[i].Trim() == "#endregion") { cases.Add((open.Value.name, open.Value.from, i + 1)); open = null; }
            }
            var r = Engine.VerifyFiles(new[] { file }, new VerifierOptions());
            Assert.Empty(r.CompilationErrors);
            var reported = r.Diagnostics.Where(d => d.IsError)
                .Select(d => cases.FirstOrDefault(c => c.from <= d.Line && d.Line <= c.to).name)
                .Where(n => n != null).Distinct().OrderBy(n => n).ToArray();
            Assert.Equal(Reported.OrderBy(n => n).ToArray(), reported);
        }
    }
}
