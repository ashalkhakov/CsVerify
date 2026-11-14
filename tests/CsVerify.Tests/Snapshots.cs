using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text.Json;
using Xunit;

namespace CsVerify.Tests
{
    /// <summary>
    /// What each method of a test's program reports (each error's id and line), recorded in
    /// Expected/BoogieEngine.json under the test's key. With CSVERIFY_RECORD=1, a test writes its entry instead of checking it.
    /// </summary>
    internal static class Snapshots
    {
        private static readonly object Gate = new object();

        private static string File => Path.Combine(Harness.RepoRoot(), "tests", "CsVerify.Tests", "Expected", "BoogieEngine.json");

        private static SortedDictionary<string, SortedDictionary<string, string[]>> Load() =>
            System.IO.File.Exists(File)
                ? JsonSerializer.Deserialize<SortedDictionary<string, SortedDictionary<string, string[]>>>(System.IO.File.ReadAllText(File))
                : new SortedDictionary<string, SortedDictionary<string, string[]>>(StringComparer.Ordinal);

        public static void Check(string key, Dictionary<string, string[]> actual)
        {
            lock (Gate)
            {
                var all = Load();
                if (Environment.GetEnvironmentVariable("CSVERIFY_RECORD") == "1")
                {
                    all[key] = new SortedDictionary<string, string[]>(actual, StringComparer.Ordinal);
                    Directory.CreateDirectory(Path.GetDirectoryName(File));
                    System.IO.File.WriteAllText(File, JsonSerializer.Serialize(all, new JsonSerializerOptions { WriteIndented = true }) + "\n");
                    return;
                }
                Assert.True(all.TryGetValue(key, out var expected), key + ": no snapshot (run with CSVERIFY_RECORD=1 to take one)");
                var problems = new List<string>();
                foreach (var (method, ids) in expected)
                    if (!actual.TryGetValue(method, out var got)) problems.Add($"{method}: missing");
                    else if (!got.SequenceEqual(ids)) problems.Add($"{method}: expected [{string.Join(", ", ids)}], got [{string.Join(", ", got)}]");
                foreach (var method in actual.Keys.Where(m => !expected.ContainsKey(m))) problems.Add($"{method}: not in the snapshot");
                Assert.True(problems.Count == 0, key + ":\n" + string.Join("\n", problems));
            }
        }
    }
}
