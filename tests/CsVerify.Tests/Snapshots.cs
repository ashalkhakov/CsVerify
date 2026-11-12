using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text.Json;
using Xunit;

namespace CsVerify.Tests
{
    /// <summary>
    /// What each method of a test's program reports (each error's id and line), as it was when the snapshot was taken:
    /// Expected/BoogieEngine.json, a test's key to its methods. The snapshot was taken where both engines agreed, before
    /// CsVerify's own engine was removed, so a method's expectation is that engine's too. With CSVERIFY_RECORD=1, a test
    /// writes its entry instead of checking it.
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
