using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Text;
using CsVerify.Verifier;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Xunit;
using Xunit.Abstractions;

namespace CsVerify.Tests.Fuzz
{
    /// <summary>
    /// The verifier tested on random programs (ProgramGenerator), as "Testing Dafny" (Irfan et al., ISSTA 2022) tests
    /// Dafny. Oracles:
    /// <list type="bullet">
    /// <item>soundness: a method reported verified passes its assertions and postcondition, and throws nothing (with
    /// overflow checked), on every input its precondition admits;</item>
    /// <item>robustness: no method makes the verifier fail internally (CSV1999);</item>
    /// <item>bite: enough methods verify that the first oracle tests something.</item>
    /// </list>
    /// CI runs a few fixed seeds. CSVERIFY_FUZZ_SEEDS=from..to (and CSVERIFY_FUZZ_METHODS) runs more: a soak.
    /// </summary>
    public class VerifierFuzzTests
    {
        private readonly ITestOutputHelper _out;
        public VerifierFuzzTests(ITestOutputHelper output) { _out = output; }

        [Fact]
        public void RandomPrograms_VerifiedMeansCorrect()
        {
            var (from, to) = Seeds();
            int perBatch = int.TryParse(Environment.GetEnvironmentVariable("CSVERIFY_FUZZ_METHODS"), out var n) ? n : 15;
            var all = new Outcome();
            var log = Environment.GetEnvironmentVariable("CSVERIFY_FUZZ_LOG");
            for (int seed = from; seed <= to; seed++)
            {
                var clock = System.Diagnostics.Stopwatch.StartNew();
                var batch = Batch(seed, perBatch);
                all.Add(batch);
                // (a soak's progress, batch by batch, problems first)
                if (log != null)
                    File.AppendAllText(log, string.Concat(batch.Problems.Select(p => "PROBLEM " + p + "\n")) +
                        $"seed {seed}: {batch.Verified}/{batch.Methods} verified, {batch.PlantedRejected}/{batch.Planted} planted rejected, " +
                        $"{batch.Problems.Count} problem(s), {clock.Elapsed.TotalSeconds:F0} s; slowest {batch.Log.LastOrDefault()}\n");
            }
            foreach (var line in all.Log) _out.WriteLine(line);
            _out.WriteLine("verified methods with: " + string.Join(", ", all.Features.Select(f => $"{f.Key} {f.Value}")));
            _out.WriteLine($"{all.Verified} of {all.Methods} true variants verified ({all.PinnedVerified} of {all.Pinned} pinned); " +
                           $"{all.PlantedRejected} of {all.Planted} planted rejected; {all.Problems.Count} problem(s)");
            Assert.True(all.Problems.Count == 0, string.Join("\n\n", all.Problems.Take(5)));
            // (the test bites only if the verifier proves things: pinned inputs make it all but exact)
            Assert.True(all.PinnedVerified * 3 >= all.Pinned, $"only {all.PinnedVerified} of {all.Pinned} pinned methods verified");
        }

        private static (int from, int to) Seeds()
        {
            var s = Environment.GetEnvironmentVariable("CSVERIFY_FUZZ_SEEDS");
            if (s != null && s.Split("..") is { Length: 2 } parts) return (int.Parse(parts[0]), int.Parse(parts[1]));
            return (1, 3);
        }

        /// <summary>What one batch found.</summary>
        public sealed class Outcome
        {
            public int Methods, Verified, Pinned, PinnedVerified, Planted, PlantedRejected;
            public readonly List<string> Problems = new List<string>();
            public readonly List<string> Log = new List<string>();
            /// <summary>How many verified methods (whose run-time checks were run) have each feature.</summary>
            public readonly SortedDictionary<string, int> Features = new SortedDictionary<string, int>();
            public void Add(Outcome o)
            {
                Methods += o.Methods; Verified += o.Verified; Pinned += o.Pinned; PinnedVerified += o.PinnedVerified;
                Planted += o.Planted; PlantedRejected += o.PlantedRejected; Problems.AddRange(o.Problems); Log.AddRange(o.Log);
                foreach (var (k, v) in o.Features) Features[k] = (Features.TryGetValue(k, out var n) ? n : 0) + v;
            }
        }

        /// <summary>What running a method with every slot recorded showed, over its probe inputs.</summary>
        private sealed class Probed
        {
            public readonly HashSet<int> Reached = new HashSet<int>(), False = new HashSet<int>(), Throws = new HashSet<int>();
            public readonly HashSet<int> PostFalse = new HashSet<int>();
            public readonly Dictionary<int, string> Witness = new Dictionary<int, string>();
            public string Crash;
        }

        /// <summary>
        /// One batch. Each method is probed: run on its inputs with every assertion slot and candidate postcondition
        /// recorded. Its true variant keeps the slots and a postcondition that held on all of them; its planted
        /// variant adds one that failed on an input the precondition admits. The true variant, where it verifies, must
        /// pass on fresh inputs too; the planted variant must not verify.
        /// </summary>
        public static Outcome Batch(int seed, int count)
        {
            var gen = new ProgramGenerator(seed);
            if (int.TryParse(Environment.GetEnvironmentVariable("CSVERIFY_FUZZ_SIZE"), out var size)) gen.Size = size;
            var methods = Enumerable.Range(0, count).Select(i => gen.Next($"M{i}")).ToList();
            var o = new Outcome { Methods = count };

            // probe
            var probe = Compile(seed, "P", methods.Select(m => m.Render(ProgramGenerator.Mode.Probe, m.Name)));
            var probed = new Dictionary<string, Probed>();
            var hit = probe.Assembly.GetType("Probe");
            foreach (var m in methods)
            {
                var p = probed[m.Name] = new Probed();
                foreach (var input in m.Inputs)
                {
                    hit.GetMethod("Reset").Invoke(null, null);
                    try { probe.GetMethod(m.Name + "_").Invoke(null, input.Arguments()); }
                    catch (TargetInvocationException e) when (e.InnerException?.GetType().Name == "Skip") { continue; }
                    catch (TargetInvocationException e) when (e.InnerException?.GetType().Name == "Escape") { } // (it may leave by throwing)
                    catch (TargetInvocationException e) { p.Crash ??= $"{input}: {e.InnerException?.GetType().Name}"; }
                    var reached = (HashSet<int>)hit.GetField("Reached").GetValue(null);
                    var falses = (HashSet<int>)hit.GetField("False").GetValue(null);
                    p.Reached.UnionWith(reached);
                    p.Throws.UnionWith((HashSet<int>)hit.GetField("Throws").GetValue(null));
                    foreach (var f in falses) if (p.False.Add(f)) p.Witness[f] = input.ToString();
                    foreach (var f in (HashSet<int>)hit.GetField("PostFalse").GetValue(null))
                        if (p.PostFalse.Add(f)) p.Witness[1000 + f] = input.ToString();
                }
            }

            // the variants
            var plan = new List<(ProgramGenerator.Method m, HashSet<int> keep, int post, int planted, int plantedPost)>();
            var verify = new StringBuilder();
            foreach (var m in methods)
            {
                var p = probed[m.Name];
                var keep = new HashSet<int>(Enumerable.Range(0, m.Slots).Where(id => !p.False.Contains(id) && !p.Throws.Contains(id)));
                int post = Enumerable.Range(0, m.Posts.Count).Where(k => !p.PostFalse.Contains(k)).DefaultIfEmpty(-1).First();
                int planted = p.Crash != null ? -1 : p.False.Where(id => p.Reached.Contains(id) && !p.Throws.Contains(id)).DefaultIfEmpty(-1).First();
                int plantedPost = p.Crash != null || planted >= 0 ? -1 : p.PostFalse.DefaultIfEmpty(-1).First();
                plan.Add((m, keep, post, planted, plantedPost));
                verify.Append(m.Render(ProgramGenerator.Mode.Verify, m.Name + "T", keep, -1, post));
                if (planted >= 0) verify.Append(m.Render(ProgramGenerator.Mode.Verify, m.Name + "F", keep, planted, post));
                else if (plantedPost >= 0) verify.Append(m.Render(ProgramGenerator.Mode.Verify, m.Name + "F", keep, -1, plantedPost));
            }
            var source = "#nullable enable\nusing System; using System.Diagnostics; using System.Linq; using CsVerify;\n" + ProgramGenerator.Prelude + "public static class G\n{\n" + verify + "}\n";
            if (Environment.GetEnvironmentVariable("CSVERIFY_FUZZ_SAVE") is string dir) File.WriteAllText(Path.Combine(dir, $"fuzz{seed}.cs"), source);
            var clock = System.Diagnostics.Stopwatch.StartNew();
            var result = Engine.VerifySources(new[] { ($"fuzz{seed}.cs", source) }, new VerifierOptions { CheckOverflow = true, TimeoutMs = 1000 });
            if (result.CompilationErrors.Count > 0)
            {
                o.Problems.Add($"seed {seed}: the generated program does not compile:\n" + string.Join("\n", result.CompilationErrors.Take(5)));
                return o;
            }
            o.Log.Add($"seed {seed}: verified {result.Methods.Count} units in {clock.ElapsedMilliseconds} ms; slowest: " +
                      string.Join(", ", result.Methods.OrderByDescending(r => r.Milliseconds).Take(4).Select(r => $"{r.Name} {r.Milliseconds} ms")));
            // (the helpers' contracts are what calls to them rely on: each must verify, or a "bug" could be theirs)
            foreach (var r in result.Methods.Where(r => !r.Name.StartsWith("G.") && !r.Verified))
                o.Problems.Add($"seed {seed}: the helper {r.Name} does not verify: " + string.Join("; ", r.Diagnostics.Where(d => d.IsError).Select(d => d.Message)));
            foreach (var r in result.Methods)
                foreach (var d in r.Diagnostics.Where(d => d.Id == "CSV1999"))
                    o.Problems.Add($"seed {seed}, {r.Name}: internal error: {d.Message}");
            // (a method with its lambdas, each a unit of its own)
            bool Verified(string name) =>
                result.Methods.Any(r => r.Name == "G." + name) &&
                result.Methods.Where(r => r.Name == "G." + name || r.Name.StartsWith("G." + name + ".")).All(r => r.Verified);
            string Text(ProgramGenerator.Method m, HashSet<int> keep, int planted, int post) =>
                m.Render(ProgramGenerator.Mode.Verify, m.Name, keep, planted, post);

            // run the true variants that verified, on the probe's inputs and fresh ones
            var run = Compile(seed, "R", plan.Select(x => x.m.Render(ProgramGenerator.Mode.Run, x.m.Name + "T", x.keep, -1, x.post)));
            foreach (var (m, keep, post, planted, plantedPost) in plan)
            {
                // (completeness is measured where it can be had: pinned, and not crashing on its own input)
                bool counts = m.Pinned && probed[m.Name].Crash == null;
                if (counts) o.Pinned++;
                var dump = Environment.GetEnvironmentVariable("CSVERIFY_FUZZ_DUMP");
                if (dump != null && counts && !Verified(m.Name + "T"))
                    File.AppendAllText(dump, Text(m, keep, -1, post) + string.Concat(result.Methods.Where(r => r.Name == "G." + m.Name + "T" || r.Name.StartsWith("G." + m.Name + "T."))
                        .SelectMany(r => r.Diagnostics.Where(d => d.IsError)).Select(d => $"    // {d.Id} {d.Span.StartLinePosition.Line - 3}: {d.Message}\n")) + "\n");
                if (Verified(m.Name + "T"))
                {
                    o.Verified++;
                    if (counts) o.PinnedVerified++;
                    var text = Text(m, keep, -1, post);
                    foreach (var (feature, mark) in FeatureMarks)
                        if (text.Contains(mark)) o.Features[feature] = (o.Features.TryGetValue(feature, out var k) ? k : 0) + 1;
                    foreach (var input in m.Inputs.Concat(m.Fresh))
                    {
                        string failure = null;
                        try { run.GetMethod(m.Name + "T_").Invoke(null, input.Arguments()); }
                        catch (TargetInvocationException e) when (e.InnerException?.GetType().Name is "Skip" or "Escape") { } // (partial correctness: leaving by a throw is allowed)
                        catch (TargetInvocationException e) { failure = e.InnerException?.GetType().Name + ": " + e.InnerException?.Message; }
                        if (failure == null) continue;
                        o.Problems.Add($"seed {seed}, {m.Name}: verified, but on {input}: {failure}\n{Text(m, keep, -1, post)}");
                        break;
                    }
                }
                if (planted >= 0 || plantedPost >= 0)
                {
                    o.Planted++;
                    if (!Verified(m.Name + "F")) o.PlantedRejected++;
                    else
                    {
                        var what = planted >= 0 ? $"assertion {planted}" : "the postcondition";
                        o.Problems.Add($"seed {seed}, {m.Name}: verified with {what}, which fails on {probed[m.Name].Witness[planted >= 0 ? planted : 1000 + plantedPost]}\n" +
                                       Text(m, keep, planted, planted >= 0 ? post : plantedPost));
                    }
                }
            }
            return o;
        }

        private static readonly (string, string)[] FeatureMarks =
        {
            ("arrays written", "] = "), ("loops", "for ("), ("LINQ", "x => "), ("fields", ".V = "), ("d (maybe null, maybe c)", "d.V"),
            ("new cells", "new Cell"), ("records", "new Pt("), ("doubles", "double "), ("double to int", "(int)"),
            ("throws", "throw new Escape"), ("catch Escape", "catch (Escape)"), ("checked, caught", "catch (OverflowException)"),
            ("frames (Bump)", "H.Bump"), ("frames (Scramble)", "H.Scramble"), ("cell permissions (SetCell)", "H.SetCell"), ("[Pure] calls", "H.Twice"),
            ("owned accounts", "new Account("), ("transfers", "Account.Transfer"), ("read shares", "Own.Share"),
            ("loop invariants", "Spec.Invariant"), ("lemmas", "L.TriFormula"), ("recursion (Tri)", "L.Tri("),
            ("virtual calls", ".Next("), ("virtual queries", ".Weight()"),
            ("boxes", "new Box("), ("give", "Own.Give"), ("take", "Own.Take"), ("fold", "Spec.Fold"), ("unfold", "Spec.Unfold"),
        };

        /// <summary>Methods compiled to run, with overflow checked (an overflow throws).</summary>
        private static Type Compile(int seed, string klass, IEnumerable<string> methods)
        {
            var source = "#nullable disable\nusing System; using System.Diagnostics; using System.Linq; using System.Collections.Generic; using CsVerify;\n" + Runtime + ProgramGenerator.Prelude +
                         $"public static class {klass}\n{{\n" + string.Concat(methods) + "}\n";
            var c = CSharpCompilation.Create($"Fuzz{seed}{klass}", new[] { CSharpSyntaxTree.ParseText(source, new CSharpParseOptions(LanguageVersion.Latest)) },
                Engine.FrameworkReferences().Append(MetadataReference.CreateFromFile(typeof(CsVerify.Own).Assembly.Location)), // (Own, the attributes)
                new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary, checkOverflow: true));
            using var ms = new MemoryStream();
            var emit = c.Emit(ms);
            Assert.True(emit.Success, $"seed {seed}: the run-time program does not compile:\n" +
                string.Join("\n", emit.Diagnostics.Where(d => d.Severity == DiagnosticSeverity.Error).Take(5)));
            return Assembly.Load(ms.ToArray()).GetType(klass);
        }

        private const string Runtime = @"
public static class RT
{
    public static bool Forall(int lo, int hi, Func<int, bool> p) { for (int i = lo; i < hi; i++) if (!p(i)) return false; return true; }
}
public sealed class Skip : Exception { }
public sealed class Failed : Exception { public Failed(string what) : base(what + "" fails"") { } }
public static class Probe
{
    public static HashSet<int> Reached = new HashSet<int>(), False = new HashSet<int>(), Throws = new HashSet<int>(), PostFalse = new HashSet<int>();
    public static void Reset() { Reached = new HashSet<int>(); False = new HashSet<int>(); Throws = new HashSet<int>(); PostFalse = new HashSet<int>(); }
    public static void Hit(int id, Func<bool> c)
    {
        Reached.Add(id);
        try { if (!c()) False.Add(id); } catch { Throws.Add(id); }
    }
    public static void Post(int k, Func<bool> c) { try { if (!c()) PostFalse.Add(k); } catch { PostFalse.Add(k); } }
}
";
    }
}
