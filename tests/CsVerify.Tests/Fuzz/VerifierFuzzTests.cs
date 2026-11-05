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

        // (a method past it is reported not verified, never verified: a cap on time, not on soundness)
        private static readonly int Budget = int.TryParse(Environment.GetEnvironmentVariable("CSVERIFY_FUZZ_BUDGET"), out var ms) ? ms : 8000;

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
            public readonly HashSet<int> PostFalse = new HashSet<int>(), ThrowFalse = new HashSet<int>();
            // (candidates whose evaluation threw, a checked cast or division in it: neither false nor true, so neither kept nor planted)
            public readonly HashSet<int> PostThrows = new HashSet<int>(), ThrowPostThrows = new HashSet<int>();
            public readonly Dictionary<int, string> Witness = new Dictionary<int, string>();
            public string Crash;
            public bool Escaped; // (it left by Escape on some input: its EnsuresOnThrow candidates were tested)
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
                    catch (TargetInvocationException e) when (Allowed(e)) { if (e.InnerException?.GetType().Name == "Escape") p.Escaped = true; } // (it may leave by throwing)
                    catch (TargetInvocationException e) { p.Crash ??= $"{input}: {e.InnerException?.GetType().Name}"; }
                    var reached = (HashSet<int>)hit.GetField("Reached").GetValue(null);
                    var falses = (HashSet<int>)hit.GetField("False").GetValue(null);
                    p.Reached.UnionWith(reached);
                    p.Throws.UnionWith((HashSet<int>)hit.GetField("Throws").GetValue(null));
                    foreach (var f in falses) if (p.False.Add(f)) p.Witness[f] = input.ToString();
                    foreach (var f in (HashSet<int>)hit.GetField("PostFalse").GetValue(null))
                        if (p.PostFalse.Add(f)) p.Witness[1000 + f] = input.ToString();
                    foreach (var f in (HashSet<int>)hit.GetField("ThrowFalse").GetValue(null))
                        if (p.ThrowFalse.Add(f)) p.Witness[2000 + f] = input.ToString();
                    p.PostThrows.UnionWith((HashSet<int>)hit.GetField("PostThrows").GetValue(null));
                    p.ThrowPostThrows.UnionWith((HashSet<int>)hit.GetField("ThrowPostThrows").GetValue(null));
                }
            }

            // the variants
            var plan = new List<(ProgramGenerator.Method m, HashSet<int> keep, int post, int planted, int plantedPost, int throwPost, int plantedThrow)>();
            var verify = new StringBuilder();
            foreach (var m in methods)
            {
                var p = probed[m.Name];
                var keep = new HashSet<int>(Enumerable.Range(0, m.Slots).Where(id => !p.False.Contains(id) && !p.Throws.Contains(id)));
                int post = Enumerable.Range(0, m.Posts.Count).Where(k => !p.PostFalse.Contains(k) && !p.PostThrows.Contains(k)).DefaultIfEmpty(-1).First();
                // (to plant: a slot that failed where it was reached, or a ghost check, true by construction, that was reached:
                // its negation; one of each kind in turn)
                var failed = p.False.Where(id => p.Reached.Contains(id) && !p.Throws.Contains(id)).ToList();
                var ghosts = m.StaticSlots.Where(id => p.Reached.Contains(id)).ToList();
                int planted = p.Crash != null ? -1
                    : ghosts.Count > 0 && (failed.Count == 0 || int.Parse(m.Name.Substring(1)) % 2 == 0) ? ghosts[0]
                    : failed.DefaultIfEmpty(-1).First();
                int plantedPost = p.Crash != null || planted >= 0 ? -1 : p.PostFalse.Where(k => !p.PostThrows.Contains(k)).DefaultIfEmpty(-1).First();
                // (EnsuresOnThrow: one that held whenever it left by Escape; or planted, one that failed then)
                // (only one that was tested: else it must hold after every call, any of which may throw, and rarely does)
                int throwPost = !p.Escaped ? -1 : Enumerable.Range(0, m.ThrowPosts.Count).Where(k => !p.ThrowFalse.Contains(k) && !p.ThrowPostThrows.Contains(k)).DefaultIfEmpty(-1).First();
                int plantedThrow = p.Crash != null || planted >= 0 || plantedPost >= 0 ? -1 : p.ThrowFalse.Where(k => !p.ThrowPostThrows.Contains(k)).DefaultIfEmpty(-1).First();
                plan.Add((m, keep, post, planted, plantedPost, throwPost, plantedThrow));
                verify.Append(m.Render(ProgramGenerator.Mode.Verify, m.Name + "T", keep, -1, post, throwPost));
                if (planted >= 0) verify.Append(m.Render(ProgramGenerator.Mode.Verify, m.Name + "F", keep, planted, post, throwPost));
                else if (plantedPost >= 0) verify.Append(m.Render(ProgramGenerator.Mode.Verify, m.Name + "F", keep, -1, plantedPost, throwPost));
                else if (plantedThrow >= 0) verify.Append(m.Render(ProgramGenerator.Mode.Verify, m.Name + "F", keep, -1, post, plantedThrow));
            }
            var source = "#nullable enable\nusing System; using System.Diagnostics; using System.Linq; using System.Collections.Generic; using CsVerify;\n" + ProgramGenerator.Prelude + "public static class G\n{\n" + verify + "}\n";
            if (Environment.GetEnvironmentVariable("CSVERIFY_FUZZ_SAVE") is string dir) File.WriteAllText(Path.Combine(dir, $"fuzz{seed}.cs"), source);
            var clock = System.Diagnostics.Stopwatch.StartNew();
            var result = Engine.VerifySources(new[] { ($"fuzz{seed}.cs", source) }, new VerifierOptions { CheckOverflow = true, TimeoutMs = 1000, MethodBudgetMs = Budget });
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
            bool Unit(string name) =>
                result.Methods.Any(r => r.Name == "G." + name) &&
                result.Methods.Where(r => r.Name == "G." + name || r.Name.StartsWith("G." + name + ".")).All(r => r.Verified);
            // (a method with its lambdas and local functions; and only if the methods it calls are, whose contracts it used)
            var byName = methods.ToDictionary(x => x.Name);
            bool Verified(string name)
            {
                var m0 = byName[name.Substring(0, name.Length - 1)];
                return Unit(name) && m0.Callees.All(callee => Unit(callee + "T"));
            }
            string Text(ProgramGenerator.Method m, HashSet<int> keep, int planted, int post, int throwPost = -1) =>
                m.Render(ProgramGenerator.Mode.Verify, m.Name, keep, planted, post, throwPost);

            // run the true variants that verified, on the probe's inputs and fresh ones
            var run = Compile(seed, "R", plan.Select(x => x.m.Render(ProgramGenerator.Mode.Run, x.m.Name + "T", x.keep, -1, x.post, x.throwPost)));
            foreach (var (m, keep, post, planted, plantedPost, throwPost, plantedThrow) in plan)
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
                        catch (TargetInvocationException e) when (e.InnerException?.GetType().Name == "Skip" || Allowed(e)) { } // (partial correctness: leaving by a throw is allowed)
                        catch (TargetInvocationException e) { failure = e.InnerException?.GetType().Name + ": " + e.InnerException?.Message; }
                        if (failure == null) continue;
                        o.Problems.Add($"seed {seed}, {m.Name}: verified, but on {input}: {failure}\n{Text(m, keep, -1, post, throwPost)}");
                        break;
                    }
                }
                if (planted >= 0 || plantedPost >= 0 || plantedThrow >= 0)
                {
                    o.Planted++;
                    if (!Verified(m.Name + "F")) o.PlantedRejected++;
                    else
                    {
                        var what = planted >= 0 ? $"assertion {planted}" : plantedPost >= 0 ? "the postcondition" : "the EnsuresOnThrow";
                        var witness = probed[m.Name].Witness[planted >= 0 ? planted : plantedPost >= 0 ? 1000 + plantedPost : 2000 + plantedThrow];
                        o.Problems.Add($"seed {seed}, {m.Name}: verified with {what}, which fails on {witness}\n" +
                                       Text(m, keep, planted, plantedPost >= 0 ? plantedPost : post, plantedThrow >= 0 ? plantedThrow : throwPost));
                    }
                }
            }
            return o;
        }

        /// <summary>
        /// The throws a verified method may end by (partial correctness): the program's own, and a failed downcast,
        /// which ordinary code assumes did not fail. Any other exception from a verified method is a bug.
        /// </summary>
        private static bool Allowed(TargetInvocationException e) => e.InnerException?.GetType().Name is "Escape" or "InvalidCastException";

        private static readonly (string, string)[] FeatureMarks =
        {
            ("arrays written", "] = "), ("loops", "for ("), ("LINQ", "x => "), ("fields", ".V = "), ("d (maybe null, maybe c)", "d.V"),
            ("new cells", "new Cell"), ("records", "new Pt("), ("doubles", "double "), ("double to int", "(int)"),
            ("throws", "throw new Escape"), ("catch Escape", "catch (Escape)"), ("checked, caught", "catch (OverflowException)"),
            ("frames (Bump)", "H.Bump"), ("frames (Scramble)", "H.Scramble"), ("cell permissions (SetCell)", "H.SetCell"), ("[Pure] calls", "H.Twice"),
            ("owned accounts", "new Account("), ("transfers", "Account.Transfer"), ("read shares", "Own.Share"),
            ("loop invariants", "Spec.Invariant"), ("lemmas", "L.TriFormula"), ("recursion (Tri)", "L.Tri("),
            ("virtual calls", ".Next("), ("virtual queries", ".Weight()"),
            ("interface calls", ".Read(Math"), ("interface queries", ".Scale()"), ("dynamic frames", "new Duo()"), ("Mem cells", "Mem.Alloc"),
            ("lists", "new List<int>"), ("dictionaries", "new Dictionary<int, int>"), ("hash sets", "new HashSet<int>"), ("stacks", "new Stack<int>"),
            ("strings", "var str"), ("nullable ints", "int? nul"), ("unchecked", "unchecked("), ("foreach", "foreach ("),
            ("data types", "Shape sh"), ("patterns", " is Shape."), ("switch expressions", "switch {"), ("downcasts", "((Shape.Seg)"),
            ("record invariants", "new Range("), ("mutable structs", "new Pos"), ("ref locals", "ref int"),
            ("spans", "AsSpan("), ("rectangular arrays", "new int[2, 3]"), ("goto loops", "goto again"),
            ("local functions", "Spec.Ensures((int r) => x <= r"), ("lambdas", "Func<int, int>"), ("EnsuresOnThrow", "EnsuresOnThrow"),
            ("multisets", "Spec.Multiset("), ("sequences", "Seq.Const("), ("Spec.Old", "Spec.Old("), ("immutable invariants", "new Frac("),
            ("field permissions", "FP."), ("Mem arrays", "Mem.AllocArray"), ("split/join", "Mem.Split"), ("take-out", "Mem.TakeOut"),
            ("recursive predicates", "LS.Cons"), ("StringBuilder", "StringBuilder()"), ("disposables", "using (var ms"),
            ("calls between methods", "T(a, b, xs, c, d)"), ("async", "await AH."),
            ("while/do", "while (w"), ("switch statements", "switch ("), ("finally", "finally"), ("filters", "when ("), ("rethrow", "throw;"),
            ("properties with code", "new Meter("), ("static fields", "Totals.Total"), ("abstract classes", "new Hammer()"),
            ("float", "float fl"), ("queues", "new Queue<int>"), ("streams", "MemoryStream()) { st"), ("generic data types", "Opt<int>"),
            ("lambdas writing locals", "Action ac"), ("struct members by ref", "Misc.Inc(ref"), ("linear packages", "new Wallet("),
            ("string members", ".IndexOf('a')"), ("TextWriter", "StringWriter()"), ("BinaryPrimitives", "BinaryPrimitives."), ("decimal", "decimal dm"),
            ("deeper hierarchies", "Base3 bh"), ("ghost maps", "Map.Const"), ("lemmas (monotone)", "L.TriMono("),
            ("ghost functions", "Misc.Sq("), ("termination measures", "Spec.Decreases("), ("relational patterns", " is > "), ("list patterns", "xs is ["),
            ("boxes", "new Box("), ("give", "Own.Give"), ("take", "Own.Take"), ("fold", "Spec.Fold"), ("unfold", "Spec.Unfold"),
        };

        /// <summary>Methods compiled to run, with overflow checked (an overflow throws).</summary>
        /// <summary>
        /// Methods compiled to run, as users run them: through the erasure pass (ghost state, views, specifications and
        /// lemma calls removed; the Spec library replaced by its run-time part), then compiled with overflow checked,
        /// so an overflow throws. So erasure is under test too: what it changed, the checks would see.
        /// </summary>
        private static Type Compile(int seed, string klass, IEnumerable<string> methods)
        {
            var source = "#nullable disable\nusing System; using System.Diagnostics; using System.Linq; using System.Collections.Generic; using CsVerify;\n" + Runtime + ProgramGenerator.Prelude +
                         $"public static class {klass}\n{{\n" + string.Concat(methods) + "}\n";
            if (Environment.GetEnvironmentVariable("CSVERIFY_FUZZ_SAVE") is string saveTo) File.WriteAllText(Path.Combine(saveTo, $"fuzz{seed}{klass}.cs"), source);
            var erased = Erasure.Erase(new[] { ($"fuzz{seed}{klass}.cs", source) }, Array.Empty<string>(), Array.Empty<string>());
            Assert.True(erased.Success, $"seed {seed}: the run-time program does not erase:\n" + string.Join("\n", erased.Errors.Take(5).Select(e => e.Message)));
            var c = CSharpCompilation.Create($"Fuzz{seed}{klass}",
                erased.Files.Select(f => CSharpSyntaxTree.ParseText(f.Text, new CSharpParseOptions(LanguageVersion.Latest), f.OutputName)),
                Engine.FrameworkReferences(), new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary, checkOverflow: true));
            using var ms = new MemoryStream();
            var emit = c.Emit(ms);
            Assert.True(emit.Success, $"seed {seed}: the run-time program does not compile:\n" +
                string.Join("\n", emit.Diagnostics.Where(d => d.Severity == DiagnosticSeverity.Error).Take(5)));
            return Assembly.Load(ms.ToArray()).GetType(klass);
        }

        private const string Runtime = @"
public static class RT
{
    // (a call from one generated method to another: its records are not the caller's, and a failed precondition is a bug)
    [ThreadStatic] public static int Depth;
    public static int Call(Func<int> f)
    {
        Depth++;
        bool quiet = Probe.Quiet;
        Probe.Quiet = true;
        try { return f(); }
        finally { Depth--; Probe.Quiet = quiet; }
    }
    public static bool Forall(int lo, int hi, Func<int, bool> p) { for (int i = lo; i < hi; i++) if (!p(i)) return false; return true; }
}
public sealed class Skip : Exception { }
public sealed class Failed : Exception { public Failed(string what) : base(what + "" fails"") { } }
public static class Probe
{
    public static HashSet<int> Reached = new HashSet<int>(), False = new HashSet<int>(), Throws = new HashSet<int>(), PostFalse = new HashSet<int>(), ThrowFalse = new HashSet<int>();
    public static HashSet<int> PostThrows = new HashSet<int>(), ThrowPostThrows = new HashSet<int>();
    public static void Reset()
    {
        Reached = new HashSet<int>(); False = new HashSet<int>(); Throws = new HashSet<int>(); PostFalse = new HashSet<int>(); ThrowFalse = new HashSet<int>();
        PostThrows = new HashSet<int>(); ThrowPostThrows = new HashSet<int>();
    }
    public static bool Quiet;
    public static void Hit(int id, Func<bool> c)
    {
        if (Quiet) return;
        Reached.Add(id);
        try { if (!c()) False.Add(id); } catch { Throws.Add(id); }
    }
    public static void Post(int k, Func<bool> c) { if (Quiet) return; try { if (!c()) PostFalse.Add(k); } catch { PostThrows.Add(k); } }
    public static void ThrowPost(int k, Func<bool> c) { try { if (!c()) ThrowFalse.Add(k); } catch { ThrowPostThrows.Add(k); } }
}
";
    }
}
