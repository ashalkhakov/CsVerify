using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using Microsoft.Boogie;
using VCGeneration;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>
    /// Runs Boogie in process on a translated program, with the Z3 CsVerify uses, and turns each failure into the
    /// CsVerify diagnostic its line was written for (BoogieTranslator.Lines).
    /// </summary>
    internal static class BoogieRunner
    {
        /// <summary>
        /// The failures, each a diagnostic of the method it is in; an error of Boogie's own is thrown. A procedure that
        /// times out is verified once more an assertion at a time (/vcsSplitOnEveryAssert), as CsVerify's engine
        /// proves its obligations one by one: a long one that is hard as a whole is often easy split. So is one that
        /// fails: once Boogie has a counterexample it looks for more, and where the solver then answers unknown it stops,
        /// the assertions it hadn't decided reported neither failed nor undecided (and it reports five at most). Split,
        /// each is decided on its own; where that says other than the whole did, the method is undecided.
        /// </summary>
        public static List<(MethodResult method, VerificationDiagnostic diagnostic)> Verify(BoogieTranslator program, string z3Path, int timeoutMs)
        {
            // (loops' inferred facts, as CsVerify's engine has them: one that doesn't hold on entry or at a back edge is left
            // out, and the program verified again, until those assumed all held; what that run says is what's reported)
            // (again, of only the procedures whose facts failed: the others' results stand)
            // (first, each whole in a quarter of the time: one that is hard whole is mostly easy split, which gets all of it;
            // only one that split doesn't decide is tried whole again, for all of it)
            int quick = timeoutMs <= 10000 ? timeoutMs : Math.Max(10000, timeoutMs / 4);
            var names = new Dictionary<MethodResult, string>();
            var (failures, undecided, factsIn) = Run(program, z3Path, quick, null, null, names);
            for (int round = 1; factsIn.Count > 0; round++)
            {
                var facts = failures.Where(f => f.diagnostic.Id == Checks.Candidate).Select(f => int.Parse(f.diagnostic.Message)).ToList();
                var redo = new HashSet<MethodResult>(failures.Where(f => f.diagnostic.Id == Checks.Candidate).Select(f => f.method));
                if (round > 5) { foreach (var (line, c) in program.Lines) if (c.Id == Checks.Candidate && redo.Contains(c.Method)) program.Disabled.Add(line); }
                else foreach (var line in facts) program.Disabled.Add(line);
                var (redone0, undecidedAgain0, factsAgain) = Run(program, z3Path, quick, null, factsIn, names);
                failures = failures.Where(f => !redo.Contains(f.method)).Concat(redone0).ToList();
                undecided = undecided.Where(u => !factsIn.Contains(u)).Concat(undecidedAgain0).Distinct().ToList();
                factsIn = round > 5 ? new List<string>() : factsAgain;
            }
            failures = failures.Where(f => f.diagnostic.Id != Checks.Candidate).ToList();
            var redone = new HashSet<MethodResult>(failures.Where(f => f.diagnostic.Id == "CSV1900").Select(f => f.method));
            // (the methods that failed, and weren't undecided: each again, split, to see nothing went unreported)
            var failed = failures.Select(f => f.method).Where(m => !redone.Contains(m) && names.ContainsKey(m)).Distinct().ToList();
            var splitProcs = undecided.Concat(failed.Select(m => names[m])).Distinct().ToList();
            if (splitProcs.Count == 0) return failures;
            var (again, _, _) = Run(program, z3Path, timeoutMs, splitProcs);
            object Key((MethodResult method, VerificationDiagnostic diagnostic) f) => (f.diagnostic.Id, f.diagnostic.Span.StartLinePosition, f.diagnostic.Message);
            foreach (var m in failed)
            {
                var whole = new HashSet<object>(failures.Where(f => f.method == m).Select(Key));
                var parts = again.Where(f => f.method == m).ToList();
                if (parts.Any(f => f.diagnostic.Id == "CSV1900") || !whole.SetEquals(parts.Select(Key)))
                {
                    var span = failures.First(f => f.method == m).diagnostic.Span;
                    failures = failures.Where(f => f.method != m).Append((m, new VerificationDiagnostic("CSV1900", false,
                        "Boogie couldn't decide all of it: split an assertion at a time, it says other than whole", span))).ToList();
                }
            }
            if (undecided.Count == 0) return failures;
            // (split, an assertion that isn't proved is no evidence of a bug: each is then without what the solver
            // learned from the others. A redone method proved whole by its parts is verified; else it stays undecided,
            // for CsVerify's engine to verify where it is the fallback)
            var undecidedAgain = again.Where(f => redone.Contains(f.method)).GroupBy(f => f.method)
                .Select(g => g.FirstOrDefault(f => f.diagnostic.Id == "CSV1900") is var u && u.method != null ? u
                    : (g.Key, new VerificationDiagnostic("CSV1900", false, "Boogie couldn't decide it: split an assertion at a time, one wasn't proved", g.First().diagnostic.Span))).ToList();
            // (whole again, with all the time, of those split didn't decide where the first try had less: proved, it's verified)
            if (quick < timeoutMs && undecidedAgain.Count > 0)
            {
                var stillOpen = undecidedAgain.Select(u => u.Item1).Where(names.ContainsKey).Distinct().ToList();
                var (whole, _, _) = Run(program, z3Path, timeoutMs, null, stillOpen.Select(m => names[m]).ToList());
                var proved = stillOpen.Where(m => !whole.Any(f => f.method == m)).ToHashSet();
                undecidedAgain = undecidedAgain.Where(u => !proved.Contains(u.Item1)).ToList();
            }
            return failures.Where(f => !redone.Contains(f.method)).Concat(undecidedAgain).ToList();
        }

        private static (List<(MethodResult method, VerificationDiagnostic diagnostic)> failures, List<string> undecided, List<string> facts) Run(
            BoogieTranslator program, string z3Path, int timeoutMs, List<string> split, List<string> procs = null, Dictionary<MethodResult, string> names = null)
        {
            var output = new StringWriter();
            var options = new CommandLineOptions(output, new ConsolePrinter());
            // (CSVERIFY_BOOGIE_OPTIONS: more of Boogie's options, space-separated, to debug a translation: /proverLog:x.smt2)
            var extra = Environment.GetEnvironmentVariable("CSVERIFY_BOOGIE_OPTIONS")?.Split(' ', StringSplitOptions.RemoveEmptyEntries) ?? new string[0];
            var only = split == null ? (procs ?? new List<string>()).Select(x => "/proc:" + x) : new[] { "/vcsSplitOnEveryAssert" }.Concat(split.Select(x => "/proc:" + x));

            // (procedures verified side by side, a solver each: their results don't depend on each other)
            var cores = "/vcsCores:" + Math.Max(1, Environment.ProcessorCount);
            options.Parse(new[] { "/proverOpt:PROVER_PATH=" + z3Path, "/timeLimit:" + Math.Max(1, timeoutMs / 1000), cores }.Concat(only).Concat(extra).ToArray());
            using var engine = ExecutionEngine.CreateWithoutSharedCache(options);
            if (Parser.Parse(program.Text, "csverify.bpl", out Microsoft.Boogie.Program parsed, false) != 0 || parsed == null)
                throw new InvalidOperationException("the translated program doesn't parse:\n" + output);
            if (engine.ResolveAndTypecheck(parsed, "csverify.bpl", out _) != PipelineOutcome.ResolvedAndTypeChecked)
                throw new InvalidOperationException("the translated program doesn't type check:\n" + output);
            var failures = new List<(MethodResult, VerificationDiagnostic)>();
            var undecided = new List<string>();
            var facts = new List<string>();
            var stats = new PipelineStatistics();
            var outcome = engine.InferAndVerify(output, parsed, stats, "csverify", info =>
            {
                var d = Diagnostic(program, info);
                lock (failures)
                {
                    failures.Add(d);
                    if (names != null && d.Item1 != null && info.ImplementationName != null) names[d.Item1] = info.ImplementationName;
                    if (d.Item2?.Id == "CSV1900" && info.ImplementationName != null && !undecided.Contains(info.ImplementationName)) undecided.Add(info.ImplementationName);
                    if (d.Item2?.Id == Checks.Candidate && info.ImplementationName != null && !facts.Contains(info.ImplementationName)) facts.Add(info.ImplementationName);
                }
            }, "csverify", default).GetAwaiter().GetResult();
            if (outcome != PipelineOutcome.VerificationCompleted && outcome != PipelineOutcome.Done)
                throw new InvalidOperationException("Boogie: " + outcome + "\n" + output);
            if (Environment.GetEnvironmentVariable("CSVERIFY_TRACE") == "2")
                Console.Error.WriteLine(output + $"\n[stats] verified {stats.VerifiedCount} errors {stats.ErrorCount} inconclusive {stats.InconclusiveCount} timeouts {stats.TimeoutCount} outOfResource {stats.OutOfResourceCount} outOfMemory {stats.OutOfMemoryCount}");
            // (one report of a check, however many paths fail it)
            return (failures.Where(f => f.Item1 != null).GroupBy(f => (f.Item1, f.Item2.Id, f.Item2.Span.StartLinePosition, f.Item2.Message)).Select(g => g.First()).ToList(), undecided, facts);
        }

        /// <summary>A failure as CsVerify reports it: the check of its line, of the kind Boogie says it is.</summary>
        private static (MethodResult, VerificationDiagnostic) Diagnostic(BoogieTranslator program, ErrorInformation info)
        {
            program.Lines.TryGetValue(info.Tok.line, out var at);
            var about = info.Aux.Select(a => program.Lines.TryGetValue(a.Tok.line, out var c) ? c : null).FirstOrDefault(c => c != null && c.Id == BoogieTranslator.Aux);
            string kind = info.Kind.ToString();
            if (at == null) return (null, null);
            // (a loop's inferred fact that doesn't hold: its line, for the next run to leave it out)
            if (at.Id == Checks.Candidate) return (at.Method, new VerificationDiagnostic(Checks.Candidate, false, info.Tok.line.ToString(), at.Span));
            // (a timeout, or running out of memory or resources: nothing was decided, which isn't verified)
            if (at.Id == BoogieTranslator.Undecided) return (at.Method, new VerificationDiagnostic("CSV1900", false, info.Msg, at.Span));
            var (id, message) = kind switch
            {
                "Precondition" when about?.ReportAs == "CSV1014" => ("CSV1014", $"{at.Message}: {about.Message}"),
                "Precondition" => ("CSV1001", $"{at.Message} might throw: its precondition{(about != null ? " (" + about.Message + ")" : "")} might not hold"),
                "Postcondition" when about?.ReportAs == "CSV1014" => ("CSV1014", about.Message),
                "Postcondition" => ("CSV1002", $"{about?.Message ?? "a postcondition"} might not hold on this return path"),
                // (an assert at a loop head is an invariant to Boogie: a well-definedness check there is still one)
                "InvariantEntry" when at.Id == "CSV1005" => ("CSV1005", $"{at.Message} might not hold on entry"),
                "InvariantMaintainance" when at.Id == "CSV1005" => ("CSV1006", $"{at.Message} might not be maintained by the loop"),
                _ => (at.Id, at.Message + (at.Id == "CSV1004" ? " might not hold" : "")),
            };
            return (at.Method, new VerificationDiagnostic(id, true, message + " (boogie)", at.Span));
        }
    }
}
