using System;
using System.Threading;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using Microsoft.Boogie;
using VCGeneration;
using VcOutcome = VC.VcOutcome;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>
    /// Runs Boogie in process on a translated program, with the Z3 CsVerify uses, and turns each failure into the
    /// CsVerify diagnostic its line was written for (BoogieTranslator.Lines).
    /// </summary>
    internal static class BoogieRunner
    {
        /// <summary>
        /// The threads Boogie verifies on (as ExecutionEngine makes them: a large stack each): a pool of them for each run at
        /// a time, never disposed (disposing one interrupts its threads, which the solver's processes may still be
        /// finishing on, and an interrupt there is unhandled and ends the process), taken by a run and given back after.
        /// Not one for every run: a run's work waits on work it queued on the same threads, so runs side by side (tests
        /// in parallel) can take them all, each waiting on work queued behind the others', and none goes on.
        /// </summary>
        private static readonly System.Collections.Concurrent.ConcurrentBag<System.Threading.Tasks.TaskScheduler> Schedulers =
            new System.Collections.Concurrent.ConcurrentBag<System.Threading.Tasks.TaskScheduler>();

        /// <summary>
        /// Two runs at a time, at most: one alone has a solver for each core, two half of them each. Each run with a solver
        /// for each core, tests side by side ran dozens of solvers at once, a gigabyte each on a hard query, and the
        /// machine killed them (Boogie: "Prover died with no further output") or they starved.
        /// </summary>
        private static readonly SemaphoreSlim Gate = new SemaphoreSlim(2);
        private static int _running;

        /// <summary>
        /// The failures, each a diagnostic of the method it is in; an error of Boogie's own is thrown. A procedure that
        /// times out is verified once more an assertion at a time (/vcsSplitOnEveryAssert): a long one that is hard as a
        /// whole is often easy split. So is one that fails: once Boogie has a counterexample it looks for more, and where
        /// the solver then answers unknown it stops, the assertions it hadn't decided reported neither failed nor
        /// undecided (and it reports five at most). Split, each is decided on its own. What split finds of a method the
        /// whole didn't find failing is checked whole again, with more time (below); a method is verified only where
        /// Boogie said its procedure was correct.
        /// </summary>
        public static List<(MethodResult method, VerificationDiagnostic diagnostic)> Verify(BoogieTranslator program, string z3Path, int timeoutMs)
        {
            // (loops' inferred facts: one that doesn't hold on entry or at a back edge is left
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
                if (round > 5)
                {
                    foreach (var (line, c) in program.Lines)
                    {
                        if (c.Id == Checks.Candidate && redo.Contains(c.Method))
                        {
                            program.AddDisabled(line);
                        }
                    }
                }
                else
                {
                    foreach (var line in facts)
                    {
                        program.AddDisabled(line);
                    }
                }
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
            if (splitProcs.Count == 0)
            {
                return failures;
            }
            var (again, _, _) = Run(program, z3Path, timeoutMs, splitProcs);
            // (a failure split finds that the whole didn't: Boogie reports the solver's unknown, where it gives up, as a
            // failure, and split, without what it learned from the others, it gives up more. So the method is verified
            // whole again, with four times the time: what that finds too is a failure, what it proves is proved; where the
            // time runs out again, the method is undecided. Of a method the whole found failing, split's are kept)
            var wholeKeys = failures.Select(f => (f.method, DiagnosticKey(f))).ToHashSet();
            var fresh = again.Where(f => f.diagnostic.Id != "CSV1900" && !wholeKeys.Contains((f.method, DiagnosticKey(f)))).ToList();
            if (fresh.Count > 0)
            {
                // (of a method the whole found failing, a failure split finds is one more counterexample, the others'
                // assertions assumed, as the whole's are: Boogie stops looking after a few, or at an unknown, so the
                // whole may not find it again. Only a method the whole didn't find failing, a correct one maybe, is checked)
                var failing = new HashSet<MethodResult>(failed);
                var recheck = fresh.Select(f => f.method).Distinct().Where(names.ContainsKey).Where(m => !failing.Contains(m)).ToHashSet();
                var (confirm, _, _) = Run(program, z3Path, timeoutMs * 4, null, recheck.Select(m => names[m]).ToList());
                var kept = confirm.Where(f => f.diagnostic.Id != "CSV1900").Select(f => (f.method, DiagnosticKey(f))).ToHashSet();
                var timedOut = confirm.Where(f => f.diagnostic.Id == "CSV1900" && recheck.Contains(f.method)).ToList();
                var outOfTime = timedOut.Select(f => f.method).ToHashSet();
                again = again.Where(f => !recheck.Contains(f.method) || f.diagnostic.Id == "CSV1900" || wholeKeys.Contains((f.method, DiagnosticKey(f))) ||
                                         kept.Contains((f.method, DiagnosticKey(f))) || outOfTime.Contains(f.method))
                    .Concat(timedOut).ToList();
                // (and what that run finds of its own, a counterexample split didn't get to: a failure too, never dropped,
                // or a method whose split failures it doesn't confirm, and whose own it finds, would be verified)
                var present = again.Select(f => (f.method, DiagnosticKey(f))).ToHashSet();
                again = again.Concat(confirm.Where(f => f.diagnostic.Id != "CSV1900" && recheck.Contains(f.method) && present.Add((f.method, DiagnosticKey(f))))).ToList();
            }
            foreach (var m in failed)
            {
                var whole = new HashSet<object>(failures.Where(f => f.method == m).Select(DiagnosticKey));
                var parts = again.Where(f => f.method == m).ToList();
                if (parts.Any(f => f.diagnostic.Id == "CSV1900"))
                {
                    var span = failures.First(f => f.method == m).diagnostic.Span;
                    failures = failures.Where(f => f.method != m).Append((m, new VerificationDiagnostic("CSV1900", false,
                        "Boogie couldn't decide all of it: split an assertion at a time, one wasn't decided", span))).ToList();
                }
                // (each a counterexample, of the whole or of an assertion with the others assumed: both are failures)
                else
                {
                    failures = failures.Concat(parts.Where(f => !whole.Contains(DiagnosticKey(f)))).ToList();
                }
            }
            if (undecided.Count == 0)
            {
                return failures;
            }
            // (split, each assertion is decided with the others assumed: a counterexample to one is an execution that
            // fails it, as one of the whole is, and the rest are proved. A redone method all of whose assertions split
            // decided is decided: verified, or failed where they failed. One that split doesn't decide all of is
            // undecided: not verified, CSV1902)
            var splitDecided = again.Where(f => redone.Contains(f.method)).GroupBy(f => f.method).Where(g => g.All(f => f.diagnostic.Id != "CSV1900")).ToList();
            var decidedSplit = splitDecided.SelectMany(g => g).ToList();
            var decidedMethods = splitDecided.Select(g => g.Key).ToHashSet();
            var undecidedAgain = again.Where(f => redone.Contains(f.method) && !decidedMethods.Contains(f.method)).GroupBy(f => f.method)
                .Select(g => g.First(f => f.diagnostic.Id == "CSV1900")).ToList();
            // (whole again, with all the time, of those split didn't decide where the first try had less: proved, it's verified)
            if (quick < timeoutMs && undecidedAgain.Count > 0)
            {
                var stillOpen = undecidedAgain.Select(u => u.Item1).Where(names.ContainsKey).Distinct().ToList();
                var (whole, _, _) = Run(program, z3Path, timeoutMs, null, stillOpen.Select(m => names[m]).ToList());
                var proved = stillOpen.Where(m => !whole.Any(f => f.method == m)).ToHashSet();
                undecidedAgain = undecidedAgain.Where(u => !proved.Contains(u.Item1)).ToList();
            }
            return failures.Where(f => !redone.Contains(f.method)).Concat(decidedSplit).Concat(undecidedAgain).ToList();
        }

        private static object DiagnosticKey((MethodResult method, VerificationDiagnostic diagnostic) f) => (f.diagnostic.Id, f.diagnostic.Span.StartLinePosition, f.diagnostic.Span.EndLinePosition);

        private static (List<(MethodResult method, VerificationDiagnostic diagnostic)> failures, List<string> undecided, List<string> facts) Run(
            BoogieTranslator program, string z3Path, int timeoutMs, List<string> split, List<string> procs = null, Dictionary<MethodResult, string> names = null)
        {
            // (a run that a mishap of the solver's ended, not anything the program says, once more: Boogie's own wait for
            // a check is as long as the time limit the solver is given, so a solver that answers late (its process slow
            // to start, on Windows; a loaded machine) ends the run with a TimeoutException; a solver killed for memory,
            // with Boogie's fatal error. The second time on threads of its own: the first run's may still be held)
            for (int attempt = 0; ; attempt++)
            {
                if (!Schedulers.TryTake(out var scheduler))
                {
                    scheduler = CustomStackSizePoolTaskScheduler.Create(16 * 1024 * 1024, Math.Max(1, Environment.ProcessorCount));
                }
                Gate.Wait();
                (List<(MethodResult method, VerificationDiagnostic diagnostic)> failures, List<string> undecided, List<string> facts) result;
                try
                {
                    var alone = Interlocked.Increment(ref _running) == 1;
                    var cores = Math.Max(1, alone ? Environment.ProcessorCount : Environment.ProcessorCount / 2);
                    result = Run(scheduler, cores, program, z3Path, timeoutMs, split, procs, names);
                }
                catch (Exception e) when (attempt == 0 && SolverMishap(e))
                {
                    if (Environment.GetEnvironmentVariable("CSVERIFY_TRACE") != null)
                    {
                        Console.Error.WriteLine("[run] again, after: " + e.Message);
                    }
                    continue;
                }
                finally
                {
                    Interlocked.Decrement(ref _running);
                    Gate.Release();
                }
                // (given back after a run that ended: one that didn't may still hold its threads)
                Schedulers.Add(scheduler);
                return result;
            }
        }

        /// <summary>Boogie's printer, keeping each procedure's outcome as Boogie decides it (its name, its line, the outcome).</summary>
        private sealed class OutcomePrinter : ConsolePrinter
        {
            public readonly System.Collections.Concurrent.ConcurrentBag<(string impl, int line, VcOutcome outcome)> Outcomes =
                new System.Collections.Concurrent.ConcurrentBag<(string, int, VcOutcome)>();

            public override void ReportEndVerifyImplementation(Implementation implementation, ImplementationRunResult result)
            {
                Outcomes.Add((implementation.Name, implementation.tok.line, result.VcOutcome));
                base.ReportEndVerifyImplementation(implementation, result);
            }
        }

        /// <summary>A run ended by the solver, not by the program: Boogie's wait for a late answer, or a solver that died.</summary>
        private static bool SolverMishap(Exception e) =>
            e is TimeoutException || e is AggregateException a && a.Flatten().InnerExceptions.Any(SolverMishap) ||
            e.InnerException != null && SolverMishap(e.InnerException) ||
            e is InvalidOperationException && (e.Message.StartsWith("Boogie: FatalError") || e.Message.Contains("Prover died") || e.Message.StartsWith("Boogie: no answer"));

        private static (List<(MethodResult method, VerificationDiagnostic diagnostic)> failures, List<string> undecided, List<string> facts) Run(
            System.Threading.Tasks.TaskScheduler scheduler, int solvers, BoogieTranslator program, string z3Path, int timeoutMs, List<string> split,
            List<string> procs, Dictionary<MethodResult, string> names)
        {
            var output = new StringWriter();
            if (Environment.GetEnvironmentVariable("CSVERIFY_TRACE") == "2")
            {
                Console.Error.WriteLine($"[run] {(split == null ? "whole" : "split")} {timeoutMs} ms, {(split ?? procs)?.Count.ToString() ?? "all"} procedures, {program.Disabled.Count} facts left out");
            }
            var outcomes = new OutcomePrinter();
            var options = new CommandLineOptions(output, outcomes);
            // (CSVERIFY_BOOGIE_OPTIONS: more of Boogie's options, space-separated, to debug a translation: /proverLog:x.smt2)
            var extra = Environment.GetEnvironmentVariable("CSVERIFY_BOOGIE_OPTIONS")?.Split(' ', StringSplitOptions.RemoveEmptyEntries) ?? new string[0];
            var only = split == null ? (procs ?? new List<string>()).Select(x => "/proc:" + x) : new[] { "/vcsSplitOnEveryAssert" }.Concat(split.Select(x => "/proc:" + x));

            // (procedures verified side by side, a solver each: their results don't depend on each other)
            var cores = "/vcsCores:" + solvers;
            options.Parse(new[] { "/proverOpt:PROVER_PATH=" + z3Path, "/timeLimit:" + Math.Max(1, timeoutMs / 1000), cores }.Concat(only).Concat(extra).ToArray());
            using var engine = new ExecutionEngine(options, new EmptyVerificationResultCache(), scheduler, false);
            if (Parser.Parse(program.Text, "csverify.bpl", out Microsoft.Boogie.Program parsed, false) != 0 || parsed == null)
            {
                throw new InvalidOperationException("the translated program doesn't parse:\n" + output);
            }
            if (engine.ResolveAndTypecheck(parsed, "csverify.bpl", out _) != PipelineOutcome.ResolvedAndTypeChecked)
            {
                throw new InvalidOperationException("the translated program doesn't type check:\n" + output);
            }
            var failures = new List<(MethodResult, VerificationDiagnostic)>();
            var lines = new Dictionary<VerificationDiagnostic, int>();
            var undecided = new List<string>();
            var facts = new List<string>();
            var stats = new PipelineStatistics();
            var progress = 0;
            var running = engine.InferAndVerify(output, parsed, stats, "csverify", info =>
            {
                var d = Diagnostic(program, info);
                if (Environment.GetEnvironmentVariable("CSVERIFY_TRACE") == "2")
                {
                    Console.Error.WriteLine($"[boogie] {info.ImplementationName} {(split == null ? "whole" : "split")} {info.Kind} line {info.Tok.line}: {d.Item2?.Id} {d.Item2?.Message}");
                }
                Interlocked.Increment(ref progress);
                lock (failures)
                {
                    failures.Add(d);
                    if (d.Item2 != null)
                    {
                        lines[d.Item2] = info.Tok.line;
                    }
                    if (names != null && d.Item1 != null && info.ImplementationName != null)
                    {
                        names[d.Item1] = info.ImplementationName;
                    }
                    if (d.Item2?.Id == "CSV1900" && info.ImplementationName != null && !undecided.Contains(info.ImplementationName))
                    {
                        undecided.Add(info.ImplementationName);
                    }
                    if (d.Item2?.Id == Checks.Candidate && info.ImplementationName != null && !facts.Contains(info.ImplementationName))
                    {
                        facts.Add(info.ImplementationName);
                    }
                }
            }, "csverify", default);
            // (a run that goes on with nothing done for a long while has lost a solver's answer: Boogie waits for it, its
            // solvers idle, and would wait for ever. Not verified, then: what it was verifying is undecided)
            var idle = TimeSpan.FromSeconds(Math.Max(300, 5 * Math.Max(1, timeoutMs / 1000)));
            for (var seen = -1; !running.Wait(idle);)
            {
                var now = stats.VerifiedCount + stats.ErrorCount + stats.InconclusiveCount + stats.TimeoutCount + stats.OutOfResourceCount + stats.OutOfMemoryCount + Volatile.Read(ref progress);
                if (now == seen)
                {
                    throw new InvalidOperationException($"Boogie: no answer from its solvers in {idle.TotalSeconds:0} s");
                }
                seen = now;
            }
            var outcome = running.Result;
            if (outcome != PipelineOutcome.VerificationCompleted && outcome != PipelineOutcome.Done)
            {
                // (its reason first, on the line a diagnostic keeps: what Boogie wrote of the error)
                var why = output.ToString().Split('\n').Select(l => l.Trim()).Where(l => l.Length > 0).LastOrDefault(l => l.Contains("rror") || l.Contains("xception"));
                throw new InvalidOperationException("Boogie: " + outcome + (why == null ? "" : ": " + why) + "\n" + output);
            }
            // (a procedure Boogie didn't find correct, but for which no failure came that maps to a check: undecided, never
            // verified. A method is verified only where Boogie said so)
            var reported = new HashSet<string>(failures.Where(f => f.Item1 != null).Select(f => names != null && names.TryGetValue(f.Item1, out var n) ? n : null).Where(n => n != null));
            foreach (var (impl, line, vc) in outcomes.Outcomes)
            {
                if (vc == VcOutcome.Correct || reported.Contains(impl) || !program.Lines.TryGetValue(line, out var head) || head.Id != BoogieTranslator.Undecided || head.Method == null)
                {
                    continue;
                }
                if (failures.Any(f => f.Item1 == head.Method && f.Item2 != null))
                {
                    continue;
                }
                var silent = new VerificationDiagnostic("CSV1900", false, $"Boogie's outcome for '{impl}' was {vc}, with nothing reported", head.Span);
                failures.Add((head.Method, silent));
                lines[silent] = line;
                if (names != null)
                {
                    names[head.Method] = impl;
                }
                if (!undecided.Contains(impl))
                {
                    undecided.Add(impl);
                }
            }
            if (Environment.GetEnvironmentVariable("CSVERIFY_TRACE") == "2")
            {
                Console.Error.WriteLine(output + $"\n[stats] verified {stats.VerifiedCount} errors {stats.ErrorCount} inconclusive {stats.InconclusiveCount} timeouts {stats.TimeoutCount} outOfResource {stats.OutOfResourceCount} outOfMemory {stats.OutOfMemoryCount}");
            }
            // (one report of a check, however many paths fail it; and one of a kind at a
            // place: the first in the program)
            return (failures.Where(f => f.Item1 != null).OrderBy(f => lines[f.Item2]).GroupBy(f => (f.Item1, f.Item2.Id, f.Item2.Span.StartLinePosition, f.Item2.Span.EndLinePosition))
                .Select(g => g.First()).ToList(), undecided, facts);
        }

        /// <summary>A failure as CsVerify reports it: the check of its line, of the kind Boogie says it is.</summary>
        private static (MethodResult, VerificationDiagnostic) Diagnostic(BoogieTranslator program, ErrorInformation info)
        {
            program.Lines.TryGetValue(info.Tok.line, out var at);
            var about = info.Aux.Select(a => program.Lines.TryGetValue(a.Tok.line, out var c) ? c : null).FirstOrDefault(c => c != null && c.Id == BoogieTranslator.Aux);
            string kind = info.Kind.ToString();
            if (at == null)
            {
                return (null, null);
            }
            // (a loop's inferred fact that doesn't hold: its line, for the next run to leave it out)
            if (at.Id == Checks.Candidate)
            {
                return (at.Method, new VerificationDiagnostic(Checks.Candidate, false, info.Tok.line.ToString(), at.Span));
            }
            // (a timeout, or running out of memory or resources: nothing was decided, which isn't verified)
            if (at.Id == BoogieTranslator.Undecided)
            {
                return (at.Method, new VerificationDiagnostic("CSV1900", false, info.Msg, at.Span));
            }
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
            var diagnostic = new VerificationDiagnostic(id, true, message + " (boogie)", at.Span);
            if (at.Causes.Count > 0)
            {
                diagnostic.Causes = at.Causes.OrderBy(x => x, StringComparer.Ordinal).ToList();
            }
            return (at.Method, diagnostic);
        }
    }
}
