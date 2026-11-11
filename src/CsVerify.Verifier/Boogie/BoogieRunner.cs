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
        /// proves its obligations one by one: a long one that is hard as a whole is often easy split.
        /// </summary>
        public static List<(MethodResult method, VerificationDiagnostic diagnostic)> Verify(BoogieTranslator program, string z3Path, int timeoutMs)
        {
            var (failures, undecided) = Run(program, z3Path, timeoutMs, null);
            if (undecided.Count == 0) return failures;
            var (again, _) = Run(program, z3Path, timeoutMs, undecided);
            var redone = new HashSet<MethodResult>(failures.Where(f => f.diagnostic.Id == "CSV1900").Select(f => f.method));
            // (split, an assertion that isn't proved is no evidence of a bug: each is then without what the solver
            // learned from the others. A redone method proved whole by its parts is verified; else it stays undecided,
            // for CsVerify's engine to verify where it is the fallback)
            var undecidedAgain = again.Where(f => redone.Contains(f.method)).GroupBy(f => f.method)
                .Select(g => g.FirstOrDefault(f => f.diagnostic.Id == "CSV1900") is var u && u.method != null ? u
                    : (g.Key, new VerificationDiagnostic("CSV1900", false, "Boogie couldn't decide it: split an assertion at a time, one wasn't proved", g.First().diagnostic.Span)));
            return failures.Where(f => !redone.Contains(f.method)).Concat(undecidedAgain).ToList();
        }

        private static (List<(MethodResult method, VerificationDiagnostic diagnostic)> failures, List<string> undecided) Run(
            BoogieTranslator program, string z3Path, int timeoutMs, List<string> split)
        {
            var output = new StringWriter();
            var options = new CommandLineOptions(output, new ConsolePrinter());
            // (CSVERIFY_BOOGIE_OPTIONS: more of Boogie's options, space-separated, to debug a translation: /proverLog:x.smt2)
            var extra = Environment.GetEnvironmentVariable("CSVERIFY_BOOGIE_OPTIONS")?.Split(' ', StringSplitOptions.RemoveEmptyEntries) ?? new string[0];
            var only = split == null ? new string[0] : new[] { "/vcsSplitOnEveryAssert" }.Concat(split.Select(x => "/proc:" + x));
            options.Parse(new[] { "/proverOpt:PROVER_PATH=" + z3Path, "/timeLimit:" + Math.Max(1, timeoutMs / 1000) }.Concat(only).Concat(extra).ToArray());
            using var engine = ExecutionEngine.CreateWithoutSharedCache(options);
            if (Parser.Parse(program.Text, "csverify.bpl", out Microsoft.Boogie.Program parsed, false) != 0 || parsed == null)
                throw new InvalidOperationException("the translated program doesn't parse:\n" + output);
            if (engine.ResolveAndTypecheck(parsed, "csverify.bpl", out _) != PipelineOutcome.ResolvedAndTypeChecked)
                throw new InvalidOperationException("the translated program doesn't type check:\n" + output);
            var failures = new List<(MethodResult, VerificationDiagnostic)>();
            var undecided = new List<string>();
            var stats = new PipelineStatistics();
            var outcome = engine.InferAndVerify(output, parsed, stats, "csverify", info =>
            {
                var d = Diagnostic(program, info);
                lock (failures)
                {
                    failures.Add(d);
                    if (d.Item2?.Id == "CSV1900" && info.ImplementationName != null && !undecided.Contains(info.ImplementationName)) undecided.Add(info.ImplementationName);
                }
            }, "csverify", default).GetAwaiter().GetResult();
            if (outcome != PipelineOutcome.VerificationCompleted && outcome != PipelineOutcome.Done)
                throw new InvalidOperationException("Boogie: " + outcome + "\n" + output);
            // (one report of a check, however many paths fail it)
            return (failures.Where(f => f.Item1 != null).GroupBy(f => (f.Item1, f.Item2.Id, f.Item2.Span.StartLinePosition, f.Item2.Message)).Select(g => g.First()).ToList(), undecided);
        }

        /// <summary>A failure as CsVerify reports it: the check of its line, of the kind Boogie says it is.</summary>
        private static (MethodResult, VerificationDiagnostic) Diagnostic(BoogieTranslator program, ErrorInformation info)
        {
            program.Lines.TryGetValue(info.Tok.line, out var at);
            var about = info.Aux.Select(a => program.Lines.TryGetValue(a.Tok.line, out var c) ? c : null).FirstOrDefault(c => c != null && c.Id == BoogieTranslator.Aux);
            string kind = info.Kind.ToString();
            if (at == null) return (null, null);
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
