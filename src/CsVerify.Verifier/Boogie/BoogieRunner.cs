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
        /// <summary>The failures, each a diagnostic of the method it is in; an error of Boogie's own is thrown.</summary>
        public static List<(MethodResult method, VerificationDiagnostic diagnostic)> Verify(BoogieTranslator program, string z3Path, int timeoutMs)
        {
            var output = new StringWriter();
            var options = new CommandLineOptions(output, new ConsolePrinter());
            options.Parse(new[] { "/proverOpt:PROVER_PATH=" + z3Path, "/timeLimit:" + Math.Max(1, timeoutMs / 1000) });
            using var engine = ExecutionEngine.CreateWithoutSharedCache(options);
            if (Parser.Parse(program.Text, "csverify.bpl", out Microsoft.Boogie.Program parsed, false) != 0 || parsed == null)
                throw new InvalidOperationException("the translated program doesn't parse:\n" + output);
            if (engine.ResolveAndTypecheck(parsed, "csverify.bpl", out _) != PipelineOutcome.ResolvedAndTypeChecked)
                throw new InvalidOperationException("the translated program doesn't type check:\n" + output);
            var failures = new List<(MethodResult, VerificationDiagnostic)>();
            var stats = new PipelineStatistics();
            var outcome = engine.InferAndVerify(output, parsed, stats, "csverify", info =>
            {
                lock (failures) failures.Add(Diagnostic(program, info));
            }, "csverify", default).GetAwaiter().GetResult();
            if (outcome != PipelineOutcome.VerificationCompleted && outcome != PipelineOutcome.Done)
                throw new InvalidOperationException("Boogie: " + outcome + "\n" + output);
            return failures.Where(f => f.Item1 != null).ToList();
        }

        /// <summary>A failure as CsVerify reports it: the check of its line, of the kind Boogie says it is.</summary>
        private static (MethodResult, VerificationDiagnostic) Diagnostic(BoogieTranslator program, ErrorInformation info)
        {
            program.Lines.TryGetValue(info.Tok.line, out var at);
            var about = info.Aux.Select(a => program.Lines.TryGetValue(a.Tok.line, out var c) ? c : null).FirstOrDefault(c => c != null && c.Id == BoogieTranslator.Aux);
            string kind = info.Kind.ToString();
            if (at == null) return (null, null);
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
