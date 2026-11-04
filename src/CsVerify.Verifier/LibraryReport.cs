using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Text.RegularExpressions;

namespace CsVerify.Verifier
{
    /// <summary>
    /// The library report (<c>--library-report</c>): what stands between a program and its proof, ranked, so that the
    /// contracts and verifier features worth adding first are the ones that unblock the most. A failed obligation is
    /// charged to the causes of the unknown values its condition mentions (<see cref="VerificationDiagnostic.Causes"/>):
    /// a library member without a contract (its result, or what it may have changed), a method of the program without
    /// postconditions, or a loop without invariants. A failure may have several causes, or none (the code's own
    /// arithmetic and checks over values it knows).
    /// </summary>
    public static class LibraryReport
    {
        private static readonly Dictionary<string, string> Kinds = new Dictionary<string, string>
        {
            ["CSV1001"] = "callee precondition",
            ["CSV1002"] = "postcondition",
            ["CSV1003"] = "index out of range",
            ["CSV1004"] = "assertion",
            ["CSV1005"] = "loop invariant on entry",
            ["CSV1006"] = "loop invariant maintained",
            ["CSV1007"] = "loop measure",
            ["CSV1008"] = "recursion measure",
            ["CSV1009"] = "division by zero",
            ["CSV1010"] = "overflow",
            ["CSV1011"] = "termination of a proof",
            ["CSV1012"] = "well-defined specification",
            ["CSV1013"] = "null dereference",
            ["CSV1014"] = "null where not nullable",
            ["CSV1015"] = "object invariant",
            ["CSV1016"] = "owned object without its view",
            ["CSV1017"] = "dynamic frame",
            ["CSV1018"] = "behavioural subtyping",
            ["CSV1019"] = "predicate fold",
            ["CSV1020"] = "aliased by-reference arguments",
            ["CSV1021"] = "ill-formed stub or model",
            ["CSV1999"] = "internal or solver error",
        };

        private const string Library = "library ";
        private const string Source = "source ";

        public static string Render(VerificationResult result)
        {
            var sb = new StringBuilder();
            var failures = result.Methods.SelectMany(m => m.Diagnostics).Where(d => d.IsError && d.Id != "CSV1901").ToList();
            var unsupported = result.Methods.Where(m => m.Diagnostics.Any(d => d.Id == "CSV1901")).ToList();
            sb.AppendLine("library report");
            sb.AppendLine($"  {result.Methods.Count} methods: {result.Methods.Count(m => m.Verified)} verified, " +
                          $"{result.Methods.Count(m => !m.Verified && !unsupported.Contains(m))} with failed obligations, " +
                          $"{unsupported.Count} not verified (unsupported constructs)");
            sb.AppendLine($"  {failures.Count} failed obligations");

            // library members: every one called without a contract, by the failures it causes, then by its calls
            var calls = result.Methods.SelectMany(m => m.LibraryCalls).Distinct()
                .GroupBy(c => c.member).ToDictionary(g => g.Key, g => g.Count(), StringComparer.Ordinal);
            var charged = Charged(failures, Library);
            var members = calls.Keys.Union(charged.Keys, StringComparer.Ordinal)
                .Select(k => (member: k, failures: charged.GetValueOrDefault(k), calls: calls.GetValueOrDefault(k)))
                .OrderByDescending(x => x.failures).ThenByDescending(x => x.calls).ThenBy(x => x.member, StringComparer.Ordinal).ToList();
            sb.AppendLine();
            sb.AppendLine("library members without contracts, by the failures they cause");
            if (members.Count == 0) sb.AppendLine("  (none)");
            else
            {
                sb.AppendLine("  failures  calls  member");
                foreach (var x in members) sb.AppendLine($"  {x.failures,8}  {x.calls,5}  {x.member}");
            }

            var sources = Charged(failures, Source).OrderByDescending(x => x.Value).ThenBy(x => x.Key, StringComparer.Ordinal).ToList();
            sb.AppendLine();
            sb.AppendLine("methods of the program without postconditions, by the failures their calls cause");
            if (sources.Count == 0) sb.AppendLine("  (none)");
            else
            {
                sb.AppendLine("  failures  method");
                foreach (var x in sources) sb.AppendLine($"  {x.Value,8}  {x.Key}");
            }

            // the classes of failure: what each failed obligation's unknown values come from (a failure may have several)
            sb.AppendLine();
            sb.AppendLine("failed obligations by cause (one may have several)");
            Row(sb, failures.Count(d => d.Causes.Any(c => c.StartsWith(Library, StringComparison.Ordinal))), "a library member without a contract");
            Row(sb, failures.Count(d => d.Causes.Any(c => c.StartsWith(Source, StringComparison.Ordinal))), "a method without postconditions");
            Row(sb, failures.Count(d => d.Causes.Contains("a loop without invariants")), "a loop without invariants");
            Row(sb, failures.Count(d => d.Causes.Count == 0), "none of these (the code's own values)");

            sb.AppendLine();
            sb.AppendLine("failed obligations by kind");
            foreach (var g in failures.GroupBy(d => d.Id).OrderByDescending(g => g.Count()).ThenBy(g => g.Key, StringComparer.Ordinal))
                Row(sb, g.Count(), $"{g.Key}  {Kinds.GetValueOrDefault(g.Key, "")}");
            if (failures.Count == 0) sb.AppendLine("  (none)");

            Grouped(sb, "unsupported constructs (CSV1901): each leaves its method not verified",
                result.Methods.SelectMany(m => m.Diagnostics).Where(d => d.Id == "CSV1901"));
            Grouped(sb, "unknown values (CSV1900)",
                result.Methods.SelectMany(m => m.Diagnostics).Where(d => d.Id == "CSV1900"));
            return sb.ToString();
        }

        private static Dictionary<string, int> Charged(IEnumerable<VerificationDiagnostic> failures, string prefix) =>
            failures.SelectMany(d => d.Causes.Where(c => c.StartsWith(prefix, StringComparison.Ordinal)).Select(c => c.Substring(prefix.Length)))
                .GroupBy(c => c, StringComparer.Ordinal).ToDictionary(g => g.Key, g => g.Count(), StringComparer.Ordinal);

        private static void Row(StringBuilder sb, int n, string what) => sb.AppendLine($"  {n,8}  {what}");

        // the same message about different code counts as one: what is quoted ('a.Length') is left out
        private static readonly Regex Quoted = new Regex("'[^']*'");

        private static void Grouped(StringBuilder sb, string title, IEnumerable<VerificationDiagnostic> diagnostics)
        {
            sb.AppendLine();
            sb.AppendLine(title);
            var groups = diagnostics.GroupBy(d => Quoted.Replace(d.Message, "'…'"), StringComparer.Ordinal)
                .OrderByDescending(g => g.Count()).ThenBy(g => g.Key, StringComparer.Ordinal).ToList();
            if (groups.Count == 0) sb.AppendLine("  (none)");
            foreach (var g in groups) Row(sb, g.Count(), g.Key);
        }
    }
}
