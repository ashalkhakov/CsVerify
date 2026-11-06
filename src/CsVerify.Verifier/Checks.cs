using System;
using System.Collections.Generic;
using System.Linq;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Check profiles (<c>--checks null,linear,bounds,overflow,contracts</c>): which kinds of obligation are proved.
    /// The others are assumed (each counted, and the summary says how many), so a program is checked for what it is
    /// ready for: an application for null safety and its resources first, a parser for its bounds and overflow.
    /// Without a profile, everything is checked. Within a profile, a construct the verifier does not model is a
    /// warning instead of an error: its value is unknown and the method is verified around it (the summary counts
    /// them, since what such a construct does is not checked).
    /// </summary>
    public static class Checks
    {
        public const string Null = "null", Linear = "linear", Bounds = "bounds", Overflow = "overflow", Contracts = "contracts";

        public static readonly IReadOnlyList<string> All = new[] { Null, Linear, Bounds, Overflow, Contracts };

        /// <summary>The kind of check a diagnostic belongs to; null for those always reported (the verifier's own soundness).</summary>
        public static string KindOf(string id)
        {
            switch (id)
            {
                case "CSV1013": case "CSV1014": return Null;
                case "CSV1003": return Bounds;
                case "CSV1009": case "CSV1010": return Overflow;
                case "CSV0001": case "CSV0002": case "CSV0003": case "CSV0004": case "CSV0005": case "CSV0006": case "CSV0007":
                case "CSV1016":
                case "CSV0020": case "CSV0021": case "CSV0022":
                    return Linear;
                case "CSV1001": case "CSV1002": case "CSV1004": case "CSV1005": case "CSV1006": case "CSV1007": case "CSV1008":
                case "CSV1011": case "CSV1012": case "CSV1015": case "CSV1022": case "CSV1017": case "CSV1018": case "CSV1019": case "CSV1023": case "CSV1024": case "CSV1025":
                    return Contracts;
                // the ghost analyzer (specifications erased soundly), aliased by-reference arguments (the model of
                // memory), ill-formed stubs, unsupported constructs, unknown values, internal errors: always
                default: return null;
            }
        }

        /// <summary>Parses "null,bounds" (any order); throws ArgumentException on an unknown kind.</summary>
        public static HashSet<string> Parse(string list)
        {
            var kinds = new HashSet<string>(StringComparer.Ordinal);
            foreach (var k in list.Split(',', StringSplitOptions.RemoveEmptyEntries | StringSplitOptions.TrimEntries))
            {
                if (k == "all") { kinds.UnionWith(All); continue; }
                if (!All.Contains(k)) throw new ArgumentException($"unknown check '{k}' (the checks are {string.Join(", ", All)}, or all)");
                kinds.Add(k);
            }
            return kinds;
        }
    }
}
