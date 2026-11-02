using Microsoft.CodeAnalysis;

namespace CsVerify.Analyzers
{
    public static class Descriptors
    {
        private const string Linearity = "CsVerify.Linearity";
        private const string Ghosts = "CsVerify.Ghost";

        private static DiagnosticDescriptor Error(string id, string category, string title, string format) =>
            new DiagnosticDescriptor(id, title, format, category, DiagnosticSeverity.Error, isEnabledByDefault: true);

        public static readonly DiagnosticDescriptor NotConsumed = Error("CSV0001", Linearity,
            "Linear value is not consumed",
            "Linear value '{0}' is not consumed on every path{1}");

        public static readonly DiagnosticDescriptor UsedAfterConsume = Error("CSV0002", Linearity,
            "Linear value used after it was consumed",
            "Linear value '{0}' may already have been consumed");

        public static readonly DiagnosticDescriptor Captured = Error("CSV0003", Linearity,
            "Linear value captured",
            "Linear value '{0}' cannot be captured by a lambda or local function");

        public static readonly DiagnosticDescriptor Copied = Error("CSV0004", Linearity,
            "Linear value copied or stored",
            "Linear value cannot be {0}");

        public static readonly DiagnosticDescriptor BorrowConsumed = Error("CSV0005", Linearity,
            "Borrowed linear value consumed",
            "'{0}' is borrowed (ref/in) and cannot be consumed");

        public static readonly DiagnosticDescriptor Forged = Error("CSV0006", Linearity,
            "Linear value created from nothing",
            "A value of linear type '{0}' can only be created by [Trusted] code");

        public static readonly DiagnosticDescriptor GhostOutsideSpec = Error("CSV0010", Ghosts,
            "Ghost value read outside a specification",
            "'{0}' is ghost and can only be used inside Spec.* arguments, lemma arguments or lemma bodies");

        public static readonly DiagnosticDescriptor BadLemma = Error("CSV0011", Ghosts,
            "Malformed lemma",
            "Lemma '{0}' must return void and be marked [Conditional(\"CSVERIFY_SPEC\")]");

        public static readonly DiagnosticDescriptor ResultOutsideEnsures = Error("CSV0012", Ghosts,
            "Spec.Result/Spec.Old outside a postcondition",
            "'{0}' can only be used inside Spec.Ensures");
    }
}
