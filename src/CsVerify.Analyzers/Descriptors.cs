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
            "'{0}' is a read-only borrow (in) and cannot be consumed");

        public static readonly DiagnosticDescriptor Forged = Error("CSV0006", Linearity,
            "Linear value created from nothing",
            "A value of linear type '{0}' can only be created by [Trusted] code");

        public static readonly DiagnosticDescriptor PassedTwice = Error("CSV0007", Linearity,
            "Linear value passed twice in one call",
            "Linear value '{0}' is passed to more than one parameter of this call; only several read-only (in) borrows may share it");

        private const string Disposal = "CsVerify.Disposal";

        public static readonly DiagnosticDescriptor NotDisposed = Error("CSV0020", Disposal,
            "Disposable not disposed",
            "'{0}' ({1}) is not disposed on every path{2}: dispose it (using, Dispose()), return it, or hand it over");

        public static readonly DiagnosticDescriptor UsedAfterDispose = Error("CSV0021", Disposal,
            "Disposable used after it was disposed",
            "'{0}' may already have been disposed{1}");

        public static readonly DiagnosticDescriptor OwnerDoesNotDispose = Error("CSV0022", Disposal,
            "Owned disposable field not disposed",
            "'{0}' holds a {1} that {2} owns, but {3}");

        public static readonly DiagnosticDescriptor GhostOutsideSpec = Error("CSV0010", Ghosts,
            "Ghost value read outside a specification",
            "'{0}' is ghost and can only be used inside Spec.* arguments, lemma arguments or lemma bodies");

        public static readonly DiagnosticDescriptor BadLemma = Error("CSV0011", Ghosts,
            "Malformed lemma",
            "Lemma '{0}' must return void and be marked [Conditional(\"CSVERIFY_SPEC\")]");

        public static readonly DiagnosticDescriptor ResultOutsideEnsures = Error("CSV0012", Ghosts,
            "Spec.Result/Spec.Old outside a postcondition",
            "'{0}' can only be used inside Spec.Ensures (Spec.Old also inside Spec.Invariant and Spec.Assert)");

        public static readonly DiagnosticDescriptor ImpureGhost = Error("CSV0013", Ghosts,
            "Side effect in ghost or pure code",
            "{0}: lemmas, [Pure] and [GhostFunction] bodies and specification arguments must not have side effects");
    }
}
