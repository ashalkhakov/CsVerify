using System.Collections.Immutable;
using System.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Diagnostics;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Analyzers
{
    /// <summary>Ghost hygiene: ghost values stay inside specifications, lemmas are erasable proof functions.</summary>
    [DiagnosticAnalyzer(Microsoft.CodeAnalysis.LanguageNames.CSharp)]
    public sealed class GhostAnalyzer : DiagnosticAnalyzer
    {
        public override ImmutableArray<DiagnosticDescriptor> SupportedDiagnostics =>
            ImmutableArray.Create(Descriptors.GhostOutsideSpec, Descriptors.BadLemma, Descriptors.ResultOutsideEnsures);

        public override void Initialize(AnalysisContext context)
        {
            context.ConfigureGeneratedCodeAnalysis(GeneratedCodeAnalysisFlags.None);
            context.EnableConcurrentExecution();
            context.RegisterSymbolAction(CheckLemma, SymbolKind.Method);
            context.RegisterOperationAction(CheckGhostRead, OperationKind.PropertyReference);
            context.RegisterOperationAction(CheckSpecFunction, OperationKind.Invocation);
        }

        private static void CheckLemma(SymbolAnalysisContext context)
        {
            var method = (IMethodSymbol)context.Symbol;
            if (!SpecSymbols.IsLemma(method)) return;
            bool conditional = method.GetAttributes().Any(a =>
                a.AttributeClass?.ToDisplayString() == "System.Diagnostics.ConditionalAttribute" &&
                a.ConstructorArguments.Length == 1 && (a.ConstructorArguments[0].Value as string) == SpecSymbols.SpecSymbol);
            if (!method.ReturnsVoid || !conditional)
                context.ReportDiagnostic(Diagnostic.Create(Descriptors.BadLemma, method.Locations.FirstOrDefault(), method.Name));
        }

        private static void CheckGhostRead(OperationAnalysisContext context)
        {
            var op = (IPropertyReferenceOperation)context.Operation;
            bool ghostRead = op.Property.Name == "Value" && SpecSymbols.IsGhostType(op.Property.ContainingType);
            if (!ghostRead && !SpecSymbols.IsSeqType(op.Property.ContainingType)) return;
            if (!SpecSymbols.IsInGhostContext(op.Syntax, op.SemanticModel))
                context.ReportDiagnostic(Diagnostic.Create(Descriptors.GhostOutsideSpec, op.Syntax.GetLocation(), op.Syntax.ToString()));
        }

        private static void CheckSpecFunction(OperationAnalysisContext context)
        {
            var op = (IInvocationOperation)context.Operation;
            var m = op.TargetMethod;
            if (SpecSymbols.IsSeqType(m.ContainingType) || SpecSymbols.IsGhostFunction(m.OriginalDefinition))
            {
                if (!SpecSymbols.IsInGhostContext(op.Syntax, op.SemanticModel))
                    context.ReportDiagnostic(Diagnostic.Create(Descriptors.GhostOutsideSpec, op.Syntax.GetLocation(), m.Name));
                return;
            }
            if (!SpecSymbols.IsSpecClass(m.ContainingType)) return;
            if (m.Name == "Forall" || m.Name == "Exists")
            {
                if (!SpecSymbols.IsInGhostContext(op.Syntax, op.SemanticModel))
                    context.ReportDiagnostic(Diagnostic.Create(Descriptors.GhostOutsideSpec, op.Syntax.GetLocation(), "Spec." + m.Name));
                return;
            }
            if (m.Name != "Result" && m.Name != "Old") return;
            var call = SpecSymbols.EnclosingSpecCall(op.Syntax, op.SemanticModel);
            var where = call != null && op.SemanticModel.GetSymbolInfo(call).Symbol is IMethodSymbol spec ? spec.Name : null;
            bool allowed = where == "Ensures" || (m.Name == "Old" && (where == "Invariant" || where == "Assert"));
            if (!allowed)
                context.ReportDiagnostic(Diagnostic.Create(Descriptors.ResultOutsideEnsures, op.Syntax.GetLocation(), "Spec." + m.Name));
        }
    }
}
