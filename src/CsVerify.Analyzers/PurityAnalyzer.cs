using System.Collections.Immutable;
using System.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.Diagnostics;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Analyzers
{
    /// <summary>
    /// Proofs and specifications are side-effect free. The verifier relies on it: a lemma or [Pure] call is assumed
    /// to leave the heap alone, and a specification argument, erased from the program, must not change the state the
    /// verifier reasons about. Ghost and pure code may assign only its own locals and value parameters, may call only
    /// lemmas, pure functions and the spec library, and does not allocate.
    /// </summary>
    [DiagnosticAnalyzer(LanguageNames.CSharp)]
    public sealed class PurityAnalyzer : DiagnosticAnalyzer
    {
        public override ImmutableArray<DiagnosticDescriptor> SupportedDiagnostics => ImmutableArray.Create(Descriptors.ImpureGhost);

        public override void Initialize(AnalysisContext context)
        {
            context.ConfigureGeneratedCodeAnalysis(GeneratedCodeAnalysisFlags.None);
            context.EnableConcurrentExecution();
            context.RegisterSymbolAction(CheckSignature, SymbolKind.Method);
            context.RegisterOperationAction(CheckWrite,
                OperationKind.SimpleAssignment, OperationKind.CompoundAssignment, OperationKind.CoalesceAssignment,
                OperationKind.Increment, OperationKind.Decrement, OperationKind.DeconstructionAssignment);
            context.RegisterOperationAction(CheckCall, OperationKind.Invocation);
            context.RegisterOperationAction(CheckAllocation,
                OperationKind.ObjectCreation, OperationKind.ArrayCreation, OperationKind.AnonymousObjectCreation, OperationKind.TypeParameterObjectCreation);
        }

        private static void Report(OperationAnalysisContext context, IOperation op, string what) =>
            context.ReportDiagnostic(Diagnostic.Create(Descriptors.ImpureGhost, op.Syntax.GetLocation(), what));

        /// <summary>A pure function's result depends on its arguments only: no ref/out parameters.</summary>
        private static void CheckSignature(SymbolAnalysisContext context)
        {
            var m = (IMethodSymbol)context.Symbol;
            if (!SpecSymbols.IsProofMethod(m) || SpecSymbols.IsTrusted(m))
            {
                return;
            }
            // a lemma or ghost function is one fixed proof or definition; a [Pure] query may be virtual (its overrides
            // are [Pure] too, and honour its contract)
            if ((SpecSymbols.IsLemma(m) || SpecSymbols.IsGhostFunction(m)) &&
                (m.IsVirtual || m.IsAbstract || m.IsOverride || m.ContainingType?.TypeKind == TypeKind.Interface))
            {
                context.ReportDiagnostic(Diagnostic.Create(Descriptors.ImpureGhost, m.Locations.FirstOrDefault(),
                    $"'{m.Name}' is virtual, abstract or an interface member; a lemma or ghost function must have one fixed body"));
            }
            foreach (var p in m.Parameters.Where(p => p.RefKind == RefKind.Ref || p.RefKind == RefKind.Out))
            {
                context.ReportDiagnostic(Diagnostic.Create(Descriptors.ImpureGhost, p.Locations.FirstOrDefault(),
                    $"'{p.Name}' is passed by {(p.RefKind == RefKind.Ref ? "ref" : "out")}"));
            }
        }

        private static void CheckWrite(OperationAnalysisContext context)
        {
            var op = context.Operation;
            if (!SpecSymbols.MustBePure(op.Syntax, op.SemanticModel))
            {
                return;
            }
            IOperation target;
            switch (op)
            {
                case IAssignmentOperation a:
                    target = a.Target;
                    break;
                case IIncrementOrDecrementOperation inc:
                    target = inc.Target;
                    break;
                default: return;
            }
            var member = SpecSymbols.EnclosingMember(op.Syntax, op.SemanticModel);
            foreach (var t in Targets(target))
            {
                // a proof method's own locals and value parameters are its scratch space; nothing else is
                bool own = SpecSymbols.IsProofMethod(member) &&
                           (t is ILocalReferenceOperation || (t is IParameterReferenceOperation p && p.Parameter.RefKind == RefKind.None));
                if (!own && !(t is IDiscardOperation))
                {
                    Report(context, op, $"assignment to '{t.Syntax}'");
                }
            }
        }

        private static System.Collections.Generic.IEnumerable<IOperation> Targets(IOperation target)
        {
            if (target is IDeclarationExpressionOperation d)
            {
                target = d.Expression;
            }
            if (target is ITupleOperation tuple)
            {
                foreach (var e in tuple.Elements)
                {
                    foreach (var t in Targets(e))
                    {
                        yield return t;
                    }
                }
            }
            else
            {
                yield return target;
            }
        }

        private static void CheckCall(OperationAnalysisContext context)
        {
            var op = (IInvocationOperation)context.Operation;
            if (!SpecSymbols.MustBePure(op.Syntax, op.SemanticModel))
            {
                return;
            }
            // (a query of LINQ to Objects, which its comprehension defines: it reads its source and calls what it is
            // handed, so it has the effects of those. A lambda's body is checked where it is written; a method handed
            // over by name is called, so it is checked as a call of it would be)
            if (ContractStubs.For(op.SemanticModel.Compilation).QueryOf(op.TargetMethod) != null)
            {
                foreach (var handed in op.Arguments.Select(a => Unconverted(a.Value)).OfType<IDelegateCreationOperation>().Select(d => d.Target).OfType<IMethodReferenceOperation>())
                {
                    if (!Function(handed.Method, op))
                    {
                        Report(context, handed, $"'{handed.Method.Name}' handed to '{op.TargetMethod.Name}', which calls it, is not a lemma or [Pure]");
                    }
                }
                return;
            }
            // (or a method of one expression with no effects: a function without saying so)
            if (!Function(op.TargetMethod, op) && SpecSymbols.GenericLaw(op, out _) == null && !EntryRead(op.TargetMethod))
            {
                Report(context, op, $"call to '{op.TargetMethod.Name}', which is not a lemma or [Pure]");
            }
        }

        private static bool Function(IMethodSymbol m, IOperation at) =>
            SpecSymbols.IsPureCallee(m) || ContractStubs.For(at.SemanticModel.Compilation).IsPureMember(m) || SpecSymbols.IsTickArithmetic(m) ||
            ExpressionFunctions.Inferred(m, at.SemanticModel.Compilation);

        private static IOperation Unconverted(IOperation o)
        {
            while (o is IConversionOperation c)
            {
                o = c.Operand;
            }
            return o;
        }

        /// <summary>EF's DbContext.Entry and an entry's Property: an entry read, as the verifier models them (Lowering.EfEntries).</summary>
        private static bool EntryRead(IMethodSymbol m) =>
            m.Name == "Entry" && m.ContainingType?.ToDisplayString() == "Microsoft.EntityFrameworkCore.DbContext" ||
            m.Name == "Property" && m.ContainingType is { Name: "EntityEntry" } t && t.ContainingNamespace?.ToDisplayString() == "Microsoft.EntityFrameworkCore.ChangeTracking";

        private static void CheckAllocation(OperationAnalysisContext context)
        {
            var op = context.Operation;
            if (!SpecSymbols.MustBePure(op.Syntax, op.SemanticModel))
            {
                return;
            }
            // building an immutable value (a positional record) is not an effect: it is a data constructor
            if (op is IObjectCreationOperation oc && oc.Initializer == null && SpecSymbols.IsValueRecord(oc.Type))
            {
                return;
            }
            // an exception made to be thrown: where a [Pure] member throws it has no value, so nothing sees the object
            for (var parent = op.Parent; parent != null; parent = parent.Parent)
            {
                if (parent is IThrowOperation)
                {
                    return;
                }
                if (!(parent is IConversionOperation || parent is IParenthesizedOperation || parent is IArgumentOperation || parent is IObjectCreationOperation ||
                      parent is IInterpolatedStringOperation || parent is IInterpolationOperation))
                {
                    break;
                }
            }
            Report(context, op, $"allocation '{op.Syntax}'");
        }
    }
}
