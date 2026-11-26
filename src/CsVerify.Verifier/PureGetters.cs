using System.Collections.Generic;
using System.Linq;
using System.Runtime.CompilerServices;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Purity inferred for getters. A property of the program whose getter is one expression with no effects is a
    /// function of the state without saying so, and is taken as [Pure]: its expression is its definition, known where
    /// code reads it and where a specification does (SPARK's expression functions; Code Contracts takes every getter
    /// so, here its body is looked at). Such a getter can state no contract (a contract is a statement), so its
    /// expression is all there is to know of it. The expression: fields and such properties read, operators,
    /// conditionals, patterns, [Pure] calls, and throw expressions (what a throw is handed isn't part of the function's
    /// value).
    /// </summary>
    internal static class PureGetters
    {
        private static readonly ConditionalWeakTable<Compilation, HashSet<ISymbol>> _inferred = new ConditionalWeakTable<Compilation, HashSet<ISymbol>>();

        /// <summary>A getter taken as [Pure]: its body is an expression with no effects.</summary>
        public static bool Inferred(IMethodSymbol m, Compilation compilation) =>
            m.MethodKind == MethodKind.PropertyGet && m.AssociatedSymbol is IPropertySymbol p && p.DeclaringSyntaxReferences.Length > 0 &&
            _inferred.GetValue(compilation, Read).Contains(p.OriginalDefinition);

        /// <summary>A property computed by its getter's code, which nothing says is [Pure]; not one an override may answer for.</summary>
        private static bool Candidate(IPropertySymbol p) =>
            p != null && !p.IsAbstract && !p.IsVirtual && !p.IsOverride && !p.IsIndexer && p.ExplicitInterfaceImplementations.Length == 0 &&
            p.GetMethod != null && p.DeclaringSyntaxReferences.Length > 0 && Body(p) != null &&
            !SpecSymbols.IsPure(p) && !SpecSymbols.IsPure(p.GetMethod) && p.ContainingNamespace?.ToDisplayString() != SpecSymbols.Namespace;

        /// <summary>A getter's body where it is one expression: => e, get => e, or get { return e; }.</summary>
        private static ExpressionSyntax Body(IPropertySymbol p)
        {
            if (p.DeclaringSyntaxReferences.Length != 1 || !(p.DeclaringSyntaxReferences[0].GetSyntax() is PropertyDeclarationSyntax decl))
            {
                return null;
            }
            if (decl.ExpressionBody != null)
            {
                return decl.ExpressionBody.Expression;
            }
            var get = decl.AccessorList?.Accessors.FirstOrDefault(a => a.IsKind(SyntaxKind.GetAccessorDeclaration));
            return get?.ExpressionBody?.Expression ?? (get?.Body is { Statements: { Count: 1 } statements } && statements[0] is ReturnStatementSyntax ret ? ret.Expression : null);
        }

        private static HashSet<ISymbol> Read(Compilation compilation)
        {
            var inferred = new HashSet<ISymbol>(SymbolEqualityComparer.Default);
            var refused = new HashSet<ISymbol>(SymbolEqualityComparer.Default);
            // (the program's trees: a referenced project's too, whose code is the program's)
            foreach (var tree in compilation.ProgramTrees())
            {
                SemanticModel model = null;
                foreach (var d in tree.GetRoot().DescendantNodes().OfType<PropertyDeclarationSyntax>())
                {
                    if (d.ExpressionBody == null && d.AccessorList?.Accessors.Any(a => a.Body != null || a.ExpressionBody != null) != true)
                    {
                        continue;
                    }
                    model ??= compilation.ModelOf(tree);
                    if (model.GetDeclaredSymbol(d) is IPropertySymbol p && Candidate(p.OriginalDefinition))
                    {
                        Infer(p.OriginalDefinition, compilation, inferred, refused, new HashSet<ISymbol>(SymbolEqualityComparer.Default));
                    }
                }
            }
            return inferred;
        }

        /// <summary>Is the property's getter an expression with no effects (the properties it reads such, or [Pure], in turn)?</summary>
        private static bool Infer(IPropertySymbol p, Compilation compilation, HashSet<ISymbol> inferred, HashSet<ISymbol> refused, HashSet<ISymbol> visiting)
        {
            if (inferred.Contains(p))
            {
                return true;
            }
            // (one that reads itself: no function's definition)
            if (refused.Contains(p) || !visiting.Add(p))
            {
                return false;
            }
            var body = Body(p);
            var op = compilation.ModelOf(body.SyntaxTree).GetOperation(body);
            bool pure = op != null && NoEffects(op, compilation, inferred, refused, visiting);
            visiting.Remove(p);
            (pure ? inferred : refused).Add(p);
            return pure;
        }

        private static bool NoEffects(IOperation op, Compilation compilation, HashSet<ISymbol> inferred, HashSet<ISymbol> refused, HashSet<ISymbol> visiting)
        {
            switch (op)
            {
                // (what a throw is handed is evaluated where the function has no value: an exception made, a message
                // formatted; but it writes nothing a caller that catches it would see)
                case IThrowOperation:
                    return WritesNothing(op.Descendants(), compilation, inferred, refused, visiting, new HashSet<ISymbol>(SymbolEqualityComparer.Default));
                case ILiteralOperation: case IInstanceReferenceOperation: case IParameterReferenceOperation: case ILocalReferenceOperation:
                case IDefaultValueOperation: case INameOfOperation: case ITypeOfOperation: case IConditionalAccessInstanceOperation:
                case IPatternOperation: case IPropertySubpatternOperation: case IDiscardOperation: case IDeclarationExpressionOperation:
                    break;
                case IFieldReferenceOperation: case IParenthesizedOperation: case IConditionalOperation: case ICoalesceOperation:
                case IConditionalAccessOperation: case IIsTypeOperation: case IIsPatternOperation: case ISwitchExpressionOperation:
                case ISwitchExpressionArmOperation: case ITupleOperation: case IArrayElementReferenceOperation:
                    break;
                // (an immutable value built: a term, as a data constructor's is)
                case IObjectCreationOperation { Initializer: null } made when SpecSymbols.IsValueRecord(made.Type):
                    break;
                case IArgumentOperation:
                    break;
                // (an operator of the language's, or one the compiler writes (a record's ==); a library's, as its getters)
                case IUnaryOperation { OperatorMethod: var um }:
                    if (!OperatorWithoutEffects(um))
                    {
                        return false;
                    }
                    break;
                case IBinaryOperation { OperatorMethod: var bm }:
                    if (!OperatorWithoutEffects(bm))
                    {
                        return false;
                    }
                    break;
                case IConversionOperation { OperatorMethod: var cm }:
                    if (!OperatorWithoutEffects(cm))
                    {
                        return false;
                    }
                    break;
                // (a field's: an auto-property; a library's getter; the program's: [Pure], or such an expression itself)
                case IPropertyReferenceOperation pr:
                {
                    var q = pr.Property.OriginalDefinition;
                    // (a library's static one, DateTime.UtcNow: no function of the program's state)
                    if (q.IsStatic && q.DeclaringSyntaxReferences.Length == 0)
                    {
                        return false;
                    }
                    if (Computed(q) && !PureOrInferred(q, compilation, inferred, refused, visiting))
                    {
                        return false;
                    }
                    break;
                }
                case IInvocationOperation call:
                    if (!SpecSymbols.IsPureCallee(call.TargetMethod) && !ContractStubs.For(compilation).IsPureMember(call.TargetMethod))
                    {
                        return false;
                    }
                    break;
                default:
                    return false;
            }
            return op.ChildOperations.All(c => NoEffects(c, compilation, inferred, refused, visiting));
        }

        /// <summary>
        /// What a throw is handed, written out: no assignment, nothing awaited or deferred, and each method of the
        /// program it calls is a function, or a helper that builds the exception, whose own body is such in turn
        /// (private InvalidOperationException Missing(string what) => new($"No {what}.")).
        /// </summary>
        private static bool WritesNothing(IEnumerable<IOperation> ops, Compilation compilation, HashSet<ISymbol> inferred, HashSet<ISymbol> refused, HashSet<ISymbol> visiting, HashSet<ISymbol> helpers) =>
            ops.All(d => !(d is IAssignmentOperation || d is IIncrementOrDecrementOperation || d is IAwaitOperation ||
                           d is IAnonymousFunctionOperation || d is IDelegateCreationOperation) &&
                         !(d is IInvocationOperation { TargetMethod: var called } && called.DeclaringSyntaxReferences.Length > 0 && !SpecSymbols.IsPureCallee(called) &&
                           !Builds(called.OriginalDefinition, compilation, inferred, refused, visiting, helpers)) &&
                         !(d is IPropertyReferenceOperation { Property: var read } && Computed(read.OriginalDefinition) &&
                           !PureOrInferred(read.OriginalDefinition, compilation, inferred, refused, visiting)));

        /// <summary>A method of the program whose body writes nothing: not one an override may answer for, nor one that calls itself.</summary>
        private static bool Builds(IMethodSymbol m, Compilation compilation, HashSet<ISymbol> inferred, HashSet<ISymbol> refused, HashSet<ISymbol> visiting, HashSet<ISymbol> helpers)
        {
            if (m.IsAbstract || m.IsVirtual || m.IsOverride || m.Parameters.Any(x => x.RefKind != RefKind.None) || m.DeclaringSyntaxReferences.Length != 1 ||
                !(m.DeclaringSyntaxReferences[0].GetSyntax() is MethodDeclarationSyntax decl) || !helpers.Add(m))
            {
                return false;
            }
            var body = (SyntaxNode)decl.Body ?? decl.ExpressionBody?.Expression;
            return body != null && compilation.ModelOf(body.SyntaxTree).GetOperation(body) is IOperation op &&
                   WritesNothing(op.DescendantsAndSelf(), compilation, inferred, refused, visiting, helpers);
        }

        /// <summary>A property of the program's that its getter's code computes (no auto-property, no positional one).</summary>
        private static bool Computed(IPropertySymbol q) =>
            q.DeclaringSyntaxReferences.Any(r => r.GetSyntax() is PropertyDeclarationSyntax d &&
                                                 (d.ExpressionBody != null || d.AccessorList?.Accessors.Any(a => a.Body != null || a.ExpressionBody != null) == true));

        private static bool PureOrInferred(IPropertySymbol q, Compilation compilation, HashSet<ISymbol> inferred, HashSet<ISymbol> refused, HashSet<ISymbol> visiting) =>
            SpecSymbols.IsPure(q) || q.GetMethod != null && SpecSymbols.IsPure(q.GetMethod) || Candidate(q) && Infer(q, compilation, inferred, refused, visiting);

        private static bool OperatorWithoutEffects(IMethodSymbol m) =>
            m == null || m.IsImplicitlyDeclared || m.DeclaringSyntaxReferences.Length == 0 || SpecSymbols.IsPure(m);
    }
}
