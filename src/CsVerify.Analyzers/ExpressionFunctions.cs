using System.Collections.Generic;
using System.Linq;
using System.Runtime.CompilerServices;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Analyzers
{
    /// <summary>
    /// Expression functions (SPARK's): a member of the program whose body is one expression with no effects (a getter,
    /// a method, an operator) is a function of the state without saying so, and is taken as [Pure]: its expression is
    /// its definition, known where code calls it and where a specification reads it. Such a member can state no
    /// contract (a contract is a statement), so its expression is all there is to know of it. The expression: fields
    /// and such members read, operators, conditionals, patterns, [Pure] calls, and throw expressions (what a throw is
    /// handed isn't part of the function's value). Not a member an override may answer for, nor one that reads itself.
    /// </summary>
    public static class ExpressionFunctions
    {
        private static readonly ConditionalWeakTable<Compilation, HashSet<ISymbol>> _inferred = new ConditionalWeakTable<Compilation, HashSet<ISymbol>>();

        /// <summary>A member taken as [Pure]: its body is an expression with no effects.</summary>
        public static bool Inferred(IMethodSymbol m, Compilation compilation) =>
            Member(m) is ISymbol s && s.DeclaringSyntaxReferences.Length > 0 && _inferred.GetValue(compilation, Read).Contains(s);

        /// <summary>What a method is the code of, as kept here: a getter's property, or the method or operator itself.</summary>
        private static ISymbol Member(IMethodSymbol m) =>
            m.MethodKind == MethodKind.PropertyGet ? (m.AssociatedSymbol as IPropertySymbol)?.OriginalDefinition
            : m.MethodKind is MethodKind.Ordinary or MethodKind.UserDefinedOperator or MethodKind.Conversion ? (m.ReducedFrom ?? m).OriginalDefinition
            : null;

        /// <summary>A member computed by its code, which nothing says is [Pure]; not one an override may answer for.</summary>
        private static bool Candidate(ISymbol s) =>
            s != null && !s.IsAbstract && !s.IsVirtual && !s.IsOverride && !s.IsExtern && Body(s) != null &&
            s.ContainingType is { TypeKind: not TypeKind.Interface } && s.ContainingNamespace?.ToDisplayString() != SpecSymbols.Namespace &&
            s switch
            {
                IPropertySymbol p => !p.IsIndexer && p.ExplicitInterfaceImplementations.Length == 0 && p.GetMethod != null &&
                                     !SpecSymbols.IsPure(p) && !SpecSymbols.IsPure(p.GetMethod),
                // (of values given and a value returned; a proof's method, or one the program vouches for, is what it says)
                IMethodSymbol m => m.ExplicitInterfaceImplementations.Length == 0 && !m.ReturnsVoid && !m.IsAsync &&
                                   m.Parameters.All(x => x.RefKind == RefKind.None) && !SpecSymbols.IsProofMethod(m) && !SpecSymbols.IsTrusted(m) &&
                                   !SpecSymbols.IsGhostMethod(m),
                _ => false,
            };

        /// <summary>A member's body where it is one expression: => e, get => e, or { return e; }.</summary>
        private static ExpressionSyntax Body(ISymbol s)
        {
            if (s.DeclaringSyntaxReferences.Length != 1)
            {
                return null;
            }
            switch (s.DeclaringSyntaxReferences[0].GetSyntax())
            {
                case PropertyDeclarationSyntax p:
                {
                    var get = p.AccessorList?.Accessors.FirstOrDefault(a => a.IsKind(SyntaxKind.GetAccessorDeclaration));
                    return p.ExpressionBody?.Expression ?? get?.ExpressionBody?.Expression ?? Returned(get?.Body);
                }
                case BaseMethodDeclarationSyntax m when m is MethodDeclarationSyntax or OperatorDeclarationSyntax or ConversionOperatorDeclarationSyntax:
                    return m.ExpressionBody?.Expression ?? Returned(m.Body);
                default:
                    return null;
            }
        }

        private static ExpressionSyntax Returned(BlockSyntax block) =>
            block is { Statements: { Count: 1 } statements } && statements[0] is ReturnStatementSyntax ret ? ret.Expression : null;

        private static HashSet<ISymbol> Read(Compilation compilation)
        {
            var inferred = new HashSet<ISymbol>(SymbolEqualityComparer.Default);
            var refused = new HashSet<ISymbol>(SymbolEqualityComparer.Default);
            // (the program's trees: a referenced project's too, whose code is the program's)
            foreach (var tree in compilation.ProgramTrees())
            {
                SemanticModel model = null;
                foreach (var d in tree.GetRoot().DescendantNodes().Where(n => n is PropertyDeclarationSyntax || n is BaseMethodDeclarationSyntax))
                {
                    // (only the declarations that may be one are looked up)
                    bool expression = d switch
                    {
                        PropertyDeclarationSyntax p => p.ExpressionBody != null || p.AccessorList?.Accessors.Any(a => a.Body != null || a.ExpressionBody != null) == true,
                        BaseMethodDeclarationSyntax m => m.ExpressionBody != null || Returned(m.Body) != null,
                        _ => false,
                    };
                    if (!expression)
                    {
                        continue;
                    }
                    model ??= compilation.ModelOf(tree);
                    var s = model.GetDeclaredSymbol(d) switch
                    {
                        IPropertySymbol p => (ISymbol)p.OriginalDefinition,
                        IMethodSymbol m => Member(m),
                        _ => null,
                    };
                    if (Candidate(s))
                    {
                        Infer(s, compilation, inferred, refused, new HashSet<ISymbol>(SymbolEqualityComparer.Default));
                    }
                }
            }
            return inferred;
        }

        /// <summary>Is the member's body an expression with no effects (the members it reads such, or [Pure], in turn)?</summary>
        private static bool Infer(ISymbol p, Compilation compilation, HashSet<ISymbol> inferred, HashSet<ISymbol> refused, HashSet<ISymbol> visiting)
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
            // (an operator of the language's, or one the compiler writes (a record's ==); a library's, as its getters; the program's: a function)
            bool Operator(IMethodSymbol m) => m == null || m.IsImplicitlyDeclared || m.DeclaringSyntaxReferences.Length == 0 || Function(m, compilation, inferred, refused, visiting);
            // (arithmetic that throws where it overflows: a checked operation, an integer's / or % by what may be -1 or
            // zero, Math.Abs. In code the path ends there, or the failure is reported; a function of it would have to
            // show it can't happen)
            if (op is IBinaryOperation { IsChecked: true } || op is IUnaryOperation { IsChecked: true } || op is IConversionOperation { IsChecked: true } ||
                op is IBinaryOperation { OperatorMethod: null, OperatorKind: BinaryOperatorKind.Divide or BinaryOperatorKind.Remainder } division &&
                    division.Type is { SpecialType: >= SpecialType.System_SByte and <= SpecialType.System_UInt64 } &&
                    !(division.RightOperand.ConstantValue is { HasValue: true, Value: var by } && System.Convert.ToDecimal(by) is not (0m or -1m)) ||
                op is IInvocationOperation { TargetMethod: { Name: "Abs", ContainingType: { Name: "Math", ContainingNamespace.Name: "System" } } abs } &&
                    abs.ReturnType is { SpecialType: >= SpecialType.System_SByte and <= SpecialType.System_UInt64 })
            {
                return false;
            }
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
                case IUnaryOperation { OperatorMethod: var um }:
                    if (!Operator(um))
                    {
                        return false;
                    }
                    break;
                case IBinaryOperation { OperatorMethod: var bm }:
                    if (!Operator(bm))
                    {
                        return false;
                    }
                    break;
                case IConversionOperation { OperatorMethod: var cm }:
                    if (!Operator(cm))
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
                    if (!Function(call.TargetMethod, compilation, inferred, refused, visiting))
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
                         !(d is IInvocationOperation { TargetMethod: var called } && called.DeclaringSyntaxReferences.Length > 0 &&
                           !Function(called, compilation, inferred, refused, visiting) && !Builds(called.OriginalDefinition, compilation, inferred, refused, visiting, helpers)) &&
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

        /// <summary>A function: a proof's, a library's with a [Pure] contract, or a member of the program taken as one here.</summary>
        private static bool Function(IMethodSymbol called, Compilation compilation, HashSet<ISymbol> inferred, HashSet<ISymbol> refused, HashSet<ISymbol> visiting) =>
            SpecSymbols.IsPureCallee(called) || ContractStubs.For(compilation).IsPureMember(called) ||
            Member(called) is ISymbol s && Candidate(s) && Infer(s, compilation, inferred, refused, visiting);
    }
}
