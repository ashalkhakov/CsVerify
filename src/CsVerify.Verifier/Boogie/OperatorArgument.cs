using System.Collections.Generic;
using System.Collections.Immutable;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>
    /// An operand of a user-defined operator, as the argument of a call of its method: Roslyn has no invocation for
    /// `a + b`, so Lowering calls op_Addition with these. Only Lowering reads them; they never go back to Roslyn.
    /// </summary>
#pragma warning disable RS1009
    internal sealed class OperatorArgument : IArgumentOperation
    {
        public OperatorArgument(IParameterSymbol parameter, IOperation value)
        {
            Parameter = parameter;
            Value = value;
        }

        public ArgumentKind ArgumentKind => ArgumentKind.Explicit;
        public IParameterSymbol Parameter { get; }
        public IOperation Value { get; }
        public CommonConversion InConversion => default;
        public CommonConversion OutConversion => default;
        public IOperation Parent => Value.Parent;
        public OperationKind Kind => OperationKind.Argument;
        public SyntaxNode Syntax => Value.Syntax;
        public ITypeSymbol Type => null;
        public Optional<object> ConstantValue => default;
#pragma warning disable CS0618
        public IEnumerable<IOperation> Children => new[] { Value };
#pragma warning restore CS0618
        public IOperation.OperationList ChildOperations => throw new System.NotSupportedException();
        public string Language => Value.Language;
        public bool IsImplicit => true;
        public SemanticModel SemanticModel => Value.SemanticModel;
        public void Accept(OperationVisitor visitor) => visitor.VisitArgument(this);
        public TResult Accept<TArgument, TResult>(OperationVisitor<TArgument, TResult> visitor, TArgument argument) => visitor.VisitArgument(this, argument);
    }
#pragma warning restore RS1009
}
