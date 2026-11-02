using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>A postcondition: an expression, optionally the body of <c>r =&gt; ...</c> whose parameter is the result.</summary>
    public sealed class Postcondition
    {
        public IOperation Expr;
        public IParameterSymbol ResultParameter;
        public SyntaxNode Syntax;
    }

    /// <summary>A method's contract, read from the Spec.* statements at the top level of its body.</summary>
    public sealed class Contract
    {
        public IMethodSymbol Method;
        public SyntaxNode Declaration;
        public SemanticModel Model;
        public readonly List<IOperation> Requires = new List<IOperation>();
        public readonly List<Postcondition> Ensures = new List<Postcondition>();
        public IOperation Decreases;
        /// <summary>For [Pure] methods whose body is a single return: the returned expression (the definition).</summary>
        public IOperation PureBody;
        public bool HasSource => Declaration != null;
        public bool IsTrusted, IsLemma, IsPure;

        public static Contract Read(IMethodSymbol method, Compilation compilation)
        {
            method = method.OriginalDefinition;
            if (method.ReducedFrom != null) method = method.ReducedFrom;
            var c = new Contract
            {
                Method = method,
                IsTrusted = SpecSymbols.IsTrusted(method),
                IsLemma = SpecSymbols.IsLemma(method),
                IsPure = SpecSymbols.IsPure(method),
            };
            var syntax = method.DeclaringSyntaxReferences.Select(r => r.GetSyntax()).FirstOrDefault();
            BlockSyntax block; ExpressionSyntax exprBody;
            switch (syntax)
            {
                case MethodDeclarationSyntax m: block = m.Body; exprBody = m.ExpressionBody?.Expression; break;
                case LocalFunctionStatementSyntax lf: block = lf.Body; exprBody = lf.ExpressionBody?.Expression; break;
                case ConstructorDeclarationSyntax ctor: block = ctor.Body; exprBody = ctor.ExpressionBody?.Expression; break;
                default: return c;
            }
            c.Declaration = syntax;
            c.Model = compilation.GetSemanticModel(syntax.SyntaxTree);

            if (exprBody != null)
            {
                if (c.IsPure) c.PureBody = c.Model.GetOperation(exprBody);
                return c;
            }
            if (block == null) return c;

            var rest = new List<StatementSyntax>();
            foreach (var stmt in block.Statements)
            {
                if (stmt is ExpressionStatementSyntax es && es.Expression is InvocationExpressionSyntax inv &&
                    c.Model.GetOperation(inv) is IInvocationOperation op && SpecSymbols.IsSpecClass(op.TargetMethod.ContainingType))
                {
                    var arg = op.Arguments.Length > 0 ? op.Arguments[0].Value : null;
                    switch (op.TargetMethod.Name)
                    {
                        case "Requires": c.Requires.Add(arg); continue;
                        case "Decreases": c.Decreases = arg; continue;
                        case "Ensures": c.Ensures.Add(ReadEnsures(arg, inv)); continue;
                    }
                }
                rest.Add(stmt);
            }
            if (c.IsPure && rest.Count == 1 && rest[0] is ReturnStatementSyntax ret && ret.Expression != null)
                c.PureBody = c.Model.GetOperation(ret.Expression);
            return c;
        }

        private static Postcondition ReadEnsures(IOperation arg, SyntaxNode syntax)
        {
            if (arg is IDelegateCreationOperation dc && dc.Target is IAnonymousFunctionOperation fn)
            {
                var body = fn.Body.Operations.OfType<IReturnOperation>().FirstOrDefault()?.ReturnedValue;
                return new Postcondition { Expr = body, ResultParameter = fn.Symbol.Parameters.FirstOrDefault(), Syntax = syntax };
            }
            return new Postcondition { Expr = arg, Syntax = syntax };
        }
    }
}
