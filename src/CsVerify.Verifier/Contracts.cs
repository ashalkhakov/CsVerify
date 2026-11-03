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
        /// <summary>
        /// For a postcondition inherited by an override that weakened the precondition: the base's preconditions,
        /// under which alone the base promised it (evaluated in the entry state).
        /// </summary>
        public IReadOnlyList<IOperation> Guard;
    }

    /// <summary>A method's contract, read from the Spec.* statements at the top level of its body.</summary>
    public sealed class Contract
    {
        public IMethodSymbol Method;
        public SyntaxNode Declaration;
        public SemanticModel Model;
        /// <summary>The effective precondition: the method's own, or else the one it inherits.</summary>
        public readonly List<IOperation> Requires = new List<IOperation>();
        /// <summary>The effective postcondition: its own and everything it inherits.</summary>
        public readonly List<Postcondition> Ensures = new List<Postcondition>();
        /// <summary>The preconditions written on this method itself (or its contract class).</summary>
        public readonly List<IOperation> OwnRequires = new List<IOperation>();
        /// <summary>The members it overrides or implements (their effective contracts), which it must honour.</summary>
        public readonly List<Contract> Bases = new List<Contract>();
        /// <summary>The frames (Spec.Modifies) of the members it overrides: its own frame must lie within each.</summary>
        public readonly List<(Contract Base, IOperation Frame)> BaseModifies = new List<(Contract, IOperation)>();
        /// <summary>Methods whose parameters stand for this one's in the specifications (a contract class's method, bases).</summary>
        public readonly List<IMethodSymbol> Aliases = new List<IMethodSymbol>();
        /// <summary>The termination measure's components, compared lexicographically; null without Spec.Decreases.</summary>
        public IReadOnlyList<IOperation> Decreases;
        /// <summary>Spec.Modifies: the objects whose fields the method may write (besides those it allocates); null if none given.</summary>
        public IOperation Modifies;
        /// <summary>Spec.Reads: the objects whose fields a [Pure] function may read; null if none given.</summary>
        public IOperation Reads;
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
                if (c.IsPure && !c.IsTrusted) c.PureBody = c.Model.GetOperation(exprBody);
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
                        case "Requires": c.Requires.Add(arg); c.OwnRequires.Add(arg); continue;
                        case "Decreases": c.Decreases = op.Arguments.Select(a => a.Value).ToList(); continue;
                        case "Ensures": c.Ensures.Add(ReadEnsures(arg, inv)); continue;
                        case "Modifies": c.Modifies = arg; continue;
                        case "Reads": c.Reads = arg; continue;
                    }
                }
                rest.Add(stmt);
            }
            if (c.IsPure && !c.IsTrusted && rest.Count == 1 && rest[0] is ReturnStatementSyntax ret && ret.Expression != null)
                c.PureBody = c.Model.GetOperation(ret.Expression);
            return c;
        }

        /// <summary>
        /// Adds what a member without a body (interface, abstract) declares in its contract class, and what an override
        /// or implementation inherits: the base's postconditions always, its precondition when it gives none of its own.
        /// </summary>
        internal void Inherit(Contract contractClassMethod, IEnumerable<Contract> bases)
        {
            if (contractClassMethod != null)
            {
                Requires.AddRange(contractClassMethod.Requires);
                OwnRequires.AddRange(contractClassMethod.Requires);
                Ensures.AddRange(contractClassMethod.Ensures);
                Modifies ??= contractClassMethod.Modifies;
                Reads ??= contractClassMethod.Reads;
                Aliases.Add(contractClassMethod.Method);
            }
            foreach (var b in bases)
            {
                Bases.Add(b);
                Aliases.Add(b.Method);
                Aliases.AddRange(b.Aliases);
                bool weakened = OwnRequires.Count > 0 && b.Requires.Count > 0;
                foreach (var post in b.Ensures)
                    Ensures.Add(weakened && post.Guard == null
                        ? new Postcondition { Expr = post.Expr, ResultParameter = post.ResultParameter, Syntax = post.Syntax, Guard = b.Requires }
                        : post);
                if (OwnRequires.Count == 0 && Requires.Count == 0) Requires.AddRange(b.Requires);
                if (b.Modifies != null) BaseModifies.Add((b, b.Modifies));
                Modifies ??= b.Modifies;
                Reads ??= b.Reads;
            }
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
