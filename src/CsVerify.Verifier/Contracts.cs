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
        /// <summary>Spec.EnsuresOnThrow&lt;E&gt;(cond): what holds if the method exits by throwing an E.</summary>
        public readonly List<(ITypeSymbol exception, IOperation condition, SyntaxNode syntax)> ThrowEnsures = new List<(ITypeSymbol, IOperation, SyntaxNode)>();
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
        /// <summary>
        /// For other [Pure] methods: the body's statements (contract calls removed), from which a definition is read if
        /// they are local declarations, ifs and returns (StaticChecks.PureStatementsTerm).
        /// </summary>
        public IReadOnlyList<IOperation> PureStatements;
        public bool HasSource => Declaration != null;
        /// <summary>
        /// The Invoke of a delegate type with a [ContractClassFor] contract: a call of the delegate proves its precondition
        /// and assumes its postcondition, as for an interface member, and what it may change is anything (its body isn't known).
        /// </summary>
        public bool OfDelegate;
        public bool IsTrusted, IsLemma, IsPure;
        /// <summary>
        /// For an external member with a [ContractsFor] stub: the stub method, whose contract this is (trusted: assumed
        /// at calls, never proved). Its parameters are an alias of the member's, after <c>@this</c> if it has one.
        /// </summary>
        public IMethodSymbol Stub;
        public bool IsStub => Stub != null;
        /// <summary>The stub's <c>@this</c> parameter, which stands for the receiver; null for a static member.</summary>
        public IParameterSymbol StubReceiver;
        /// <summary>
        /// For a [Pure] stub with a postcondition <c>r == E</c> (or <c>Ghost.Of(r) == E</c>, or a conjunct of one): E,
        /// the member's value, used in its place (list[i] is the model's element itself, not a function of it).
        /// </summary>
        public IOperation StubDefinition;
        /// <summary>A stub that promises a fresh result (<c>Spec.Fresh(r)</c>): a returned array is a new one.</summary>
        public bool StubFreshResult;

        /// <summary>The contract an external member gets from its stub.</summary>
        public static Contract ReadStub(IMethodSymbol member, IMethodSymbol stub, Compilation compilation)
        {
            var c = Read(stub, compilation, isStub: true);
            c.Method = member.OriginalDefinition;
            c.Stub = stub.OriginalDefinition;
            if (ContractStubs.TakesReceiver(stub))
            {
                c.StubReceiver = c.Stub.Parameters[0];
            }
            c.Aliases.Add(c.Stub);
            if (c.IsPure)
            {
                c.StubDefinition = c.Ensures.Select(e => Definition(e.Expr, e.ResultParameter)).FirstOrDefault(d => d != null);
            }
            c.StubFreshResult = c.Ensures.Any(e => e.Expr != null && e.Expr.DescendantsAndSelf().OfType<IInvocationOperation>().Any(i =>
                SpecSymbols.IsSpecClass(i.TargetMethod.ContainingType) && i.TargetMethod.Name == "Fresh" && Mentions(i.Arguments[0].Value, e.ResultParameter)));
            return c;
        }

        /// <summary>E, if <paramref name="post"/> is (a conjunction with) <c>r == E</c>, r the result.</summary>
        private static IOperation Definition(IOperation post, IParameterSymbol result)
        {
            post = Unwrap(post);
            if (!(post is IBinaryOperation b))
            {
                return null;
            }
            if (b.OperatorKind == BinaryOperatorKind.ConditionalAnd)
            {
                return Definition(b.LeftOperand, result) ?? Definition(b.RightOperand, result);
            }
            if (b.OperatorKind != BinaryOperatorKind.Equals)
            {
                return null;
            }
            if (IsResult(b.LeftOperand, result) && !Mentions(b.RightOperand, result))
            {
                return b.RightOperand;
            }
            if (IsResult(b.RightOperand, result) && !Mentions(b.LeftOperand, result))
            {
                return b.LeftOperand;
            }
            return null;
        }

        private static bool IsResult(IOperation o, IParameterSymbol result)
        {
            o = Unwrap(o);
            if (o is IInvocationOperation g && SpecSymbols.IsGhostOf(g.TargetMethod))
            {
                o = Unwrap(g.Arguments[0].Value);
            }
            return o is IParameterReferenceOperation p && result != null && SymbolEqualityComparer.Default.Equals(p.Parameter, result) ||
                   o is IInvocationOperation r && SpecSymbols.IsSpecClass(r.TargetMethod.ContainingType) && r.TargetMethod.Name == "Result";
        }

        private static IOperation Unwrap(IOperation o)
        {
            while (o is IConversionOperation conv && conv.IsImplicit)
            {
                o = conv.Operand;
            }
            while (o is IParenthesizedOperation p)
            {
                o = p.Operand;
            }
            return o;
        }

        private static bool Mentions(IOperation o, IParameterSymbol result) =>
            o.DescendantsAndSelf().Any(x => x is IParameterReferenceOperation p && SymbolEqualityComparer.Default.Equals(p.Parameter, result) ||
                                            x is IInvocationOperation r && SpecSymbols.IsSpecClass(r.TargetMethod.ContainingType) && r.TargetMethod.Name == "Result");

        public static Contract Read(IMethodSymbol method, Compilation compilation) => Read(method, compilation, isStub: false);

        private static Contract Read(IMethodSymbol method, Compilation compilation, bool isStub)
        {
            method = method.OriginalDefinition;
            if (method.ReducedFrom != null)
            {
                method = method.ReducedFrom;
            }
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
                case MethodDeclarationSyntax m:
                    block = m.Body;
                    exprBody = m.ExpressionBody?.Expression;
                    break;
                case LocalFunctionStatementSyntax lf:
                    block = lf.Body;
                    exprBody = lf.ExpressionBody?.Expression;
                    break;
                case ConstructorDeclarationSyntax ctor:
                    block = ctor.Body;
                    exprBody = ctor.ExpressionBody?.Expression;
                    break;
                case AccessorDeclarationSyntax acc:
                    block = acc.Body;
                    exprBody = acc.ExpressionBody?.Expression;
                    break;
                case ArrowExpressionClauseSyntax arrow:
                    block = null;
                    exprBody = arrow.Expression;
                    break; // int P => ... // int P => ...
                case AnonymousFunctionExpressionSyntax lambda:
                    block = lambda.Block;
                    exprBody = lambda.ExpressionBody;
                    break; // x => ... // x => ...
                case SyntaxNode clause when method.MethodKind == MethodKind.AnonymousFunction:
                    // a query clause's lambda (select x + y, where p, let y = ...): its expression, without a specification
                    c.Declaration = clause;
                    c.Model = compilation.GetSemanticModel(clause.SyntaxTree);
                    return c;
                default: return c;
            }
            c.Declaration = syntax;
            c.Model = compilation.GetSemanticModel(syntax.SyntaxTree);

            if (exprBody != null)
            {
                if (isStub)
                {
                    return c; // (a stub's body is not a definition)
                } // (a stub's body is not a definition)
                if ((c.IsPure || SpecSymbols.IsPredicate(method)) && !c.IsTrusted)
                {
                    c.PureBody = c.Model.GetOperation(exprBody);
                }
                return c;
            }
            if (block == null)
            {
                return c;
            }

            var rest = new List<StatementSyntax>();
            foreach (var stmt in block.Statements)
            {
                if (stmt is ExpressionStatementSyntax es && es.Expression is InvocationExpressionSyntax inv &&
                    c.Model.GetOperation(inv) is IInvocationOperation op && SpecSymbols.IsSpecClass(op.TargetMethod.ContainingType))
                {
                    var arg = op.Arguments.Length > 0 ? op.Arguments[0].Value : null;
                    switch (op.TargetMethod.Name)
                    {
                        case "Requires":
                            c.Requires.Add(arg);
                            c.OwnRequires.Add(arg);
                            continue;
                        case "Decreases":
                            c.Decreases = op.Arguments.Select(a => a.Value).ToList();
                            continue;
                        case "Ensures":
                            c.Ensures.Add(ReadEnsures(arg, inv));
                            continue;
                        case "EnsuresOnThrow":
                            c.ThrowEnsures.Add((op.TargetMethod.TypeArguments[0], arg, inv));
                            continue;
                        case "Modifies":
                            c.Modifies = arg;
                            continue;
                        case "Reads":
                            c.Reads = arg;
                            continue;
                    }
                }
                rest.Add(stmt);
            }
            // (Spec.Unfold statements before the return only give the definition's checks the predicate's facts)
            if (isStub)
            {
                return c;
            }
            rest.RemoveAll(s => s is ExpressionStatementSyntax es && es.Expression is InvocationExpressionSyntax inv &&
                                c.Model.GetOperation(inv) is IInvocationOperation op && SpecSymbols.IsSpecClass(op.TargetMethod.ContainingType) && op.TargetMethod.Name == "Unfold");
            if ((c.IsPure || SpecSymbols.IsPredicate(method)) && !c.IsTrusted && rest.Count == 1 && rest[0] is ReturnStatementSyntax ret && ret.Expression != null)
            {
                c.PureBody = c.Model.GetOperation(ret.Expression);
            }
            else if (c.IsPure && !c.IsTrusted && rest.Count > 0)
            {
                c.PureStatements = rest.Select(st => c.Model.GetOperation(st)).ToList();
            }
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
                ThrowEnsures.AddRange(contractClassMethod.ThrowEnsures);
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
                {
                    Ensures.Add(weakened && post.Guard == null
                        ? new Postcondition
                        {
                            Expr = post.Expr,
                            ResultParameter = post.ResultParameter,
                            Syntax = post.Syntax,
                            Guard = b.Requires,
                        }
                        : post);
                }
                ThrowEnsures.AddRange(b.ThrowEnsures); // (what the base promises on a throw, every override does)
                if (OwnRequires.Count == 0 && Requires.Count == 0)
                {
                    Requires.AddRange(b.Requires);
                }
                if (b.Modifies != null)
                {
                    BaseModifies.Add((b, b.Modifies));
                }
                Modifies ??= b.Modifies;
                Reads ??= b.Reads;
            }
        }

        private static Postcondition ReadEnsures(IOperation arg, SyntaxNode syntax)
        {
            if (arg is IDelegateCreationOperation dc && dc.Target is IAnonymousFunctionOperation fn)
            {
                var body = fn.Body.Operations.OfType<IReturnOperation>().FirstOrDefault()?.ReturnedValue;
                return new Postcondition
                {
                    Expr = body,
                    ResultParameter = fn.Symbol.Parameters.FirstOrDefault(),
                    Syntax = syntax,
                };
            }
            return new Postcondition
            {
                Expr = arg,
                Syntax = syntax,
            };
        }
    }
}
