using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Code that runs alongside other code with permissions: a call of a method whose contract names them, that isn't awaited
    /// at once, or that is all a delegate of Task.Run or new Thread does. A delegate is verified on its own, knowing nothing,
    /// so it can have no permissions; but if it is just a call, with values already fixed where the delegate is made, the
    /// call can be proved there instead.
    /// </summary>
    internal sealed class StartedDelegates
    {
        private readonly Engine _engine;
        private readonly Compilation _compilation;
        private readonly Dictionary<SyntaxNode, InvocationExpressionSyntax> _calls = new Dictionary<SyntaxNode, InvocationExpressionSyntax>();
        private HashSet<IMethodSymbol> _alongside;

        public StartedDelegates(Engine engine, Compilation compilation)
        {
            _engine = engine;
            _compilation = compilation;
        }

        /// <summary>The call that is all a delegate does, if it can take permissions; null for any other delegate.</summary>
        public InvocationExpressionSyntax CallOf(AnonymousFunctionExpressionSyntax lambda)
        {
            if (_calls.TryGetValue(lambda, out var known)) return known;
            return _calls[lambda] = Find(lambda, _compilation.GetSemanticModel(lambda.SyntaxTree));
        }

        private InvocationExpressionSyntax Find(AnonymousFunctionExpressionSyntax lambda, SemanticModel model)
        {
            if (lambda.ParameterList() > 0 || !(lambda.Parent is ArgumentSyntax arg)) return null;
            bool thread;
            if (arg.Parent?.Parent is InvocationExpressionSyntax run && model.GetSymbolInfo(run).Symbol is IMethodSymbol r && r.Name == "Run" && r.ContainingType?.ToDisplayString() == "System.Threading.Tasks.Task")
                thread = false;
            else if (arg.Parent?.Parent is BaseObjectCreationExpressionSyntax c && model.GetTypeInfo(c).Type?.ToDisplayString() == "System.Threading.Thread" && IsThreadLocal(c, model))
                thread = true;
            else return null;
            var call = TheCall(lambda);
            if (call == null || !(model.GetSymbolInfo(call).Symbol is IMethodSymbol m)) return null;
            if (thread && m.IsAsync) return null; // (it would be over at its first await)
            var contract = _engine.ContractOf(m.OriginalDefinition);
            if (!contract.HasSource || !contract.Requires.Concat(contract.Ensures.Select(e => e.Expr)).Any(e => e != null && e.DescendantsAndSelf().Any(o => MethodVerifier.IsAccCall(o, out _)))) return null;
            var member = lambda.Ancestors().First(a => a is BaseMethodDeclarationSyntax || a is AccessorDeclarationSyntax);
            if (call.Expression is MemberAccessExpressionSyntax ma && !IsFixed(ma.Expression, model, member) && m.IsStatic == false) return null;
            return call.ArgumentList.Arguments.All(a => a.RefKindKeyword.IsKind(SyntaxKind.None) && IsFixed(a.Expression, model, member)) ? call : null;
        }

        /// <summary>F(x), await F(x), { F(x); }, { await F(x); }, { return F(x); }, { return await F(x); }.</summary>
        private static InvocationExpressionSyntax TheCall(AnonymousFunctionExpressionSyntax lambda)
        {
            ExpressionSyntax e = lambda.ExpressionBody;
            if (lambda.Block is BlockSyntax b)
            {
                if (b.Statements.Count != 1) return null;
                e = b.Statements[0] is ExpressionStatementSyntax es ? es.Expression : b.Statements[0] is ReturnStatementSyntax rs ? rs.Expression : null;
            }
            if (e is AwaitExpressionSyntax aw) e = aw.Expression;
            return e as InvocationExpressionSyntax;
        }

        /// <summary>A thread kept in a local, that is started and joined and has its properties set: nothing else can start it.</summary>
        private static bool IsThreadLocal(BaseObjectCreationExpressionSyntax creation, SemanticModel model)
        {
            if (!(creation.Parent is EqualsValueClauseSyntax eq) || !(eq.Parent is VariableDeclaratorSyntax d) || !(model.GetDeclaredSymbol(d) is ILocalSymbol local)) return false;
            var member = creation.Ancestors().First(a => a is BaseMethodDeclarationSyntax || a is AccessorDeclarationSyntax);
            int starts = 0;
            foreach (var id in member.DescendantNodes().OfType<IdentifierNameSyntax>().Where(x => SymbolEqualityComparer.Default.Equals(model.GetSymbolInfo(x).Symbol, local)))
            {
                if (!(id.Parent is MemberAccessExpressionSyntax ma) || ma.Expression != id) return false;
                if (ma.Name.Identifier.Text == "Start") { if (!(ma.Parent is InvocationExpressionSyntax)) return false; starts++; }
                else if (ma.Name.Identifier.Text != "Join" && !(ma.Parent is AssignmentExpressionSyntax a && a.Left == ma)) return false;
            }
            // (a local in a loop is another thread each round; two starts of one would throw)
            return starts <= 1;
        }

        /// <summary>Its value is the same when the delegate runs as it was when it was made: constants, and what no one writes.</summary>
        private static bool IsFixed(ExpressionSyntax e, SemanticModel model, SyntaxNode member)
        {
            switch (e)
            {
                case ParenthesizedExpressionSyntax p: return IsFixed(p.Expression, model, member);
                case ThisExpressionSyntax _: return true;
                case BinaryExpressionSyntax b: return IsFixed(b.Left, model, member) && IsFixed(b.Right, model, member);
                case PrefixUnaryExpressionSyntax u when u.IsKind(SyntaxKind.UnaryMinusExpression): return IsFixed(u.Operand, model, member);
                // (an array's length never changes)
                case MemberAccessExpressionSyntax ma when ma.Name.Identifier.Text == "Length" && model.GetTypeInfo(ma.Expression).Type is IArrayTypeSymbol: return IsFixed(ma.Expression, model, member);
            }
            if (model.GetConstantValue(e).HasValue) return true;
            if (!(e is IdentifierNameSyntax id)) return false;
            return StaysTheSame(model.GetSymbolInfo(id).Symbol, member, model);
        }

        private static bool IsWritten(ISymbol s, SyntaxNode member, SemanticModel model) =>
            member.DescendantNodes().OfType<IdentifierNameSyntax>().Any(x => SymbolEqualityComparer.Default.Equals(model.GetSymbolInfo(x).Symbol, s) && LockGuards.IsWriteTarget(x));

        /// <summary>A parameter or an initialized local that's never written: it is one object for all of a method.</summary>
        public static bool StaysTheSame(ISymbol s, SyntaxNode member, SemanticModel model)
        {
            if (s is ILocalSymbol local)
            {
                if (local.RefKind != RefKind.None) return false;
                if (!local.DeclaringSyntaxReferences.Select(r => r.GetSyntax()).All(d => d is VariableDeclaratorSyntax v && v.Initializer != null || d is ForEachStatementSyntax)) return false;
            }
            else if (!(s is IParameterSymbol { RefKind: RefKind.None })) return false;
            return !IsWritten(s, member, model);
        }

        /// <summary>Does this method run alongside other code, with permissions, by itself or as called from what does?</summary>
        public bool RunsAlongside(IMethodSymbol method)
        {
            if (_alongside == null)
            {
                _alongside = new HashSet<IMethodSymbol>(SymbolEqualityComparer.Default);
                foreach (var tree in _compilation.SyntaxTrees)
                {
                    var model = _compilation.GetSemanticModel(tree);
                    foreach (var inv in tree.GetRoot().DescendantNodes().OfType<InvocationExpressionSyntax>())
                        if (model.GetSymbolInfo(inv).Symbol is IMethodSymbol m && m.DeclaringSyntaxReferences.Length > 0 && IsStartedWithCells(inv, m, model))
                            Add(m);
                }
            }
            return _alongside.Contains(method.OriginalDefinition);
        }

        private bool IsStartedWithCells(InvocationExpressionSyntax inv, IMethodSymbol m, SemanticModel model)
        {
            var contract = _engine.ContractOf(m.OriginalDefinition);
            if (!contract.Requires.Concat(contract.Ensures.Select(e => e.Expr)).Any(e => e != null && e.DescendantsAndSelf().Any(MethodVerifier.IsCellAcc))) return false;
            if (inv.Ancestors().OfType<AnonymousFunctionExpressionSyntax>().FirstOrDefault() is AnonymousFunctionExpressionSyntax l && CallOf(l) == inv) return true;
            if (!m.IsAsync) return false;
            SyntaxNode e = inv.Parent;
            while (e is ParenthesizedExpressionSyntax) e = e.Parent;
            if (e is MemberAccessExpressionSyntax ma && ma.Name.Identifier.Text == "ConfigureAwait" && ma.Parent is InvocationExpressionSyntax c) e = c.Parent;
            return !(e is AwaitExpressionSyntax);
        }

        private void Add(IMethodSymbol m)
        {
            if (!_alongside.Add(m.OriginalDefinition)) return;
            foreach (var r in m.OriginalDefinition.DeclaringSyntaxReferences)
            {
                var model = _compilation.GetSemanticModel(r.SyntaxTree);
                foreach (var inv in r.GetSyntax().DescendantNodes().OfType<InvocationExpressionSyntax>())
                    if (model.GetSymbolInfo(inv).Symbol is IMethodSymbol callee && callee.DeclaringSyntaxReferences.Length > 0 && !SpecSymbols.IsSpecClass(callee.ContainingType))
                        Add(callee);
            }
        }
    }

    internal static class LambdaSyntax
    {
        /// <summary>How many parameters it declares.</summary>
        public static int ParameterList(this AnonymousFunctionExpressionSyntax f) => f switch
        {
            ParenthesizedLambdaExpressionSyntax p => p.ParameterList.Parameters.Count,
            SimpleLambdaExpressionSyntax _ => 1,
            AnonymousMethodExpressionSyntax a => a.ParameterList?.Parameters.Count ?? 0,
            _ => 1,
        };
    }
}
