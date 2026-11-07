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
        private HashSet<SyntaxNode> _alongside;

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

        /// <summary>
        /// Does this code run alongside other code? A task not awaited at once, a delegate given to a thread, what a method
        /// does between starting a task and finishing it, [RunsConcurrently], and what any of those calls. As far as the
        /// program's source shows: a delegate of unknown origin isn't followed.
        /// </summary>
        public bool RunsAlongside(IMethodSymbol method)
        {
            if (_alongside == null)
            {
                _alongside = new HashSet<SyntaxNode>();
                foreach (var tree in _engine.UserTrees)
                {
                    var model = _compilation.GetSemanticModel(tree);
                    foreach (var n in tree.GetRoot().DescendantNodes())
                        if (!SpecSymbols.IsInGhostContext(n, model)) Scan(n, model);
                }
            }
            return method.OriginalDefinition.DeclaringSyntaxReferences.Any(r => _alongside.Contains(r.GetSyntax()));
        }

        private void Scan(SyntaxNode n, SemanticModel model)
        {
            switch (n)
            {
                case MethodDeclarationSyntax d when model.GetDeclaredSymbol(d) is IMethodSymbol m && (SpecSymbols.HasAttribute(m, "RunsConcurrentlyAttribute") || SpecSymbols.HasAttribute(m.ContainingType, "RunsConcurrentlyAttribute")):
                    AddCode(d, model);
                    break;
                case InvocationExpressionSyntax inv when model.GetSymbolInfo(inv).Symbol is IMethodSymbol m:
                    bool awaited = IsAwaitedHere(inv);
                    bool threading = m.DeclaringSyntaxReferences.Length == 0 && (m.ContainingNamespace?.ToDisplayString() ?? "").StartsWith("System.Threading");
                    // Task.Run(d), Parallel.For(.., d), t.ContinueWith(d): what it's given goes on by itself
                    if (threading && !(awaited && m.Name == "Run"))
                        foreach (var a in inv.ArgumentList.Arguments) AddDelegate(a.Expression, model);
                    if (m.Name == "Start" && inv.Expression is MemberAccessExpressionSyntax th && model.GetTypeInfo(th.Expression).Type?.ToDisplayString() == "System.Threading.Thread")
                        AddAfter(inv, th.Expression.ToString(), model);
                    else if (!awaited && (threading && m.Name == "Run" || IsSourceTask(m) && !IsForwarded(inv, model)))
                    {
                        if (IsSourceTask(m)) Add(m);
                        AddAfter(inv, TaskName(inv, model), model);
                    }
                    break;
                case BaseObjectCreationExpressionSyntax c when model.GetTypeInfo(c).Type?.ToDisplayString() == "System.Threading.Thread" && c.ArgumentList != null:
                    foreach (var a in c.ArgumentList.Arguments) AddDelegate(a.Expression, model);
                    break;
            }
        }

        private static bool IsSourceTask(IMethodSymbol m) =>
            m.DeclaringSyntaxReferences.Length > 0 && !SpecSymbols.IsSpecClass(m.ContainingType) && m.ReturnType is INamedTypeSymbol t && (t.Name == "Task" || t.Name == "ValueTask") && t.ContainingNamespace?.ToDisplayString() == "System.Threading.Tasks";

        /// <summary><c>return F(x);</c> from a method that isn't async: whoever called it has the task, and is who starts it.</summary>
        private static bool IsForwarded(InvocationExpressionSyntax inv, SemanticModel model)
        {
            SyntaxNode e = inv.Parent;
            while (e is ParenthesizedExpressionSyntax) e = e.Parent;
            if (!(e is ReturnStatementSyntax || e is ArrowExpressionClauseSyntax)) return false;
            return inv.Ancestors().FirstOrDefault(a => a is AnonymousFunctionExpressionSyntax || a is BaseMethodDeclarationSyntax || a is LocalFunctionStatementSyntax) is BaseMethodDeclarationSyntax d && model.GetDeclaredSymbol(d) is IMethodSymbol { IsAsync: false };
        }

        private static string TaskName(SyntaxNode start, SemanticModel model) =>
            start.Parent is EqualsValueClauseSyntax eq && eq.Parent is VariableDeclaratorSyntax d ? d.Identifier.Text : null;

        private void AddDelegate(ExpressionSyntax e, SemanticModel model)
        {
            if (e is AnonymousFunctionExpressionSyntax) AddCode(e, model);
            else if (model.GetSymbolInfo(e).Symbol is IMethodSymbol group && group.DeclaringSyntaxReferences.Length > 0) Add(group);
        }

        /// <summary>What a method calls while what it started goes on.</summary>
        private void AddAfter(SyntaxNode start, string task, SemanticModel model)
        {
            if (start.Ancestors().FirstOrDefault(a => a is BaseMethodDeclarationSyntax || a is AnonymousFunctionExpressionSyntax || a is LocalFunctionStatementSyntax || a is AccessorDeclarationSyntax) is SyntaxNode body)
                foreach (var code in CodeAlongside(start, task, body, model))
                    AddCalls(code, model);
        }

        private void Add(IMethodSymbol m)
        {
            foreach (var r in m.OriginalDefinition.DeclaringSyntaxReferences) AddCode(r.GetSyntax(), _compilation.GetSemanticModel(r.SyntaxTree));
            foreach (var o in _engine.Fields.Overrides(m.OriginalDefinition)) Add(o);
        }

        private void AddCode(SyntaxNode code, SemanticModel model)
        {
            if (_alongside.Add(code)) AddCalls(code, model);
        }

        private void AddCalls(SyntaxNode code, SemanticModel model)
        {
            foreach (var n in code.DescendantNodesAndSelf())
            {
                if (SpecSymbols.IsInGhostContext(n, model)) continue;
                switch (n)
                {
                    case AnonymousFunctionExpressionSyntax _:
                    case LocalFunctionStatementSyntax _:
                        if (n != code) AddCode(n, model);
                        break;
                    case InvocationExpressionSyntax inv when model.GetSymbolInfo(inv).Symbol is IMethodSymbol callee:
                        if (callee.MethodKind == MethodKind.LocalFunction || callee.DeclaringSyntaxReferences.Length > 0 && !SpecSymbols.IsSpecClass(callee.ContainingType)) Add(callee);
                        break;
                    case BaseObjectCreationExpressionSyntax c when model.GetSymbolInfo(c).Symbol is IMethodSymbol ctor && ctor.DeclaringSyntaxReferences.Length > 0:
                        Add(ctor);
                        break;
                    case SimpleNameSyntax name when model.GetSymbolInfo(name).Symbol is IPropertySymbol p && p.DeclaringSyntaxReferences.Length > 0:
                        if (p.GetMethod != null) Add(p.GetMethod);
                        if (p.SetMethod != null) Add(p.SetMethod);
                        break;
                }
            }
        }

        /// <summary><c>await X</c> or <c>await X.ConfigureAwait(b)</c>: X doesn't run alongside what comes after.</summary>
        internal static bool IsAwaitedHere(SyntaxNode call)
        {
            var e = call.Parent;
            while (e is ParenthesizedExpressionSyntax) e = e.Parent;
            if (e is MemberAccessExpressionSyntax ma && ma.Name.Identifier.Text == "ConfigureAwait" && ma.Parent is InvocationExpressionSyntax c) e = c.Parent;
            return e is AwaitExpressionSyntax;
        }

        /// <summary>What a method does while a task it started goes on: from there to where it is awaited or joined, as far as can be told.</summary>
        internal static IEnumerable<SyntaxNode> CodeAlongside(SyntaxNode start, string task, SyntaxNode body, SemanticModel model)
        {
            SyntaxNode at = start.FirstAncestorOrSelf<StatementSyntax>();
            while (at != null && at != body)
            {
                var parent = at.Parent;
                if (parent is AnonymousFunctionExpressionSyntax || parent is LocalFunctionStatementSyntax) yield break;
                if (parent is BlockSyntax b && at is StatementSyntax here)
                    foreach (var next in b.Statements.Skip(b.Statements.IndexOf(here) + 1))
                    {
                        if (task != null && Finishes(next, task, model)) yield break;
                        yield return next;
                    }
                if (parent is ForStatementSyntax || parent is WhileStatementSyntax || parent is DoStatementSyntax || parent is CommonForEachStatementSyntax) yield return parent;
                if (parent is TryStatementSyntax t && at == t.Block)
                {
                    foreach (var c in t.Catches) yield return c;
                    if (t.Finally != null) yield return t.Finally;
                }
                at = parent;
            }
        }

        /// <summary><c>await t;</c>, <c>x = await t;</c>, <c>return await t;</c>, the same with Task.WhenAll(..., t, ...), or <c>t.Join();</c>.</summary>
        private static bool Finishes(StatementSyntax st, string task, SemanticModel model)
        {
            var e = st is ExpressionStatementSyntax es ? es.Expression
                : st is ReturnStatementSyntax rs ? rs.Expression
                : st is LocalDeclarationStatementSyntax ld && ld.Declaration.Variables.Count == 1 ? ld.Declaration.Variables[0].Initializer?.Value : null;
            if (e is AssignmentExpressionSyntax a) e = a.Right;
            if (e is InvocationExpressionSyntax join && join.Expression is MemberAccessExpressionSyntax j && j.Name.Identifier.Text == "Join" && j.Expression.ToString() == task) return true;
            if (!(e is AwaitExpressionSyntax aw)) return false;
            e = aw.Expression;
            if (e is InvocationExpressionSyntax ca && ca.Expression is MemberAccessExpressionSyntax cm && cm.Name.Identifier.Text == "ConfigureAwait") e = cm.Expression;
            if (e.ToString() == task) return true;
            return e is InvocationExpressionSyntax all && model.GetSymbolInfo(all).Symbol is IMethodSymbol m && m.Name == "WhenAll" && m.ContainingType?.ToDisplayString() == "System.Threading.Tasks.Task" && all.ArgumentList.Arguments.Any(x => x.Expression.ToString() == task);
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
