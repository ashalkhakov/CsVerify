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
        private List<(SyntaxNode at, IMethodSymbol callee, string why)> _needed;

        public StartedDelegates(Engine engine, Compilation compilation)
        {
            _engine = engine;
            _compilation = compilation;
        }

        /// <summary>The call that is all a delegate does, if it can take permissions; null for any other delegate.</summary>
        public InvocationExpressionSyntax CallOf(AnonymousFunctionExpressionSyntax lambda)
        {
            if (_calls.TryGetValue(lambda, out var known))
            {
                return known;
            }
            return _calls[lambda] = Find(lambda, _compilation.GetSemanticModel(lambda.SyntaxTree));
        }

        private InvocationExpressionSyntax Find(AnonymousFunctionExpressionSyntax lambda, SemanticModel model)
        {
            if (lambda.ParameterList() > 0 || !(lambda.Parent is ArgumentSyntax arg))
            {
                return null;
            }
            bool thread;
            if (arg.Parent?.Parent is InvocationExpressionSyntax run && model.GetSymbolInfo(run).Symbol is IMethodSymbol r && r.Name == "Run" && r.ContainingType?.ToDisplayString() == "System.Threading.Tasks.Task")
            {
                thread = false;
            }
            else if (arg.Parent?.Parent is BaseObjectCreationExpressionSyntax c && model.GetTypeInfo(c).Type?.ToDisplayString() == "System.Threading.Thread" && IsThreadLocal(c, model))
            {
                thread = true;
            }
            else
            {
                return null;
            }
            var call = TheCall(lambda);
            if (call == null || !(model.GetSymbolInfo(call).Symbol is IMethodSymbol m))
            {
                return null;
            }
            if (thread && m.IsAsync)
            {
                return null; // (it would be over at its first await)
            } // (it would be over at its first await)
            var contract = _engine.ContractOf(m.OriginalDefinition);
            if (!contract.HasSource || !contract.Requires.Concat(contract.Ensures.Select(e => e.Expr)).Any(e => e != null && e.DescendantsAndSelf().Any(o => StaticChecks.IsAccCall(o, out _))))
            {
                return null;
            }
            var member = lambda.Ancestors().First(a => a is BaseMethodDeclarationSyntax || a is AccessorDeclarationSyntax);
            if (call.Expression is MemberAccessExpressionSyntax ma && !IsFixed(ma.Expression, model, member) && m.IsStatic == false)
            {
                return null;
            }
            return call.ArgumentList.Arguments.All(a => a.RefKindKeyword.IsKind(SyntaxKind.None) && IsFixed(a.Expression, model, member)) ? call : null;
        }

        /// <summary>F(x), await F(x), { F(x); }, { await F(x); }, { return F(x); }, { return await F(x); }.</summary>
        private static InvocationExpressionSyntax TheCall(AnonymousFunctionExpressionSyntax lambda)
        {
            ExpressionSyntax e = lambda.ExpressionBody;
            if (lambda.Block is BlockSyntax b)
            {
                if (b.Statements.Count != 1)
                {
                    return null;
                }
                e = b.Statements[0] is ExpressionStatementSyntax es ? es.Expression : b.Statements[0] is ReturnStatementSyntax rs ? rs.Expression : null;
            }
            if (e is AwaitExpressionSyntax aw)
            {
                e = aw.Expression;
            }
            return e as InvocationExpressionSyntax;
        }

        /// <summary>A thread kept in a local, that is started and joined and has its properties set: nothing else can start it.</summary>
        private static bool IsThreadLocal(BaseObjectCreationExpressionSyntax creation, SemanticModel model)
        {
            if (!(creation.Parent is EqualsValueClauseSyntax eq) || !(eq.Parent is VariableDeclaratorSyntax d) || !(model.GetDeclaredSymbol(d) is ILocalSymbol local))
            {
                return false;
            }
            var member = creation.Ancestors().First(a => a is BaseMethodDeclarationSyntax || a is AccessorDeclarationSyntax);
            int starts = 0;
            foreach (var id in member.DescendantNodes().OfType<IdentifierNameSyntax>().Where(x => SymbolEqualityComparer.Default.Equals(model.GetSymbolInfo(x).Symbol, local)))
            {
                if (!(id.Parent is MemberAccessExpressionSyntax ma) || ma.Expression != id)
                {
                    return false;
                }
                if (ma.Name.Identifier.Text == "Start")
                {
                    if (!(ma.Parent is InvocationExpressionSyntax))
                    {
                        return false;
                    }
                    starts++;
                }
                else if (ma.Name.Identifier.Text != "Join" && !(ma.Parent is AssignmentExpressionSyntax a && a.Left == ma))
                {
                    return false;
                }
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
            if (model.GetConstantValue(e).HasValue)
            {
                return true;
            }
            if (!(e is IdentifierNameSyntax id))
            {
                return false;
            }
            return StaysTheSame(model.GetSymbolInfo(id).Symbol, member, model);
        }

        private static bool IsWritten(ISymbol s, SyntaxNode member, SemanticModel model) =>
            member.DescendantNodes().OfType<IdentifierNameSyntax>().Any(x => SymbolEqualityComparer.Default.Equals(model.GetSymbolInfo(x).Symbol, s) && LockGuards.IsWriteTarget(x));

        /// <summary>A parameter or an initialized local that's never written: it is one object for all of a method.</summary>
        public static bool StaysTheSame(ISymbol s, SyntaxNode member, SemanticModel model)
        {
            if (s is ILocalSymbol local)
            {
                if (local.RefKind != RefKind.None)
                {
                    return false;
                }
                if (!local.DeclaringSyntaxReferences.Select(r => r.GetSyntax()).All(d => d is VariableDeclaratorSyntax v && v.Initializer != null || d is ForEachStatementSyntax))
                {
                    return false;
                }
            }
            else if (!(s is IParameterSymbol { RefKind: RefKind.None }))
            {
                return false;
            }
            return !IsWritten(s, member, model);
        }

        /// <summary>
        /// Does this code run alongside other code? A method marked [RunsConcurrently] (or in a marked class), a delegate
        /// given to a thread, Task.Run or the like, and the lambdas and local functions within those. Nothing is followed
        /// from one method to another: whatever such code starts or calls of the program's must say so too (see
        /// <see cref="UnmarkedIn"/>), and so must an override of a marked method. That makes each mark a claim checked where
        /// it's used, rather than a guess at what the whole program does.
        /// </summary>
        public bool RunsAlongside(IMethodSymbol method)
        {
            ScanAll();
            return IsMarked(method) || method.OriginalDefinition.DeclaringSyntaxReferences.Any(r => _alongside.Contains(r.GetSyntax()));
        }

        /// <summary>Where code in <paramref name="code"/> starts or calls a method of the program that runs concurrently but isn't marked so.</summary>
        public IEnumerable<(SyntaxNode at, IMethodSymbol callee, string why)> UnmarkedIn(SyntaxNode code)
        {
            ScanAll();
            return _needed.Where(x => code.Span.Contains(x.at.Span) && code.SyntaxTree == x.at.SyntaxTree);
        }

        private readonly System.Collections.Concurrent.ConcurrentDictionary<SyntaxNode, bool> _claimed = new System.Collections.Concurrent.ConcurrentDictionary<SyntaxNode, bool>();

        /// <summary>Is this the first to report the site?</summary>
        public bool Claim(SyntaxNode at) => _claimed.TryAdd(at, true);

        private readonly object _scanning = new object();

        private void ScanAll()
        {
            lock (_scanning)
            {
                if (_needed != null)
                {
                    return;
                }
                _alongside = new HashSet<SyntaxNode>();
                var needed = _needed = new List<(SyntaxNode, IMethodSymbol, string)>();
                foreach (var tree in _engine.UserTrees)
                {
                    var model = _compilation.GetSemanticModel(tree);
                    foreach (var n in tree.GetRoot().DescendantNodes())
                    {
                        if (!SpecSymbols.IsInGhostContext(n, model))
                        {
                            Scan(n, model);
                        }
                    }
                }
                _needed = needed.Where(x => !IsMarked(x.callee)).ToList();
            }
        }

        /// <summary>[RunsConcurrently] on the method, its property, or a type it is in.</summary>
        public static bool IsMarked(IMethodSymbol m)
        {
            m = m.OriginalDefinition;
            if (SpecSymbols.HasAttribute(m, "RunsConcurrentlyAttribute"))
            {
                return true;
            }
            if (m.AssociatedSymbol is IPropertySymbol p && SpecSymbols.HasAttribute(p, "RunsConcurrentlyAttribute"))
            {
                return true;
            }
            for (var t = m.ContainingType; t != null; t = t.ContainingType)
            {
                if (SpecSymbols.HasAttribute(t, "RunsConcurrentlyAttribute"))
                {
                    return true;
                }
            }
            return false;
        }

        /// <summary>Code of the program that this concurrent code runs: it must be marked, unless it's lexically within (a lambda, a local function), or has no code (an auto-property).</summary>
        private void Need(SyntaxNode at, IMethodSymbol m, string why)
        {
            m = m.OriginalDefinition;
            if (m.MethodKind == MethodKind.LocalFunction || m.MethodKind == MethodKind.AnonymousFunction)
            {
                return;
            }
            if (m.DeclaringSyntaxReferences.Length == 0 || SpecSymbols.IsSpecClass(m.ContainingType))
            {
                return;
            }
            if (SpecSymbols.HasAttribute(m, "TrustedAttribute"))
            {
                return; // (nothing in it is checked, so there's nothing to check it as)
            } // (nothing in it is checked, so there's nothing to check it as)
            if (m.DeclaringSyntaxReferences.All(r => r.GetSyntax() is AccessorDeclarationSyntax a && a.Body == null && a.ExpressionBody == null))
            {
                return;
            }
            // (a positional record's own members: its properties and the constructor that sets them)
            if (m.DeclaringSyntaxReferences.All(r => r.GetSyntax() is ParameterSyntax || r.GetSyntax() is RecordDeclarationSyntax))
            {
                return;
            }
            _needed.Add((at, m, why));
        }

        private void Scan(SyntaxNode n, SemanticModel model)
        {
            switch (n)
            {
                case BaseMethodDeclarationSyntax d when model.GetDeclaredSymbol(d) is IMethodSymbol m:
                    if (IsMarked(m))
                    {
                        AddCode(d, model);
                    }
                    // (a call of a marked method may reach any override)
                    var over = m.OverriddenMethod ?? m.ContainingType.AllInterfaces.SelectMany(i => i.GetMembers().OfType<IMethodSymbol>())
                        .FirstOrDefault(i => SymbolEqualityComparer.Default.Equals(m.ContainingType.FindImplementationForInterfaceMember(i), m));
                    if (over != null && IsMarked(over))
                    {
                        Need(d is MethodDeclarationSyntax md ? (SyntaxNode)md.ReturnType : d, m, $"it overrides '{over.Name}', which runs concurrently");
                    }
                    break;
                case AccessorDeclarationSyntax acc when model.GetDeclaredSymbol(acc) is IMethodSymbol am && IsMarked(am):
                    AddCode(acc, model);
                    break;
                case InvocationExpressionSyntax inv when model.GetSymbolInfo(inv).Symbol is IMethodSymbol m:
                    bool awaited = IsAwaitedHere(inv);
                    bool threading = m.DeclaringSyntaxReferences.Length == 0 && (m.ContainingNamespace?.ToDisplayString() ?? "").StartsWith("System.Threading");
                    // Task.Run(d), Parallel.For(.., d), t.ContinueWith(d): what it's given goes on by itself
                    if (threading && !(awaited && m.Name == "Run"))
                    {
                        foreach (var a in inv.ArgumentList.Arguments)
                        {
                            AddDelegate(a.Expression, model);
                        }
                    }
                    if (m.Name == "Start" && inv.Expression is MemberAccessExpressionSyntax th && model.GetTypeInfo(th.Expression).Type?.ToDisplayString() == "System.Threading.Thread")
                    {
                        AddAfter(inv, th.Expression.ToString(), model);
                    }
                    else if (!awaited && (threading && m.Name == "Run" || IsSourceTask(m) && !IsForwarded(inv, model)))
                    {
                        // a task awaited later in the same method needs no mark: start and finish are both in sight, and its code is checked as concurrent all the same
                        if (IsSourceTask(m) && AwaitedInSameMethod(inv, model))
                        {
                            AddStarted(m);
                        }
                        else if (IsSourceTask(m))
                        {
                            Need(inv, m, "it is started here and not awaited in the same method");
                        }
                        AddAfter(inv, TaskName(inv, model), model);
                    }
                    break;
                // a lambda made a delegate of a marked type: a call of it runs concurrently
                case AnonymousFunctionExpressionSyntax fn when model.GetTypeInfo(fn).ConvertedType is INamedTypeSymbol { TypeKind: TypeKind.Delegate, DelegateInvokeMethod: IMethodSymbol made } && IsMarked(made):
                    AddCode(fn, model);
                    break;
                case BaseObjectCreationExpressionSyntax c when model.GetTypeInfo(c).Type?.ToDisplayString() == "System.Threading.Thread" && c.ArgumentList != null:
                    foreach (var a in c.ArgumentList.Arguments)
                    {
                        AddDelegate(a.Expression, model);
                    }
                    break;
            }
        }

        private void AddStarted(IMethodSymbol m)
        {
            foreach (var r in m.OriginalDefinition.DeclaringSyntaxReferences)
            {
                AddCode(r.GetSyntax(), _compilation.GetSemanticModel(r.SyntaxTree));
            }
        }

        /// <summary><c>var t = F(); ... await t;</c> in one method, or <c>await Task.WhenAll(F(), G())</c>.</summary>
        private static bool AwaitedInSameMethod(InvocationExpressionSyntax inv, SemanticModel model)
        {
            if (inv.Parent is ArgumentSyntax arg && arg.Parent?.Parent is InvocationExpressionSyntax all && IsAwaitedHere(all) &&
                model.GetSymbolInfo(all).Symbol is IMethodSymbol w && w.Name == "WhenAll" && w.ContainingType?.ToDisplayString() == "System.Threading.Tasks.Task")
            {
                return true;
            }
            var task = TaskName(inv, model);
            if (task == null)
            {
                return false;
            }
            SyntaxNode at = inv.FirstAncestorOrSelf<StatementSyntax>();
            while (at != null && !(at is BaseMethodDeclarationSyntax || at is AccessorDeclarationSyntax))
            {
                var parent = at.Parent;
                if (parent is AnonymousFunctionExpressionSyntax || parent is LocalFunctionStatementSyntax)
                {
                    return false;
                }
                if (parent is BlockSyntax b && at is StatementSyntax here &&
                    b.Statements.Skip(b.Statements.IndexOf(here) + 1).Any(next => Finishes(next, task, model)))
                {
                    return true;
                }
                at = parent;
            }
            return false;
        }

        private static bool IsSourceTask(IMethodSymbol m) =>
            m.DeclaringSyntaxReferences.Length > 0 && !SpecSymbols.IsSpecClass(m.ContainingType) && m.ReturnType is INamedTypeSymbol t && (t.Name == "Task" || t.Name == "ValueTask") && t.ContainingNamespace?.ToDisplayString() == "System.Threading.Tasks";

        /// <summary><c>return F(x);</c> from a method that isn't async: whoever called it has the task, and is who starts it.</summary>
        private static bool IsForwarded(InvocationExpressionSyntax inv, SemanticModel model)
        {
            SyntaxNode e = inv.Parent;
            while (e is ParenthesizedExpressionSyntax)
            {
                e = e.Parent;
            }
            if (!(e is ReturnStatementSyntax || e is ArrowExpressionClauseSyntax))
            {
                return false;
            }
            return inv.Ancestors().FirstOrDefault(a => a is AnonymousFunctionExpressionSyntax || a is BaseMethodDeclarationSyntax || a is LocalFunctionStatementSyntax) is BaseMethodDeclarationSyntax d && model.GetDeclaredSymbol(d) is IMethodSymbol { IsAsync: false };
        }

        private static string TaskName(SyntaxNode start, SemanticModel model) =>
            start.Parent is EqualsValueClauseSyntax eq && eq.Parent is VariableDeclaratorSyntax d ? d.Identifier.Text : null;

        private void AddDelegate(ExpressionSyntax e, SemanticModel model)
        {
            if (e is AnonymousFunctionExpressionSyntax)
            {
                AddCode(e, model);
            }
            else if ((e is IdentifierNameSyntax || e is MemberAccessExpressionSyntax) && model.GetSymbolInfo(e).Symbol is IMethodSymbol group && group.DeclaringSyntaxReferences.Length > 0)
            {
                Need(e, group, "it is handed here to run by itself");
            }
        }

        /// <summary>What a method calls while what it started goes on.</summary>
        private void AddAfter(SyntaxNode start, string task, SemanticModel model)
        {
            if (start.Ancestors().FirstOrDefault(a => a is BaseMethodDeclarationSyntax || a is AnonymousFunctionExpressionSyntax || a is LocalFunctionStatementSyntax || a is AccessorDeclarationSyntax) is SyntaxNode body)
            {
                foreach (var code in CodeAlongside(start, task, body, model))
                {
                    AddCalls(code, model, "it is called while a task started here goes on");
                }
            }
        }


        private void AddCode(SyntaxNode code, SemanticModel model)
        {
            if (_alongside.Add(code))
            {
                AddCalls(code, model, "it is called by code that runs concurrently");
            }
        }

        private void AddCalls(SyntaxNode code, SemanticModel model, string why)
        {
            foreach (var n in code.DescendantNodesAndSelf())
            {
                if (SpecSymbols.IsInGhostContext(n, model))
                {
                    continue;
                }
                switch (n)
                {
                    case AnonymousFunctionExpressionSyntax _:
                    case LocalFunctionStatementSyntax _:
                        if (n != code)
                        {
                            AddCode(n, model);
                        }
                        break;
                    case InvocationExpressionSyntax inv when model.GetSymbolInfo(inv).Symbol is IMethodSymbol callee:
                        if (callee.MethodKind == MethodKind.LocalFunction)
                        {
                            foreach (var r in callee.DeclaringSyntaxReferences)
                            {
                                AddCode(r.GetSyntax(), model);
                            }
                        }
                        else
                        {
                            Need(inv, callee, why);
                        }
                        break;
                    case BaseObjectCreationExpressionSyntax c when model.GetSymbolInfo(c).Symbol is IMethodSymbol ctor:
                        Need(c, ctor, why);
                        break;
                    case SimpleNameSyntax name when model.GetSymbolInfo(name).Symbol is IPropertySymbol p && p.DeclaringSyntaxReferences.Length > 0:
                        if (p.GetMethod != null)
                        {
                            Need(name, p.GetMethod, why);
                        }
                        if (p.SetMethod != null)
                        {
                            Need(name, p.SetMethod, why);
                        }
                        break;
                }
            }
        }

        /// <summary><c>await X</c> or <c>await X.ConfigureAwait(b)</c>: X doesn't run alongside what comes after.</summary>
        internal static bool IsAwaitedHere(SyntaxNode call)
        {
            var e = call.Parent;
            while (e is ParenthesizedExpressionSyntax)
            {
                e = e.Parent;
            }
            if (e is MemberAccessExpressionSyntax ma && ma.Name.Identifier.Text == "ConfigureAwait" && ma.Parent is InvocationExpressionSyntax c)
            {
                e = c.Parent;
            }
            return e is AwaitExpressionSyntax;
        }

        /// <summary>What a method does while a task it started goes on: from there to where it is awaited or joined, as far as can be told.</summary>
        internal static IEnumerable<SyntaxNode> CodeAlongside(SyntaxNode start, string task, SyntaxNode body, SemanticModel model)
        {
            SyntaxNode at = start.FirstAncestorOrSelf<StatementSyntax>();
            while (at != null && at != body)
            {
                var parent = at.Parent;
                if (parent is AnonymousFunctionExpressionSyntax || parent is LocalFunctionStatementSyntax)
                {
                    yield break;
                }
                if (parent is BlockSyntax b && at is StatementSyntax here)
                {
                    foreach (var next in b.Statements.Skip(b.Statements.IndexOf(here) + 1))
                    {
                        if (task != null && Finishes(next, task, model))
                        {
                            yield break;
                        }
                        yield return next;
                    }
                }
                if (parent is ForStatementSyntax || parent is WhileStatementSyntax || parent is DoStatementSyntax || parent is CommonForEachStatementSyntax)
                {
                    yield return parent;
                }
                if (parent is TryStatementSyntax t && at == t.Block)
                {
                    foreach (var c in t.Catches)
                    {
                        yield return c;
                    }
                    if (t.Finally != null)
                    {
                        yield return t.Finally;
                    }
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
            if (e is AssignmentExpressionSyntax a)
            {
                e = a.Right;
            }
            if (e is InvocationExpressionSyntax join && join.Expression is MemberAccessExpressionSyntax j && j.Name.Identifier.Text == "Join" && j.Expression.ToString() == task)
            {
                return true;
            }
            if (!(e is AwaitExpressionSyntax aw))
            {
                return false;
            }
            e = aw.Expression;
            if (e is InvocationExpressionSyntax ca && ca.Expression is MemberAccessExpressionSyntax cm && cm.Name.Identifier.Text == "ConfigureAwait")
            {
                e = cm.Expression;
            }
            if (e.ToString() == task)
            {
                return true;
            }
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
