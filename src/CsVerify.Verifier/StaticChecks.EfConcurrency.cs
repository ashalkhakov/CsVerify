using System.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace CsVerify.Verifier
{
    /// <summary>
    /// One operation at a time on a DbContext (CSV1036): it is not thread safe, and EF throws ("A second operation was
    /// started on this context instance before a previous operation completed") when two overlap. So each of its
    /// asynchronous operations is awaited where it starts, and code that runs alongside (Task.Run, threads, Parallel)
    /// doesn't use a context from outside it.
    /// </summary>
    internal partial class StaticChecks
    {
        internal const string OneAtATimeId = "CSV1036";

        private void CheckContextConcurrency()
        {
            if (Ef == null || _contract.Declaration == null) return;
            var root = _contract.Declaration;
            foreach (var call in root.DescendantNodes().OfType<InvocationExpressionSyntax>())
            {
                if (!(_model.GetSymbolInfo(call).Symbol is IMethodSymbol m)) continue;
                if (IsContextOperation(call, m) && !AwaitedAtOnce(call))
                    Report(OneAtATimeId, call, $"'{call}' starts an operation on a DbContext and doesn't await it here: another one started before it ends makes EF throw. Await each where it starts", isError: true);
                if (RunsAlongside(m))
                    foreach (var lambda in call.ArgumentList.Arguments.Select(a => a.Expression).OfType<AnonymousFunctionExpressionSyntax>())
                        foreach (var used in ContextsFromOutside(lambda))
                            Report(OneAtATimeId, used, $"'{used}' is a DbContext from outside code that runs alongside this one ({m.ContainingType.Name}.{m.Name}): two threads at once on it make EF throw. Make a context inside (IDbContextFactory), or await the work first", isError: true);
            }
            foreach (var made in root.DescendantNodes().OfType<ObjectCreationExpressionSyntax>())
                if (_model.GetTypeInfo(made).Type is INamedTypeSymbol t && t.ToDisplayString() == "System.Threading.Thread" && made.ArgumentList != null)
                    foreach (var lambda in made.ArgumentList.Arguments.Select(a => a.Expression).OfType<AnonymousFunctionExpressionSyntax>())
                        foreach (var used in ContextsFromOutside(lambda))
                            Report(OneAtATimeId, used, $"'{used}' is a DbContext from outside a thread's code: two threads at once on it make EF throw. Make a context inside (IDbContextFactory)", isError: true);
        }

        /// <summary>An asynchronous EF operation on a context: of the context, a DbSet, a query on one, its Database, an entry, a transaction.</summary>
        private bool IsContextOperation(InvocationExpressionSyntax call, IMethodSymbol m)
        {
            if (!m.Name.EndsWith("Async") || m.Name == "CreateDbContextAsync") return false;
            if (!(IsEfMethod(m) || IsTransactionType(m.ContainingType) || Ef.IsContextType(m.ContainingType))) return false;
            var receiver = call.Expression is MemberAccessExpressionSyntax ma ? _model.GetTypeInfo(ma.Expression).Type : null;
            var first = m.IsExtensionMethod || m.ReducedFrom != null ? receiver : null;
            bool Ours(ITypeSymbol t) => t != null && (Ef.IsContextType(t) || t.Name == "DbSet" || t.Name == "IQueryable" || t.Name == "IOrderedQueryable" ||
                t.AllInterfaces.Any(i => i.Name == "IQueryable") || t.Name == "DatabaseFacade" || t.Name == "EntityEntry" || IsTransactionType(t));
            return Ours(receiver) || Ours(first);
        }

        /// <summary>
        /// Is the task awaited where it is made (through ConfigureAwait and parentheses), or returned by a method that
        /// isn't async (whose caller then has it)?
        /// </summary>
        private bool AwaitedAtOnce(ExpressionSyntax call)
        {
            SyntaxNode n = call;
            while (true)
            {
                var p = n.Parent;
                if (p is ParenthesizedExpressionSyntax) { n = p; continue; }
                if (p is MemberAccessExpressionSyntax ma && ma.Name.Identifier.Text == "ConfigureAwait" && ma.Parent is InvocationExpressionSyntax ca) { n = ca; continue; }
                if (p is AwaitExpressionSyntax) return true;
                if ((p is ReturnStatementSyntax || p is ArrowExpressionClauseSyntax) && !_method.IsAsync) return true;
                return false;
            }
        }

        private static bool RunsAlongside(IMethodSymbol m)
        {
            var type = m.ContainingType?.ToDisplayString();
            return type == "System.Threading.Tasks.Task" && m.Name == "Run" ||
                   type == "System.Threading.Tasks.TaskFactory" && m.Name == "StartNew" ||
                   type == "System.Threading.Tasks.Parallel" ||
                   type == "System.Threading.ThreadPool" && m.Name.StartsWith("QueueUserWorkItem");
        }

        /// <summary>The uses in a lambda of contexts it didn't make: locals and parameters from outside it, and fields.</summary>
        private System.Collections.Generic.IEnumerable<SyntaxNode> ContextsFromOutside(AnonymousFunctionExpressionSyntax lambda)
        {
            foreach (var id in lambda.Body.DescendantNodesAndSelf().OfType<IdentifierNameSyntax>())
            {
                var s = _model.GetSymbolInfo(id).Symbol;
                ITypeSymbol type = s switch { ILocalSymbol l => l.Type, IParameterSymbol p => p.Type, IFieldSymbol fs => fs.Type, IPropertySymbol ps => ps.Type, _ => null };
                if (type == null || !(Ef.IsContextType(type) || type.Name == "DbSet")) continue;
                if (s is IPropertySymbol && type.Name == "DbSet") continue; // (ctx.Orders: ctx is the use)
                bool inside = s.DeclaringSyntaxReferences.Any(r => lambda.Span.Contains(r.Span));
                if (!inside) yield return id;
            }
        }
    }
}
