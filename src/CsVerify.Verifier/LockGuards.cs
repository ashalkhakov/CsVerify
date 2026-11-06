using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Which lock protects which state. A field or auto-property with <c>[GuardedBy]</c> says so itself. Otherwise a field
    /// written inside <c>lock (L)</c>, and under no other lock, is taken to be guarded by L: that is what the program's
    /// own locking says it means. (volatile fields and readonly ones are not: they don't need it.)
    /// </summary>
    internal sealed class LockGuards
    {
        private readonly Compilation _compilation;
        private readonly Dictionary<ISymbol, ISymbol> _guards = new Dictionary<ISymbol, ISymbol>(SymbolEqualityComparer.Default);
        private readonly Dictionary<ISymbol, List<IMethodSymbol>> _invariants = new Dictionary<ISymbol, List<IMethodSymbol>>(SymbolEqualityComparer.Default);

        public bool Any => _guards.Count > 0 || _invariants.Count > 0;

        public LockGuards(Compilation compilation, IEnumerable<SyntaxTree> trees)
        {
            _compilation = compilation;
            var inferred = new Dictionary<ISymbol, HashSet<ISymbol>>(SymbolEqualityComparer.Default);
            var explicitly = new HashSet<ISymbol>(SymbolEqualityComparer.Default);
            foreach (var tree in trees)
            {
                var model = compilation.GetSemanticModel(tree);
                foreach (var n in tree.GetRoot().DescendantNodes())
                    switch (n)
                    {
                        case VariableDeclaratorSyntax v when model.GetDeclaredSymbol(v) is IFieldSymbol fd:
                            Declared(fd, explicitly);
                            break;
                        case PropertyDeclarationSyntax p when model.GetDeclaredSymbol(p) is IPropertySymbol pd:
                            Declared(pd, explicitly);
                            break;
                        case MethodDeclarationSyntax m when model.GetDeclaredSymbol(m) is IMethodSymbol md && SpecSymbols.HasAttribute(md, "LockInvariantAttribute"):
                            if (Named(md, "LockInvariantAttribute") is ISymbol held)
                            {
                                if (!_invariants.TryGetValue(held, out var list)) _invariants[held] = list = new List<IMethodSymbol>();
                                list.Add(md);
                            }
                            break;
                        case LockStatementSyntax l when LockOf(l.Expression, model) is IFieldSymbol lockField && (lockField.IsReadOnly || lockField.IsConst):
                            foreach (var written in l.Statement.DescendantNodes().OfType<ExpressionSyntax>().Where(IsWriteTarget))
                                if (model.GetSymbolInfo(written).Symbol is ISymbol s && (s is IFieldSymbol || s is IPropertySymbol) && Inferable(s) &&
                                    SymbolEqualityComparer.Default.Equals(s.ContainingType, lockField.ContainingType))
                                {
                                    if (!inferred.TryGetValue(s, out var locks)) inferred[s] = locks = new HashSet<ISymbol>(SymbolEqualityComparer.Default);
                                    locks.Add(lockField);
                                }
                            break;
                    }
            }
            foreach (var (s, locks) in inferred)
                if (!explicitly.Contains(s) && locks.Count == 1) _guards[s] = locks.First();
        }

        private void Declared(ISymbol s, HashSet<ISymbol> explicitly)
        {
            if (!SpecSymbols.HasAttribute(s, "GuardedByAttribute")) return;
            explicitly.Add(s);
            if (Named(s, "GuardedByAttribute") is ISymbol held) _guards[s] = held;
        }

        /// <summary>The field an attribute names as a lock, in the type of what it is on.</summary>
        private static ISymbol Named(ISymbol s, string attribute)
        {
            var a = s.GetAttributes().FirstOrDefault(x => x.AttributeClass?.Name == attribute);
            return a?.ConstructorArguments.FirstOrDefault().Value is string name
                ? s.ContainingType.GetMembers(name).OfType<IFieldSymbol>().FirstOrDefault() : null;
        }

        private static bool Inferable(ISymbol s) =>
            s is IFieldSymbol f ? !f.IsReadOnly && !f.IsVolatile && !f.IsConst
            : s is IPropertySymbol p && !p.IsIndexer && p.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() is PropertyDeclarationSyntax d &&
              d.AccessorList != null && d.AccessorList.Accessors.All(x => x.Body == null && x.ExpressionBody == null);

        private static bool IsWriteTarget(ExpressionSyntax e)
        {
            var whole = e.Parent is MemberAccessExpressionSyntax ma && ma.Name == e ? (ExpressionSyntax)ma : e;
            switch (whole.Parent)
            {
                case AssignmentExpressionSyntax a: return a.Left == whole;
                case PrefixUnaryExpressionSyntax u: return u.IsKind(SyntaxKind.PreIncrementExpression) || u.IsKind(SyntaxKind.PreDecrementExpression);
                case PostfixUnaryExpressionSyntax u: return u.IsKind(SyntaxKind.PostIncrementExpression) || u.IsKind(SyntaxKind.PostDecrementExpression);
                case ArgumentSyntax arg: return !arg.RefKindKeyword.IsKind(SyntaxKind.None);
                default: return false;
            }
        }

        /// <summary>The lock field an expression of a lock statement names, or null.</summary>
        public static IFieldSymbol LockOf(ExpressionSyntax e, SemanticModel model) => model.GetSymbolInfo(e).Symbol as IFieldSymbol;

        public ISymbol GuardOf(ISymbol member) =>
            // (an invariant reads what the lock guards: outside it, that would be a read like any other)
            member is IMethodSymbol m ? (Named(m.OriginalDefinition, "GuardedByAttribute") ?? Named(m.OriginalDefinition, "LockInvariantAttribute"))
            : _guards.TryGetValue(member.OriginalDefinition, out var l) ? l : null;

        public IEnumerable<ISymbol> GuardedBy(ISymbol lockField) =>
            _guards.Where(kv => SymbolEqualityComparer.Default.Equals(kv.Value, lockField)).Select(kv => kv.Key);

        public IReadOnlyList<IMethodSymbol> InvariantsOf(ISymbol lockField) =>
            _invariants.TryGetValue(lockField, out var list) ? list : new List<IMethodSymbol>();

        /// <summary>The lock invariants of a type's own locks, with the lock each is of.</summary>
        public IEnumerable<(ISymbol lockField, IMethodSymbol invariant)> InvariantsIn(INamedTypeSymbol type) =>
            _invariants.Where(kv => SymbolEqualityComparer.Default.Equals(kv.Key.ContainingType, type)).SelectMany(kv => kv.Value.Select(m => (kv.Key, m)));

        public static bool IsInvariant(ISymbol s) => SpecSymbols.HasAttribute(s, "LockInvariantAttribute");
    }
}
