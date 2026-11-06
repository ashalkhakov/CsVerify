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
                            Infer(new[] { l.Statement }, lockField, model, inferred);
                            break;
                        case TryStatementSyntax t when GateOfTry(t, model) is IFieldSymbol gate && gate.IsReadOnly && IsMutex(gate):
                            Infer(HeldParts(t, model), gate, model, inferred);
                            break;
                    }
            }
            foreach (var (s, locks) in inferred)
                if (!explicitly.Contains(s) && locks.Count == 1) _guards[s] = locks.First();
        }

        private static void Infer(IEnumerable<SyntaxNode> held, IFieldSymbol lockField, SemanticModel model, Dictionary<ISymbol, HashSet<ISymbol>> inferred)
        {
            foreach (var written in held.SelectMany(h => h.DescendantNodes()).OfType<ExpressionSyntax>().Where(IsWriteTarget))
                if (model.GetSymbolInfo(written).Symbol is ISymbol s && (s is IFieldSymbol || s is IPropertySymbol) && Inferable(s) &&
                    SymbolEqualityComparer.Default.Equals(s.ContainingType, lockField.ContainingType))
                {
                    if (!inferred.TryGetValue(s, out var locks)) inferred[s] = locks = new HashSet<ISymbol>(SymbolEqualityComparer.Default);
                    locks.Add(lockField);
                }
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

        // ---- a SemaphoreSlim used as a lock: await g.WaitAsync(); try { ... } finally { g.Release(); } ----

        public static bool IsSemaphore(ISymbol s) => s is IFieldSymbol f && f.Type?.ToDisplayString() == "System.Threading.SemaphoreSlim";

        /// <summary>The field a call g.Wait(), g.WaitAsync() or g.Release() is on, or null.</summary>
        private static IFieldSymbol GateOfCall(InvocationExpressionSyntax inv, string name, SemanticModel model) =>
            inv.Expression is MemberAccessExpressionSyntax ma && ma.Name.Identifier.Text == name && model.GetSymbolInfo(ma.Expression).Symbol is IFieldSymbol g && IsSemaphore(g) ? g : null;

        /// <summary>Taking it, as a statement of its own: it must have succeeded to get past it. (Wait(timeout) says by what it returns.)</summary>
        private static IFieldSymbol GateTakenBy(StatementSyntax st, SemanticModel model)
        {
            if (!(st is ExpressionStatementSyntax es)) return null;
            var e = es.Expression;
            bool awaited = e is AwaitExpressionSyntax;
            if (e is AwaitExpressionSyntax aw) e = aw.Expression;
            if (awaited && e is InvocationExpressionSyntax ca && ca.Expression is MemberAccessExpressionSyntax cm && cm.Name.Identifier.Text == "ConfigureAwait") e = cm.Expression;
            if (!(e is InvocationExpressionSyntax inv) || !(model.GetSymbolInfo(inv).Symbol is IMethodSymbol m)) return null;
            // (a Task<bool> or a bool is a wait that may not have got it)
            if (awaited ? m.ReturnType.ToDisplayString() != "System.Threading.Tasks.Task" : !m.ReturnsVoid) return null;
            return GateOfCall(inv, awaited ? "WaitAsync" : "Wait", model);
        }

        /// <summary>The statement before a statement of a block.</summary>
        private static StatementSyntax Before(StatementSyntax st)
        {
            if (!(st.Parent is BlockSyntax b)) return null;
            int i = b.Statements.IndexOf(st);
            return i > 0 ? b.Statements[i - 1] : null;
        }

        /// <summary>The one g.Release() of a finally, as a statement of its own, or null.</summary>
        private static ExpressionStatementSyntax ReleaseIn(TryStatementSyntax t, IFieldSymbol gate, SemanticModel model)
        {
            if (t.Finally == null) return null;
            var releases = t.Finally.Block.DescendantNodes().OfType<InvocationExpressionSyntax>().Where(i => SymbolEqualityComparer.Default.Equals(GateOfCall(i, "Release", model), gate)).ToList();
            return releases.Count == 1 && releases[0].ArgumentList.Arguments.Count == 0 && releases[0].Parent is ExpressionStatementSyntax es && es.Parent == t.Finally.Block ? es : null;
        }

        /// <summary>The semaphore a try statement holds: it comes right after taking it, and its finally gives it back. Null for any other try.</summary>
        public static IFieldSymbol GateOfTry(TryStatementSyntax t, SemanticModel model)
        {
            if (!(Before(t) is StatementSyntax before) || !(GateTakenBy(before, model) is IFieldSymbol gate) || ReleaseIn(t, gate, model) == null) return null;
            string Receiver(StatementSyntax st) => st.DescendantNodes().OfType<MemberAccessExpressionSyntax>()
                .Where(ma => SymbolEqualityComparer.Default.Equals(model.GetSymbolInfo(ma.Expression).Symbol, gate)).Select(ma => ma.Expression.ToString()).FirstOrDefault();
            // (o._gate taken, and p._gate given back, is not this)
            return Receiver(before) == Receiver(ReleaseIn(t, gate, model)) ? gate : null;
        }

        /// <summary>The parts of such a try that run with it held.</summary>
        public static IEnumerable<SyntaxNode> HeldParts(TryStatementSyntax t, SemanticModel model)
        {
            yield return t.Block;
            foreach (var c in t.Catches) yield return c;
            var release = ReleaseIn(t, GateOfTry(t, model), model);
            foreach (var st in t.Finally.Block.Statements.TakeWhile(x => x != release)) yield return st;
        }

        /// <summary>The try statement a taking statement starts; null if it isn't one.</summary>
        public static TryStatementSyntax TryAfter(StatementSyntax taking)
        {
            if (!(taking.Parent is BlockSyntax b)) return null;
            int i = b.Statements.IndexOf(taking);
            return i >= 0 && i + 1 < b.Statements.Count ? b.Statements[i + 1] as TryStatementSyntax : null;
        }

        /// <summary>Is this call of Wait, WaitAsync or Release the form above?</summary>
        public static bool IsInForm(InvocationExpressionSyntax inv, IFieldSymbol gate, SemanticModel model)
        {
            var st = inv.FirstAncestorOrSelf<StatementSyntax>();
            if (st?.Parent is BlockSyntax fin && fin.Parent is FinallyClauseSyntax fc && fc.Parent is TryStatementSyntax t0)
                return SymbolEqualityComparer.Default.Equals(GateOfTry(t0, model), gate) && ReleaseIn(t0, gate, model) == st;
            return st != null && SymbolEqualityComparer.Default.Equals(GateTakenBy(st, model), gate) && TryAfter(st) is TryStatementSyntax t &&
                   SymbolEqualityComparer.Default.Equals(GateOfTry(t, model), gate);
        }

        /// <summary>Does it let one in at a time? Made with a count of 1, every time it is made; and (see IsInForm) given back only by whoever took it.</summary>
        public bool IsMutexGate(IFieldSymbol gate) => IsMutex(gate);

        private bool IsMutex(IFieldSymbol gate)
        {
            var made = new List<(ExpressionSyntax value, SemanticModel model)>();
            foreach (var r in gate.DeclaringSyntaxReferences)
            {
                var d = r.GetSyntax();
                var model = _compilation.GetSemanticModel(d.SyntaxTree);
                if (d is VariableDeclaratorSyntax v && v.Initializer != null) made.Add((v.Initializer.Value, model));
                if (gate.ContainingType.DeclaringSyntaxReferences.Length != 1) return false;
                foreach (var a in gate.ContainingType.DeclaringSyntaxReferences[0].GetSyntax().DescendantNodes().OfType<AssignmentExpressionSyntax>())
                    if (SymbolEqualityComparer.Default.Equals(model.GetSymbolInfo(a.Left).Symbol, gate)) made.Add((a.Right, model));
            }
            return made.Count > 0 && made.All(x => x.value is BaseObjectCreationExpressionSyntax c && c.ArgumentList != null &&
                c.ArgumentList.Arguments.Count >= 1 && c.ArgumentList.Arguments.Count <= 2 &&
                c.ArgumentList.Arguments.All(a => x.model.GetConstantValue(a.Expression) is { HasValue: true, Value: 1 }));
        }

        /// <summary>The semaphores on "this" a method takes, by itself or through its calls on "this". (Taking one it holds waits for itself.)</summary>
        public IEnumerable<IFieldSymbol> GatesTakenBy(IMethodSymbol method)
        {
            var seen = new HashSet<IMethodSymbol>(SymbolEqualityComparer.Default);
            var gates = new HashSet<IFieldSymbol>(SymbolEqualityComparer.Default);
            void Walk(IMethodSymbol m)
            {
                if (!seen.Add(m.OriginalDefinition)) return;
                foreach (var r in m.OriginalDefinition.DeclaringSyntaxReferences)
                {
                    var model = _compilation.GetSemanticModel(r.SyntaxTree);
                    foreach (var inv in r.GetSyntax().DescendantNodes().OfType<InvocationExpressionSyntax>())
                    {
                        if (!(model.GetSymbolInfo(inv).Symbol is IMethodSymbol callee)) continue;
                        bool onThis = inv.Expression is IdentifierNameSyntax || inv.Expression is GenericNameSyntax ||
                                      inv.Expression is MemberAccessExpressionSyntax ma && ma.Expression is ThisExpressionSyntax;
                        if (onThis) { Walk(callee); continue; }
                        if (inv.Expression is MemberAccessExpressionSyntax wa && (wa.Name.Identifier.Text == "Wait" || wa.Name.Identifier.Text == "WaitAsync") &&
                            (wa.Expression is IdentifierNameSyntax || wa.Expression is MemberAccessExpressionSyntax mt && mt.Expression is ThisExpressionSyntax) &&
                            model.GetSymbolInfo(wa.Expression).Symbol is IFieldSymbol g && IsSemaphore(g))
                            gates.Add(g);
                    }
                }
            }
            Walk(method);
            return gates;
        }

        public static bool IsInvariant(ISymbol s) => SpecSymbols.HasAttribute(s, "LockInvariantAttribute");
    }
}
