using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Deadlock freedom by lock levels (see LockLevels): while a lock is held, a lock taken, a call, or a task waited for
    /// takes only locks of higher levels (CSV1025). Then every thread takes its locks in increasing order, and no cycle of
    /// threads can wait on each other. Two locks of one field are ordered by their objects' ids (OrderedBy), proved where
    /// both are taken; an array's elements by index (CheckLockOrder).
    /// </summary>
    internal sealed partial class MethodVerifier
    {
        private void CheckLockLevels()
        {
            if (SpecSymbols.HasAttribute(_method, "TrustedAttribute")) return;
            // (a lambda or local function is looked at with the code around it, but for one in a field's initializer, which has none)
            var root = _contract.Declaration;
            if (NestedGraph != null && !(root.Ancestors().Any(a => a is EqualsValueClauseSyntax) && !root.Ancestors().Any(a => a is AnonymousFunctionExpressionSyntax || a is LocalFunctionStatementSyntax))) return;
            var levels = _engine.Levels;
            if (NestedGraph == null && levels.TakesNoLocks(_method) && levels.OfBody(_method) is LockLevels.Summary own && !own.IsEmpty)
                Report("CSV1025", MethodLocationNode(), $"'{_method.Name}' is said to take no locks, but {Takes(own)}", isError: true);
            foreach (var n in root.DescendantNodesAndSelf())
            {
                CheckSaidToTakeNone(n);
                var acquired = levels.AcquiredAt(n, _model);
                bool calls = n is InvocationExpressionSyntax || n is BaseObjectCreationExpressionSyntax || n is ElementAccessExpressionSyntax ||
                             n is SimpleNameSyntax && _model.GetSymbolInfo(n).Symbol is IPropertySymbol;
                var waited = LockLevels.WaitedFor(n, _model).ToList();
                if (acquired == null && !calls && waited.Count == 0) continue;
                var held = levels.HeldAt(n, root, _model).Where(h => h != null).ToList();
                if (held.Count == 0) continue;
                if (acquired != null)
                    foreach (var h in held) OrderDirect(h, acquired, n);
                if (calls) OrderCalled(held, levels.OfCall(n, _model, _method), n);
                foreach (var w in waited)
                {
                    if (LockLevels.Given(w, _model, root) is string why)
                    {
                        Report("CSV1025", n, $"'{n}' waits while '{held[0].Expression}' is held, for {why}. Wait outside the lock", isError: true);
                        continue;
                    }
                    // (a task this code started: it may need what's held to finish)
                    foreach (var v in LockLevels.ValuesOf(w, _model, root) ?? new System.Collections.Generic.List<ExpressionSyntax>())
                    {
                        var started = v is InvocationExpressionSyntax si && si.ArgumentList.Arguments.FirstOrDefault()?.Expression is AnonymousFunctionExpressionSyntax lam &&
                                      _model.GetSymbolInfo(si).Symbol is IMethodSymbol sm && sm.DeclaringSyntaxReferences.Length == 0
                            ? levels.OfRegion(lam, _model, _method) : levels.OfCall(v, _model, _method);
                        OrderCalled(held, started, n, $"'{n}' waits for '{v}'");
                    }
                }
            }
        }

        /// <summary>A lambda or method made a [TakesNoLocks] delegate takes none.</summary>
        private void CheckSaidToTakeNone(SyntaxNode n)
        {
            if (!(n is ExpressionSyntax e) || !(_model.GetTypeInfo(e).ConvertedType is INamedTypeSymbol dt) || dt.TypeKind != TypeKind.Delegate || !LockLevels.TakesNoLocks(dt)) return;
            LockLevels.Summary s;
            if (n is AnonymousFunctionExpressionSyntax lambda) s = _engine.Levels.OfRegion(lambda, _model, _method);
            else if (!(n.Parent is InvocationExpressionSyntax call && call.Expression == n) && !(n.Parent is MemberAccessExpressionSyntax ma && ma.Name == n) &&
                     _model.GetSymbolInfo(n).Symbol is IMethodSymbol group && SymbolEqualityComparer.Default.Equals(_model.GetTypeInfo(e).Type, null))
                s = _engine.Levels.Of(group);
            else return;
            if (!s.IsEmpty) Report("CSV1025", n, $"'{dt.Name}' takes no locks, but {Takes(s)}", isError: true);
        }

        private static string Takes(LockLevels.Summary s) =>
            s.Taken.Count > 0 ? $"it may take '{s.Taken[0].Lock.Name}' (in '{s.Taken[0].In?.Name}')" : $"it could take any lock: {s.Unknown}";

        private static string Named(LockLevels.Acquired a) => a.Expression is LockStatementSyntax || a.Expression is StatementSyntax ? a.Lock?.Name ?? a.Expression.ToString() : a.Expression.ToString();

        /// <summary>A lock taken right here, while another is held.</summary>
        private void OrderDirect(LockLevels.Acquired h, LockLevels.Acquired a, SyntaxNode at)
        {
            string H = Named(h), A = Named(a);
            if (a.Lock != null && SymbolEqualityComparer.Default.Equals(h.Lock, a.Lock) && h.Element == a.Element)
            {
                // (an array's elements: by index, CheckLockOrder; the same lock again: a lock is reentrant, and a semaphore taken twice is reported where it's checked)
                if (h.Receiver == a.Receiver || a.Lock is IFieldSymbol { IsStatic: true }) return;
                if (a.Element) { Report("CSV1025", at, $"'{A}' is taken while '{H}' is held: elements of two arrays, in an order nothing fixes, could deadlock", isError: true); return; }
                if (!a.Semaphore && !h.Semaphore && LockLevels.OrderedBy(a.Lock) != null) return; // (proved, CheckLockOrder)
                Report("CSV1025", at, a.Semaphore
                    ? $"'{a.Expression}' takes '{a.Lock.Name}' of '{a.Receiver}' while that of '{h.Receiver}' is held: two such semaphores, in an order nothing fixes, could deadlock"
                    : $"'{a.Expression}' is taken while '{h.Expression}' is held: two '{a.Lock.Name}' locks of different objects, in an order nothing fixes, could deadlock. Order them by an id: [LockLevel(n, OrderedBy = nameof(Id))]", isError: true);
                return;
            }
            Levels(h.Lock, a.Lock, at, $"'{A}' is taken while '{H}' is held", h.Element, a.Element);
        }

        /// <summary>What a call (or a task waited for) may take, while locks are held.</summary>
        private void OrderCalled(System.Collections.Generic.List<LockLevels.Acquired> held, LockLevels.Summary s, SyntaxNode at, string what = null)
        {
            what ??= $"'{at}'";
            if (s.Unknown != null)
            {
                Report("CSV1025", at, $"{what} while '{Named(held[0])}' is held, and it could take any lock: {s.Unknown}. Do it outside the lock, or say [TakesNoLocks] of what it runs", isError: true);
                return;
            }
            foreach (var t in s.Taken)
                foreach (var h in held)
                {
                    if (SymbolEqualityComparer.Default.Equals(h.Lock, t.Lock) && h.Element == t.Element)
                    {
                        // (the same object: a lock is reentrant; a semaphore taken again through a call is reported where it's checked)
                        if (!t.Element && (t.Lock is IFieldSymbol { IsStatic: true } || t.OnThis && h.Receiver == "this")) continue;
                        Report("CSV1025", at, $"{what} may take '{t.Lock.Name}' of another object (in '{t.In?.Name}') while '{Named(h)}' is held: in an order nothing fixes, they could deadlock. Take both in one method, ordered by [LockLevel(n, OrderedBy = ...)]", isError: true);
                        return;
                    }
                    if (!Levels(h.Lock, t.Lock, at, $"{what} may take '{t.Lock.Name}' (in '{t.In?.Name}') while '{Named(h)}' is held", h.Element, t.Element)) return;
                }
        }

        /// <summary>The held lock is of a lower level than the one taken. Reported, and false, if not.</summary>
        private bool Levels(ISymbol held, ISymbol taken, SyntaxNode at, string what, bool heldElement, bool takenElement)
        {
            int? lh = LockLevels.Level(held), lt = LockLevels.Level(taken);
            if (lh is int a && lt is int b)
            {
                if (a < b) return true;
                Report("CSV1025", at, $"{what}, of level {a}, not lower than {b}: locks must be taken in increasing order of level, or threads taking them in the other order could deadlock", isError: true);
                return false;
            }
            var notField = new[] { (held, heldElement), (taken, takenElement) }.FirstOrDefault(x => !(x.Item1 is IFieldSymbol));
            if (notField.Item1 != null || held == null || taken == null)
                Report("CSV1025", at, $"{what}, and a lock that isn't a field can't be given a level, so their order can't be fixed: lock on readonly fields with [LockLevel]", isError: true);
            else
                Report("CSV1025", at, $"{what}: give {(lh == null && lt == null ? "both" : lh == null ? $"'{held.Name}'" : $"'{taken.Name}'")} [LockLevel], the held one lower, so that no thread takes them in the other order", isError: true);
            return false;
        }

        /// <summary>
        /// Nested locks of one field on two objects, ordered by an id: the outer one's is lower. (Called where the inner one
        /// is entered, as for an array's elements.)
        /// </summary>
        private void CheckOrderedBy(LockStatementSyntax inner, Frame f, SpecEnv spec)
        {
            if (inner.Expression is ElementAccessExpressionSyntax || !(LockGuards.LockOf(inner.Expression, _model) is IFieldSymbol field) || field.IsStatic ||
                !(LockLevels.OrderedBy(field) is IFieldSymbol key)) return;
            if (!(key.IsReadOnly || key.IsConst))
            {
                Report("CSV1025", inner, $"'{field.Name}' is ordered by '{key.Name}', which may change: it must be readonly", isError: true);
                return;
            }
            var (_, _, innerReceiver) = LockLevels.LockTarget(inner.Expression, _model);
            for (var p = inner.Parent; p != null && p != _contract.Declaration; p = p.Parent)
            {
                if (p is AnonymousFunctionExpressionSyntax || p is LocalFunctionStatementSyntax) return;
                if (!(p is LockStatementSyntax outer) || !SymbolEqualityComparer.Default.Equals(LockGuards.LockOf(outer.Expression, _model), field)) continue;
                var (_, _, outerReceiver) = LockLevels.LockTarget(outer.Expression, _model);
                if (outerReceiver == innerReceiver) continue;
                if (!StaysTheSame(outerReceiver, outer.Statement) || !StaysTheSame(innerReceiver, inner.Statement) ||
                    !(_model.GetOperation(outer.Expression) is IFieldReferenceOperation o) || !(_model.GetOperation(inner.Expression) is IFieldReferenceOperation i))
                {
                    Report("CSV1025", inner, $"'{outer.Expression}' and '{inner.Expression}': their order can't be told, since '{outerReceiver}' or '{innerReceiver}' may change under the lock", isError: true);
                    continue;
                }
                var before = ReadField(key, o.Instance, key.Type, outer, f, spec);
                var after = ReadField(key, i.Instance, key.Type, inner, f, spec);
                Prove(T.Lt(T.Coerce(before, Sort.Int), T.Coerce(after, Sort.Int)), "CSV1025", inner,
                    $"'{inner.Expression}' might not come after '{outer.Expression}' by '{key.Name}': two '{field.Name}' locks taken in different orders can deadlock");
            }
        }
    }
}
