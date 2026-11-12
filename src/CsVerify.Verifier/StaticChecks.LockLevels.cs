using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Deadlock freedom by lock levels (see LockLevels): while a lock is held, a lock taken, a call, or a task waited for
    /// takes only locks of higher levels, and nothing is waited for that only another thread can end (CSV1025). Then every
    /// thread takes its locks in increasing order and no cycle of threads can wait on each other. Two locks of one field
    /// or class are ordered by their objects' ids (OrderedBy), proved where the second is taken, directly or by a call;
    /// an array's elements by index (CheckLockOrder). And blocking on async code that comes back to the context it
    /// started on would wait for itself.
    /// </summary>
    internal sealed partial class StaticChecks
    {
        private void CheckLockLevels()
        {
            if (SpecSymbols.HasAttribute(_method, "TrustedAttribute")) return;
            // (a lambda or local function is looked at with the code around it, but for one in a field's initializer, which has none)
            var root = _contract.Declaration;
            if (NestedGraph != null && !(root.Ancestors().Any(a => a is EqualsValueClauseSyntax) && !root.Ancestors().Any(a => a is AnonymousFunctionExpressionSyntax || a is LocalFunctionStatementSyntax))) return;
            var levels = _engine.Levels;
            foreach (var (at, message) in levels.Misdeclared())
                if (levels.Claim(at))
                    Report("CSV1025", at, message, isError: true);
            if (NestedGraph == null && levels.TakesNoLocks(_method) && levels.OfBody(_method) is LockLevels.Summary own && !own.IsEmpty)
                Report("CSV1025", MethodLocationNode(), $"'{_method.Name}' is said to take no locks, but {Takes(own)}", isError: true);
            foreach (var n in root.DescendantNodesAndSelf())
            {
                CheckSaidToTakeNone(n);
                CheckBlockingOnContext(n, root);
                var acquired = levels.AcquiredAt(n, _model);
                if (acquired?.Formless == true)
                    Report("CSV1025", n, $"'{n.ToString().Trim()}' takes a lock that no finally right after gives back: write it as '{n.ToString().Trim()} try {{ ... }} finally {{ ...Exit...; }}', so where it is held can be told", isError: true);
                bool calls = n is InvocationExpressionSyntax || n is BaseObjectCreationExpressionSyntax || n is ElementAccessExpressionSyntax ||
                             n is SimpleNameSyntax && _model.GetSymbolInfo(n).Symbol is IPropertySymbol;
                var waited = LockLevels.WaitedFor(n, _model).ToList();
                var monitor = MonitorCall(n);
                var blocks = monitor == null ? levels.Blocking(n, _model) : null;
                bool implicitly = n is ExpressionSyntax || n is CommonForEachStatementSyntax || n is UsingStatementSyntax || n is LocalDeclarationStatementSyntax || n is SubpatternSyntax;
                if (acquired == null && !calls && !implicitly && waited.Count == 0 && monitor == null && blocks == null) continue;
                var held = levels.HeldAt(n, root, _model).Where(h => h != null).ToList();
                if (monitor != null) CheckMonitor(monitor.Value.name, monitor.Value.target, held, n);
                if (held.Count == 0) continue;
                if (acquired != null)
                    foreach (var h in held) OrderDirect(h, acquired, n);
                if (calls) OrderCalled(held, levels.OfCall(n, _model, _method), n, CallSite(n));
                if (implicitly && levels.OfImplicit(n, _model, _method) is LockLevels.Summary hidden && !hidden.IsEmpty) OrderCalled(held, hidden, n, null);
                if (blocks != null)
                    Report("CSV1025", n, $"{blocks}, while '{Named(held[0])}' is held: whoever would signal it may need that lock. Wait outside the lock", isError: true);
                foreach (var w in waited)
                {
                    if (LockLevels.Given(w, _model, root) is string why)
                    {
                        Report("CSV1025", n, $"'{n}' waits while '{Named(held[0])}' is held, for {why}. Wait outside the lock", isError: true);
                        continue;
                    }
                    // (a task this code started: it may need what's held to finish)
                    foreach (var v in LockLevels.ValuesOf(w, _model, root) ?? new List<ExpressionSyntax>())
                    {
                        var e = LockLevels.Stripped(v);
                        var started = e is InvocationExpressionSyntax si && si.ArgumentList.Arguments.FirstOrDefault()?.Expression is AnonymousFunctionExpressionSyntax lam &&
                                      _model.GetSymbolInfo(si).Symbol is IMethodSymbol sm && sm.DeclaringSyntaxReferences.Length == 0
                            ? levels.OfRegion(lam, _model, _method) : levels.OfCall(e, _model, _method);
                        OrderCalled(held, started, n, null, $"'{n}' waits for '{v}'");
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
                     _model.GetSymbolInfo(n).Symbol is IMethodSymbol group && _model.GetTypeInfo(e).Type == null)
                s = _engine.Levels.Of(group);
            else return;
            if (!s.IsEmpty) Report("CSV1025", n, $"'{dt.Name}' takes no locks, but {Takes(s)}", isError: true);
        }

        private static string Takes(LockLevels.Summary s) =>
            s.Taken.Count > 0 ? $"it may take '{s.Taken[0].Lock.Name}' (in '{s.Taken[0].In?.Name}')" : $"it could take any lock: {s.Unknown}";

        private static string Named(LockLevels.Acquired a) => a.Expression is StatementSyntax ? a.Lock?.Name ?? a.Expression.ToString() : a.Expression.ToString();

        /// <summary>Where a held lock is held: a lock's statement, a semaphore's try, a using, or the rest of a block.</summary>
        private static SyntaxNode HeldRegion(LockLevels.Acquired h) =>
            h.At is LockStatementSyntax l ? l.Statement : h.At is UsingStatementSyntax u ? u.Statement :
            h.At is StatementSyntax st && LockGuards.TryAfter(st) is TryStatementSyntax t ? t : h.At.Parent;

        /// <summary>Is the held lock's object the one named so, and does that name keep its object while it's held?</summary>
        private bool SameObject(LockLevels.Acquired h, string receiver) =>
            receiver != null && h.Receiver == receiver && StaysTheSame(receiver, HeldRegion(h));

        /// <summary>A lock taken right here, while another is held.</summary>
        private void OrderDirect(LockLevels.Acquired h, LockLevels.Acquired a, SyntaxNode at)
        {
            string H = Named(h), A = Named(a);
            if (a.Lock != null && SymbolEqualityComparer.Default.Equals(h.Lock, a.Lock) && h.Element == a.Element)
            {
                // (the same lock again: a lock is reentrant, and a semaphore taken twice is reported where it's checked; an array's elements: by index, CheckLockOrder)
                if (h.Receiver == a.Receiver || a.Static) return;
                if (a.Element) { Report("CSV1025", at, $"'{A}' is taken while '{H}' is held: elements of two arrays, in an order nothing fixes, could deadlock", isError: true); return; }
                if (LockLevels.OrderedBy(a.Lock) != null) return; // (proved, ProveOrderAt)
                Report("CSV1025", at, $"'{A}' is taken while '{H}' is held: two '{a.Lock.Name}' locks of different objects, in an order nothing fixes, could deadlock. Order them by an id: [LockLevel(n, OrderedBy = nameof(Id))]", isError: true);
                return;
            }
            Levels(h.Lock, a.Lock, at, $"'{A}' is taken while '{H}' is held");
        }

        /// <summary>What a call is made on and with, as written: to tell whose the locks it takes are.</summary>
        private sealed class Site
        {
            public string Receiver;
            public Dictionary<int, string> Arguments = new Dictionary<int, string>();
        }

        private Site CallSite(SyntaxNode n)
        {
            var node = n is SimpleNameSyntax name && name.Parent is MemberAccessExpressionSyntax pm && pm.Name == name ? pm : n;
            var site = new Site();
            IOperation instance = null;
            IEnumerable<IArgumentOperation> args = null;
            switch (_model.GetOperation(node))
            {
                case IInvocationOperation inv: instance = inv.Instance; args = inv.Arguments; break;
                case IPropertyReferenceOperation pr: instance = pr.Instance; args = pr.Arguments; break;
                case IObjectCreationOperation oc: args = oc.Arguments; site.Receiver = null; break;
                default: return site;
            }
            if (!(_model.GetOperation(node) is IObjectCreationOperation))
                site.Receiver = instance == null || instance is IInstanceReferenceOperation ? "this" : instance.Syntax.ToString();
            foreach (var a in args ?? Enumerable.Empty<IArgumentOperation>())
                if (a.Parameter != null && a.ArgumentKind == ArgumentKind.Explicit) site.Arguments[a.Parameter.Ordinal] = a.Value.Syntax.ToString();
            return site;
        }

        /// <summary>Whose a lock taken by a call is, as written here; null if that can't be told.</summary>
        private string ReceiverOf(LockLevels.Origin? o, Site site)
        {
            if (!(o is LockLevels.Origin origin)) return null;
            if (!origin.AtCall) return origin.Index < 0 ? "this" : origin.Index < _method.Parameters.Length ? _method.Parameters[origin.Index].Name : null;
            if (site == null) return null;
            return origin.Index < 0 ? site.Receiver : site.Arguments.TryGetValue(origin.Index, out var a) ? a : null;
        }

        /// <summary>What a call (or a task waited for) may take, while locks are held.</summary>
        private void OrderCalled(List<LockLevels.Acquired> held, LockLevels.Summary s, SyntaxNode at, Site site, string what = null)
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
                        var whose = ReceiverOf(t.Origin, site);
                        bool isStatic = t.Lock is IFieldSymbol { IsStatic: true };
                        if (!t.Element && (isStatic || SameObject(h, whose)))
                        {
                            // (the same object: a lock is reentrant; a semaphore isn't)
                            if (!t.Semaphore) continue;
                            Report("CSV1025", at, $"{what} takes '{t.Lock.Name}' (in '{t.In?.Name}'), which is held here: it would wait for itself", isError: true);
                            return;
                        }
                        // (two objects ordered by an id: proved where the call is made, ProveOrderAtCall)
                        if (!t.Element && LockLevels.OrderedBy(t.Lock) != null && t.Origin is LockLevels.Origin { AtCall: true } && site != null) continue;
                        Report("CSV1025", at, $"{what} may take '{t.Lock.Name}' of {(whose == null ? "an object that can't be told" : $"'{whose}'")} (in '{t.In?.Name}') while '{Named(h)}' is held: in an order nothing fixes, they could deadlock. Order them by an id: [LockLevel(n, OrderedBy = nameof(Id))]", isError: true);
                        return;
                    }
                    if (!Levels(h.Lock, t.Lock, at, $"{what} may take '{t.Lock.Name}' (in '{t.In?.Name}') while '{Named(h)}' is held")) return;
                }
        }

        /// <summary>The held lock is of a lower level than the one taken. Reported, and false, if not.</summary>
        private bool Levels(ISymbol held, ISymbol taken, SyntaxNode at, string what)
        {
            int? lh = LockLevels.Level(held), lt = LockLevels.Level(taken);
            if (lh is int a && lt is int b)
            {
                if (a < b) return true;
                Report("CSV1025", at, $"{what}, of level {a}, not lower than {b}: locks must be taken in increasing order of level, or threads taking them in the other order could deadlock", isError: true);
                return false;
            }
            if (held == null || taken == null)
                Report("CSV1025", at, $"{what}, and a lock on an object (or interface) can't be given a level, so their order can't be fixed: lock on a field, or on an object of a class with [LockLevel]", isError: true);
            else
                Report("CSV1025", at, $"{what}: give {(lh == null && lt == null ? "both" : lh == null ? $"'{held.Name}'" : $"'{taken.Name}'")} [LockLevel] (on the field, or the class whose objects are locked), the held one lower, so that no thread takes them in the other order", isError: true);
            return false;
        }

        // ---- Monitor.Wait and Pulse ----

        private (string name, ExpressionSyntax target)? MonitorCall(SyntaxNode n)
        {
            if (!(n is InvocationExpressionSyntax inv) || !(_model.GetSymbolInfo(inv).Symbol is IMethodSymbol m) || m.ContainingType?.ToDisplayString() != "System.Threading.Monitor") return null;
            if (!(m.Name == "Wait" || m.Name == "Pulse" || m.Name == "PulseAll") || inv.ArgumentList.Arguments.Count == 0) return null;
            return (m.Name, inv.ArgumentList.Arguments[0].Expression);
        }

        /// <summary>
        /// Wait and Pulse need the lock held (or they throw). And Wait gives back only that lock: any other still held could be
        /// what the thread that would pulse it needs first.
        /// </summary>
        private void CheckMonitor(string name, ExpressionSyntax target, List<LockLevels.Acquired> held, SyntaxNode at)
        {
            var (sym, element, _, receiver, isStatic) = _engine.Levels.LockTarget(target, _model);
            bool Same(LockLevels.Acquired h) => SymbolEqualityComparer.Default.Equals(h.Lock, sym) && h.Element == element && !h.Semaphore && (isStatic || SameObject(h, receiver));
            bool ownLock = SymbolEqualityComparer.Default.Equals(_engine.Locks.GuardOf(_method), sym) && receiver == "this";
            if (!held.Any(Same) && !ownLock)
            {
                Report("CSV1023", at, $"'{at}' needs '{target}' held here, or it throws: call it inside 'lock ({target})'", isError: true);
                return;
            }
            if (name != "Wait") return;
            if (held.FirstOrDefault(h => !Same(h)) is LockLevels.Acquired other)
                Report("CSV1025", at, $"'{at}' waits, giving back '{target}' but still holding '{Named(other)}': the thread that would pulse it may need that lock first", isError: true);
            if (_engine.Locks.GuardOf(_method) is IFieldSymbol g && !SymbolEqualityComparer.Default.Equals(g, sym))
                Report("CSV1025", at, $"'{at}' waits, giving back '{target}' but still holding '{g.Name}', which its caller holds for it: the thread that would pulse it may need that lock first", isError: true);
        }

        // ---- blocking on async code that comes back to its context ----

        /// <summary>
        /// Blocking on a task of the program's async code (<c>F().Result</c>, <c>F().Wait()</c>, <c>GetResult()</c>) while
        /// that code, somewhere, resumes on the context it started on: from a single-threaded context (a UI thread), the
        /// context is the blocked thread, so it never resumes.
        /// </summary>
        private void CheckBlockingOnContext(SyntaxNode n, SyntaxNode root)
        {
            foreach (var (task, blocks) in LockLevels.Blocked(n, _model))
            {
                if (!blocks || LockLevels.OnThePool(n, _model)) continue;
                var calls = task is InvocationExpressionSyntax ? new List<ExpressionSyntax> { task } : LockLevels.ValuesOf(task, _model, root) ?? new List<ExpressionSyntax>();
                foreach (var c in calls.Select(LockLevels.Stripped).OfType<InvocationExpressionSyntax>())
                {
                    if (!(_model.GetSymbolInfo(c).Symbol is IMethodSymbol m) || !IsTaskLike(m.ReturnType)) continue;
                    if (_engine.Levels.KeepsContext(m) is SyntaxNode back)
                    {
                        Report("CSV1025", n, $"'{n}' blocks on '{c}', which resumes on the context it started on at '{Short(back)}' ({back.SyntaxTree.FilePath.Split('/', '\\').Last()}:{LineOf(back)}): on a UI thread or another single-threaded context, that is this blocked thread, so it never resumes. Write ConfigureAwait(false) there, or await instead of blocking", isError: true);
                        break;
                    }
                }
            }
        }

        private static string Short(SyntaxNode n)
        {
            var s = n.ToString().Replace('\n', ' ');
            return s.Length > 60 ? s.Substring(0, 57) + "..." : s;
        }
    }
}
