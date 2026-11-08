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
    internal sealed partial class MethodVerifier
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

        // ---- two locks of one field or class, ordered by an id: proved where the second is taken ----

        /// <summary>The object whose key orders a lock: its owner, as a term here. Null if that expression can't be read again without running anything.</summary>
        private Term OwnerTerm(ExpressionSyntax owner, Frame f, SpecEnv spec)
        {
            if (owner == null) return f.This;
            var op = _model.GetOperation(owner);
            while (op is IConversionOperation c && c.IsImplicit || op is IParenthesizedOperation) op = op is IConversionOperation cc ? cc.Operand : ((IParenthesizedOperation)op).Operand;
            return Rereadable(op) ? T.Coerce(Eval(op, f, spec), Sort.Int) : null;
        }

        private static bool Rereadable(IOperation op) =>
            op is IInstanceReferenceOperation || op is ILocalReferenceOperation || op is IParameterReferenceOperation ||
            op is IFieldReferenceOperation fr && (fr.Instance == null || Rereadable(fr.Instance));

        private Term Key(IFieldSymbol key, Term owner, Frame f)
        {
            var v = T.Coerce(T.Select(FieldMap(f, key), owner, ValueSort(key)), Sort.Int);
            return InRangeOf(v, key.Type);
        }

        private bool OrderKeyIsFixed(IFieldSymbol key, SyntaxNode at, ISymbol lockSymbol)
        {
            if (key.IsReadOnly || key.IsConst) return true;
            Report("CSV1025", at, $"'{lockSymbol.Name}' is ordered by '{key.Name}', which may change: it must be readonly", isError: true);
            return false;
        }

        /// <summary>A lock taken here (in a lock statement, a semaphore's form or a using) after another of its field or class: in increasing order of id.</summary>
        private void ProveOrderAt(SyntaxNode inner, Frame f, SpecEnv spec)
        {
            if (!_codeMode) return;
            LockLevels.Acquired a = null;
            foreach (var x in inner.AncestorsAndSelf())
            {
                if ((a = _engine.Levels.AcquiredAt(x, _model)) != null || x is StatementSyntax && !(x is LocalDeclarationStatementSyntax || x is UsingStatementSyntax)) break;
            }
            if (a?.Lock == null || a.Element || a.Static || !(LockLevels.OrderedBy(a.Lock) is IFieldSymbol key) || !OrderKeyIsFixed(key, a.At, a.Lock)) return;
            foreach (var h in _engine.Levels.HeldAt(a.At, _contract.Declaration, _model))
            {
                if (h == null || !SymbolEqualityComparer.Default.Equals(h.Lock, a.Lock) || h.Element || h.Receiver == a.Receiver) continue;
                var before = OwnerTerm(h.Owner, f, spec);
                var after = OwnerTerm(a.Owner, f, spec);
                if (before == null || after == null || !StaysTheSame(h.Receiver, HeldRegion(h)))
                {
                    Report("CSV1025", a.At, $"'{Named(a)}' and '{Named(h)}': their order can't be told, since '{h.Receiver}' or '{a.Receiver}' may change while they're held", isError: true);
                    continue;
                }
                Prove(T.Lt(Key(key, before, f), Key(key, after, f)), "CSV1025", a.At,
                    $"'{a.Receiver}''s '{a.Lock.Name}' might not come after '{h.Receiver}''s by '{key.Name}': two of them taken in different orders can deadlock");
            }
        }

        /// <summary>A call, while a lock is held, that takes another of its field or class, of an object it's given: in increasing order of id.</summary>
        private void ProveOrderAtCall(IOperation op, Frame f, SpecEnv spec)
        {
            if (!_codeMode || !(op is IInvocationOperation || op is IPropertyReferenceOperation || op is IObjectCreationOperation)) return;
            var node = op.Syntax is MemberAccessExpressionSyntax pm && op is IPropertyReferenceOperation ? pm.Name : op.Syntax;
            var held = _engine.Levels.HeldAt(node, _contract.Declaration, _model).Where(h => h?.Lock != null && !h.Element && !h.Static && LockLevels.OrderedBy(h.Lock) != null).ToList();
            if (held.Count == 0) return;
            IOperation instance = op is IInvocationOperation inv ? inv.Instance : op is IPropertyReferenceOperation pr ? pr.Instance : null;
            var args = op is IInvocationOperation i2 ? i2.Arguments : op is IPropertyReferenceOperation p2 ? p2.Arguments : ((IObjectCreationOperation)op).Arguments;
            var site = CallSite(node);
            foreach (var t in _engine.Levels.OfCall(node, _model, _method).Taken)
                foreach (var h in held)
                {
                    if (!SymbolEqualityComparer.Default.Equals(h.Lock, t.Lock) || t.Element || !(t.Origin is LockLevels.Origin { AtCall: true } o)) continue;
                    if (SameObject(h, ReceiverOf(t.Origin, site)) || !(LockLevels.OrderedBy(t.Lock) is IFieldSymbol key) || !OrderKeyIsFixed(key, node, t.Lock)) continue;
                    var given = o.Index < 0 ? instance : args.FirstOrDefault(a => a.Parameter?.Ordinal == o.Index)?.Value;
                    while (given is IConversionOperation c && c.IsImplicit) given = c.Operand;
                    var before = OwnerTerm(h.Owner, f, spec);
                    Term after = given == null ? null : given is IInstanceReferenceOperation ? f.This : Rereadable(given) ? T.Coerce(Eval(given, f, spec), Sort.Int) : null;
                    if (before == null || after == null || !StaysTheSame(h.Receiver, HeldRegion(h)))
                    {
                        Report("CSV1025", node, $"'{node}' takes '{t.Lock.Name}' (in '{t.In?.Name}') while '{Named(h)}' is held, and their order can't be told: pass a local, a parameter or a field", isError: true);
                        continue;
                    }
                    Prove(T.Lt(Key(key, before, f), Key(key, after, f)), "CSV1025", node,
                        $"'{node}' takes '{t.Lock.Name}' (in '{t.In?.Name}') of '{given.Syntax}', which might not come after '{h.Receiver}''s by '{key.Name}': two of them taken in different orders can deadlock");
                }
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

        /// <summary>
        /// Monitor.Wait gives the lock back and takes it again: what it guards may have changed meanwhile, and its invariants
        /// must hold for the others, and hold again after. Pulse changes nothing here. Null for any other call.
        /// </summary>
        private Term MonitorSignal(IInvocationOperation inv, Frame f, SpecEnv spec)
        {
            if (!_codeMode || inv.TargetMethod.ContainingType?.ToDisplayString() != "System.Threading.Monitor") return null;
            var name = inv.TargetMethod.Name;
            if (name == "Pulse" || name == "PulseAll") { Eval(inv.Arguments[0].Value, f, spec); return T.True; }
            if (name != "Wait") return null;
            foreach (var a in inv.Arguments.Skip(1)) Eval(a.Value, f, spec);
            if (inv.Arguments[0].Value.Syntax is ExpressionSyntax target && LockGuards.LockOf(target, _model) is IFieldSymbol guard)
            {
                Term owner = guard.IsStatic ? null : _model.GetOperation(target) is IFieldReferenceOperation fr && fr.Instance != null && !(fr.Instance is IInstanceReferenceOperation) ? T.Coerce(Eval(fr.Instance, f, spec), Sort.Int) : f.This;
                foreach (var invariant in LockInvariantsOf(guard, owner, f))
                    Prove(invariant, "CSV1024", inv.Syntax, $"the invariant of lock '{guard.Name}' might not hold at '{inv.Syntax}', which gives it to others");
                foreach (var field in _engine.Locks.GuardedBy(guard))
                    if (FieldEffects.IsHeapField(field))
                        f.Fields[FieldEffects.Key(field)] = _z3.Fresh(field.Name + "$waited", FieldMap(f, field).Sort);
                foreach (var invariant in LockInvariantsOf(guard, owner, f)) _z3.Assume(invariant);
            }
            else
                Eval(inv.Arguments[0].Value, f, spec);
            // (with a timeout, whether it was pulsed; without one, true)
            return inv.Arguments.Length == 1 ? T.True : _z3.Fresh("pulsed", Sort.Bool);
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
