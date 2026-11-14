using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Locks (see LockGuards). What a lock guards is reachable only under it, which is checked from the syntax, as in
    /// Clang's thread safety analysis (CSV1023). So no other thread writes it while this one holds the lock, and the
    /// assumption that nothing else writes the state a method uses (A4) is proved for it. Entering a lock forgets what it
    /// guards, since others have had it, and gives its invariants; leaving it, or a call that might enter it again,
    /// must restore them (CSV1024).
    /// </summary>
    internal sealed partial class StaticChecks
    {
        /// <summary>Every use of guarded state in this method is under its lock. The lambdas in it are looked at with it.</summary>
        private void CheckLocking()
        {
            var locks = _engine.Locks;
            if (!locks.Any || SpecSymbols.HasAttribute(_method, "TrustedAttribute")) return;
            CheckInvariantIsEstablished();
            CheckWrapper();
            var asked = new HashSet<ISymbol>(SymbolEqualityComparer.Default);
            foreach (var n in _contract.Declaration.DescendantNodes().OfType<SimpleNameSyntax>())
            {
                var symbol = _model.GetSymbolInfo(n).Symbol;
                if (symbol == null || !(symbol is IFieldSymbol || symbol is IPropertySymbol || symbol is IMethodSymbol)) continue;
                CheckGateUse(n, symbol);
                if (locks.GuardOf(symbol) is not IFieldSymbol guard)
                {
                    // (written under a lock elsewhere, and used here without it: the program seems to mean it guarded, but doesn't say so)
                    if (locks.UnmarkedGuard(symbol) is IFieldSymbol meant && !(n.Parent is NameColonSyntax || n.Parent is NameEqualsSyntax) &&
                        !IsBeingBuilt(n, ReceiverOf(n)) && !Holds(n, meant, ReceiverOf(n)) && asked.Add(symbol))
                        Report("CSV1023", n, $"'{symbol.Name}' is written under lock '{meant.Name}' elsewhere, but used here without it: this could race. If the lock guards it, say [GuardedBy(nameof({meant.Name}))]", isError: true);
                    continue;
                }
                if (n.Parent is NameColonSyntax || n.Parent is NameEqualsSyntax) continue;
                var receiver = ReceiverOf(n);
                if (IsBeingBuilt(n, receiver)) continue;
                if (!(guard.IsReadOnly || guard.IsConst || _engine.Locks.IsFlag(guard)))
                    Report("CSV1023", n, $"'{guard.Name}' guards '{symbol.Name}', but it isn't readonly: threads could hold different objects", isError: true);
                else if (_engine.Locks.IsSemaphore(guard) && !locks.IsMutexGate(guard))
                    Report("CSV1023", n, $"'{guard.Name}' guards '{symbol.Name}', but it isn't made with a count of 1: it may let more than one in", isError: true);
                else if (n.FirstAncestorOrSelf<RefExpressionSyntax>() is RefExpressionSyntax r && !(symbol is IMethodSymbol) && r.Expression.DescendantNodesAndSelf().Contains(n))
                    Report("CSV1023", n, $"a ref to '{n}' outlives lock '{guard.Name}': whoever has it can use it without the lock", isError: true);
                else if (!Holds(n, guard, receiver))
                    Report("CSV1023", n, $"'{n}' {(symbol is IMethodSymbol ? "needs" : "is guarded by")} lock '{guard.Name}', which might not be held here: this could race", isError: true);
            }
        }

        /// <summary>
        /// A lock's invariant is known from its first use, so something must have made it true: a constructor does, and proves
        /// it (see ConstructorEstablishesLocks). An implicit one has no body to prove it of, so the class must write one.
        /// </summary>
        private void CheckInvariantIsEstablished()
        {
            if (!LockGuards.IsInvariant(_method) || !(_engine.Locks.GuardOf(_method) is IFieldSymbol guard)) return;
            var ctors = guard.IsStatic ? _method.ContainingType.StaticConstructors : _method.ContainingType.InstanceConstructors;
            if (!ctors.Any(c => !c.IsImplicitlyDeclared))
                Report("CSV1024", MethodLocationNode(), $"nothing establishes the invariant of lock '{guard.Name}': give {_method.ContainingType.Name} a {(guard.IsStatic ? "static " : "")}constructor, which must", isError: true);
        }

        /// <summary>What a member is used on, as written; "this" when it isn't.</summary>
        private static string ReceiverOf(SyntaxNode n)
        {
            if (n.Parent is MemberAccessExpressionSyntax ma && ma.Name == n) return ma.Expression.ToString();
            return "this";
        }

        /// <summary>The object isn't shared yet: a constructor's own, or a new object's initializer.</summary>
        private bool IsBeingBuilt(SyntaxNode n, string receiver)
        {
            if (n.Parent is AssignmentExpressionSyntax a && a.Left == n && a.Parent is InitializerExpressionSyntax) return true;
            // (a static constructor has its type's statics to itself: the runtime runs it once, before anything else uses them)
            if (_method.MethodKind == MethodKind.StaticConstructor && _model.GetSymbolInfo(n).Symbol is ISymbol s && s.IsStatic &&
                SymbolEqualityComparer.Default.Equals(s.ContainingType, _method.ContainingType) && !CrossesFunction(n)) return true;
            return receiver == "this" && _method.MethodKind == MethodKind.Constructor && !CrossesFunction(n);
        }

        private bool CrossesFunction(SyntaxNode n)
        {
            for (var p = n.Parent; p != null && p != _contract.Declaration; p = p.Parent)
                if (p is AnonymousFunctionExpressionSyntax || p is LocalFunctionStatementSyntax) return true;
            return false;
        }

        /// <summary>
        /// Is the lock held at this point, on that object? By an enclosing lock statement (not outside a lambda or local
        /// function, which run who knows when), or by the method's own [GuardedBy], for its own object.
        /// </summary>
        private bool Holds(SyntaxNode n, IFieldSymbol guard, string receiver)
        {
            string wanted = guard.IsStatic ? null : receiver;
            for (var p = n.Parent; p != null; p = p.Parent)
            {
                switch (p)
                {
                    case LockStatementSyntax l when l.Statement.Span.Contains(n.Span) && SymbolEqualityComparer.Default.Equals(LockGuards.LockOf(l.Expression, _model), guard):
                        if (wanted == null) return true;
                        var lockReceiver = l.Expression is MemberAccessExpressionSyntax ma ? ma.Expression.ToString() : "this";
                        if (lockReceiver == wanted && StaysTheSame(wanted, l.Statement)) return true;
                        break;
                    case TryStatementSyntax t when SymbolEqualityComparer.Default.Equals(_engine.Locks.GateOfTry(t, _model), guard) && _engine.Locks.HeldParts(t, _model).Any(h => h.Span.Contains(n.Span)):
                        if (wanted == null) return true;
                        if (GateReceiver(t, guard) == wanted && StaysTheSame(wanted, t)) return true;
                        break;
                    case TryStatementSyntax pt when LockGuards.PrimitiveForm(pt, _model) is { } form && (form.kind == "Monitor" || form.kind == "Flag") && form.held.Any(h => h.Span.Contains(n.Span)) &&
                                                    SymbolEqualityComparer.Default.Equals(LockGuards.LockOf(form.lockExpr, _model), guard):
                        if (wanted == null) return true;
                        if ((form.lockExpr is MemberAccessExpressionSyntax pma ? pma.Expression.ToString() : "this") == wanted && StaysTheSame(wanted, pt)) return true;
                        break;
                    case UsingStatementSyntax u when u.Statement.Span.Contains(n.Span) && SymbolEqualityComparer.Default.Equals(_engine.Locks.GateOfUsing(u, _model), guard):
                        if (wanted == null) return true;
                        if (UsingOwner(u.Expression ?? u.Declaration.Variables[0].Initializer.Value) == wanted && StaysTheSame(wanted, u)) return true;
                        break;
                    case BlockSyntax b:
                        foreach (var (gate, at) in _engine.Locks.UsingsBefore(n, b, _model))
                            if (SymbolEqualityComparer.Default.Equals(gate, guard) && (wanted == null || UsingOwner(at.Declaration.Variables[0].Initializer.Value) == wanted && StaysTheSame(wanted, b)))
                                return true;
                        break;
                    case AnonymousFunctionExpressionSyntax _:
                    case LocalFunctionStatementSyntax _:
                        return false;
                }
                if (p == _contract.Declaration) break;
            }
            // (a method holding its own lock, or one its contract is about)
            return (wanted == "this" || wanted == null) && SymbolEqualityComparer.Default.Equals(_engine.Locks.GuardOf(_method), guard) &&
                   SymbolEqualityComparer.Default.Equals(_method.ContainingType, guard.ContainingType);
        }

        /// <summary>The receiver is one object for all of the lock: this, or a name that the lock statement doesn't assign.</summary>
        private bool StaysTheSame(string receiver, SyntaxNode l)
        {
            if (receiver == "this") return true;
            if (!SyntaxFacts.IsValidIdentifier(receiver)) return false;
            return !l.DescendantNodes().OfType<AssignmentExpressionSyntax>().Any(a => StaysTheSameNamed(a.Left, receiver)) &&
                   !l.DescendantNodes().OfType<ForEachVariableStatementSyntax>().Any(fe => StaysTheSameNamed(fe.Variable, receiver)) &&
                   !l.DescendantNodes().OfType<ArgumentSyntax>().Any(a => !a.RefKindKeyword.IsKind(SyntaxKind.None) && a.Expression.ToString() == receiver);
        }

        private bool StaysTheSameNamed(ExpressionSyntax e, string receiver) => e.ToString() == receiver || e is TupleExpressionSyntax t && t.Arguments.Any(x => StaysTheSameNamed(x.Expression, receiver));

        // ---- a SemaphoreSlim used as a lock (see LockGuards). Unlike a lock it may be held across an await, and a second try at it waits forever. ----

        /// <summary>The object whose semaphore a try holds, as written.</summary>
        private string GateReceiver(TryStatementSyntax t, IFieldSymbol gate) =>
            t.Finally.Block.DescendantNodes().OfType<InvocationExpressionSyntax>()
                .Where(i => SymbolEqualityComparer.Default.Equals(_engine.Locks.GateOfWrapper(i, _model, false), gate) ||
                            i.Expression is MemberAccessExpressionSyntax ma && ma.Name.Identifier.Text == "Release" && SymbolEqualityComparer.Default.Equals(_model.GetSymbolInfo(ma.Expression).Symbol, gate))
                .Select(i => _engine.Locks.OwnerOf(i, _model)).First();

        private string UsingOwner(ExpressionSyntax taking)
        {
            var e = taking is AwaitExpressionSyntax aw ? aw.Expression : taking;
            if (e is InvocationExpressionSyntax ca && ca.Expression is MemberAccessExpressionSyntax cm && cm.Name.Identifier.Text == "ConfigureAwait") e = cm.Expression;
            return _engine.Locks.OwnerOf((InvocationExpressionSyntax)e, _model);
        }

        /// <summary>
        /// A semaphore that guards something can only be taken and given back in the one form, and can't be handed to anyone:
        /// a Release elsewhere would let a second one in. And taking it while it is held waits for itself (CSV1025).
        /// </summary>
        private void CheckGateUse(SimpleNameSyntax n, ISymbol symbol)
        {
            // (a wrapper's own body: what it does with it is looked at by CheckWrapper)
            if (_engine.Locks.Acquires(_method) || _engine.Locks.Releases(_method)) return;
            // EnterAsync(): the lock it names is taken by it, in one of the forms only
            if (symbol is IMethodSymbol wrapper && (_engine.Locks.Acquires(wrapper) || _engine.Locks.Releases(wrapper)) && WholeCall(n) is InvocationExpressionSyntax whole0)
            {
                bool acquiring = _engine.Locks.Acquires(wrapper);
                if (_engine.Locks.GateOfWrapper(whole0, _model, acquiring) is IFieldSymbol wrapped && _engine.Locks.GuardedBy(wrapped).Any())
                {
                    if (!_engine.Locks.IsWrapperInForm(whole0, wrapped, _model))
                        Report("CSV1023", whole0, $"'{whole0}': '{wrapped.Name}' guards state, so it must be taken as 'using ({(wrapper.IsAsync ? "await " : "")}{whole0}) {{ ... }}', or in a try whose finally gives it back", isError: true);
                    else if (acquiring && Holds(n, wrapped, _engine.Locks.OwnerOf(whole0, _model)))
                        Report("CSV1025", whole0, $"'{wrapped.Name}' is held here, and it can't be taken twice: this would wait for itself", isError: true);
                }
                return;
            }
            if (symbol is IMethodSymbol callee && (n.Parent is InvocationExpressionSyntax || n.Parent is MemberAccessExpressionSyntax m0 && m0.Name == n && (m0.Expression is ThisExpressionSyntax)))
                foreach (var gate in _engine.Locks.GatesTakenBy(callee))
                    if (Holds(n, gate, "this"))
                        Report("CSV1025", n, $"'{n}' takes '{gate.Name}', which is held here: it would wait for itself", isError: true);
            if (!_engine.Locks.IsSemaphore(symbol) || !(symbol is IFieldSymbol g) || !_engine.Locks.GuardedBy(g).Any()) return;
            ExpressionSyntax whole = n.Parent is MemberAccessExpressionSyntax own && own.Name == n ? own : n;
            if (whole.Parent is MemberAccessExpressionSyntax use && use.Expression == whole)
            {
                string name = use.Name.Identifier.Text;
                if (name == "Dispose" || name == "CurrentCount") return;
                // (_lock.LockAsync(): looked at above, as a call)
                if (use.Parent is InvocationExpressionSyntax wrapperCall && _model.GetSymbolInfo(wrapperCall).Symbol is IMethodSymbol w && (_engine.Locks.Acquires(w) || _engine.Locks.Releases(w))) return;
                if (use.Parent is InvocationExpressionSyntax inv && (name == "Wait" || name == "WaitAsync" || name == "Release"))
                {
                    if (!_engine.Locks.IsInForm(inv, g, _model))
                        Report("CSV1023", inv, $"'{inv}': '{g.Name}' guards state, so it must be taken as 'await {g.Name}.WaitAsync(); try {{ ... }} finally {{ {g.Name}.Release(); }}'", isError: true);
                    else if (name != "Release" && Holds(n, g, whole is MemberAccessExpressionSyntax o && !(o.Expression is ThisExpressionSyntax) ? o.Expression.ToString() : "this"))
                        Report("CSV1025", inv, $"'{g.Name}' is held here, and a semaphore can't be taken twice: this would wait for itself", isError: true);
                    return;
                }
            }
            if (whole.Parent is AssignmentExpressionSyntax a && a.Left == whole && _method.MethodKind == MethodKind.Constructor) return;
            if (whole.Ancestors().OfType<InvocationExpressionSyntax>().Any(i => i.Expression is IdentifierNameSyntax { Identifier: { Text: "nameof" } })) return;
            Report("CSV1023", n, $"'{g.Name}' guards state, and this hands it on: whoever has it could release it", isError: true);
        }

        private static InvocationExpressionSyntax WholeCall(SimpleNameSyntax n)
        {
            SyntaxNode e = n.Parent is MemberAccessExpressionSyntax ma && ma.Name == n ? ma : n;
            return e.Parent is InvocationExpressionSyntax i && i.Expression == e ? i : null;
        }

        /// <summary>
        /// A wrapper does what it says, as far as its shape shows: [Acquires] waits on a semaphore of count 1, or calls another
        /// wrapper that does, and if it gives something to dispose, its Dispose releases; [Releases] releases.
        /// </summary>
        private void CheckWrapper()
        {
            var locks = _engine.Locks;
            bool acquiring = locks.Acquires(_method), releasing = locks.Releases(_method);
            if (!acquiring && !releasing) return;
            var calls = _contract.Declaration.DescendantNodes().OfType<InvocationExpressionSyntax>().ToList();
            if (releasing && !Calls("Release", false, calls, locks))
                Report("CSV1023", MethodLocationNode(), $"[Releases] on '{_method.Name}', but it doesn't call Release on a semaphore", isError: true);
            if (!acquiring) return;
            if (!Calls("Wait", true, calls, locks) && !Calls("WaitAsync", true, calls, locks))
                Report("CSV1023", MethodLocationNode(), $"[Acquires] on '{_method.Name}', but it doesn't call Wait or WaitAsync on a semaphore", isError: true);
            foreach (var i in calls)
                if (i.Expression is MemberAccessExpressionSyntax ma && (ma.Name.Identifier.Text == "Wait" || ma.Name.Identifier.Text == "WaitAsync") && _model.GetSymbolInfo(ma.Expression).Symbol is IFieldSymbol g && !locks.IsMutexGate(g))
                    Report("CSV1023", i, $"[Acquires] on '{_method.Name}', but '{g.Name}' isn't made with a count of 1: it may let more than one in", isError: true);
            var given = AwaitedType(_method) ?? _method.ReturnType;
            if (given is INamedTypeSymbol r && r.DeclaringSyntaxReferences.Length > 0 && !IsTaskLike(r) && r.SpecialType != SpecialType.System_Void &&
                r.GetMembers("Dispose").OfType<IMethodSymbol>().FirstOrDefault() is IMethodSymbol dispose &&
                !dispose.DeclaringSyntaxReferences.SelectMany(x => x.GetSyntax().DescendantNodes().OfType<MemberAccessExpressionSyntax>()).Any(ma => ma.Name.Identifier.Text == "Release"))
                Report("CSV1023", MethodLocationNode(), $"[Acquires] on '{_method.Name}', but the Dispose of what it gives, '{r.Name}', doesn't call Release", isError: true);
        }

        private bool Calls(string name, bool wrapperAcquiring, List<InvocationExpressionSyntax> calls, LockGuards locks) => calls.Any(i => i.Expression is MemberAccessExpressionSyntax ma && ma.Name.Identifier.Text == name && _model.GetTypeInfo(ma.Expression).Type?.ToDisplayString() == "System.Threading.SemaphoreSlim" ||
                                                                         _model.GetSymbolInfo(i).Symbol is IMethodSymbol m && (wrapperAcquiring ? locks.Acquires(m) : locks.Releases(m)));
    }
}
