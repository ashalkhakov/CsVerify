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
    /// Locks (see LockGuards). What a lock guards is reachable only under it, which is checked from the syntax, as in
    /// Clang's thread safety analysis (CSV1023). So no other thread writes it while this one holds the lock, and the
    /// assumption that nothing else writes the state a method uses (A4) is proved for it. Entering a lock forgets what it
    /// guards, since others have had it, and gives its invariants; leaving it, or a call that might enter it again,
    /// must restore them (CSV1024).
    /// </summary>
    internal sealed partial class MethodVerifier
    {
        /// <summary>Every use of guarded state in this method is under its lock. The lambdas in it are looked at with it.</summary>
        private void CheckLocking()
        {
            var locks = _engine.Locks;
            if (!locks.Any || SpecSymbols.HasAttribute(_method, "TrustedAttribute")) return;
            CheckInvariantIsEstablished();
            foreach (var n in _contract.Declaration.DescendantNodes().OfType<SimpleNameSyntax>())
            {
                var symbol = _model.GetSymbolInfo(n).Symbol;
                if (symbol == null || !(symbol is IFieldSymbol || symbol is IPropertySymbol || symbol is IMethodSymbol)) continue;
                if (locks.GuardOf(symbol) is not IFieldSymbol guard) continue;
                if (n.Parent is NameColonSyntax || n.Parent is NameEqualsSyntax) continue;
                var receiver = ReceiverOf(n);
                if (IsBeingBuilt(n, receiver)) continue;
                if (!(guard.IsReadOnly || guard.IsConst))
                    Report("CSV1023", n, $"'{guard.Name}' guards '{symbol.Name}', but it isn't readonly: threads could hold different objects", isError: true);
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

        /// <summary>At the end of a constructor: the invariants of its object's locks hold, before anyone can take them.</summary>
        private void ConstructorEstablishesLocks(Frame f)
        {
            if (!_engine.Locks.Any || !(_method.MethodKind == MethodKind.Constructor || _method.MethodKind == MethodKind.StaticConstructor)) return;
            foreach (var (lockField, invariant) in _engine.Locks.InvariantsIn(_method.ContainingType))
                if (lockField.IsStatic == _method.IsStatic && lockField is IFieldSymbol guard)
                    foreach (var fact in LockInvariants(guard, null, f))
                        Prove(fact, "CSV1024", MethodLocationNode(), $"the constructor might not establish the invariant of lock '{guard.Name}'");
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
                        if (lockReceiver == wanted && StaysTheSame(wanted, l)) return true;
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
        private bool StaysTheSame(string receiver, LockStatementSyntax l)
        {
            if (receiver == "this") return true;
            if (!SyntaxFacts.IsValidIdentifier(receiver)) return false;
            bool Named(ExpressionSyntax e) => e.ToString() == receiver || e is TupleExpressionSyntax t && t.Arguments.Any(x => Named(x.Expression));
            return !l.Statement.DescendantNodes().OfType<AssignmentExpressionSyntax>().Any(a => Named(a.Left)) &&
                   !l.Statement.DescendantNodes().OfType<ForEachVariableStatementSyntax>().Any(fe => Named(fe.Variable)) &&
                   !l.Statement.DescendantNodes().OfType<ArgumentSyntax>().Any(a => !a.RefKindKeyword.IsKind(SyntaxKind.None) && a.Expression.ToString() == receiver);
        }

        /// <summary>
        /// Nested locks on elements of one array are taken in increasing order of index, as a table of forks must: then no
        /// cycle of threads waiting on each other can form among them (CSV1025). Only what this method's lock statements show.
        /// </summary>
        private void CheckLockOrder(IInvocationOperation inv, Frame f, SpecEnv spec)
        {
            if (!_codeMode || inv.TargetMethod.Name != "Enter" || inv.TargetMethod.ContainingType?.ToDisplayString() != "System.Threading.Monitor") return;
            if (!(inv.Syntax.Parent is LockStatementSyntax inner) || !(inner.Expression is ElementAccessExpressionSyntax ia) || ia.ArgumentList.Arguments.Count != 1) return;
            for (var p = inner.Parent; p != null && p != _contract.Declaration; p = p.Parent)
            {
                if (p is AnonymousFunctionExpressionSyntax || p is LocalFunctionStatementSyntax) return;
                if (!(p is LockStatementSyntax outer) || !(outer.Expression is ElementAccessExpressionSyntax oa) || oa.ArgumentList.Arguments.Count != 1) continue;
                if (oa.Expression.ToString() != ia.Expression.ToString()) continue;
                string index = oa.ArgumentList.Arguments[0].Expression.ToString();
                if (!(_model.GetOperation(oa.ArgumentList.Arguments[0].Expression) is IOperation before) || !(before.ConstantValue.HasValue || StaysTheSame(index, outer)) ||
                    !(_model.GetOperation(ia.ArgumentList.Arguments[0].Expression) is IOperation after))
                {
                    Report("CSV1025", inner, $"'{outer.Expression}' and '{inner.Expression}': their order can't be told, since '{index}' may change under the lock", isError: true);
                    continue;
                }
                Prove(T.Lt(T.Coerce(Eval(before, f, spec), Sort.Int), T.Coerce(Eval(after, f, spec), Sort.Int)), "CSV1025", inner,
                    $"'{inner.Expression}' might not come after '{outer.Expression}': locks of one array taken in different orders can deadlock");
            }
        }

        /// <summary>
        /// Monitor.Enter or Monitor.Exit of a lock statement on a lock field: what it means to this thread, in place of
        /// a library call. Null for any other call.
        /// </summary>
        private Term LockEvent(IInvocationOperation inv, Frame f, SpecEnv spec)
        {
            CheckLockOrder(inv, f, spec);
            // (the flow graph gives the lock's expression as Enter's syntax, the statement as Exit's)
            var stmt = inv.Syntax as LockStatementSyntax ?? inv.Syntax.Parent as LockStatementSyntax;
            if (!_codeMode || stmt == null || inv.TargetMethod.ContainingType?.ToDisplayString() != "System.Threading.Monitor") return null;
            var taken = inv.Arguments.FirstOrDefault(a => a.Parameter?.RefKind == RefKind.Ref);
            // (entering, it always ends up taken, or throws)
            if (inv.TargetMethod.Name == "Enter" && taken != null) Write(taken.Value, T.True, f, spec);
            // a lock on something else guards nothing the verifier knows of, and by itself changes no state
            if (!(LockGuards.LockOf(stmt.Expression, _model) is IFieldSymbol guard))
            {
                if (inv.TargetMethod.Name == "Enter") Deref(inv.Arguments[0].Value, Eval(inv.Arguments[0].Value, f, spec), stmt);
                return T.True;
            }
            // (taken again, in its own holder: nothing changes hands)
            string receiver = stmt.Expression is MemberAccessExpressionSyntax ma ? ma.Expression.ToString() : "this";
            if (Holds(stmt, guard, receiver)) return T.True;
            // (a constructor's own lock: it has the object to itself, and has not established anything yet)
            if (receiver == "this" && (_method.MethodKind == MethodKind.Constructor || _method.MethodKind == MethodKind.StaticConstructor)) return T.True;
            if (inv.TargetMethod.Name == "Enter")
            {
                var o = Eval(inv.Arguments[0].Value, f, spec);
                Deref(inv.Arguments[0].Value, o, stmt);
                foreach (var field in _engine.Locks.GuardedBy(guard))
                    if (FieldEffects.IsHeapField(field))
                        f.Fields[FieldEffects.Key(field)] = _z3.Fresh(field.Name + "$locked", FieldMap(f, field).Sort);
                foreach (var invariant in LockInvariants(guard, stmt, f)) _z3.Assume(invariant);
            }
            else
                foreach (var invariant in LockInvariants(guard, stmt, f))
                    Prove(invariant, "CSV1024", stmt, $"the invariant of lock '{guard.Name}' might not hold when it is released");
            return T.True;
        }

        /// <summary>A call under a lock that may run code that enters it again, which relies on its invariants.</summary>
        private void CallUnderLock(IInvocationOperation inv, Contract callee, Frame f)
        {
            if (!_codeMode || !_engine.Locks.Any || callee.IsPure || callee.IsLemma || SpecSymbols.IsSpecClass(inv.TargetMethod.ContainingType)) return;
            if (!callee.HasSource && !_engine.Fields.RunsUserCode(inv.TargetMethod)) return;
            for (var p = inv.Syntax.Parent; p != null && p != _contract.Declaration; p = p.Parent)
            {
                if (p is AnonymousFunctionExpressionSyntax || p is LocalFunctionStatementSyntax) return;
                if (!(p is LockStatementSyntax stmt) || !(LockGuards.LockOf(stmt.Expression, _model) is IFieldSymbol guard)) continue;
                if (SymbolEqualityComparer.Default.Equals(_engine.Locks.GuardOf(inv.TargetMethod), guard)) continue;
                foreach (var invariant in LockInvariants(guard, stmt, f))
                    Prove(invariant, "CSV1024", inv.Syntax, $"the invariant of lock '{guard.Name}' might not hold at '{inv.Syntax}', which may enter the lock again");
            }
            // (a method that its caller holds the lock for is under it all along)
            if (_engine.Locks.GuardOf(_method) is IFieldSymbol own && !SymbolEqualityComparer.Default.Equals(_engine.Locks.GuardOf(inv.TargetMethod), own))
                foreach (var invariant in LockInvariants(own, null, f))
                    Prove(invariant, "CSV1024", inv.Syntax, $"the invariant of lock '{own.Name}' might not hold at '{inv.Syntax}', which may enter the lock again");
        }

        private IEnumerable<Term> LockInvariants(IFieldSymbol guard, LockStatementSyntax stmt, Frame f)
        {
            var methods = _engine.Locks.InvariantsOf(guard);
            if (methods.Count == 0) yield break;
            Term owner = null;
            if (!guard.IsStatic)
                owner = stmt != null && _model.GetOperation(stmt.Expression) is IFieldReferenceOperation fr && fr.Instance != null ? T.Coerce(Eval(fr.Instance, f, null), Sort.Int) : f.This;
            foreach (var m in methods)
                yield return AsBool(PureApply(_engine.ContractOf(m), m.IsStatic ? null : owner, new Term[0], f.Heap, Sort.Bool, null, f));
        }
    }
}
