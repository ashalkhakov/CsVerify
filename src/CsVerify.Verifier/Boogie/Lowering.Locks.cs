using System;
using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.FlowAnalysis;
using Microsoft.CodeAnalysis.Operations;
using static CsVerify.Verifier.Boogie.KernelTypes;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>Locks: lock statements, Monitor, lock invariants and order, gates and flags of lock wrappers.</summary>
    internal sealed partial class Lowering
    {
        private KExpr InvariantCall(IMethodSymbol invariant, KExpr owner)
        {
            if (!_isFunction(invariant.OriginalDefinition)) throw new NotTranslated("a lock invariant that isn't a function: " + invariant.Name);
            return new KFnCall { Callee = invariant.OriginalDefinition, Receiver = invariant.IsStatic ? null : owner, ReceiverIsThis = owner is KVar { Name: "this" }, Args = new KExpr[0], At = _decl };
        }

        /// <summary>
        /// lock (o) { ... }: Monitor.Enter forgets what the lock guards (others have had it) and gives its invariants;
        /// Monitor.Exit, in its finally, proves them (CSV1024). Only a lock field of this object or a static one, not
        /// inside another lock (whose order, lock levels, isn't translated yet).
        /// </summary>
        private void Monitor(IInvocationOperation call)
        {
            var arg = call.Arguments.OrderBy(a => a.Parameter.Ordinal).First().Value;
            var lockOp = Unconverted(arg is IFlowCaptureReferenceOperation r && _captured.TryGetValue(r.Id, out var v) ? v : arg);
            if (KernelTypes.Locks == null) throw new NotTranslated("locks without their guards");
            var stmt = call.Syntax.AncestorsAndSelf().OfType<LockStatementSyntax>().FirstOrDefault() ?? (SyntaxNode)call.Syntax;
            // (whose lock: a lock field of this object, of an object a variable holds, a static one; or an object of a class with a level)
            IFieldSymbol lockField = null;
            KExpr owner;
            if (lockOp is IFieldReferenceOperation { Field: IFieldSymbol lf } fr && IsLockObject(lf))
            {
                lockField = lf;
                owner = lf.IsStatic ? null : fr.Instance is IInstanceReferenceOperation ? new KVar("this") : Fixed(fr.Instance) ? Expr(fr.Instance) : throw new NotTranslated("a lock of an object that may change");
            }
            else if (Fixed(lockOp) && LockLevels.LeveledClass(lockOp.Type) != null) owner = Expr(lockOp);
            else if (stmt is LockStatementSyntax && IsRef(lockOp.Type))
            {
                // (a lock of anything else guards nothing the kernel knows of: it changes no state; nested locks of one
                // array's elements are taken in increasing order of index, CSV1025)
                if (call.TargetMethod.Name != "Enter") return;
                var o = Expr(arg);
                if (!(lockOp is IInstanceReferenceOperation))
                    Emit(new KCheck { Cond = new KOp("!=", o, new KLit("null")), Id = "CSV1013", At = stmt, Message = $"'{lockOp.Syntax}' might be null in '{stmt}'" });
                ElementLockOrder((LockStatementSyntax)stmt);
                return;
            }
            else throw new NotTranslated("a lock of something other than a lock field or an object with a level");
            // (taken again where an enclosing lock statement holds it, on the same object: nothing changes hands)
            if (lockField != null && stmt is LockStatementSyntax ls && HeldAround(ls, lockField))
            {
                if (call.TargetMethod.Name == "Enter" && call.Arguments.Length == 2) Emit(new KAssign { Var = RefVariable(call.Arguments.OrderBy(a => a.Parameter.Ordinal).Last()), Value = new KLit("true") });
                return;
            }
            if (call.TargetMethod.Name == "Enter")
            {
                if (call.Arguments.Length == 2) Emit(new KAssign { Var = RefVariable(call.Arguments.OrderBy(a => a.Parameter.Ordinal).Last()), Value = new KLit("true") });
                ProveOrderAt(stmt);
                if (lockField == null) return;
                foreach (var g in KernelTypes.Locks.GuardedBy(lockField).Where(g => g.IsStatic == lockField.IsStatic))
                {
                    if (!IsField(g)) throw new NotTranslated("a guarded member the kernel doesn't have: " + g.Name);
                    var t = Declare("t$" + _temps++, FieldType(g));
                    Emit(new KHavoc { Var = t });
                    _p.Fields.Add(g.OriginalDefinition);
                    Emit(new KFieldStore { Field = g.OriginalDefinition, Instance = owner, OnThis = owner != null, Value = new KVar(t), At = stmt, InstanceAt = stmt });
                }
                foreach (var inv in KernelTypes.Locks.InvariantsOf(lockField))
                    Emit(new KSpecStmt { Spec = InvariantCall(inv, owner), Assume = true, At = stmt, ArgumentAt = stmt });
            }
            else if (lockField != null)
                foreach (var inv in KernelTypes.Locks.InvariantsOf(lockField))
                    Emit(new KCheck { Cond = InvariantCall(inv, owner), Id = "CSV1024", At = stmt, Message = $"the invariant of lock '{lockField.Name}' might not hold when it is released" });
        }

        /// <summary>
        /// Is the lock held around this lock statement, on the same object? By an enclosing lock statement (not across a
        /// lambda or local function), or by the method's own [GuardedBy] for its own object:.
        /// </summary>
        private bool HeldAround(LockStatementSyntax n, IFieldSymbol guard)
        {
            string receiver = n.Expression is MemberAccessExpressionSyntax ma ? ma.Expression.ToString() : "this";
            string wanted = guard.IsStatic ? null : receiver;
            for (var p = n.Parent; p != null; p = p.Parent)
            {
                switch (p)
                {
                    case LockStatementSyntax l when l.Statement.Span.Contains(n.Span) && SymbolEqualityComparer.Default.Equals(LockGuards.LockOf(l.Expression, _model), guard):
                        if (wanted == null) return true;
                        var lockReceiver = l.Expression is MemberAccessExpressionSyntax lma ? lma.Expression.ToString() : "this";
                        if (lockReceiver == wanted && (wanted == "this" || StaysTheSame(wanted, l.Statement))) return true;
                        break;
                    case AnonymousFunctionExpressionSyntax _:
                    case LocalFunctionStatementSyntax _:
                        return false;
                }
                if (p == _decl) break;
            }
            return (wanted == "this" || wanted == null) && SymbolEqualityComparer.Default.Equals(KernelTypes.Locks.GuardOf(_m), guard) &&
                   SymbolEqualityComparer.Default.Equals(_m.ContainingType, guard.ContainingType);
        }

        /// <summary>Nested lock statements on elements of one array: the outer's index below the inner's (CSV1025).</summary>
        private void ElementLockOrder(LockStatementSyntax inner)
        {
            if (!(inner.Expression is ElementAccessExpressionSyntax ia) || ia.ArgumentList.Arguments.Count != 1) return;
            for (var p = inner.Parent; p != null && p != _decl; p = p.Parent)
            {
                if (p is AnonymousFunctionExpressionSyntax || p is LocalFunctionStatementSyntax) return;
                if (!(p is LockStatementSyntax outer) || !(outer.Expression is ElementAccessExpressionSyntax oa) || oa.ArgumentList.Arguments.Count != 1) continue;
                if (oa.Expression.ToString() != ia.Expression.ToString()) continue;
                string index = oa.ArgumentList.Arguments[0].Expression.ToString();
                var before = _model.GetOperation(oa.ArgumentList.Arguments[0].Expression);
                var after = _model.GetOperation(ia.ArgumentList.Arguments[0].Expression);
                if (before == null || after == null || !(before.ConstantValue.HasValue || StaysTheSame(index, outer.Statement)))
                {
                    Emit(new KCheck { Cond = new KLit("false"), Id = "CSV1025", At = inner, NotAssumedAfter = true,
                                      Message = $"'{outer.Expression}' and '{inner.Expression}': their order can't be told, since '{index}' may change under the lock" });
                    continue;
                }
                Emit(new KCheck { Cond = new KOp("<", Spec(before, null), Spec(after, null)), Id = "CSV1025", At = inner, NotAssumedAfter = true,
                                  Message = $"'{inner.Expression}' might not come after '{outer.Expression}': locks of one array taken in different orders can deadlock" });
            }
        }

        /// <summary>A name the statement doesn't assign: the same value all through it.</summary>
        private static bool StaysTheSame(string name, SyntaxNode l)
        {
            if (!SyntaxFacts.IsValidIdentifier(name)) return false;
            bool Named(ExpressionSyntax e) => e.ToString() == name || e is TupleExpressionSyntax t && t.Arguments.Any(x => Named(x.Expression));
            return !l.DescendantNodes().OfType<AssignmentExpressionSyntax>().Any(a => Named(a.Left)) &&
                   !l.DescendantNodes().OfType<ForEachVariableStatementSyntax>().Any(fe => Named(fe.Variable)) &&
                   !l.DescendantNodes().OfType<ArgumentSyntax>().Any(a => !a.RefKindKeyword.IsKind(SyntaxKind.None) && a.Expression.ToString() == name);
        }

        /// <summary>Monitor.Wait(o): o's lock given back (its invariants proved, CSV1024, at the call), then taken again.</summary>
        private void Waited(IInvocationOperation call)
        {
            var arg = Unconverted(call.Arguments.OrderBy(a => a.Parameter.Ordinal).First().Value);
            if (KernelTypes.Locks == null) throw new NotTranslated("locks without their guards");
            if (!(arg is IFieldReferenceOperation { Field: IFieldSymbol lockField } fr && IsLockObject(lockField))) throw new NotTranslated("a wait on something other than a lock field");
            var owner = lockField.IsStatic ? null : fr.Instance is IInstanceReferenceOperation ? new KVar("this") : Fixed(fr.Instance) ? Expr(fr.Instance) : throw new NotTranslated("a lock of an object that may change");
            foreach (var inv in KernelTypes.Locks.InvariantsOf(lockField))
                Emit(new KCheck { Cond = InvariantCall(inv, owner), Id = "CSV1024", At = call.Syntax, Message = $"the invariant of lock '{lockField.Name}' might not hold at '{call.Syntax}', which gives it to others" });
            foreach (var g in KernelTypes.Locks.GuardedBy(lockField).Where(g => g.IsStatic == lockField.IsStatic))
            {
                if (!IsField(g)) throw new NotTranslated("a guarded member the kernel doesn't have: " + g.Name);
                var t = Declare("t$" + _temps++, FieldType(g));
                Emit(new KHavoc { Var = t });
                _p.Fields.Add(g.OriginalDefinition);
                Emit(new KFieldStore { Field = g.OriginalDefinition, Instance = owner, OnThis = owner != null, Value = new KVar(t), At = call.Syntax, InstanceAt = call.Syntax });
            }
            foreach (var inv in KernelTypes.Locks.InvariantsOf(lockField))
                Emit(new KSpecStmt { Spec = InvariantCall(inv, owner), Assume = true, At = call.Syntax, ArgumentAt = call.Syntax });
        }

        /// <summary>This object, a local or a parameter assigned nowhere in the method, or a field of one: the same object while a lock of it is held.</summary>
        private bool Fixed(IOperation op)
        {
            while (op is IConversionOperation { IsImplicit: true } c) op = c.Operand;
            return op switch
            {
                IInstanceReferenceOperation _ => true,
                ILocalReferenceOperation l => NeverWritten(l.Local) || l.Local.DeclaringSyntaxReferences.Length == 1 && OnlyDeclared(l.Local),
                IParameterReferenceOperation p => NeverWritten(p.Parameter),
                IFieldReferenceOperation f => (f.Field.IsReadOnly || f.Field.IsConst) && (f.Instance == null || Fixed(f.Instance)),
                _ => false,
            };
        }

        private bool OnlyDeclared(ILocalSymbol l) =>
            !_decl.DescendantNodes().OfType<AssignmentExpressionSyntax>().Any(a => a.Left is IdentifierNameSyntax n && n.Identifier.Text == l.Name && SymbolEqualityComparer.Default.Equals(_model.GetSymbolInfo(n).Symbol, l));

        /// <summary>An owner as written (null: this), as a value in a specification.</summary>
        private KExpr OwnerValue(ExpressionSyntax owner)
        {
            if (owner == null) return new KVar("this");
            var op = _model.GetOperation(owner);
            while (op is IConversionOperation { IsImplicit: true } c) op = c.Operand;
            while (op is IParenthesizedOperation p) op = p.Operand;
            return op != null && Fixed(op) ? Spec(op, null) : throw new NotTranslated("a lock's owner that may change: " + owner);
        }

        private KExpr KeyOf(IFieldSymbol key, KExpr owner)
        {
            _p.Fields.Add(key.OriginalDefinition);
            return new KField { Field = key.OriginalDefinition, Instance = owner, At = _decl, InstanceAt = _decl };
        }

        /// <summary>
        /// A lock taken while another of its field or class is held (Account's Lock of from, then of to): in increasing
        /// order of its OrderedBy id (CSV1025). Which locks are held is LockLevels' static analysis.
        /// </summary>
        private void ProveOrderAt(SyntaxNode stmt)
        {
            var levels = KernelTypes.Levels;
            if (levels == null) return;
            var a = levels.AcquiredAt(stmt, _model);
            if (a?.Lock == null || a.Element || a.Static || !(LockLevels.OrderedBy(a.Lock) is IFieldSymbol key)) return;
            if (!(key.IsReadOnly || key.IsConst)) throw new NotTranslated("a lock ordered by what may change");
            foreach (var h in levels.HeldAt(a.At, _decl, _model))
            {
                if (h == null || !SymbolEqualityComparer.Default.Equals(h.Lock, a.Lock) || h.Element || h.Receiver == a.Receiver) continue;
                Emit(new KCheck { Cond = new KOp("<", KeyOf(key, OwnerValue(h.Owner)), KeyOf(key, OwnerValue(a.Owner))), Id = "CSV1025", At = a.At, NotAssumedAfter = true,
                                  Message = $"'{a.Receiver}''s '{a.Lock.Name}' might not come after '{h.Receiver}''s by '{key.Name}': two of them taken in different orders can deadlock" });
            }
        }

        // ------------------------------------------------------------------ gates and concurrent code

        /// <summary>A guard clause's relation, after it returns: "0" for those of one value, an operator for those of two; null for others.</summary>
        private static string GuardRelation(IMethodSymbol m) => m.Name switch
        {
            "ThrowIfNegative" or "ThrowIfNegativeOrZero" or "ThrowIfZero" => "0",
            "ThrowIfGreaterThan" => "<=", "ThrowIfGreaterThanOrEqual" => "<", "ThrowIfLessThan" => ">=", "ThrowIfLessThanOrEqual" => ">",
            "ThrowIfEqual" => "!=", "ThrowIfNotEqual" => "==",
            _ => null,
        };

        /// <summary>A readonly semaphore field, not null where declared so, that no state is guarded by and no invariant is of.</summary>
        private static bool GuardsNothing(IFieldSymbol f) =>
            f.IsReadOnly && IsSemaphore(f.Type) && NotNullable(f.Type) && KernelTypes.Locks != null && !KernelTypes.Locks.IsMutexGate(f) &&
            !KernelTypes.Locks.GuardedBy(f).Any() && KernelTypes.Locks.InvariantsOf(f).Count == 0;

        /// <summary>A SemaphoreSlim of count 1 that is this object's field (or a static one) and guards state: a lock that can be held across awaits.</summary>
        private IFieldSymbol GateOf(IInvocationOperation call)
        {
            // (a semaphore that guards nothing, of any count: waiting on it changes nothing the kernel knows of)
            if (Unconverted(call.Instance) is IFieldReferenceOperation { Field: IFieldSymbol plain } && GuardsNothing(plain)) return null;
            _gateOwner = null;
            if (!(Unconverted(call.Instance) is IFieldReferenceOperation { Field: IFieldSymbol gate } fr) || KernelTypes.Locks == null || !KernelTypes.Locks.IsMutexGate(gate))
                throw new NotTranslated("a semaphore other than a gate");
            // (another object's, one a variable holds that nothing writes: its own gate, as its methods take it)
            if (!gate.IsStatic && !(fr.Instance is IInstanceReferenceOperation))
            {
                if (!Fixed(fr.Instance)) throw new NotTranslated("a gate of an object that may change");
                _gateOwner = Expr(fr.Instance);
                Emit(new KCheck { Cond = new KOp("!=", _gateOwner, new KLit("null")), Id = "CSV1013", At = fr.Syntax, Message = $"'{fr.Instance.Syntax}' might be null in '{fr.Syntax}'" });
            }
            var at = call.Syntax;
            // (taking one while it's held waits for itself: StaticChecks reports it, CSV1025)
            // (taken inside another lock: in order of levels, StaticChecks says)
            return gate;
        }

        /// <summary>The gate a lock wrapper's using holds, of the Dispose its end calls (whose syntax is the using's, or its resource's).</summary>
        private IFieldSymbol UsingGate(SyntaxNode at)
        {
            foreach (var n in at.AncestorsAndSelf())
            {
                if (n is UsingStatementSyntax u && (u == at || u.Expression?.Span.Contains(at.Span) == true || u.Declaration?.Span.Contains(at.Span) == true))
                    return KernelTypes.Locks.GateOfUsing(u, _model);
                if (n is LocalDeclarationStatementSyntax d && !d.UsingKeyword.IsKind(SyntaxKind.None)) return KernelTypes.Locks.GateOfUsing(d, _model);
                if (n is StatementSyntax) return null;
            }
            return null;
        }

        /// <summary>The object whose gate GateOf found, where it isn't this's (null for this's, or a static one).</summary>
        private KExpr _gateOwner;

        /// <summary>Is this method a lock wrapper ([Acquires], [Releases]): its semaphore is its callers' to hold.</summary>
        private bool InWrapper => KernelTypes.Locks != null && (KernelTypes.Locks.Acquires(_m) || KernelTypes.Locks.Releases(_m));

        /// <summary>The gate of this object (or a static one) a call of a lock wrapper takes or gives back; null for another call.</summary>
        private IFieldSymbol WrapperGate(IInvocationOperation call, bool acquiring)
        {
            if (KernelTypes.Locks == null || !(acquiring ? KernelTypes.Locks.Acquires(call.TargetMethod) : KernelTypes.Locks.Releases(call.TargetMethod))) return null;
            if (!(call.Syntax is InvocationExpressionSyntax inv) || !(KernelTypes.Locks.GateOfWrapper(inv, _model, acquiring) is IFieldSymbol gate))
                throw new NotTranslated("a lock wrapper's call whose lock isn't known");
            if (!gate.IsStatic && KernelTypes.Locks.OwnerOf(inv, _model) != "this") throw new NotTranslated("another object's lock wrapper");
            return gate;
        }

        /// <summary>
        /// A library lock wrapper's receiver: a lock's object of this one's or a static one (a readonly field of a library
        /// type, a StringWriter say), no state of the kernel's; else read as any receiver.
        /// </summary>
        private void LockReceiver(IOperation instance)
        {
            if (instance == null) return;
            if (Unconverted(instance) is IFieldReferenceOperation { Field: { IsReadOnly: true } lf } lr && IsLibraryObject(lf.Type) && (lf.IsStatic || lr.Instance is IInstanceReferenceOperation)) return;
            Expr(Unconverted(instance));
        }

        /// <summary>Taking a gate: what it guards is forgotten (others have had it), and its invariants hold.</summary>
        private void Take(IFieldSymbol gate, SyntaxNode at, KExpr of = null)
        {
            var owner = gate.IsStatic ? null : of ?? new KVar("this");
            foreach (var g in KernelTypes.Locks.GuardedBy(gate).Where(g => g.IsStatic == gate.IsStatic))
            {
                if (!IsField(g)) throw new NotTranslated("a guarded member the kernel doesn't have: " + g.Name);
                var t = Declare("t$" + _temps++, FieldType(g));
                Emit(new KHavoc { Var = t });
                _p.Fields.Add(g.OriginalDefinition);
                Emit(new KFieldStore { Field = g.OriginalDefinition, Instance = owner, OnThis = owner is KVar { Name: "this" }, Value = new KVar(t), At = at, InstanceAt = at });
            }
            foreach (var inv in KernelTypes.Locks.InvariantsOf(gate))
                Emit(new KSpecStmt { Spec = InvariantCall(inv, owner), Assume = true, At = at, ArgumentAt = at });
        }

        /// <summary>Giving a gate back: its invariants must hold (CSV1024).</summary>
        private void Give(IFieldSymbol gate, SyntaxNode at, string how = "released", KExpr of = null)
        {
            var owner = gate.IsStatic ? null : of ?? new KVar("this");
            foreach (var inv in KernelTypes.Locks.InvariantsOf(gate))
                Emit(new KCheck { Cond = InvariantCall(inv, owner), Id = "CSV1024", At = at, Message = $"the invariant of lock '{gate.Name}' might not hold when it is {how}" });
        }

        /// <summary>The try-lock flag a call of Interlocked or Volatile is on (this object's, or a static one), or null.</summary>
        private IFieldSymbol FlagOf(IInvocationOperation call)
        {
            var first = call.Arguments.OrderBy(a => a.Parameter.Ordinal).First();
            if (first.Parameter.RefKind == RefKind.None || KernelTypes.Locks == null) return null;
            var target = first.Value is IFlowCaptureReferenceOperation c && _captured.TryGetValue(c.Id, out var cv) ? cv : first.Value;
            if (!(Unconverted(target) is IFieldReferenceOperation { Field: IFieldSymbol f } fr) || !KernelTypes.Locks.IsFlag(f)) return null;
            // (another object's, of a variable that stays the same: its gate, of that object)
            if (!(f.IsStatic || fr.Instance is IInstanceReferenceOperation) && !Fixed(fr.Instance)) throw new NotTranslated("another object's try-lock, of a variable that may change");
            return f;
        }

        /// <summary>
        /// Interlocked or Volatile on a try-lock's flag: taking it (setting it to 1) gives back what it was, which isn't
        /// known (the if that tests it says where it was taken); giving it back (setting it to 0) proves its invariants (CSV1024).
        /// </summary>
        private KExpr FlagCall(IInvocationOperation call, IFieldSymbol flag)
        {
            var ordered = call.Arguments.OrderBy(a => a.Parameter.Ordinal).ToList();
            var set = ordered.Count > 1 ? ordered[1].Value.ConstantValue : default;
            bool givesBack = set.HasValue && (set.Value is int i && i == 0 || set.Value is false);
            var target = ordered[0].Value is IFlowCaptureReferenceOperation fc && _captured.TryGetValue(fc.Id, out var fcv) ? fcv : ordered[0].Value;
            var owner = Unconverted(target) is IFieldReferenceOperation { Instance: { } fi } && !(fi is IInstanceReferenceOperation) ? Expr(Unconverted(fi)) : null;
            if (givesBack) Give(flag, call.Syntax, "given back", of: owner);
            if (call.TargetMethod.ReturnsVoid) return null;
            var was = Declare("t$" + _temps++, call.TargetMethod.ReturnType);
            Emit(new KHavoc { Var = was });
            // (taken again by the thread that has it: it isn't free)
            if (!givesBack && FlagHeldAt(call.Syntax, flag, ordered[0].Value.Syntax as ExpressionSyntax))
                Emit(new KAssume { Cond = new KOp("==", new KVar(was), new KLit(call.TargetMethod.ReturnType.SpecialType == SpecialType.System_Boolean ? "true" : "1")) });
            return new KVar(was);
        }

        /// <summary>Is the try-lock's flag held here, on the same object: in the held part of a try of its form around it.</summary>
        private bool FlagHeldAt(SyntaxNode at, IFieldSymbol flag, ExpressionSyntax refArg)
        {
            var target = refArg is RefExpressionSyntax re ? re.Expression : refArg;
            string receiver = target is MemberAccessExpressionSyntax ma ? ma.Expression.ToString() : "this";
            for (var p = at.Parent; p != null && p != _decl; p = p.Parent)
            {
                if (p is AnonymousFunctionExpressionSyntax || p is LocalFunctionStatementSyntax) return false;
                if (p is TryStatementSyntax pt && LockGuards.PrimitiveForm(pt, _model) is { } form && form.kind == "Flag" && form.held.Any(h => h.Span.Contains(at.Span)) &&
                    SymbolEqualityComparer.Default.Equals(LockGuards.LockOf(form.lockExpr, _model), flag))
                {
                    if (flag.IsStatic) return true;
                    var r = form.lockExpr is MemberAccessExpressionSyntax pma ? pma.Expression.ToString() : "this";
                    if (r == receiver && (receiver == "this" || StaysTheSame(receiver, pt))) return true;
                }
            }
            return false;
        }

        /// <summary>The edge of an if where a try-lock's flag was taken: it's held there, as a lock is once taken.</summary>
        private void FlagTakenOn(BasicBlock b, KBlock whenTrue, KBlock whenFalse)
        {
            if (KernelTypes.Locks == null || !(b.BranchValue?.Syntax is ExpressionSyntax cond) || !(LockGuards.FlagTaken(cond, _model) is var (lockExpr, _, takenWhenTrue))) return;
            if (!(_model.GetSymbolInfo(lockExpr).Symbol is IFieldSymbol flag) || !KernelTypes.Locks.IsFlag(flag)) return;
            var saved = _block;
            _block = takenWhenTrue ? whenTrue : whenFalse;
            try
            {
                // (another object's: of that object, as the variable is)
                var owner = !flag.IsStatic && _model.GetOperation(lockExpr) is IFieldReferenceOperation { Instance: { } fi } && !(fi is IInstanceReferenceOperation) ? Expr(Unconverted(fi)) : null;
                Take(flag, cond, owner);
            }
            finally { _block = saved; }
        }

        /// <summary>Another object's gates held at a point (await o._gate.WaitAsync(); try { here } finally { o._gate.Release(); }), of a variable nothing writes.</summary>
        private IEnumerable<(IFieldSymbol gate, KExpr owner)> OthersGatesHeld(SyntaxNode at)
        {
            if (KernelTypes.Locks == null) yield break;
            foreach (var t in at.Ancestors().OfType<TryStatementSyntax>().Where(t => _decl.Span.Contains(t.Span) && t.Block.Span.Contains(at.Span)))
                if (KernelTypes.Locks.GateOfTry(t, _model) is IFieldSymbol g && !g.IsStatic && KernelTypes.Locks.TryOwner(t, g, _model) is string name && name != "this" &&
                    _model.LookupSymbols(t.SpanStart, name: name).FirstOrDefault() is ISymbol owner && owner is IParameterSymbol or ILocalSymbol && NeverWritten(owner))
                    yield return (g, owner is IParameterSymbol op && _assigned.TryGetValue(op, out var av) ? new KVar(av) : new KVar(owner is IParameterSymbol ? Local(owner) : Declare(Local(owner), ((ILocalSymbol)owner).Type)));
        }

        /// <summary>The gates held at a point: the try of 'await g.WaitAsync(); try { here } finally { g.Release(); }'.</summary>
        private IEnumerable<IFieldSymbol> GatesHeld(SyntaxNode at)
        {
            if (KernelTypes.Locks == null) yield break;
            // (a method its caller holds the gate for: held all along, but across a lambda's or local function's)
            if (KernelTypes.Locks.GuardOf(_m) is IFieldSymbol own && KernelTypes.Locks.IsMutexGate(own) &&
                !at.Ancestors().TakeWhile(a => a != _decl).Any(a => a is AnonymousFunctionExpressionSyntax || a is LocalFunctionStatementSyntax))
                yield return own;
            foreach (var t in at.Ancestors().OfType<TryStatementSyntax>().Where(t => _decl.Span.Contains(t.Span) && t.Block.Span.Contains(at.Span)))
                if (KernelTypes.Locks.GateOfTry(t, _model) is IFieldSymbol g && (g.IsStatic || KernelTypes.Locks.TryOwner(t, g, _model) == "this")) yield return g;
            // (a lock wrapper's using: its statement, or the rest of the block after its declaration)
            foreach (var u in at.Ancestors().OfType<UsingStatementSyntax>().Where(u => _decl.Span.Contains(u.Span) && u.Statement != null && u.Statement.Span.Contains(at.Span)))
                if (KernelTypes.Locks.GateOfUsing(u, _model) is IFieldSymbol ug) yield return ug;
            foreach (var b in at.Ancestors().OfType<BlockSyntax>().Where(b => _decl.Span.Contains(b.Span)))
                foreach (var (dg, _) in KernelTypes.Locks.UsingsBefore(at, b, _model)) yield return dg;
        }

        private void Held(ISymbol field, KExpr o, SyntaxNode at)
        {
            if (!Concurrent && Running() == null || InSpec(at) || KernelTypes.Locks?.GuardOf(field) != null || Atomics.IsAtomic(field)) return;
            // (a new object's initializer: it's in hand)
            if (at?.Parent is AssignmentExpressionSyntax { Parent: InitializerExpressionSyntax { Parent: BaseObjectCreationExpressionSyntax } }) return;
            if (field is IFieldSymbol x ? x.IsReadOnly || x.IsConst : field is IPropertySymbol p && (p.SetMethod == null || p.SetMethod.IsInitOnly)) return;
            string fix = "guard it with a lock, hold a Spec.Acc for it (the class must be [Owned]), or make it [Atomic]";
            if (o == null)
            {
                Emit(new KCheck { Cond = Alongside(new KLit("false")), Id = "CSV1027", At = at, NotAssumedAfter = true, Message = $"'{at}' is static, with no lock, and this runs alongside other code: {fix}" });
                return;
            }
            if (_p.IsCtor && o is KVar { Name: "this" }) return;
            // (an [Owned] object's field, under permissions: checked as permissions are)
            if (IsOwnedField(field) && _p.UsesPerm) return;
            Emit(new KCheck { Cond = Alongside(InHand(o)), Id = "CSV1027", At = at, NotAssumedAfter = true,
                              Message = $"'{at}' has no lock and no permission here, and this runs alongside other code that could be using it: {fix}" });
        }

        private void HeldCell(KExpr array, SyntaxNode at, bool write)
        {
            // (under cell permissions, they say: checked as any cell is, CSV1016)
            if (!Concurrent && Running() == null || InSpec(at) || _p.UsesPerm) return;
            Emit(new KCheck { Cond = Alongside(InHand(array)), Id = "CSV1027", At = at, NotAssumedAfter = true,
                              Message = write ? $"'{at}' writes an array this code has no Spec.Acc for, and it runs alongside other code that could be using it"
                                              : $"'{at}' reads an array this code has no Spec.Acc or Spec.AccRead for, and it runs alongside other code that could be writing it" });
        }

        /// <summary>An object only this code has: a confined local's.</summary>
        private KExpr InHand(KExpr o) =>
            Confined().Select(l => (KExpr)new KOp("==", o, new KVar(Declare(Local(l), l.Type)))).DefaultIfEmpty(new KLit("false")).Aggregate((a, b) => new KOp("||", a, b));

        /// <summary>
        /// A call under a lock of what may enter it again, which relies on its invariants: they hold at the call (CSV1024),
        ///. A [GuardedBy] callee of that lock is under it all along.
        /// </summary>
        private void ReentryUnderLock(IMethodSymbol callee, SyntaxNode at)
        {
            if (at == null || KernelTypes.Locks == null || !KernelTypes.Locks.Any || SpecSymbols.IsSpecClass(callee.ContainingType)) return;
            if (_contractOf?.Invoke(callee) is Contract c && (c.IsPure || c.IsLemma)) return;
            if (callee.DeclaringSyntaxReferences.Length == 0 && !(KernelTypes.RunsUserCode?.Invoke(callee) ?? false)) return;
            for (var p = at.Parent; p != null && p != _decl; p = p.Parent)
            {
                if (p is AnonymousFunctionExpressionSyntax || p is LocalFunctionStatementSyntax) return;
                if (!(p is LockStatementSyntax ls) || !(LockGuards.LockOf(ls.Expression, _model) is IFieldSymbol guard)) continue;
                if (SymbolEqualityComparer.Default.Equals(KernelTypes.Locks.GuardOf(callee), guard)) continue;
                KExpr owner = guard.IsStatic ? null : _model.GetOperation(ls.Expression) is IFieldReferenceOperation { Instance: { } li } && !(li is IInstanceReferenceOperation)
                    ? (Fixed(li) ? Spec(li, null) : throw new NotTranslated("a lock's owner that may change, at a call under it")) : new KVar("this");
                foreach (var inv in KernelTypes.Locks.InvariantsOf(guard))
                    Emit(new KCheck { Cond = InvariantCall(inv, owner), Id = "CSV1024", At = at,
                                      Message = $"the invariant of lock '{guard.Name}' might not hold at '{at}', which may enter the lock again" });
            }
            if (KernelTypes.Locks.GuardOf(_m) is IFieldSymbol own && !KernelTypes.Locks.IsSemaphore(own) && !SymbolEqualityComparer.Default.Equals(KernelTypes.Locks.GuardOf(callee), own))
                foreach (var inv in KernelTypes.Locks.InvariantsOf(own))
                    Emit(new KCheck { Cond = InvariantCall(inv, own.IsStatic ? null : new KVar("this")), Id = "CSV1024", At = at,
                                      Message = $"the invariant of lock '{own.Name}' might not hold at '{at}', which may enter the lock again" });
        }

        /// <summary>A call while a lock is held, of what may take it again (or other locks, in an order not translated yet): not yet.</summary>
        private void UnderLock(IMethodSymbol callee, SyntaxNode at, IOperation instance, IReadOnlyList<IArgumentOperation> arguments)
        {
            if (at == null || KernelTypes.Levels == null || _contractOf?.Invoke(callee) is Contract c && (c.IsPure || c.IsLemma)) return;
            // (the held locks of an object, ordered by an id; whatever else is
            // its static check's, CSV1025)
            var held = KernelTypes.Levels.HeldAt(at, _decl, _model).Where(h => h?.Lock != null && !h.Element && !h.Static && LockLevels.OrderedBy(h.Lock) != null).ToList();
            if (held.Count == 0) return;
            foreach (var t in KernelTypes.Levels.OfCall(at, _model, _m).Taken)
                foreach (var h in held)
                {
                    if (!SymbolEqualityComparer.Default.Equals(h.Lock, t.Lock) || t.Element || !(t.Origin is LockLevels.Origin { AtCall: true } o)) continue;
                    var given = o.Index < 0 ? instance : arguments.FirstOrDefault(x => x.Parameter?.Ordinal == o.Index)?.Value;
                    while (given is IConversionOperation { IsImplicit: true } cv) given = cv.Operand;
                    // (the same object's, taken again: a monitor is reentrant)
                    if (given != null && (given.Syntax.ToString() == h.Receiver || given is IInstanceReferenceOperation && h.Receiver == "this") && Fixed(given)) continue;
                    if (!(LockLevels.OrderedBy(t.Lock) is IFieldSymbol key) || !(key.IsReadOnly || key.IsConst)) continue;
                    if (given == null || !Fixed(given) || h.Owner == null)
                    {
                        Emit(new KCheck { Cond = new KLit("false"), Id = "CSV1025", At = at, NotAssumedAfter = true,
                                          Message = $"'{at}' takes '{t.Lock.Name}' (in '{t.In?.Name}') while '{h.Receiver}' is held, and their order can't be told: pass a local, a parameter or a field" });
                        continue;
                    }
                    Emit(new KCheck { Cond = new KOp("<", KeyOf(key, OwnerValue(h.Owner)), KeyOf(key, Spec(given, null))), Id = "CSV1025", At = at, NotAssumedAfter = true,
                                      Message = $"'{at}' takes '{t.Lock.Name}' (in '{t.In?.Name}') of '{given.Syntax}', which might not come after '{h.Receiver}''s by '{key.Name}': two of them taken in different orders can deadlock" });
                }
        }
    }
}
