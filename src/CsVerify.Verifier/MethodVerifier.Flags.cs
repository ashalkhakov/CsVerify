using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// A flag used as a try-lock (<see cref="LockGuards.IsFlag"/>): taken by an Interlocked exchange from 0 to 1 in an
    /// if, and given back in a finally. Taking it may fail, and then nothing was taken; where it succeeds it's a lock
    /// like any other: what it guards is forgotten, and its invariants are known, then proved where it's given back.
    /// It never waits, so it takes no part in lock levels. Any other use of it is reported (CSV1023).
    /// </summary>
    internal sealed partial class MethodVerifier
    {
        private Term FlagCall(IInvocationOperation inv, Frame f, SpecEnv spec)
        {
            var m = inv.TargetMethod;
            var type = m.ContainingType?.ToDisplayString();
            if (!_codeMode || type != "System.Threading.Interlocked" && type != "System.Threading.Volatile") return null;
            if (inv.Arguments.Length == 0 || inv.Arguments[0].Parameter?.RefKind != RefKind.Ref) return null;
            if (!(Uncaptured(inv.Arguments[0].Value) is IFieldReferenceOperation fr) || !_engine.Locks.IsFlag(fr.Field)) return null;
            if (!(inv.Syntax is InvocationExpressionSyntax call)) return null;
            var guard = fr.Field;
            var lockExpr = call.ArgumentList.Arguments[0].Expression;
            string receiver = lockExpr is MemberAccessExpressionSyntax ma ? ma.Expression.ToString() : "this";
            Term owner = null;
            if (!guard.IsStatic)
            {
                if (fr.Instance == null || fr.Instance is IInstanceReferenceOperation) owner = f.This;
                else
                {
                    owner = T.Coerce(Eval(fr.Instance, f, spec), Sort.Int);
                    Deref(fr.Instance, owner, call);
                }
            }
            foreach (var a in inv.Arguments.Skip(1)) Eval(a.Value, f, spec);
            bool own = receiver == "this" && (_method.MethodKind == MethodKind.Constructor || _method.MethodKind == MethodKind.StaticConstructor);
            bool isBool = guard.Type.SpecialType == SpecialType.System_Boolean;

            // taking it: it was free (and is now this thread's), or it wasn't (and nothing changed hands)
            var ifs = call.Ancestors().OfType<IfStatementSyntax>().FirstOrDefault(i => i.Condition.Span.Contains(call.Span));
            if (ifs != null && LockGuards.FlagTaken(ifs.Condition, _model) is var (_, takingCall, _) && takingCall == call &&
                LockGuards.PrimitiveTryOf(ifs, _model) != null)
            {
                var was = _z3.Fresh(guard.Name + "$was", Sort.Int);
                _z3.Assume(T.Or(T.Eq(was, T.Int(0)), T.Eq(was, T.Int(1))));
                var taken = T.Eq(was, T.Int(0));
                // (taken again by the thread that has it: it isn't free)
                if (Holds(ifs, guard, receiver)) _z3.Assume(T.Not(taken));
                else if (!own)
                {
                    foreach (var field in _engine.Locks.GuardedBy(guard))
                        if (FieldEffects.IsHeapField(field))
                            f.Fields[FieldEffects.Key(field)] = _z3.Fresh(field.Name + "$locked", FieldMap(f, field).Sort);
                    foreach (var invariant in LockInvariantsOf(guard, owner, f)) _z3.Assume(T.Implies(taken, invariant));
                }
                return isBool ? T.Not(taken) : was;
            }

            // giving it back, in the finally of its form
            bool release = call.Ancestors().OfType<TryStatementSyntax>().Any(t =>
                t.Finally != null && t.Finally.Span.Contains(call.Span) && LockGuards.PrimitiveForm(t, _model) is { } pf && pf.kind == "Flag" &&
                pf.lockExpr.ToString() == lockExpr.ToString() && LockGuards.GivesBack(call, pf.lockExpr, "Flag", _model));
            if (release && !own)
                foreach (var invariant in LockInvariantsOf(guard, owner, f))
                    Prove(invariant, "CSV1024", call, $"the invariant of lock '{guard.Name}' might not hold when it is given back");
            if (m.ReturnsVoid) return T.True;
            if (release) return isBool ? T.True : T.Int(1);
            return Unknown(inv.Type); // (out of its form: reported by CheckFlagUses)
        }

        /// <summary>A try-lock flag is used only to take it in its form and give it back in its finally (CSV1023).</summary>
        private void CheckFlagUses()
        {
            if (!_engine.Locks.Any) return;
            foreach (var id in _contract.Declaration.DescendantNodes().OfType<IdentifierNameSyntax>())
            {
                if (!(_model.GetSymbolInfo(id).Symbol is IFieldSymbol field) || !_engine.Locks.IsFlag(field)) continue;
                if (id.Parent is ArgumentSyntax na && na.Parent?.Parent is InvocationExpressionSyntax nn && nn.Expression.ToString() == "nameof") continue;
                var access = id.Parent is MemberAccessExpressionSyntax ma && ma.Name == id ? (ExpressionSyntax)ma : id;
                if (access.Parent is ArgumentSyntax arg && arg.Parent?.Parent is InvocationExpressionSyntax inv && ((ArgumentListSyntax)arg.Parent).Arguments.IndexOf(arg) == 0)
                {
                    var ifs = inv.Ancestors().OfType<IfStatementSyntax>().FirstOrDefault(i => i.Condition.Span.Contains(inv.Span));
                    if (ifs != null && LockGuards.FlagTaken(ifs.Condition, _model) is var (_, c, _) && c == inv && LockGuards.PrimitiveTryOf(ifs, _model) != null) continue;
                    if (inv.Ancestors().OfType<TryStatementSyntax>().Any(t => t.Finally != null && t.Finally.Span.Contains(inv.Span) &&
                            LockGuards.PrimitiveForm(t, _model) is { } pf && pf.kind == "Flag" && pf.lockExpr.ToString() == access.ToString() &&
                            LockGuards.GivesBack(inv, pf.lockExpr, "Flag", _model)))
                        continue;
                }
                bool own = (access == id || ((MemberAccessExpressionSyntax)access).Expression is ThisExpressionSyntax) &&
                           (_method.MethodKind == MethodKind.Constructor || _method.MethodKind == MethodKind.StaticConstructor);
                if (own) continue;
                string one = field.Type.SpecialType == SpecialType.System_Boolean ? "true" : "1", zero = one == "1" ? "0" : "false";
                Report("CSV1023", access, $"'{access}' is a try-lock, since it guards state: take it only as 'if (Interlocked.Exchange(ref {access}, {one}) == {zero}) {{ try {{ ... }} finally {{ Volatile.Write(ref {access}, {zero}); }} }}', or with the if leaving when it fails and the try after, so it's always given back", isError: true);
            }
        }
    }
}
