using System.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace CsVerify.Verifier
{
    /// <summary>
    /// A flag used as a try-lock (<see cref="LockGuards.IsFlag"/>): taken by an Interlocked exchange from 0 to 1 in an
    /// if, and given back in a finally. Taking it may fail, and then nothing was taken; where it succeeds it's a lock
    /// like any other: what it guards is forgotten, and its invariants are known, then proved where it's given back.
    /// It never waits, so it takes no part in lock levels. Any other use of it is reported (CSV1023).
    /// </summary>
    internal sealed partial class StaticChecks
    {

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
