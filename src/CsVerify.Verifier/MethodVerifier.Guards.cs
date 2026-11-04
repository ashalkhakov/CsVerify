using System.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// What applications check their arguments with. The generic guard clauses of ArgumentOutOfRangeException
    /// (<c>ThrowIfNegative(i)</c>, <c>ThrowIfGreaterThanOrEqual(i, n)</c>, ...) throw unless the relation holds, so a
    /// call that returns gives it, for integer types (a stub could not compare a T). <c>Debug.Assert(c)</c> and
    /// <c>Trace.Assert(c)</c> are proved like <c>Spec.Assert</c> (CSV1004), and assumed after; at run time they are
    /// unchanged.
    /// </summary>
    internal sealed partial class MethodVerifier
    {
        /// <summary>After a guard clause returns: the relation it checked. (Its exceptional path is the call's.)</summary>
        private void GuardFacts(IInvocationOperation inv, Term[] args)
        {
            var m = inv.TargetMethod;
            if (m.ContainingType?.ToDisplayString() != "System.ArgumentOutOfRangeException" || !m.IsStatic || m.TypeArguments.Length != 1 ||
                !IsIntegral(m.TypeArguments[0]) || args.Length < 1 || args[0] == null) return;
            var v = T.Coerce(args[0], Sort.Int);
            Term o = args.Length > 1 && m.Parameters.Length > 1 && SymbolEqualityComparer.Default.Equals(m.Parameters[1].Type, m.TypeArguments[0]) && args[1] != null
                ? T.Coerce(args[1], Sort.Int) : null;
            Term fact = m.Name switch
            {
                "ThrowIfNegative" => T.Ge(v, T.Int(0)),
                "ThrowIfNegativeOrZero" => T.Gt(v, T.Int(0)),
                "ThrowIfZero" => T.Not(T.Eq(v, T.Int(0))),
                "ThrowIfGreaterThan" when o != null => T.Le(v, o),
                "ThrowIfGreaterThanOrEqual" when o != null => T.Lt(v, o),
                "ThrowIfLessThan" when o != null => T.Ge(v, o),
                "ThrowIfLessThanOrEqual" when o != null => T.Gt(v, o),
                "ThrowIfEqual" when o != null => T.Not(T.Eq(v, o)),
                "ThrowIfNotEqual" when o != null => T.Eq(v, o),
                _ => null,
            };
            if (fact != null) _z3.Assume(fact);
        }

        private static bool IsDebugAssert(IMethodSymbol m) =>
            m.Name == "Assert" && m.IsStatic && m.Parameters.Length >= 1 && m.Parameters[0].Type.SpecialType == SpecialType.System_Boolean &&
            (m.ContainingType?.ToDisplayString() == "System.Diagnostics.Debug" || m.ContainingType?.ToDisplayString() == "System.Diagnostics.Trace");

        /// <summary>Debug.Assert(c, ...): c proved here (its message is evaluated as code, and not otherwise used).</summary>
        private Term DebugAssert(IInvocationOperation inv, Frame f, SpecEnv spec)
        {
            var cond = inv.Arguments.First(a => a.Parameter.Ordinal == 0).Value;
            var c = AsBool(Eval(cond, f, spec));
            foreach (var a in inv.Arguments.Where(a => a.Parameter.Ordinal > 0 && a.ArgumentKind == ArgumentKind.Explicit)) Eval(a.Value, f, spec);
            Prove(c, "CSV1004", inv.Syntax, $"'{inv.TargetMethod.ContainingType.Name}.Assert({cond.Syntax})' might not hold");
            return T.True;
        }

        /// <summary>Is this member's stub async: does awaiting it give its contract's result?</summary>
        private bool IsAsyncStubbed(IMethodSymbol m) => _engine.ContractOf(m) is Contract c && c.IsStub && c.Stub.IsAsync;

        /// <summary>The T an await of a call to <paramref name="m"/> gives: an async method's, or an async stub's.</summary>
        private ITypeSymbol AwaitedType(IMethodSymbol m) =>
            AsyncResultType(m) ?? (IsAsyncStubbed(m) && m.ReturnType is INamedTypeSymbol rt && rt.TypeArguments.Length == 1 ? rt.TypeArguments[0] : null);
    }
}
