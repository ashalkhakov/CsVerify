using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Contracts for code without sources ([ContractsFor] stubs, see <see cref="ContractStubs"/>): a stubbed member is
    /// called like a source method with its stub's contract, which is trusted. Its preconditions are proved at the
    /// call; its postconditions are assumed, and so counted among the run's assumptions. [Model] functions are ghost
    /// fields of the external objects (<see cref="FieldEffects"/>): a stub's Spec.Modifies frames them like any field.
    /// </summary>
    internal sealed partial class MethodVerifier
    {
        /// <summary>A stub's contract is used: an assumption of this proof.</summary>
        private void Assumed(Contract callee) => Assumed(callee.Method.ToDisplayString());

        /// <summary>A library member the verifier models with the stubs' model functions (foreach over a list).</summary>
        private void Assumed(string member) => _result.Assumptions.Add(member);

        /// <summary>The stub's parameter that stands for the member's i-th (after <c>@this</c>, for an instance member).</summary>
        private static IParameterSymbol StubParameter(Contract callee, int i)
        {
            int j = callee.StubReceiver != null ? i + 1 : i;
            return j < callee.Stub.Parameters.Length ? callee.Stub.Parameters[j] : null;
        }

        /// <summary>
        /// A [Pure] stubbed member with a definition (<see cref="Contract.StubDefinition"/>): its value is the definition,
        /// and its other postconditions hold of it, where its precondition does.
        /// </summary>
        private Term StubValue(Contract callee, Term receiver, Term[] args, Term heap, Sort sort, SyntaxNode specCall, Frame state)
        {
            Term pre, value;
            bool wasCode = _codeMode;
            _codeMode = false;
            _foreignSpec++; // (its contract: no obligations of ours)
            try
            {
                var frame = CalleeFrame(callee, receiver, args, heap, state);
                var env = new SpecEnv { Old = frame };
                pre = T.And(callee.Requires.Select(r => AsBool(Eval(r, frame, env))).ToArray());
                value = InRangeOf(T.Coerce(Eval(callee.StubDefinition, frame, env), SortOf(callee.Method.ReturnType)), callee.Method.ReturnType);
                foreach (var ens in callee.Ensures)
                    AssumeSide(T.Implies(pre, AsBool(Eval(ens.Expr, frame, new SpecEnv { Old = frame, Result = value, ResultParameter = ens.ResultParameter }))));
            }
            finally { _foreignSpec--; _codeMode = wasCode; }
            if (specCall != null && !_codeMode && _foreignSpec == 0)
                Require(pre, "CSV1001", specCall, $"precondition of '{callee.Method.Name}' might not hold in '{specCall}'");
            return T.Coerce(value, sort);
        }

        /// <summary>
        /// A library member returning a type parameter, as instantiated with a non-nullable type: a
        /// <c>List&lt;string&gt;</c>'s items are strings (as the library declares it).
        /// </summary>
        private static bool NonNullAsInstantiated(IMethodSymbol asCalled) =>
            asCalled.OriginalDefinition.ReturnType is ITypeParameterSymbol && IsNonNullableType(asCalled.ReturnType);

        /// <summary>A library's T, as it declares it (not T?, nor [MaybeNull]): what it is instantiated with. (GetOrAdd gives a V, a List's Find a T?.)</summary>
        private static bool LibraryGivesAsInstantiated(IMethodSymbol asCalled) =>
            asCalled.OriginalDefinition.DeclaringSyntaxReferences.Length == 0 && NonNullAsInstantiated(asCalled) &&
            !HasAttribute(asCalled.OriginalDefinition.GetReturnTypeAttributes(), "MaybeNullAttribute");

        private bool IsStubbedProperty(IOperation op) =>
            op is IPropertyReferenceOperation pr && pr.Property.GetMethod != null && _engine.HasStub(pr.Property.GetMethod);

        /// <summary><c>M(o)</c> or <c>M(o, k)</c> of a [Model] function M: the ghost field M of o (at key k).</summary>
        private Term ModelRead(IInvocationOperation inv, Frame f, SpecEnv spec)
        {
            var model = (inv.TargetMethod.ReducedFrom ?? inv.TargetMethod).OriginalDefinition;
            var args = inv.Arguments.OrderBy(a => a.Parameter?.Ordinal ?? 0).Select(a => Eval(a.Value, f, spec)).ToList();
            if (!_engine.Models.Contains(model, SymbolEqualityComparer.Default))
            {
                NotModeled(inv.Syntax, $"[Model] '{model.Name}' is not known here");
                return Unknown(inv.Type, model.Name);
            }
            return ModelAt(model, args, f, inv.Type);
        }

        /// <summary>
        /// The value of model function M at (o) or (o, k) in a state: the ghost field M of o (at key k), with what M's own
        /// postconditions say of it.
        /// </summary>
        private Term ModelAt(IMethodSymbol model, IReadOnlyList<Term> args, Frame f, ITypeSymbol type = null)
        {
            type ??= model.ReturnType;
            var o = T.Coerce(args[0], Sort.Int);
            var map = FieldMap(f, model);
            var value = model.Parameters.Length == 2
                ? InRangeOf(T.Coerce(T.Select(T.Select(map, o, Sort.Row), T.Coerce(args[1], Sort.Int), Sort.Int), SortOf(type)), type)
                : ValueSort(model) == Sort.Row ? T.Select(map, o, Sort.Row)
                : InRangeOf(T.Coerce(T.Select(map, o, Sort.Int), SortOf(type)), type);
            // what the model function's own postconditions say of every value (a size is not negative): trusted
            var contract = _engine.ContractOf(model);
            if (contract.Ensures.Count > 0)
            {
                var frame = new Frame { Heap = f.Heap };
                for (int i = 0; i < args.Count; i++) frame.Vars[contract.Method.Parameters[i]] = args[i];
                bool wasCode = _codeMode;
                _codeMode = false;
                _foreignSpec++;
                try
                {
                    foreach (var ens in contract.Ensures)
                        AssumeSide(AsBool(Eval(ens.Expr, frame, new SpecEnv { Old = frame, Result = value, ResultParameter = ens.ResultParameter })));
                }
                finally { _foreignSpec--; _codeMode = wasCode; }
            }
            return value;
        }
    }
}
