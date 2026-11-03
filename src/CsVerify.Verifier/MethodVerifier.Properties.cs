using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Properties with code: a getter or setter with a body (or an abstract, virtual or interface accessor, specified
    /// by its contract) is a method, called where the property is read or written. A [Pure] property is a function,
    /// usable in specifications; others are calls in code, with their contracts checked and assumed.
    /// </summary>
    internal sealed partial class MethodVerifier
    {
        private static bool IsComputed(IMethodSymbol accessor) =>
            accessor != null && accessor.DeclaringSyntaxReferences.Length > 0 &&
            accessor.ContainingType?.ContainingNamespace?.ToDisplayString() != SpecSymbols.Namespace && // the library's ghost members
            !(accessor.AssociatedSymbol is IPropertySymbol p && FieldEffects.IsHeapField(p)) &&
            !(accessor.AssociatedSymbol is IPropertySymbol pos && DataTypes.IsPositional(pos)) &&
            accessor.DeclaringSyntaxReferences.Select(r => r.GetSyntax()).Any(s =>
                s is ArrowExpressionClauseSyntax ||
                s is AccessorDeclarationSyntax a && (a.Body != null || a.ExpressionBody != null || accessor.IsAbstract || accessor.ContainingType.TypeKind == TypeKind.Interface));

        /// <summary>A call of a property's getter (<paramref name="value"/> null) or setter.</summary>
        private Term CallAccessor(IMethodSymbol accessor, IOperation instance, IEnumerable<IOperation> indices, Term value, ITypeSymbol resultType,
                                  SyntaxNode at, Frame f, SpecEnv spec)
        {
            var callee = _engine.ContractOf(accessor);
            if (callee.IsStub && _codeMode) Assumed(callee);
            Term receiver = null;
            if (instance != null)
            {
                receiver = Eval(instance, f, spec);
                Deref(instance, receiver, at);
            }
            var args = indices.Select(i => Eval(i, f, spec)).ToList();
            if (value != null) args.Add(value);
            var argTerms = args.ToArray();
            var sort = resultType != null ? SortOf(resultType) : Sort.Bool;

            if (!_codeMode)
            {
                if (callee.IsPure) return PureApply(callee, receiver, argTerms, f.Heap, sort, at, f);
                Warn(at, $"'{accessor.AssociatedSymbol?.Name}' is not a [Pure] property and cannot be used in a specification; treated as unknown");
                return resultType != null ? Unknown(resultType) : T.True;
            }

            var pre = CalleeFrame(callee, receiver, argTerms, f.Heap, f);
            var preEnv = new SpecEnv { Old = pre };
            foreach (var req in callee.Requires)
                Prove(AsBool(EvalForeignSpec(req, pre, preEnv)), "CSV1001", at, $"precondition '{req.Syntax}' of '{accessor.Name}' might not hold");
            if (callee.IsPure) CheckPureCallReads(callee, pre, at);

            var touched = new List<Term>();
            bool ownedCall = receiver != null && SpecSymbols.IsOwned(accessor.ContainingType) && !callee.IsPure && !accessor.IsStatic;
            if (ownedCall)
            {
                RequireWriteView(receiver, f, at, accessor.ContainingType);
                ProveOwnedInvariant(accessor.ContainingType, receiver, f, at, $"when '{accessor.Name}' is called on it");
                touched.Add(receiver);
            }
            var modifiable = callee.IsPure ? null : CalleeModifies(callee, pre, f, at, accessor);
            var post = pre.Clone();
            if (HavocsHeap(accessor)) f.Heap = post.Heap = _z3.Fresh("heap", Sort.Heap);
            HavocFields(f, accessor, touched, modifiable);
            post.Fields = new Dictionary<ISymbol, Term>(f.Fields, SymbolEqualityComparer.Default);
            post.FieldEpoch = f.FieldEpoch;
            post.Link = f.Link;

            var result = resultType != null ? FreshOf(resultType, accessor.Name) : null;
            if (result != null && (IsNonNullableReturn(callee.Method) || callee.IsStub && NonNullAsInstantiated(accessor))) _z3.Assume(NotNull(result));
            if (result != null && callee.IsPure)
                _z3.Assume(T.Eq(result, PureApply(callee, receiver, argTerms, pre.Heap, result.Sort, null, pre)));
            if (!callee.IsPure)
            {
                AllocAfterCall(f, result);
                post.Alloc = f.Alloc;
            }
            foreach (var ens in callee.Ensures)
                _z3.Assume(GuardedBy(ens, pre, AsBool(EvalForeignSpec(ens.Expr, post, new SpecEnv { Old = pre, Result = result, ResultParameter = ens.ResultParameter }))));
            if (ownedCall) AssumeOwnedInvariant(accessor.ContainingType, receiver, f);
            return result ?? T.True;
        }
    }
}
