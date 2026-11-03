using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Invariants of immutable classes: an ordinary class whose instance fields (its own and its source bases') are
    /// all readonly, or get-only auto-properties. Its fields never change once a constructor has returned, so an
    /// [Invariant] is proved where each constructor returns (CSV1015) and assumed of every object of the type whose
    /// fields are read. Inside a constructor the object is not finished: it is not assumed of <c>this</c> there, and
    /// <c>this</c> may not escape (to a call, as a receiver, into a field or variable) before the constructor ends.
    /// </summary>
    internal sealed partial class MethodVerifier
    {
        internal static bool IsImmutableClass(ITypeSymbol type)
        {
            if (!(type is INamedTypeSymbol t) || t.TypeKind != TypeKind.Class || SpecSymbols.IsOwned(t) || t.IsRecord) return false;
            for (var s = t.OriginalDefinition; s != null && s.SpecialType != SpecialType.System_Object; s = s.BaseType?.OriginalDefinition)
            {
                if (s.DeclaringSyntaxReferences.Length == 0) return false;
                foreach (var m in s.GetMembers().Where(x => !x.IsStatic && FieldEffects.IsHeapField(x)))
                    if (m is IFieldSymbol f && !f.IsReadOnly || m is IPropertySymbol p && p.SetMethod != null && !p.SetMethod.IsInitOnly)
                        return false;
            }
            return true;
        }

        private bool HasImmutableInvariants(ITypeSymbol type) => IsImmutableClass(type) && DataTypes.Invariants(type).Any();

        private bool InOwnConstructor(ITypeSymbol type) =>
            _method.MethodKind == MethodKind.Constructor && DataTypes.Derives(_method.ContainingType, type);

        /// <summary>Reading a field of a finished immutable object: its invariants hold.</summary>
        private void AssumeImmutableInvariants(Term o, ITypeSymbol staticType, Frame f)
        {
            if (!HasImmutableInvariants(staticType) || _engine.IsUnderInvariant(_method) || !_codeMode && _foreignSpec > 0 && _unfoldDepth > 0) return;
            if (f.This != null && InOwnConstructor(staticType))
            {
                // this object is still being built
                AssumeSide(T.Implies(T.And(NotNull(o), T.Not(T.Eq(o, f.This))), OwnedInvariant(staticType, o, f)));
                return;
            }
            if (!_invariantsInProgress.Add(o.S)) return;
            try { AssumeSide(T.Implies(NotNull(o), OwnedInvariant(staticType, o, f))); }
            finally { _invariantsInProgress.Remove(o.S); }
        }

        /// <summary>When a constructor of an immutable class returns, the object satisfies its invariants.</summary>
        private void ProveImmutableInvariants(Frame f, SyntaxNode at)
        {
            if (_method.MethodKind != MethodKind.Constructor || _method.IsStatic || !HasImmutableInvariants(_method.ContainingType)) return;
            _invariantsInProgress.Add(f.This.S);
            try { ProveOwnedInvariant(_method.ContainingType, f.This, f, at, $"when the constructor of {_method.ContainingType.Name} returns"); }
            finally { _invariantsInProgress.Remove(f.This.S); }
        }

        /// <summary>In a constructor of a class with invariants, <c>this</c> may only have its own fields read and written.</summary>
        private void CheckThisEscape(IOperation op)
        {
            if (_method.MethodKind != MethodKind.Constructor || !HasImmutableInvariants(_method.ContainingType)) return;
            foreach (var use in op.DescendantsAndSelf().OfType<IInstanceReferenceOperation>())
            {
                var parent = use.Parent;
                if (parent is IFieldReferenceOperation || parent is IPropertyReferenceOperation pr && FieldEffects.IsHeapField(pr.Property)) continue;
                if (parent is IInvocationOperation inv && inv.TargetMethod.MethodKind == MethodKind.Constructor) continue; // base(...)/this(...)
                Report("CSV1015", use.Syntax, $"'this' escapes the constructor of {_method.ContainingType.Name} before its invariant is established", isError: true);
            }
        }
    }
}
