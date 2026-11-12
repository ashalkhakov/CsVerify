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
    internal sealed partial class StaticChecks
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
    }
}
