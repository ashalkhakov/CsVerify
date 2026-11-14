using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Immutable classes: an ordinary class whose instance fields (its own and its source bases') are all readonly, or
    /// get-only auto-properties. An [Invariant] of one, as of a data type or an [Owned] class, is checked not to depend
    /// on what can change behind its back (CSV1015); of any other class it isn't used (a warning).
    /// </summary>
    internal sealed partial class StaticChecks
    {
        internal static bool IsImmutableClass(ITypeSymbol type)
        {
            if (!(type is INamedTypeSymbol t) || t.TypeKind != TypeKind.Class || SpecSymbols.IsOwned(t) || t.IsRecord)
            {
                return false;
            }
            for (var s = t.OriginalDefinition; s != null && s.SpecialType != SpecialType.System_Object; s = s.BaseType?.OriginalDefinition)
            {
                if (s.DeclaringSyntaxReferences.Length == 0)
                {
                    return false;
                }
                foreach (var m in s.GetMembers().Where(x => !x.IsStatic && FieldEffects.IsHeapField(x)))
                {
                    if (m is IFieldSymbol f && !f.IsReadOnly || m is IPropertySymbol p && p.SetMethod != null && !p.SetMethod.IsInitOnly)
                    {
                        return false;
                    }
                }
            }
            return true;
        }
    }
}
