using System.Collections.Generic;
using System.Linq;
using Microsoft.CodeAnalysis;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Dynamic types of ordinary objects: <c>isa(o, T)</c>, "o is an instance of T". A non-null value of a static
    /// type is an instance of it and of its supertypes; an object made by <c>new C()</c> is exactly a C. Classes form
    /// a tree (single inheritance), so unrelated classes have no instance in common, and a sealed class's instances
    /// are of no type but its supertypes. <c>is</c>, <c>as</c> and casts read isa. Generic types are left out (their
    /// instantiations would share one name), as are data records (they have tags) and value types.
    /// </summary>
    internal sealed partial class MethodVerifier
    {
        private readonly List<(Term obj, INamedTypeSymbol type, bool exact)> _typed = new List<(Term, INamedTypeSymbol, bool)>();
        private readonly HashSet<INamedTypeSymbol> _typesInPlay = new HashSet<INamedTypeSymbol>(SymbolEqualityComparer.Default);

        private static INamedTypeSymbol ModeledType(ITypeSymbol t) =>
            t is INamedTypeSymbol n && n.IsReferenceType && !n.IsGenericType && n.ContainingType?.IsGenericType != true &&
            n.TypeKind != TypeKind.Delegate && n.SpecialType != SpecialType.System_Object ? n.OriginalDefinition : null;

        private Term Isa(Term o, INamedTypeSymbol t) =>
            _z3.Apply("isa:" + t.ToDisplayString(), Sort.Bool, new[] { T.Coerce(o, Sort.Int) });

        private static IEnumerable<INamedTypeSymbol> Supertypes(INamedTypeSymbol t)
        {
            for (var b = t.BaseType; b != null; b = b.BaseType)
                if (ModeledType(b) is INamedTypeSymbol mb) yield return mb;
            foreach (var i in t.AllInterfaces)
                if (ModeledType(i) is INamedTypeSymbol mi) yield return mi;
        }

        private static bool IsSubtype(INamedTypeSymbol t, INamedTypeSymbol of) =>
            SymbolEqualityComparer.Default.Equals(t, of) || Supertypes(t).Contains(of, SymbolEqualityComparer.Default);

        /// <summary>Can no object be an instance of both? (Unrelated classes; a sealed type and anything not above it.)</summary>
        private static bool Disjoint(INamedTypeSymbol a, INamedTypeSymbol b)
        {
            if (IsSubtype(a, b) || IsSubtype(b, a)) return false;
            if (a.TypeKind == TypeKind.Class && b.TypeKind == TypeKind.Class) return true;
            return a.IsSealed || b.IsSealed;
        }

        /// <summary>A type takes part in this method's reasoning: what is already known about objects covers it too.</summary>
        private void InPlay(INamedTypeSymbol t)
        {
            if (!_typesInPlay.Add(t)) return;
            foreach (var (o, type, exact) in _typed.ToList()) Relate(o, type, exact, t);
        }

        private void Relate(Term o, INamedTypeSymbol type, bool exact, INamedTypeSymbol other)
        {
            if (exact ? !IsSubtype(type, other) : Disjoint(type, other))
                AssumeSide(T.Implies(NotNull(o), T.Not(Isa(o, other))));
        }

        /// <summary>A value of static type <paramref name="type"/> (if not null) is an instance of it: <paramref name="exact"/> for a new object.</summary>
        private void HasType(Term o, ITypeSymbol type, bool exact = false)
        {
            if (!(ModeledType(type) is INamedTypeSymbol t) || o.Sort != Sort.Int || Data.IsData(t)) return;
            AssumeSide(T.Implies(NotNull(o), Isa(o, t)));
            foreach (var s in Supertypes(t)) AssumeSide(T.Implies(NotNull(o), Isa(o, s)));
            _typed.Add((o, t, exact));
            InPlay(t);
            foreach (var other in _typesInPlay.ToList()) Relate(o, t, exact, other);
        }

        /// <summary><c>o is D</c> for an ordinary class or interface D: not null, and an instance of D; null if D is not modeled.</summary>
        private Term ClassTest(Term o, ITypeSymbol matched)
        {
            if (!(ModeledType(matched) is INamedTypeSymbol d) || Data.IsData(d)) return null;
            InPlay(d);
            return T.And(NotNull(o), Isa(o, d));
        }
    }
}
