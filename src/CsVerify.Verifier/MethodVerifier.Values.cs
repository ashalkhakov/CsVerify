using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Values and equality. A string is its value: two strings with the same characters are the same term, so
    /// <c>==</c>, <c>Equals</c>, a switch on strings, <c>Length</c> and a dictionary's string keys compare contents, as
    /// .NET does (ordinally), and a literal is the same value wherever it appears (different literals are different
    /// values). Comparing strings as objects (<c>ReferenceEquals</c>, <c>(object)a == (object)b</c>) is unknown, since
    /// equal strings may or may not be one object. The characters themselves are not modeled.
    ///
    /// <c>Spec.Equal(a, b)</c> is what <c>EqualityComparer&lt;T&gt;.Default.Equals(a, b)</c> gives, for T as the call
    /// instantiates it: the verifier's own equality where T's is known (numbers, chars, bools, enums, strings, classes
    /// that do not override Equals, data records), else a relation the verifier knows nothing of, fixed within one call's
    /// contract. A ghost Map's keys are compared the same way: by value where T's equality is known, else through a key
    /// function (as .NET's dictionaries require: a key does not change while it is one).
    /// </summary>
    internal sealed partial class MethodVerifier
    {
        private readonly Dictionary<string, Term> _stringLiterals = new Dictionary<string, Term>(System.StringComparer.Ordinal);

        /// <summary>The value of a string literal: one constant per contents (non-zero, so not null).</summary>
        private Term StringLiteral(string s, ITypeSymbol type)
        {
            if (!_stringLiterals.TryGetValue(s, out var v))
            {
                v = T.Int(-1000003 - 7 * _stringLiterals.Count);
                _stringLiterals[s] = v;
            }
            AssumeSide(T.Eq(Len(v), T.Int(s.Length)));
            if (type != null) HasType(v, type);
            return v;
        }

        /// <summary>The type substitution of the call whose contract is being evaluated (a stub's T as instantiated).</summary>
        private readonly Stack<Dictionary<ITypeSymbol, ITypeSymbol>> _instantiations = new Stack<Dictionary<ITypeSymbol, ITypeSymbol>>();
        private readonly Stack<Term> _equalityEpochs = new Stack<Term>();

        private ITypeSymbol Resolve(ITypeSymbol t)
        {
            foreach (var map in _instantiations)
                if (t is ITypeParameterSymbol && map.TryGetValue(t, out var to)) t = to;
            return t;
        }

        /// <summary>The substitution for a call: the callee's (or its stub's) type parameters, as the call instantiates them.</summary>
        private Dictionary<ITypeSymbol, ITypeSymbol> InstantiationOf(IMethodSymbol called, Contract callee)
        {
            var map = new Dictionary<ITypeSymbol, ITypeSymbol>(SymbolEqualityComparer.Default);
            void Add(IEnumerable<ITypeParameterSymbol> ps, IEnumerable<ITypeSymbol> args)
            {
                foreach (var (p, a) in ps.Zip(args, (p, a) => (p, a))) if (!SymbolEqualityComparer.Default.Equals(p, a)) map[p] = Resolve(a);
            }
            Add(called.OriginalDefinition.TypeParameters, called.TypeArguments);
            Add(called.ContainingType.OriginalDefinition.TypeParameters, called.ContainingType.TypeArguments);
            if (callee.IsStub && callee.Stub != null)
            {
                Add(callee.Stub.TypeParameters, called.TypeArguments);
                Add(callee.Stub.ContainingType.TypeParameters, called.ContainingType.TypeArguments);
            }
            return map;
        }

        /// <summary>Is T's Equals the verifier's own equality of its values?</summary>
        private bool KnownEquality(ITypeSymbol t)
        {
            t = Resolve(t);
            if (t == null || t is ITypeParameterSymbol) return false;
            if (IsIntegral(t) || t.SpecialType == SpecialType.System_Boolean || t.SpecialType == SpecialType.System_String || t.TypeKind == TypeKind.Enum)
                return true;
            if (IsFloating(t) || IsNullableValue(t)) return false; // (NaN.Equals(NaN) is true, unlike ==; int? is a value)
            bool overrides = false;
            for (var b = t; b != null && b.SpecialType != SpecialType.System_Object; b = b.BaseType)
                if (b.GetMembers("Equals").OfType<IMethodSymbol>().Any(m => !m.IsImplicitlyDeclared && !m.IsStatic && m.Parameters.Length == 1) ||
                    b.AllInterfaces.Any(i => i.Name == "IEquatable"))
                    overrides = true;
            if (t.TypeKind == TypeKind.Class && Data.IsData(t)) return t.GetMembers("Equals").OfType<IMethodSymbol>().All(m => m.IsImplicitlyDeclared);
            return t.TypeKind == TypeKind.Class && !overrides; // reference equality, as the verifier's
        }

        /// <summary>A ghost Map's index for a key of type K: the key itself where K's equality is known, else its key class.</summary>
        private Term KeyOf(Term key, ITypeSymbol keyType)
        {
            key = T.Coerce(key, Sort.Int);
            if (KnownEquality(keyType)) return key;
            var k = Resolve(keyType);
            return _z3.Apply("key:" + k.ToDisplayString(), Sort.Int, new[] { key });
        }

        /// <summary>The key type of a Map&lt;K, V&gt; (or null for other ghost collections).</summary>
        private static ITypeSymbol MapKeyType(ITypeSymbol t) =>
            t is INamedTypeSymbol n && n.Name == "Map" && n.TypeArguments.Length == 2 && SpecSymbols.IsSeqType(n) ? n.TypeArguments[0] : null;

        /// <summary><c>Spec.Equal(a, b)</c>: EqualityComparer&lt;T&gt;.Default.Equals(a, b).</summary>
        private Term SpecEqual(IInvocationOperation inv, Frame f, SpecEnv spec)
        {
            var a = T.Coerce(Eval(inv.Arguments[0].Value, f, spec), Sort.Int);
            var b = T.Coerce(Eval(inv.Arguments[1].Value, f, spec), Sort.Int);
            var t = inv.TargetMethod.TypeArguments[0];
            if (KnownEquality(t)) return T.Eq(a, b);
            // a relation fixed within one contract (a quantifier over it is consistent), fresh for each call
            var epoch = _equalityEpochs.Count > 0 ? _equalityEpochs.Peek() : _z3.Fresh("equals", Sort.Int);
            return _z3.Apply("equals:" + Resolve(t).ToDisplayString(), Sort.Bool, new[] { a, b, epoch });
        }

        /// <summary>string.Equals(a, b), a.Equals(b), with StringComparison.Ordinal; null for other calls.</summary>
        private Term StringEquals(IInvocationOperation inv, Frame f, SpecEnv spec)
        {
            var m = inv.TargetMethod;
            if (m.Name != "Equals" || m.ContainingType?.SpecialType != SpecialType.System_String) return null;
            var strings = m.Parameters.TakeWhile(p => p.Type.SpecialType == SpecialType.System_String).Count();
            var rest = m.Parameters.Skip(strings).ToList();
            // (StringComparison.Ordinal, or none: ordinal; other comparisons are not modeled)
            if (rest.Count > 1 || rest.Count == 1 && !(rest[0].Type.Name == "StringComparison" &&
                inv.Arguments.First(a => a.Parameter.Ordinal == rest[0].Ordinal).Value.ConstantValue is { HasValue: true, Value: 4 })) return null;
            Term x, y;
            if (m.IsStatic && strings == 2)
            {
                x = Eval(inv.Arguments.First(a => a.Parameter.Ordinal == 0).Value, f, spec);
                y = Eval(inv.Arguments.First(a => a.Parameter.Ordinal == 1).Value, f, spec);
            }
            else if (!m.IsStatic && strings == 1 && inv.Instance != null)
            {
                x = Eval(inv.Instance, f, spec);
                Deref(inv.Instance, x, inv.Syntax);
                y = Eval(inv.Arguments.First(a => a.Parameter.Ordinal == 0).Value, f, spec);
            }
            else return null;
            return T.Eq(T.Coerce(x, Sort.Int), T.Coerce(y, Sort.Int));
        }
    }
}
