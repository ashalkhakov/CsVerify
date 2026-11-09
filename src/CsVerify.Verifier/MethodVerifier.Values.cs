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
            if (_looksAtChars) DefineStrings();
            if (type != null) HasType(v, type);
            return v;
        }

        // ---- strings' characters: see T.StringDeclarations. What strings are made of is stated only once the method
        // looks at characters or compares a string it built, so that the rest pay nothing for it.
        private bool _looksAtChars;
        private readonly List<(Term cat, Term left, Term right)> _concats = new List<(Term, Term, Term)>();
        private readonly List<(Term x, Term y)> _compared = new List<(Term, Term)>();

        private static Term CharAt(Term x, Term i) => new Term($"(cv_at {x.S} {i.S})", Sort.Int);

        /// <summary><c>s[i]</c> (the caller has checked the bounds).</summary>
        private Term Char(Term s, Term i)
        {
            _looksAtChars = true;
            DefineStrings();
            return CharAt(T.Coerce(s, Sort.Int), i);
        }

        private void DefineStrings()
        {
            _z3.UseStrings();
            foreach (var kv in _stringLiterals)
                _z3.AssumeOnce("literal:" + kv.Value.S, () => T.And(kv.Key.Select((c, i) => T.Eq(CharAt(kv.Value, T.Int(i)), T.Int(c))).ToArray()));
            foreach (var (cat, left, right) in _concats)
                _z3.AssumeOnce("concat:" + cat.S, () => ConcatChars(cat, left, right));
            foreach (var (x, y) in _compared)
                _z3.AssumeOnce($"compared:{x.S}:{y.S}", () => Extensional(x, y));
        }

        /// <summary><c>cat</c>'s characters are those of <c>left</c> (null counts as empty), then those of <c>right</c>.</summary>
        private Term ConcatChars(Term cat, Term left, Term right)
        {
            var i = new Term("cv_i", Sort.Int);
            var leftLength = T.Ite(T.Eq(left, T.Int(0)), T.Int(0), Len(left));
            var value = T.Ite(T.Lt(i, leftLength), CharAt(left, i), CharAt(right, T.Sub(i, leftLength)));
            return new Term($"(forall (({i.S} Int)) (! {T.Implies(T.And(T.Le(T.Int(0), i), T.Lt(i, Len(cat))), T.Eq(CharAt(cat, i), value)).S} :pattern ({CharAt(cat, i).S})))", Sort.Bool);
        }

        /// <summary>Two different strings of one length differ at some index: a string is its characters.</summary>
        private Term Extensional(Term x, Term y)
        {
            var at = new Term($"(cv_diff {x.S} {y.S})", Sort.Int);
            return T.Implies(T.And(NotNull(x), NotNull(y), T.Not(T.Eq(x, y)), T.Eq(Len(x), Len(y))),
                T.And(T.Le(T.Int(0), at), T.Lt(at, Len(x)), T.Not(T.Eq(CharAt(x, at), CharAt(y, at)))));
        }

        /// <summary><c>a + b</c>'s contents, known (like everything about characters) once the method looks at them.</summary>
        private void ConcatIs(Term cat, Term left, Term right)
        {
            if (_quantFacts.Count > 0) return; // (under a quantifier the operands may name its variable: length only)
            _concats.Add((cat, T.Coerce(left, Sort.Int), T.Coerce(right, Sort.Int)));
            if (_looksAtChars) DefineStrings();
        }

        /// <summary>Two strings compared: when one was built, or characters are known, what they are made of decides it.</summary>
        private void StringsCompared(Term x, Term y)
        {
            var pair = (T.Coerce(x, Sort.Int), T.Coerce(y, Sort.Int));
            if (_quantFacts.Count > 0)
            {
                if (_looksAtChars) { DefineStrings(); AssumeSide(Extensional(pair.Item1, pair.Item2)); }
                return;
            }
            _compared.Add(pair);
            if (_concats.Count > 0 || _looksAtChars) { _looksAtChars = true; DefineStrings(); }
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
            if (t is INamedTypeSymbol { IsTupleType: true } tuple) return tuple.TupleElements.All(e => KnownEquality(e.Type)); // (item by item)
            if (t.IsAnonymousType) return ((INamedTypeSymbol)t).GetMembers().OfType<IPropertySymbol>().All(p => KnownEquality(p.Type)); // (member by member)
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
            if (_inDatabase > 0 && DatabaseEqual(Resolve(t), a, b) is Term inDatabase) return inDatabase;
            if (KnownEquality(t)) return T.Eq(a, b);
            if (IsNullableValue(Resolve(t)) && KnownEquality(Underlying(Resolve(t))))
            {
                // int?: both null, or both with equal values
                var n = Resolve(t);
                return T.And(T.Eq(HasValue(a), HasValue(b)), T.Implies(HasValue(a), T.Eq(ValueOf(a, n), ValueOf(b, n))));
            }
            if (IsFloating(Resolve(t)))
            {
                // double.Equals: IEEE == (so -0.0 equals 0.0), and NaN equals NaN
                var s = SortOf(Resolve(t));
                return T.Or(FpTest("fp.eq", s, a, b), T.And(FpTest("fp.isNaN", s, a), FpTest("fp.isNaN", s, b)));
            }
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
            StringsCompared(x, y);
            return T.Eq(T.Coerce(x, Sort.Int), T.Coerce(y, Sort.Int));
        }
    }
}
