using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// A collection changed while it is enumerated. List, Dictionary, HashSet, Stack and Queue have a version (a
    /// [Model], Version()) that a change of the collection may change, and an enumerator remembers the collection and
    /// its version from GetEnumerator. Each MoveNext requires the version to be the same still: else it throws
    /// InvalidOperationException ("Collection was modified"), and that is reported (CSV1001). Changing the collection
    /// and leaving the loop at once (break) is fine: the next MoveNext is what fails. Dictionary.Remove keeps the
    /// version (as .NET Core 3.0 and later do).
    /// </summary>
    internal sealed partial class MethodVerifier
    {
        private static readonly string[] Versioned =
        {
            "System.Collections.Generic.List<T>", "System.Collections.Generic.Dictionary<TKey, TValue>",
            "System.Collections.Generic.HashSet<T>", "System.Collections.Generic.Stack<T>", "System.Collections.Generic.Queue<T>",
        };

        /// <summary>A dictionary's Keys or Values (KeyCollection, ValueCollection): a view of it.</summary>
        private static bool IsDictionaryView(ITypeSymbol t) =>
            t is INamedTypeSymbol n && (n.Name == "KeyCollection" || n.Name == "ValueCollection") &&
            n.ContainingType?.OriginalDefinition.ToDisplayString() == "System.Collections.Generic.Dictionary<TKey, TValue>";

        private Term ViewOf(Term view) => _z3.Apply("view.dictionary", Sort.Int, new[] { T.Coerce(view, Sort.Int) });

        /// <summary>d.Keys and d.Values (views that remember their dictionary), and a view's Count; null for others.</summary>
        private Term DictionaryView(IPropertyReferenceOperation pr, Frame f, SpecEnv spec)
        {
            var prop = pr.Property;
            if (pr.Instance == null) return null;
            if ((prop.Name == "Keys" || prop.Name == "Values") && prop.ContainingType?.OriginalDefinition.ToDisplayString() == "System.Collections.Generic.Dictionary<TKey, TValue>" &&
                IsDictionaryView(prop.Type))
            {
                var d = T.Coerce(Eval(pr.Instance, f, spec), Sort.Int);
                Deref(pr.Instance, d, pr.Syntax);
                var view = _z3.Apply("view." + prop.Name, Sort.Int, new[] { d }); // (the same view each time, as Dictionary caches it)
                AssumeSide(T.And(NotNull(view), T.Eq(ViewOf(view), d)));
                return view;
            }
            if (prop.Name == "Count" && IsDictionaryView(prop.ContainingType) &&
                _engine.Models.FirstOrDefault(m => m.Name == "Size" && m.Parameters.Length == 1 &&
                    m.Parameters[0].Type.OriginalDefinition.ToDisplayString() == "System.Collections.Generic.Dictionary<TKey, TValue>") is IMethodSymbol size)
            {
                var v = T.Coerce(Eval(pr.Instance, f, spec), Sort.Int);
                Deref(pr.Instance, v, pr.Syntax);
                return T.Coerce(ModelAt(size, new[] { ViewOf(v) }, f), Sort.Int);
            }
            return null;
        }

        private IMethodSymbol DictionaryModel(string name) =>
            _engine.Models.FirstOrDefault(m => m.Name == name && m.Parameters.Length == 1 &&
                m.Parameters[0].Type.OriginalDefinition.ToDisplayString() == "System.Collections.Generic.Dictionary<TKey, TValue>");

        /// <summary>
        /// A foreach's Current over a dictionary (or its Keys): a pair it has, read right after MoveNext, when nothing
        /// has run since. A KeyValuePair's Key and Value are functions of it. Null for others.
        /// </summary>
        private Term DictionaryCurrent(IPropertyReferenceOperation pr, Frame f, SpecEnv spec)
        {
            var prop = pr.Property;
            if (prop.Name == "Key" || prop.Name == "Value")
            {
                if (pr.Instance == null || prop.ContainingType?.OriginalDefinition.ToDisplayString() != "System.Collections.Generic.KeyValuePair<TKey, TValue>") return null;
                var p = T.Coerce(Eval(pr.Instance, f, spec), Sort.Int);
                return InRangeOf(T.Coerce(_z3.Apply("kvp." + prop.Name, Sort.Int, new[] { p }), SortOf(pr.Type)), pr.Type);
            }
            if (!_foreachCurrent.Contains(pr) || !(prop.ContainingType is INamedTypeSymbol en) || en.Name != "Enumerator") return null;
            var owner = en.ContainingType;
            bool pairs = owner?.OriginalDefinition.ToDisplayString() == "System.Collections.Generic.Dictionary<TKey, TValue>";
            bool keys = owner?.Name == "KeyCollection" && IsDictionaryView(owner);
            if (!pairs && !keys || DictionaryModel("Domain") is not IMethodSymbol domain || DictionaryModel("Entries") is not IMethodSymbol entries) return null;
            var e = T.Coerce(Eval(pr.Instance, f, spec), Sort.Int);
            var d = EnumeratorOf(e);
            var dictionary = pairs ? owner : owner.ContainingType;
            var keyType = dictionary is INamedTypeSymbol dt && dt.TypeArguments.Length == 2 ? dt.TypeArguments[0] : null;
            var current = _z3.Fresh("current", Sort.Int);
            var key = pairs ? _z3.Apply("kvp.Key", Sort.Int, new[] { current }) : current;
            var k = KeyOf(key, keyType);
            var facts = T.Eq(T.Select(ModelAt(domain, new[] { d }, f), k, Sort.Int), T.Int(1));
            if (pairs) facts = T.And(facts, T.Eq(_z3.Apply("kvp.Value", Sort.Int, new[] { current }), T.Coerce(T.Select(ModelAt(entries, new[] { d }, f), k, Sort.Int), Sort.Int)));
            AssumeSide(facts);
            if (!pairs) HasType(current, pr.Type);
            return T.Coerce(current, SortOf(pr.Type));
        }

        /// <summary>The Version model of a collection type (or of the dictionary a Keys/Values view is of), if one is in use.</summary>
        private IMethodSymbol VersionModel(ITypeSymbol collection)
        {
            if (IsDictionaryView(collection)) collection = collection.ContainingType;
            var d = collection?.OriginalDefinition.ToDisplayString();
            if (d == null || !Versioned.Contains(d)) return null;
            return _engine.Models.FirstOrDefault(m => m.Name == "Version" && m.Parameters[0].Type.OriginalDefinition.ToDisplayString() == d);
        }

        private Term EnumeratorOf(Term e) => _z3.Apply("enum.collection", Sort.Int, new[] { T.Coerce(e, Sort.Int) });
        private Term EnumeratorVersion(Term e) => _z3.Apply("enum.version", Sort.Int, new[] { T.Coerce(e, Sort.Int) });

        /// <summary>GetEnumerator of a versioned collection, and MoveNext of its enumerator; null for other calls.</summary>
        private Term EnumeratorCall(IInvocationOperation inv, Frame f, SpecEnv spec)
        {
            if (!_codeMode || inv.Instance == null) return null;
            var m = inv.TargetMethod;
            if (m.Name == "GetEnumerator" && m.Parameters.Length == 0 && VersionModel(m.ContainingType) is IMethodSymbol version)
            {
                // the stub's call (its contract, its counting), then what the enumerator remembers
                var e = EvalInvocationCore(inv, f, spec, enumerators: false);
                var c = T.Coerce(Eval(inv.Instance, f, spec), Sort.Int);
                if (IsDictionaryView(m.ContainingType)) c = ViewOf(c); // (a view's enumerator checks its dictionary)
                AssumeSide(T.And(T.Eq(EnumeratorOf(e), c), T.Eq(EnumeratorVersion(e), T.Coerce(ModelAt(version, new[] { c }, f), Sort.Int))));
                return e;
            }
            if (m.Name == "MoveNext" && m.Parameters.Length == 0 && m.ContainingType?.ContainingType is INamedTypeSymbol outer &&
                m.ContainingType.Name == "Enumerator" && VersionModel(outer) is IMethodSymbol v)
            {
                var e = T.Coerce(Eval(inv.Instance, f, spec), Sort.Int);
                var c = EnumeratorOf(e);
                var what = outer.Name switch
                {
                    "Dictionary" => "dictionary", "KeyCollection" or "ValueCollection" => "dictionary", "HashSet" => "set", "Stack" => "stack", "Queue" => "queue", _ => "list",
                };
                Require(T.Eq(T.Coerce(ModelAt(v, new[] { c }, f), Sort.Int), EnumeratorVersion(e)), "CSV1001", inv.Syntax,
                    $"the {what} may have changed while it is enumerated: MoveNext would throw InvalidOperationException (collection was modified)");
                return null; // (then the call itself, as before)
            }
            return null;
        }
    }
}
