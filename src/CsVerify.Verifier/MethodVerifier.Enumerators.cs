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

        /// <summary>The Version model of a collection type, if it has one in use.</summary>
        private IMethodSymbol VersionModel(ITypeSymbol collection)
        {
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
                AssumeSide(T.And(T.Eq(EnumeratorOf(e), c), T.Eq(EnumeratorVersion(e), T.Coerce(ModelAt(version, new[] { c }, f), Sort.Int))));
                return e;
            }
            if (m.Name == "MoveNext" && m.Parameters.Length == 0 && m.ContainingType?.ContainingType is INamedTypeSymbol outer &&
                m.ContainingType.Name == "Enumerator" && VersionModel(outer) is IMethodSymbol v)
            {
                var e = T.Coerce(Eval(inv.Instance, f, spec), Sort.Int);
                var c = EnumeratorOf(e);
                var what = outer.Name switch { "Dictionary" => "dictionary", "HashSet" => "set", "Stack" => "stack", "Queue" => "queue", _ => "list" };
                Require(T.Eq(T.Coerce(ModelAt(v, new[] { c }, f), Sort.Int), EnumeratorVersion(e)), "CSV1001", inv.Syntax,
                    $"the {what} may have changed while it is enumerated: MoveNext would throw InvalidOperationException (collection was modified)");
                return null; // (then the call itself, as before)
            }
            return null;
        }
    }
}
