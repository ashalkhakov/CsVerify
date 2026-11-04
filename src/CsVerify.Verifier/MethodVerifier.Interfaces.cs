using System.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Lists seen through their interfaces: <c>Count</c> of <c>IReadOnlyCollection&lt;T&gt;</c> and
    /// <c>ICollection&lt;T&gt;</c>, and the indexer of <c>IReadOnlyList&lt;T&gt;</c> and <c>IList&lt;T&gt;</c>. They read
    /// what the object is: a <c>List&lt;T&gt;</c>'s models (so its facts cross the interface), an array's length and
    /// cells, or else (a library wrapper, a collection the verifier does not model) a function of the heap and the model
    /// state, which changes whenever they might. If a class of the program implements one of these interfaces, that last
    /// case is an unknown value at each read: the program's own list could change in ways no model follows.
    /// </summary>
    internal sealed partial class MethodVerifier
    {
        private static string Display(ITypeSymbol t) => t?.OriginalDefinition.ToDisplayString();

        private static bool IsListType(ITypeSymbol t) => Display(t) == "System.Collections.Generic.List<T>";

        private Term IsListObject(Term o) => _z3.Apply("kind:list", Sort.Bool, new[] { T.Coerce(o, Sort.Int) });
        private Term IsArrayObject(Term o) => _z3.Apply("kind:array", Sort.Bool, new[] { T.Coerce(o, Sort.Int) });

        /// <summary>What a static type says of an object's kind: a List, an array (and so not the other).</summary>
        private void ListKind(Term o, ITypeSymbol type)
        {
            if (o.Sort != Sort.Int) return;
            if (IsListType(type)) AssumeSide(T.Implies(NotNull(o), T.And(IsListObject(o), T.Not(IsArrayObject(o)))));
            else if (type is IArrayTypeSymbol at && at.Rank == 1) AssumeSide(T.Implies(NotNull(o), T.And(IsArrayObject(o), T.Not(IsListObject(o)))));
        }

        private bool ProgramImplementsListInterfaces() =>
            _engine.SourceTypes.Any(s => s.AllInterfaces.Any(i => IsListInterface(i.OriginalDefinition)));

        private static bool IsListInterface(ITypeSymbol t) =>
            t is INamedTypeSymbol n && n.TypeArguments.Length == 1 && n.ContainingNamespace?.ToDisplayString() == "System.Collections.Generic" &&
            (n.Name == "IReadOnlyCollection" || n.Name == "ICollection" || n.Name == "IReadOnlyList" || n.Name == "IList");

        /// <summary>The model state a wrapper's contents could depend on: the heap and every model's map.</summary>
        private Term[] StateOf(Frame f) => new[] { f.Heap }.Concat(_engine.Models.Select(m => FieldMap(f, m))).ToArray();

        /// <summary>Count, or the indexer, of a list interface; null for other members.</summary>
        private Term InterfaceListRead(IPropertyReferenceOperation pr, Frame f, SpecEnv spec)
        {
            var prop = pr.Property;
            if (pr.Instance == null || !IsListInterface(prop.ContainingType)) return null;
            bool count = prop.Name == "Count" && !prop.IsIndexer;
            bool item = prop.IsIndexer && pr.Arguments.Length == 1;
            if (!count && !item) return null;
            var element = ((INamedTypeSymbol)prop.ContainingType).TypeArguments[0];
            var x = T.Coerce(Eval(pr.Instance, f, spec), Sort.Int);
            Deref(pr.Instance, x, pr.Syntax);
            ListKind(x, Unconverted(pr.Instance).Type);
            var size = ListSizeOf(x, f);
            if (count) return size;
            var i = T.Coerce(Eval(pr.Arguments[0].Value, f, spec), Sort.Int);
            Require(T.And(T.Le(T.Int(0), i), T.Lt(i, size)), "CSV1003", pr.Syntax, $"index in '{pr.Syntax}' might be out of range");
            var arrayCell = InRangeOf(T.Coerce(T.Select(T.Select(f.Heap, x, Sort.Row), i, Sort.Int), SortOf(element)), element);
            var items = ListModel("Items");
            var listItem = items != null ? T.Coerce(T.Select(ModelAt(items, new[] { x }, f), i, Sort.Int), SortOf(element)) : null;
            var other = ProgramImplementsListInterfaces()
                ? Unknown(element, "item")
                : InRangeOf(T.Coerce(_z3.Apply("ilist.item", Sort.Int, new[] { x, i }.Concat(StateOf(f)).ToArray()), SortOf(element)), element);
            return T.Ite(IsArrayObject(x), arrayCell, listItem != null ? T.Ite(IsListObject(x), listItem, other) : other);
        }

        private Term ListSizeOf(Term x, Frame f)
        {
            var sizeModel = ListModel("Size");
            Term other;
            if (ProgramImplementsListInterfaces()) { other = _z3.Fresh("count", Sort.Int); AssumeSide(T.Le(T.Int(0), other)); }
            else
            {
                other = _z3.Apply("ilist.count", Sort.Int, new[] { x }.Concat(StateOf(f)).ToArray());
                AssumeSide(T.Le(T.Int(0), other));
            }
            var listSize = sizeModel != null ? ModelAt(sizeModel, new[] { x }, f) : null;
            return T.Ite(IsArrayObject(x), Len(x), listSize != null ? T.Ite(IsListObject(x), listSize, other) : other);
        }
    }
}
