using System.Collections.Generic;
using System.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Lists seen through their interfaces (<c>IReadOnlyList&lt;T&gt;</c>, <c>IList&lt;T&gt;</c>,
    /// <c>IReadOnlyCollection&lt;T&gt;</c>, <c>ICollection&lt;T&gt;</c>), by what the object is: a <c>List&lt;T&gt;</c>
    /// (its models, so its facts cross the interface and changes through the list are seen), an array (its length and
    /// cells), or else a library collection the verifier does not model (a function of the heap and the model state,
    /// which changes whenever they might). If a class of the program implements one of these interfaces, that last case
    /// is an unknown value at each read: the program's own list could change in ways no model follows.
    ///
    /// Reads: <c>Count</c>, the indexer, <c>Contains</c>, <c>IndexOf</c>. Writes (the indexer, <c>Add</c>, <c>Insert</c>,
    /// <c>RemoveAt</c>, <c>Remove</c>, <c>Clear</c>) change, by what the object is, a list's models as its contract says,
    /// an array's cells (an array is fixed-size: the others throw NotSupportedException), or anything (a library call
    /// without a contract). A foreach over an IReadOnlyList or IList whose loop changes no state runs over the indexer,
    /// like a foreach over an array.
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

        private static bool IsIndexedListInterface(ITypeSymbol t) => IsListInterface(t) && (t.Name == "IReadOnlyList" || t.Name == "IList");

        /// <summary>The model state a wrapper's contents could depend on: the heap and every model's map.</summary>
        private Term[] StateOf(Frame f) => new[] { f.Heap }.Concat(_engine.Models.Select(m => FieldMap(f, m))).ToArray();

        private bool ListModels => ListModel("Items") != null && ListModel("Size") != null;

        // ---- reads --------------------------------------------------------------------------------------------

        private Term ListSizeOf(Term x, Frame f)
        {
            Term other;
            if (ProgramImplementsListInterfaces()) other = _z3.Fresh("count", Sort.Int);
            else other = _z3.Apply("ilist.count", Sort.Int, new[] { x }.Concat(StateOf(f)).ToArray());
            AssumeSide(T.Le(T.Int(0), other));
            var listSize = ListModels ? ModelAt(ListModel("Size"), new[] { x }, f) : null;
            return T.Ite(IsArrayObject(x), Len(x), listSize != null ? T.Ite(IsListObject(x), listSize, other) : other);
        }

        /// <summary>Element i, as an SMT term over a variable or a term (for quantifiers too), of type <paramref name="element"/>.</summary>
        private Term ListItemOf(Term x, Term i, ITypeSymbol element, Frame f, bool fresh = true)
        {
            var arrayCell = T.Coerce(T.Select(T.Select(f.Heap, x, Sort.Row), i, Sort.Int), SortOf(element));
            var listItem = ListModels ? T.Coerce(T.Select(T.Select(FieldMap(f, ListModel("Items")), x, Sort.Row), i, Sort.Int), SortOf(element)) : null;
            Term other = ProgramImplementsListInterfaces() && fresh
                ? Unknown(element, "item")
                : T.Coerce(_z3.Apply("ilist.item", Sort.Int, new[] { x, i }.Concat(StateOf(f)).ToArray()), SortOf(element));
            return T.Ite(IsArrayObject(x), arrayCell, listItem != null ? T.Ite(IsListObject(x), listItem, other) : other);
        }

        /// <summary>The objects whose reads are known exactly (a List with its models, an array).</summary>
        private Term KnownList(Term x) => ListModels ? T.Or(IsListObject(x), IsArrayObject(x)) : IsArrayObject(x);

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
            return InRangeOf(ListItemOf(x, i, element, f), element);
        }

        // ---- calls --------------------------------------------------------------------------------------------

        /// <summary>The members of IList / ICollection modeled here, called through the interface; null for others.</summary>
        private Term InterfaceListCall(IInvocationOperation inv, Frame f, SpecEnv spec)
        {
            var m = inv.TargetMethod;
            if (inv.Instance == null || !IsListInterface(m.ContainingType) || !_codeMode && m.Name != "Contains" && m.Name != "IndexOf") return null;
            var element = ((INamedTypeSymbol)m.ContainingType).TypeArguments[0];
            Term Arg(int ordinal) => Eval(inv.Arguments.First(a => a.Parameter.Ordinal == ordinal).Value, f, spec);
            switch (m.Name)
            {
                case "Contains" when m.Parameters.Length == 1:
                case "IndexOf" when m.Parameters.Length == 1 && IsIndexedListInterface(m.ContainingType):
                {
                    var x = Receiver(inv, f, spec);
                    var v = T.Coerce(Arg(0), SortOf(element));
                    var size = ListSizeOf(x, f);
                    var r = _z3.Fresh(m.Name, m.Name == "Contains" ? Sort.Bool : Sort.Int);
                    // exact for a List and an array, by EqualityComparer<T>.Default's equality (Spec.Equal)
                    var y = new Term("i", Sort.Int);
                    string Eq(Term a) => KnownEquality(element) ? T.Eq(a, v).S
                        : _z3.Apply("equals:" + Resolve(element).ToDisplayString(), Sort.Bool, new[] { T.Coerce(a, Sort.Int), T.Coerce(v, Sort.Int), _z3.Fresh("equals", Sort.Int) }).S;
                    var item = ListItemOf(x, y, element, f, fresh: false);
                    Term facts;
                    if (m.Name == "Contains")
                        facts = new Term($"(= {r} (exists ((i Int)) (and (<= 0 i) (< i {size}) {Eq(item)})))", Sort.Bool);
                    else
                    {
                        var at = ListItemOf(x, r, element, f, fresh: false);
                        facts = T.And(T.Le(T.Int(-1), r), T.Lt(r, size), T.Or(T.Lt(r, T.Int(0)), new Term(Eq(at), Sort.Bool)),
                            new Term($"(forall ((i Int)) (=> (and (<= 0 i) (< i (ite (< {r} 0) {size} {r}))) (not {Eq(item)})))", Sort.Bool));
                    }
                    // (a library collection is trusted to search as its indexer reads, as for Count; the program's own lists are not)
                    AssumeSide(ProgramImplementsListInterfaces() ? T.Implies(KnownList(x), facts) : facts);
                    return r;
                }
                case "Add" when m.Parameters.Length == 1:
                case "Insert" when m.Parameters.Length == 2:
                case "RemoveAt" when m.Parameters.Length == 1:
                case "Clear" when m.Parameters.Length == 0:
                case "Remove" when m.Parameters.Length == 1:
                    return InterfaceListWrite(inv, m.Name, element, f, spec);
            }
            return null;
        }

        private Term Receiver(IInvocationOperation inv, Frame f, SpecEnv spec)
        {
            var x = T.Coerce(Eval(inv.Instance, f, spec), Sort.Int);
            Deref(inv.Instance, x, inv.Syntax);
            ListKind(x, Unconverted(inv.Instance).Type);
            return x;
        }

        /// <summary>
        /// A write through a list interface: as a List's contract says for a List, a fixed-size array's (its cells, or
        /// NotSupportedException) for an array, and anything for any other collection (a library call without a
        /// contract). The state after is each case's, by what the object is.
        /// </summary>
        private Term InterfaceListWrite(IInvocationOperation inv, string name, ITypeSymbol element, Frame f, SpecEnv spec)
        {
            var x = Receiver(inv, f, spec);
            var args = inv.Arguments.OrderBy(a => a.Parameter.Ordinal).Select(a => Eval(a.Value, f, spec)).ToList();
            var isList = ListModels ? IsListObject(x) : T.False;
            var isArray = IsArrayObject(x);
            var size = ListSizeOf(x, f);
            // the index, where there is one, as the list's (an ArgumentOutOfRangeException otherwise)
            if (name == "Insert") Require(T.And(T.Le(T.Int(0), T.Coerce(args[0], Sort.Int)), T.Le(T.Coerce(args[0], Sort.Int), size)), "CSV1001", inv.Syntax, $"'{inv.Syntax}': the index might be out of range");
            if (name == "RemoveAt") Require(T.And(T.Le(T.Int(0), T.Coerce(args[0], Sort.Int)), T.Lt(T.Coerce(args[0], Sort.Int), size)), "CSV1001", inv.Syntax, $"'{inv.Syntax}': the index might be out of range");
            // an array is fixed-size: everything but the indexer throws
            if (_current != null) MayRaise(isArray, _current, KnownType("System.NotSupportedException"));
            _z3.Assume(T.Not(isArray));

            Term result = T.True;
            Term listItems = null, listSize = null;
            if (ListModels)
            {
                var itemsMap = FieldMap(f, ListModel("Items"));
                var sizeMap = FieldMap(f, ListModel("Size"));
                var items = T.Select(itemsMap, x, Sort.Row);
                var n = T.Coerce(T.Select(sizeMap, x, Sort.Int), Sort.Int);
                var v = name == "Insert" ? T.Coerce(args[1], Sort.Int) : args.Count > 0 ? T.Coerce(args[0], Sort.Int) : null;
                Term newItems = items, newSize = n;
                switch (name)
                {
                    case "Add": newItems = T.Store(items, n, v); newSize = T.Add(n, T.Int(1)); break;
                    case "Clear": newSize = T.Int(0); break;
                    case "RemoveAt":
                        newItems = new Term($"(cv_concat {items} {v} (cv_drop {items} (+ {v} 1)))", Sort.Row); newSize = T.Sub(n, T.Int(1)); break;
                    case "Insert":
                    {
                        var idx = T.Coerce(args[0], Sort.Int);
                        newItems = new Term($"(cv_concat {items} {idx} (cv_concat (store {T.ZeroRow()} 0 {v}) 1 (cv_drop {items} {idx})))", Sort.Row);
                        newSize = T.Add(n, T.Int(1)); break;
                    }
                    case "Remove":
                    {
                        // the first equal element goes, as List<T>.Remove does
                        var idx = _z3.Fresh("removed", Sort.Int);
                        var y = new Term("i", Sort.Int);
                        string Eq(Term a) => KnownEquality(element) ? T.Eq(a, v).S
                            : _z3.Apply("equals:" + Resolve(element).ToDisplayString(), Sort.Bool, new[] { a, v, _z3.Fresh("equals", Sort.Int) }).S;
                        AssumeSide(T.Implies(isList, T.And(T.Le(T.Int(-1), idx), T.Lt(idx, n), T.Or(T.Lt(idx, T.Int(0)), new Term(Eq(T.Select(items, idx, Sort.Int)), Sort.Bool)),
                            new Term($"(forall ((i Int)) (=> (and (<= 0 i) (< i (ite (< {idx} 0) {n} {idx}))) (not {Eq(T.Select(items, y, Sort.Int))})))", Sort.Bool))));
                        newItems = T.Ite(T.Lt(idx, T.Int(0)), items, new Term($"(cv_concat {items} {idx} (cv_drop {items} (+ {idx} 1)))", Sort.Row));
                        newSize = T.Ite(T.Lt(idx, T.Int(0)), n, T.Sub(n, T.Int(1)));
                        result = _z3.Fresh("removed", Sort.Bool);
                        AssumeSide(T.Implies(isList, T.Eq(result, T.Ge(idx, T.Int(0)))));
                        break;
                    }
                }
                listItems = T.Store(itemsMap, x, newItems);
                listSize = T.Store(sizeMap, x, newSize);
            }
            if (name == "Remove" && !ListModels) result = _z3.Fresh("removed", Sort.Bool);
            // anything else: what a library call may do, unless it is a List
            var before = f.Clone();
            var heapBefore = f.Heap;
            f.Heap = _z3.Fresh("heap", Sort.Heap);
            _z3.Assume(T.Implies(isList, T.Eq(f.Heap, heapBefore)));
            HavocAllFieldsUnless(f, isList, before);
            if (ListModels)
            {
                f.Fields[ListModel("Items")] = T.Ite(isList, listItems, _z3.Fresh("Items$map", Sort.Heap));
                f.Fields[ListModel("Size")] = T.Ite(isList, listSize, _z3.Fresh("Size$map", Sort.Row));
            }
            AllocAfterCall(f);
            if (RunsCode(inv.TargetMethod)) HavocClosureLocals(f);
            return name == "Remove" ? result : T.True;
        }

        /// <summary>The indexer's setter through IList: an array's cell, a List's item, or anything.</summary>
        private bool InterfaceListSet(IPropertyReferenceOperation pr, Term v, Frame f, SpecEnv spec)
        {
            if (!_codeMode || pr.Instance == null || !pr.Property.IsIndexer || !IsIndexedListInterface(pr.Property.ContainingType) || pr.Arguments.Length != 1) return false;
            var element = ((INamedTypeSymbol)pr.Property.ContainingType).TypeArguments[0];
            var x = T.Coerce(Eval(pr.Instance, f, spec), Sort.Int);
            Deref(pr.Instance, x, pr.Syntax);
            ListKind(x, Unconverted(pr.Instance).Type);
            var i = T.Coerce(Eval(pr.Arguments[0].Value, f, spec), Sort.Int);
            var size = ListSizeOf(x, f);
            Require(T.And(T.Le(T.Int(0), i), T.Lt(i, size)), "CSV1003", pr.Syntax, $"index in '{pr.Syntax}' might be out of range");
            var isList = ListModels ? IsListObject(x) : T.False;
            var isArray = IsArrayObject(x);
            var cell = T.Coerce(v, Sort.Int);
            var before = f.Clone();
            var heapBefore = f.Heap;
            var arrayHeap = T.Store(heapBefore, x, T.Store(T.Select(heapBefore, x, Sort.Row), i, cell));
            f.Heap = _z3.Fresh("heap", Sort.Heap);
            _z3.Assume(T.Implies(isArray, T.Eq(f.Heap, arrayHeap)));
            _z3.Assume(T.Implies(isList, T.Eq(f.Heap, heapBefore)));
            HavocAllFieldsUnless(f, T.Or(isList, isArray), before);
            if (ListModels)
            {
                var itemsMap = FieldMap(before, ListModel("Items"));
                var listItems = T.Store(itemsMap, x, T.Store(T.Select(itemsMap, x, Sort.Row), i, cell));
                f.Fields[ListModel("Items")] = T.Ite(isList, listItems, T.Ite(isArray, itemsMap, _z3.Fresh("Items$map", Sort.Heap)));
                f.Fields[ListModel("Size")] = T.Ite(T.Or(isList, isArray), FieldMap(before, ListModel("Size")), _z3.Fresh("Size$map", Sort.Row));
            }
            AllocAfterCall(f);
            return true;
        }

        // ---- foreach ------------------------------------------------------------------------------------------

        /// <summary>
        /// A foreach over an IReadOnlyList or IList (when the program implements neither) whose elements become the
        /// iteration variable unchanged: the element type; else null.
        /// </summary>
        private ITypeSymbol InterfaceForEachElement(Microsoft.CodeAnalysis.CSharp.Syntax.CommonForEachStatementSyntax fe, IForEachLoopOperation fo)
        {
            var t = Unconverted(fo.Collection).Type;
            if (!IsIndexedListInterface(t) || ProgramImplementsListInterfaces()) return null;
            var c = _model.GetForEachStatementInfo(fe).ElementConversion;
            var target = fo.Locals.FirstOrDefault()?.Type;
            var element = ((INamedTypeSymbol)t).TypeArguments[0];
            return c.IsIdentity || c.IsImplicit && c.IsReference ||
                   c.IsImplicit && c.IsNumeric && IsIntegral(element) && target != null && IsIntegral(target) ? element : null;
        }
    }
}
