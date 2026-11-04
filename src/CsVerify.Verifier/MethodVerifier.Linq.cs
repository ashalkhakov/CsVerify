using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// The sequences LINQ's definitions (MethodVerifier.Queries) are compiled into, and their encodings: a source the
    /// verifier indexes (a List, an array, an IReadOnlyList or IList: MethodVerifier.Interfaces), a range, a filter (a
    /// running count of the matches, one step at a time), sequences one after another (running offsets), a stable
    /// sort (a permutation in key order), and folds (running values). Lambdas passed to LINQ are inlined where they
    /// are pure (an expression with no assignments, calling only [Pure] members); their own obligations are checked
    /// where each lambda is verified, as a unit of its own. ToList and ToArray copy a sequence into a new object.
    /// </summary>
    internal sealed partial class MethodVerifier
    {
        private static bool IsEnumerableMethod(IMethodSymbol m) => m.ContainingType?.ToDisplayString() == "System.Linq.Enumerable";

        /// <summary>The lambda of a predicate argument, if it is one this can inline (a pure expression of its parameter).</summary>
        private IOperation PureLambdaBody(IOperation arg, out IParameterSymbol parameter) => PureLambdaBody(arg, out parameter, out var index) is IOperation b && index == null ? b : null;

        /// <summary>As above, for a lambda that may also take the element's index (Select((x, i) => ...)).</summary>
        private IOperation PureLambdaBody(IOperation arg, out IParameterSymbol parameter, out IParameterSymbol index, bool pair = false)
        {
            parameter = null;
            index = null;
            var target = (arg as IDelegateCreationOperation)?.Target as IAnonymousFunctionOperation;
            if (target == null || target.Symbol.Parameters.Length < 1 || target.Symbol.Parameters.Length > 2 ||
                target.Symbol.Parameters.Length == 2 && !pair && target.Symbol.Parameters[1].Type.SpecialType != SpecialType.System_Int32 || target.Body.Operations.Length != 1 ||
                !(target.Body.Operations[0] is IReturnOperation ret) || ret.ReturnedValue == null) return null;
            foreach (var op in ret.ReturnedValue.DescendantsAndSelf())
            {
                switch (op)
                {
                    case IAssignmentOperation _:
                    case IIncrementOrDecrementOperation _:
                    case IObjectCreationOperation _:
                    case IArrayCreationOperation _:
                    case IAnonymousFunctionOperation _:
                    case IAwaitOperation _:
                        return null;
                    case IInvocationOperation inv when !(SpecSymbols.IsPure(inv.TargetMethod) || _engine.Stubs.IsPureMember(inv.TargetMethod) ||
                                                         inv.TargetMethod.ContainingType?.ToDisplayString() == "System.Math" ||
                                                         IsNullableValue(inv.TargetMethod.ContainingType) || inv.TargetMethod.Name == "Equals" &&
                                                         inv.TargetMethod.ContainingType?.SpecialType == SpecialType.System_String):
                        return null;
                    case IPropertyReferenceOperation pr when !(FieldEffects.IsHeapField(pr.Property) || IsStructMember(pr.Property) ||
                                                               pr.Instance != null && IsSequence(pr.Instance.Type) ||
                                                               pr.Property.Name == "Key" && pr.Property.ContainingType?.Name == "IGrouping" ||
                                                               IsNullableValue(pr.Property.ContainingType) || IsListInterface(pr.Property.ContainingType) ||
                                                               _engine.HasStub(pr.Property.GetMethod) && _engine.Stubs.IsPureMember(pr.Property.GetMethod)):
                        return null;
                }
            }
            parameter = target.Symbol.Parameters[0];
            if (target.Symbol.Parameters.Length == 2) index = target.Symbol.Parameters[1];
            return ret.ReturnedValue;
        }

        /// <summary>
        /// A function of 0..n defined one step at a time: acc(0) = init, acc(j + 1) = step(acc(j), j), under the
        /// sequence's condition. Each step is a quantified axiom triggered by acc(j + 1) (unfolding back from acc(n)) or
        /// by acc(j) (forward from acc(0), for a length the solver knows only as a value, not as a successor term).
        /// </summary>
        private System.Func<Term, Term> Recur(string hint, Term n, Term init, System.Func<Term, Term, Term> step, Term known)
        {
            BoundCompileCheck();
            var name = hint + "#" + _materialized++;
            Term Acc(Term j) => _z3.Apply(name, Sort.Int, new[] { j });
            AssumeSide(T.Implies(known, T.And(T.Eq(Acc(T.Int(0)), init),
                OverIndices("forall", T.Int(0), n, j => T.Eq(Acc(T.Add(j, T.Int(1))), step(Acc(j), j)), pattern: j => Acc(T.Add(j, T.Int(1))), pattern2: Acc))));
            return Acc;
        }

        /// <summary>
        /// The elements of a sequence that pass a test, in order and all of them: a prefix count c (m = c(n) of them),
        /// the match at j being element c(j), the elements matches at increasing indices. Also the map to the source.
        /// </summary>
        private Sequence Filter(Sequence src, System.Func<Term, Term> test, ITypeSymbol elementType, out System.Func<Term, Term> sourceIndex)
        {
            int id = _materialized++;
            var m = _z3.Fresh("matches", Sort.Int);
            Term Idx(Term i) => _z3.Apply("filter.idx#" + id, Sort.Int, new[] { i });
            var c = Recur("filter.count", src.Length, T.Int(0), (acc, j) => T.Add(acc, T.Ite(test(j), T.Int(1), T.Int(0))), src.Known);
            var facts = T.And(
                T.Eq(m, c(src.Length)), T.Le(T.Int(0), m), T.Le(m, src.Length), Monotone(c, src.Length),
                OverIndices("forall", T.Int(0), src.Length, j => T.And(T.Le(T.Int(0), c(j)), T.Le(c(j), j), T.Implies(test(j), T.And(T.Lt(c(j), m), T.Eq(Idx(c(j)), j))))),
                OverIndices("forall", T.Int(0), m, i => T.And(T.Le(T.Int(0), Idx(i)), T.Lt(Idx(i), src.Length), test(Idx(i)))),
                OverIndices("forall", T.Int(0), T.Sub(m, T.Int(1)), i => T.Lt(Idx(i), Idx(T.Add(i, T.Int(1))))));
            AssumeSide(T.Implies(src.Known, facts));
            sourceIndex = Idx;
            return new Sequence { Length = m, Element = i => src.Element(Idx(i)), ElementType = elementType, Known = src.Known };
        }

        /// <summary>
        /// A running count or offset never decreases: acc(j) &lt;= acc(k) for 0 &lt;= j &lt;= k &lt;= n. (It follows from its
        /// steps by induction, which the solver does not do: stated, so acc(n) &gt;= acc(1) needs no unfolding.)
        /// </summary>
        private Term Monotone(System.Func<Term, Term> acc, Term n)
        {
            var jn = _z3.FreshName("k"); var kn = _z3.FreshName("k");
            var j = new Term(jn, Sort.Int); var k = new Term(kn, Sort.Int);
            var guard = T.And(T.Le(T.Int(0), j), T.Le(j, k), T.Le(k, n));
            return new Term($"(forall (({jn} Int) ({kn} Int)) (! {T.Implies(guard, T.Le(acc(j), acc(k)))} :pattern ({acc(j)} {acc(k)})))", Sort.Bool);
        }

        /// <summary>
        /// A condition on the elements of [lo, hi) as a quantifier over their index: the body is evaluated for a bound
        /// variable, without obligations (they are checked where the lambda is), its side facts quantified the same way.
        /// </summary>
        private Term OverIndices(string quantifier, Term lo, Term hi, System.Func<Term, Term> body, System.Func<Term, Term> pattern = null,
                                 System.Func<Term, Term> pattern2 = null)
        {
            var name = _z3.FreshName("k");
            var bound = new Term(name, Sort.Int);
            var range = T.And(T.Le(lo, bound), T.Lt(bound, hi));
            _quantDepth++;
            int factLevels = _quantFacts.Count;
            _quantFacts.Push(new List<Term>());
            bool wasCode = _codeMode;
            _codeMode = false;
            _foreignSpec++;
            try
            {
                var b = AsBool(body(bound));
                var collected = _quantFacts.Pop();
                foreach (var plain in collected.Where(x => !x.S.Contains(name))) AssumeSide(plain);
                var facts = T.And(collected.Where(x => x.S.Contains(name)).ToArray());
                if (facts != T.True) AssumeSide(T.Quant("forall", name, T.Implies(range, facts)));
                if (pattern != null)
                    return new Term($"(forall (({name} Int)) (! {T.Implies(range, b)} :pattern ({pattern(bound)}){(pattern2 != null ? $" :pattern ({pattern2(bound)})" : "")}))", Sort.Bool);
                return quantifier == "forall" ? T.Quant("forall", name, T.Implies(range, b)) : T.Quant("exists", name, T.And(range, b));
            }
            finally
            {
                while (_quantFacts.Count > factLevels) _quantFacts.Pop();
                _foreignSpec--;
                _codeMode = wasCode;
                _quantDepth--;
            }
        }

        /// <summary>
        /// A sequence's element at Pointwise's bound "y", as an Int; the side facts reading it gives (an element's range,
        /// say) are assumed for every y in 0..n, not left naming y outside its quantifier.
        /// </summary>
        private Term ElementAtY(System.Func<Term, Term> element, Term n)
        {
            var y = new Term("y", Sort.Int);
            _quantFacts.Push(new List<Term>());
            Term e;
            try { e = T.Coerce(element(y), Sort.Int); }
            finally
            {
                var facts = _quantFacts.Pop();
                if (facts.Count > 0) AssumeSide(T.Quant("forall", "y", T.Implies(T.And(T.Le(T.Int(0), y), T.Lt(y, n)), T.And(facts.ToArray()))));
            }
            return e;
        }

        /// <summary>Is this source one whose elements the verifier reads (a List, an array, a list interface)?</summary>
        private static bool Indexable(ITypeSymbol t) =>
            IsListType(t) || t is IArrayTypeSymbol a && a.Rank == 1 || IsIndexedListInterface(t);

        private static ITypeSymbol ElementOf(ITypeSymbol t) =>
            t is IArrayTypeSymbol a ? a.ElementType : ((INamedTypeSymbol)t).TypeArguments[0];

        /// <summary>
        /// A sequence as LINQ reads it, now: its length, its element at an index (a term, for quantifiers too), and the
        /// condition under which that is what it is (a List or an array, where the program has lists of its own).
        /// </summary>
        private sealed class Sequence
        {
            public Term Length;
            public System.Func<Term, Term> Element;
            public ITypeSymbol ElementType;
            public Term Known = T.True;
        }

        private int _materialized;

        /// <summary>A pure lambda's body for one element, as a value of its type (in spec mode, without obligations).</summary>
        private Term ApplyValue(IOperation body, IParameterSymbol parameter, Term element, Frame f, IParameterSymbol index = null, Term at = null)
        {
            var inner = f.Clone();
            inner.Vars[parameter] = element;
            if (index != null) inner.Vars[index] = at;
            bool wasCode = _codeMode;
            _codeMode = false;
            _foreignSpec++;
            try { return InRangeOf(T.Coerce(Eval(body, inner, new SpecEnv { Old = _entry }), SortOf(body.Type)), body.Type); }
            finally { _foreignSpec--; _codeMode = wasCode; }
        }

        private Sequence ListSequence(Term x, ITypeSymbol type, Frame f)
        {
            var element = ElementOf(type);
            ListKind(x, type);
            // an array, or a List with its models, statically: read directly, not through the dispatch on the kind
            if (type is IArrayTypeSymbol)
                return new Sequence
                {
                    Length = Len(x), ElementType = element,
                    Element = i => InRangeOf(T.Coerce(T.Select(T.Select(f.Heap, x, Sort.Row), i, Sort.Int), SortOf(element)), element),
                };
            if (IsListType(type) && ListModels)
                return new Sequence
                {
                    Length = T.Coerce(ModelAt(ListModel("Size"), new[] { x }, f), Sort.Int), ElementType = element,
                    Element = i => InRangeOf(T.Coerce(T.Select(T.Select(FieldMap(f, ListModel("Items")), x, Sort.Row), i, Sort.Int), SortOf(element)), element),
                };
            return new Sequence
            {
                Length = ListSizeOf(x, f),
                Element = i => InRangeOf(ListItemOf(x, i, element, f, fresh: false), element),
                ElementType = element,
                Known = ProgramImplementsListInterfaces() ? KnownList(x) : T.True,
            };
        }

        /// <summary>
        /// Sequences one after another, one for each element of src: offsets o(j) (o(0) = 0, o(j + 1) = o(j) + the
        /// length of j's), element i at outer index outer(i) and index i - o(outer(i)) within it.
        /// </summary>
        private Sequence Flatten(Sequence src, System.Func<Term, Sequence> inner, ITypeSymbol elementType, Term known,
                                 out System.Func<Term, Term> outerIndex, out System.Func<Term, Term> withinIndex)
        {
            BoundCompileCheck();
            var o = Recur("flatten.offset", src.Length, T.Int(0), (acc, j) => T.Add(acc, inner(j).Length), src.Known);
            var n = o(src.Length);
            int id = _materialized++;
            Term Outer(Term i) => _z3.Apply("flatten.outer#" + id, Sort.Int, new[] { i });
            AssumeSide(T.Implies(src.Known, OverIndices("forall", T.Int(0), n, i =>
                T.And(T.Le(T.Int(0), Outer(i)), T.Lt(Outer(i), src.Length), T.Le(o(Outer(i)), i), T.Lt(i, o(T.Add(Outer(i), T.Int(1))))))));
            // (and the other way: the elements of j's sequence are at o(j) up to o(j + 1))
            var jn = _z3.FreshName("k"); var inn = _z3.FreshName("k");
            var jv = new Term(jn, Sort.Int); var iv = new Term(inn, Sort.Int);
            var guard = T.And(T.Le(T.Int(0), jv), T.Lt(jv, src.Length), T.Le(o(jv), iv), T.Lt(iv, o(T.Add(jv, T.Int(1)))));
            var inverse = new Term($"(forall (({jn} Int) ({inn} Int)) (! {T.Implies(guard, T.Eq(Outer(iv), jv))} :pattern ({Outer(iv)} {o(jv)})))", Sort.Bool);
            AssumeSide(T.Implies(src.Known, T.And(
                OverIndices("forall", T.Int(0), src.Length, j => T.Le(o(j), o(T.Add(j, T.Int(1))))), Monotone(o, src.Length), inverse)));
            outerIndex = Outer;
            withinIndex = i => T.Sub(i, o(Outer(i)));
            return new Sequence { Length = n, Element = i => inner(Outer(i)).Element(T.Sub(i, o(Outer(i)))), ElementType = elementType, Known = known };
        }

        /// <summary>
        /// A stable sort: element i is source element p(i), p a bijection (q its inverse), in the keys' order (the
        /// first key, then the next among equal ones), equal keys keeping the source's order. Keys are ordered if they
        /// are integers, chars or enums; from the first that is not, only the keys before it are.
        /// </summary>
        private Sequence SortSequence(Sequence src, List<(System.Func<Term, Term> key, ITypeSymbol type, bool down)> keys, ITypeSymbol elementType)
        {
            BoundCompileCheck();
                int id = _materialized++;
                Term Pi(Term i) => _z3.Apply("order.p#" + id, Sort.Int, new[] { i });
                Term Qi(Term j) => _z3.Apply("order.q#" + id, Sort.Int, new[] { j });
                var n = src.Length;
                
                bool Orderable(ITypeSymbol t) => t != null && (IsIntegral(t) || t.TypeKind == TypeKind.Enum || t.SpecialType == SpecialType.System_Char) && SortOf(t) == Sort.Int;
                int prefix = keys.TakeWhile(k => Orderable(k.type)).Count();
                Term KeyOf(int k, Term j) => T.Coerce(keys[k].key(src.Element(j)), Sort.Int);
                Term InOrder(Term a, Term b, int level)
                {
                    if (level == prefix) return prefix == keys.Count ? T.Lt(a, b) : T.True;
                    var x = KeyOf(level, a); var y = KeyOf(level, b);
                    return T.Or(keys[level].down ? T.Gt(x, y) : T.Lt(x, y), T.And(T.Eq(x, y), InOrder(a, b, level + 1)));
                }
                var facts = new List<Term>
                {
                    OverIndices("forall", T.Int(0), n, i => T.And(T.Le(T.Int(0), Pi(i)), T.Lt(Pi(i), n), T.Eq(Qi(Pi(i)), i))),
                    OverIndices("forall", T.Int(0), n, j => T.And(T.Le(T.Int(0), Qi(j)), T.Lt(Qi(j), n), T.Eq(Pi(Qi(j)), j))),
                };
                if (prefix > 0)
                    facts.Add(OverIndices("forall", T.Int(0), T.Sub(n, T.Int(1)), i => InOrder(Pi(i), Pi(T.Add(i, T.Int(1))), 0)));
                AssumeSide(T.Implies(src.Known, T.And(facts.ToArray())));
            return new Sequence { Length = n, Element = i => src.Element(Pi(i)), ElementType = elementType, Known = src.Known };
        }

        /// <summary>A LINQ source's sequence, read now (a List, an array or a list interface, or a query): null for others.</summary>
        private Sequence SequenceOf(IOperation sourceOp, Frame f, SpecEnv spec)
        {
            var type = Unconverted(sourceOp).Type;
            var x = T.Coerce(Eval(sourceOp, f, spec), Sort.Int);
            if (Indexable(type)) Deref(sourceOp, x, sourceOp.Syntax);
            return SequenceOfTerm(x, type, f);
        }

        /// <summary>ToArray and ToList of what the verifier reads: a new array or list of its elements.</summary>
        private Term Copying(IInvocationOperation inv, Frame f, SpecEnv spec)
        {
            var m = inv.TargetMethod;
            if (!(m.Name == "ToArray" || m.Name == "ToList" && ListModels) || m.Parameters.Length != 1) return null;
            var seq = SequenceOf(inv.Arguments.First(a => a.Parameter.Ordinal == 0).Value, f, spec);
            if (seq == null) return null;
            Assumed(m.OriginalDefinition.ToDisplayString());
            var n = seq.Length;
            Term Elem(Term i) => seq.Element(i);
            void Fact(Term t) => AssumeSide(T.Implies(seq.Known, t));
            if (m.Name == "ToArray")
            {
                var arr = Unknown(inv.Type, "toArray");
                AssumeSide(NotNull(arr));
                Fact(T.Eq(Len(arr), n));
                ListKind(arr, inv.Type);
                NewArrayIsDistinct(arr, f);
                var row = Pointwise("toArray", Sort.Row, ElementAtY(Elem, n).S);
                f.Heap = T.Store(f.Heap, arr, T.Ite(seq.Known, row, _z3.Fresh("toArray", Sort.Row)));
                return arr;
            }
            else
            {
                var list = Unknown(inv.Type, "toList");
                AssumeSide(NotNull(list));
                ListKind(list, inv.Type);
                if (f.Alloc != null)
                {
                    AssumeSide(T.Not(InSet(f.Alloc, list)));
                    f.Alloc = T.Store(f.Alloc, list, T.Int(1));
                }
                var row = Pointwise("toList", Sort.Row, ElementAtY(Elem, n).S);
                var size = _z3.Fresh("toList", Sort.Int);
                Fact(T.Eq(size, n));
                AssumeSide(T.Le(T.Int(0), size));
                f.Link = null; // (model maps changed outside a call's frame)
                f.Fields[ListModel("Items")] = T.Store(FieldMap(f, ListModel("Items")), list, T.Ite(seq.Known, row, _z3.Fresh("toList", Sort.Row)));
                f.Fields[ListModel("Size")] = T.Store(FieldMap(f, ListModel("Size")), list, size);
                return list;
            }
        }
    }
}
