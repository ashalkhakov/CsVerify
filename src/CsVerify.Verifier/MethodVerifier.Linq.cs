using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Eager LINQ over what the verifier can index (a List, an array, an IReadOnlyList or IList: MethodVerifier.Interfaces):
    /// Count, Any, All, Contains, First, FirstOrDefault, Last, LastOrDefault, ElementAt, ToList, ToArray, and List's Find,
    /// FindIndex, Exists and TrueForAll. A predicate that is a pure lambda (an expression, with no assignments, calling
    /// only [Pure] members) is inlined, as a condition on each element; its own obligations are checked where the lambda
    /// is verified as a unit. Methods that would throw (First of an empty sequence) are preconditions (CSV1001). With any
    /// other predicate, or source, a LINQ call is a library call as before.
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

        /// <summary>EqualityComparer&lt;T&gt;.Default's equality of two elements (Spec.Equal), with a relation for one read.</summary>
        private System.Func<Term, Term, Term> EqualityOf(ITypeSymbol t)
        {
            if (KnownEquality(t)) return (a, b) => T.Eq(T.Coerce(a, Sort.Int), T.Coerce(b, Sort.Int));
            var epoch = _z3.Fresh("equals", Sort.Int);
            var name = "equals:" + Resolve(t).ToDisplayString();
            return (a, b) => _z3.Apply(name, Sort.Bool, new[] { T.Coerce(a, Sort.Int), T.Coerce(b, Sort.Int), epoch });
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

        /// <summary>A pure lambda's body for one element (in spec mode, without obligations).</summary>
        private Term Apply(IOperation body, IParameterSymbol parameter, Term element, Frame f)
        {
            var inner = f.Clone();
            inner.Vars[parameter] = element;
            bool wasCode = _codeMode;
            _codeMode = false;
            _foreignSpec++;
            try { return AsBool(Eval(body, inner, new SpecEnv { Old = _entry })); }
            finally { _foreignSpec--; _codeMode = wasCode; }
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

        /// <summary>
        /// A lazy LINQ result (Select, Where, Take, Skip): what it is made of. Nothing is read until it is enumerated,
        /// and then the source is read as it is at that point, and the lambda runs then (on its captures as they are).
        /// </summary>
        private sealed class View
        {
            public string Kind;
            public View Inner;                // a view over a view
            public Term Source;               // or a List, array or list interface
            public ITypeSymbol SourceType;
            public IOperation Lambda;         // Select's selector, Where's predicate
            public IParameterSymbol Parameter;
            public Term Count;                // Take's and Skip's
            public ITypeSymbol ElementType;
            public IParameterSymbol Index;    // Select((x, i) => ...)'s index, Zip's second element
            public View Inner2;               // Zip's and Join's second source
            public Term Source2;
            public ITypeSymbol SourceType2;
            public IOperation Lambda2, Lambda3;              // Join's inner key and result selector
            public IParameterSymbol Parameter2, Parameter3, Parameter3b;
            public List<(IOperation key, IParameterSymbol parameter, bool down)> Keys; // OrderBy's, then ThenBy's
        }

        /// <summary>
        /// GroupBy's groups, read when the result is enumerated: a group is an element of the result, a term
        /// "(group#id g)", whose key is its first element's key and whose elements are the source's with that key.
        /// </summary>
        private sealed class Groups
        {
            public string Name;
            public Sequence Source;
            public System.Func<Term, Term> Key;        // of a source index
            public System.Func<Term, Term, Term> Same; // keys equal
            public System.Func<Term, Term> First;      // a group's first source index
            public ITypeSymbol KeyType, ElementType;
        }

        private readonly Dictionary<string, Groups> _groups = new Dictionary<string, Groups>(System.StringComparer.Ordinal);

        /// <summary>A group term's groups and its index in them, if it is one.</summary>
        private (Groups groups, Term g)? GroupOf(Term t)
        {
            foreach (var kv in _groups)
                if (t.S.StartsWith("(" + kv.Key + " ", System.StringComparison.Ordinal))
                    return (kv.Value, new Term(t.S.Substring(kv.Key.Length + 2, t.S.Length - kv.Key.Length - 3), Sort.Int));
            return null;
        }

        /// <summary>IGrouping.Key of a group this made: its first element's key.</summary>
        private Term GroupKey(IPropertyReferenceOperation pr, Frame f, SpecEnv spec)
        {
            if (pr.Instance == null || pr.Property.Name != "Key" || pr.Property.ContainingType?.Name != "IGrouping") return null;
            var x = T.Coerce(Eval(pr.Instance, f, spec), Sort.Int);
            if (!(GroupOf(x) is (Groups gs, Term g))) return null;
            return T.Coerce(gs.Key(gs.First(g)), SortOf(pr.Type));
        }

        private Sequence GroupSequence(Groups gs, Term g) =>
            Filter(gs.Source, j => gs.Same(gs.Key(j), gs.Key(gs.First(g))), gs.ElementType, out _);

        private readonly Dictionary<string, View> _views = new Dictionary<string, View>(System.StringComparer.Ordinal);
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

        /// <summary>A view read now: from its source as it is, with its lambda applied now.</summary>
        private Sequence Materialize(View v, Frame f)
        {
            var src = v.Inner != null ? Materialize(v.Inner, f) : ListSequence(v.Source, v.SourceType, f);
            var src2 = v.Inner2 != null ? Materialize(v.Inner2, f) : v.Source2 != null ? ListSequence(v.Source2, v.SourceType2, f) : null;
            switch (v.Kind)
            {
                case "Select":
                    return new Sequence { Length = src.Length, Element = i => ApplyValue(v.Lambda, v.Parameter, src.Element(i), f, v.Index, i), ElementType = v.ElementType, Known = src.Known };
                case "Distinct":
                {
                    // the first occurrence of each value, in order
                    var eq = EqualityOf(v.ElementType);
                    return Filter(src, j => OverIndices("forall", T.Int(0), j, i => T.Not(eq(src.Element(i), src.Element(j)))), v.ElementType, out _);
                }
                case "OrderBy":
                {
                    // a stable permutation: element i is source element p(i), p a bijection (q its inverse), in the keys'
                    // order (the first key, then ThenBy's), equal keys keeping the source's order. Keys are ordered if
                    // they are integers, chars or enums; from the first that is not, only the keys before it are.
                    int id = _materialized++;
                    Term Pi(Term i) => _z3.Apply("order.p#" + id, Sort.Int, new[] { i });
                    Term Qi(Term j) => _z3.Apply("order.q#" + id, Sort.Int, new[] { j });
                    var n = src.Length;
                    var keys = v.Keys;
                    bool Orderable(ITypeSymbol t) => t != null && (IsIntegral(t) || t.TypeKind == TypeKind.Enum || t.SpecialType == SpecialType.System_Char) && SortOf(t) == Sort.Int;
                    int prefix = keys.TakeWhile(k => Orderable(k.key.Type)).Count();
                    Term KeyOf(int k, Term j) => T.Coerce(ApplyValue(keys[k].key, keys[k].parameter, src.Element(j), f), Sort.Int);
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
                    return new Sequence { Length = n, Element = i => src.Element(Pi(i)), ElementType = v.ElementType, Known = src.Known };
                }
                case "Zip":
                {
                    // pairs at the same index, as many as the shorter has
                    var n = T.Ite(T.Le(src.Length, src2.Length), src.Length, src2.Length);
                    return new Sequence
                    {
                        Length = n, ElementType = v.ElementType, Known = T.And(src.Known, src2.Known),
                        Element = i => ApplyValue(v.Lambda, v.Parameter, src.Element(i), f, v.Index, src2.Element(i)),
                    };
                }
                case "Join":
                {
                    // for x in outer, for y in inner, if keys equal, yield result(x, y) (Cheney, Lindley and Wadler's
                    // normal form): a filter over the pairs, which are a SelectMany whose inner list is the inner source
                    var eq = EqualityOf(v.Lambda.Type);
                    var known = T.And(src.Known, src2.Known);
                    var product = Flatten(src, _ => src2, v.ElementType, known, out var outer, out var within);
                    Term X(Term i) => src.Element(outer(i));
                    Term Y(Term i) => src2.Element(within(i));
                    var pairs = new Sequence { Length = product.Length, ElementType = v.ElementType, Known = known,
                        Element = i => ApplyValue(v.Lambda3, v.Parameter3, X(i), f, v.Parameter3b, Y(i)) };
                    return Filter(pairs, i => eq(ApplyValue(v.Lambda, v.Parameter, X(i), f), ApplyValue(v.Lambda2, v.Parameter2, Y(i), f)), v.ElementType, out _);
                }
                case "SelectMany":
                {
                    Sequence Inner(Term j) => ListSequence(T.Coerce(ApplyValue(v.Lambda, v.Parameter, src.Element(j), f), Sort.Int), Unconverted(v.Lambda).Type, f);
                    var known = T.And(src.Known, OverIndices("forall", T.Int(0), src.Length, j => Inner(j).Known));
                    return Flatten(src, Inner, v.ElementType, known, out _, out _);
                }
                case "GroupBy":
                {
                    // the groups in the order their keys first appear (a key's first occurrence), each its key's elements
                    var keyType = v.Lambda.Type;
                    var eq = EqualityOf(keyType);
                    Term Key(Term j) => ApplyValue(v.Lambda, v.Parameter, src.Element(j), f);
                    var firsts = Filter(src, j => OverIndices("forall", T.Int(0), j, i => T.Not(eq(Key(i), Key(j)))), v.ElementType, out var first);
                    var name = "group#" + _materialized++;
                    Term Group(Term g) => _z3.Apply(name, Sort.Int, new[] { g });
                    var probe = Group(T.Int(0)).S;
                    var head = probe.Substring(1, probe.IndexOf(' ') - 1);
                    _groups[head] = new Groups { Name = head, Source = src, Key = Key, Same = eq, First = first, KeyType = keyType, ElementType = src.ElementType };
                    AssumeSide(OverIndices("forall", T.Int(0), firsts.Length, g => NotNull(Group(g))));
                    return new Sequence { Length = firsts.Length, Element = Group, ElementType = v.ElementType, Known = src.Known };
                }
                case "Take":
                {
                    var n = T.Ite(T.Le(v.Count, T.Int(0)), T.Int(0), T.Ite(T.Lt(v.Count, src.Length), v.Count, src.Length));
                    return new Sequence { Length = n, Element = src.Element, ElementType = v.ElementType, Known = src.Known };
                }
                case "Skip":
                {
                    var k = T.Ite(T.Lt(v.Count, T.Int(0)), T.Int(0), v.Count);
                    var n = T.Ite(T.Lt(T.Sub(src.Length, k), T.Int(0)), T.Int(0), T.Sub(src.Length, k));
                    return new Sequence { Length = n, Element = i => src.Element(T.Add(i, k)), ElementType = v.ElementType, Known = src.Known };
                }
                case "Where":
                {
                    // the matches, in order. c(j) counts the matches before source index j, one step at a time (so a
                    // concrete source unfolds), m = c(n) of them; the match at j is the view's element c(j), and the
                    // view's elements are matches at increasing source indices
                    int id = _materialized++;
                    var m = _z3.Fresh("where", Sort.Int);
                    Term Idx(Term i) => _z3.Apply("where.idx#" + id, Sort.Int, new[] { i });
                    Term C(Term j) => _z3.Apply("where.count#" + id, Sort.Int, new[] { j });
                    Term P(Term j) => AsBool(ApplyValue(v.Lambda, v.Parameter, src.Element(j), f));
                    var facts = T.And(
                        T.Eq(C(T.Int(0)), T.Int(0)), T.Eq(m, C(src.Length)), T.Le(T.Int(0), m), T.Le(m, src.Length),
                        OverIndices("forall", T.Int(0), src.Length, j => T.Eq(C(T.Add(j, T.Int(1))), T.Add(C(j), T.Ite(P(j), T.Int(1), T.Int(0)))),
                                    pattern: j => C(T.Add(j, T.Int(1)))),
                        OverIndices("forall", T.Int(0), src.Length, j => T.And(T.Le(T.Int(0), C(j)), T.Le(C(j), j), T.Implies(P(j), T.And(T.Lt(C(j), m), T.Eq(Idx(C(j)), j))))),
                        OverIndices("forall", T.Int(0), m, i => T.And(T.Le(T.Int(0), Idx(i)), T.Lt(Idx(i), src.Length), P(Idx(i)))),
                        OverIndices("forall", T.Int(0), T.Sub(m, T.Int(1)), i => T.Lt(Idx(i), Idx(T.Add(i, T.Int(1))))));
                    AssumeSide(T.Implies(src.Known, facts));
                    return new Sequence { Length = m, Element = i => src.Element(Idx(i)), ElementType = v.ElementType, Known = src.Known };
                }
            }
            return null;
        }

        /// <summary>What a LINQ source is, read now: a view, a List, an array, a list interface; null for others.</summary>
        private Sequence SequenceOf(IOperation sourceOp, Frame f, SpecEnv spec)
        {
            var type = Unconverted(sourceOp).Type;
            var x = T.Coerce(Eval(sourceOp, f, spec), Sort.Int);
            if (_views.TryGetValue(x.S, out var view)) return Materialize(view, f);
            if (GroupOf(x) is (Groups gs, Term g)) return GroupSequence(gs, g);
            if (!Indexable(type)) return null;
            Deref(sourceOp, x, sourceOp.Syntax);
            return ListSequence(x, type, f);
        }

        /// <summary>A LINQ view's source: a view, or a List, an array or a list interface (dereferenced); false for others.</summary>
        private bool ViewSourceOf(IOperation op, SyntaxNode at, Frame f, SpecEnv spec, out View inner, out Term source, out ITypeSymbol type)
        {
            source = null;
            type = Unconverted(op).Type;
            var x = T.Coerce(Eval(op, f, spec), Sort.Int);
            if (_views.TryGetValue(x.S, out inner)) return true;
            if (!Indexable(type)) return false;
            Deref(op, x, at);
            source = x;
            return true;
        }

        private static int ViewArity(string name) => name switch
        {
            "Distinct" => 1,
            "Select" or "Where" or "Take" or "Skip" or "OrderBy" or "OrderByDescending" or "ThenBy" or "ThenByDescending" or "SelectMany" or "GroupBy" => 2,
            "Zip" => 3,
            "Join" => 5,
            _ => -1,
        };

        /// <summary>The lazy LINQ methods of what this can read: a view (read when it is enumerated); null for others.</summary>
        private Term LazyLinqCall(IInvocationOperation inv, IInvocationOperation original, Frame f, SpecEnv spec)
        {
            var m = inv.TargetMethod;
            if (ViewArity(m.Name) != m.Parameters.Length) return null;
            IOperation Arg(int k) => inv.Arguments.First(a => a.Parameter.Ordinal == k).Value;
            IOperation LambdaArg(int k) => (original ?? inv).Arguments.First(a => a.Parameter.Ordinal == k).Value;
            var view = new View { Kind = m.Name, ElementType = ((INamedTypeSymbol)inv.Type).TypeArguments[0] };
            switch (m.Name)
            {
                case "Take":
                case "Skip":
                    if (m.Parameters[1].Type.SpecialType != SpecialType.System_Int32) return null;
                    break;
                case "Distinct":
                    break;
                case "Select":
                    if ((view.Lambda = PureLambdaBody(LambdaArg(1), out view.Parameter, out view.Index)) == null) return null;
                    break;
                case "Zip":
                    if ((view.Lambda = PureLambdaBody(LambdaArg(2), out view.Parameter, out view.Index, pair: true)) == null || view.Index == null) return null;
                    break;
                case "Join":
                    view.Lambda = PureLambdaBody(LambdaArg(2), out view.Parameter);
                    view.Lambda2 = PureLambdaBody(LambdaArg(3), out view.Parameter2);
                    view.Lambda3 = PureLambdaBody(LambdaArg(4), out view.Parameter3, out view.Parameter3b, pair: true);
                    if (view.Lambda == null || view.Lambda2 == null || view.Lambda3 == null || view.Parameter3b == null) return null;
                    break;
                default:
                    // (an impure lambda: the library's)
                    if ((view.Lambda = PureLambdaBody(LambdaArg(1), out view.Parameter)) == null) return null;
                    if (m.Name == "SelectMany" && !Indexable(Unconverted(view.Lambda).Type)) return null; // (inner sequences the verifier reads)
                    break;
            }
            if (!ViewSourceOf(Arg(0), inv.Syntax, f, spec, out view.Inner, out view.Source, out view.SourceType)) return null;
            if ((m.Name == "Zip" || m.Name == "Join") && !ViewSourceOf(Arg(1), inv.Syntax, f, spec, out view.Inner2, out view.Source2, out view.SourceType2)) return null;
            if (m.Name == "OrderBy" || m.Name == "OrderByDescending")
            {
                view.Kind = "OrderBy";
                view.Keys = new List<(IOperation, IParameterSymbol, bool)> { (view.Lambda, view.Parameter, m.Name == "OrderByDescending") };
            }
            else if (m.Name == "ThenBy" || m.Name == "ThenByDescending")
            {
                // (a further key of the sort its source is)
                var sorted = view.Inner;
                if (sorted?.Keys == null) return null;
                view.Kind = "OrderBy";
                (view.Inner, view.Source, view.SourceType) = (sorted.Inner, sorted.Source, sorted.SourceType);
                view.Keys = sorted.Keys.Concat(new[] { (view.Lambda, view.Parameter, m.Name == "ThenByDescending") }).ToList();
            }
            if (m.Name == "Take" || m.Name == "Skip") view.Count = T.Coerce(Eval(Arg(1), f, spec), Sort.Int);
            var result = _z3.Fresh("view", Sort.Int);
            AssumeSide(NotNull(result));
            _views[result.S] = view;
            return result;
        }

        /// <summary>
        /// A foreach's collection that is a LINQ view this can read (a chain of Select, Where, Take, Skip with pure
        /// lambdas, over a List, an array or a list interface): its element type; else null.
        /// </summary>
        private ITypeSymbol ViewForEachElement(IOperation collection)
        {
            var op = Unconverted(collection);
            var call = _model.GetOperation(op.Syntax) as IInvocationOperation ?? op as IInvocationOperation;
            if (call == null && op.Type is INamedTypeSymbol grouping && grouping.Name == "IGrouping" && grouping.TypeArguments.Length == 2)
                return grouping.TypeArguments[1]; // (a group: read if it is one this made)
            if (!ReadableView(call)) return null;
            return call.Type is INamedTypeSymbol t && t.TypeArguments.Length == 1 ? t.TypeArguments[0] : null;
        }

        /// <summary>Is this call a view LazyLinqCall makes, over sources it reads (as the syntax shows)?</summary>
        private bool ReadableView(IInvocationOperation c)
        {
            if (c == null || !IsEnumerableMethod(c.TargetMethod) || ViewArity(c.TargetMethod.Name) != c.TargetMethod.Parameters.Length) return false;
            IOperation A(int k) => c.Arguments.First(a => a.Parameter.Ordinal == k).Value;
            bool Src(int k) { var s = Unconverted(A(k)); return Indexable(s.Type) || ReadableView(_model.GetOperation(s.Syntax) as IInvocationOperation ?? s as IInvocationOperation); }
            bool L(int k) => PureLambdaBody(A(k), out _) != null;
            switch (c.TargetMethod.Name)
            {
                case "Distinct":
                case "Take":
                case "Skip":
                    return Src(0);
                case "Select":
                    return PureLambdaBody(A(1), out _, out _) != null && Src(0);
                case "Zip":
                    return PureLambdaBody(A(2), out _, out var second, pair: true) != null && second != null && Src(0) && Src(1);
                case "Join":
                    return L(2) && L(3) && PureLambdaBody(A(4), out _, out var inner, pair: true) != null && inner != null && Src(0) && Src(1);
                default:
                    return L(1) && Src(0);
            }
        }

        /// <summary>The view a foreach over one runs over: read when the loop began.</summary>
        private Sequence ViewSequenceOf(Loop loop, Term view, Frame f)
        {
            if (f.ViewSequences.TryGetValue(loop.Id, out var known)) return (Sequence)known;
            var seq = _views.TryGetValue(view.S, out var v) ? Materialize(v, f) : GroupOf(view) is (Groups gs, Term g) ? GroupSequence(gs, g) : null;
            f.ViewSequences[loop.Id] = seq;
            return seq;
        }

        /// <summary>The LINQ (and List predicate) calls modeled here; null for others.</summary>
        private Term LinqCall(IInvocationOperation inv, Frame f, SpecEnv spec)
        {
            if (!_codeMode) return null;
            var m = inv.TargetMethod;
            bool linq = IsEnumerableMethod(m);
            bool listMethod = !linq && IsListType(m.ContainingType) && (m.Name == "Find" || m.Name == "FindIndex" || m.Name == "Exists" || m.Name == "TrueForAll") &&
                              m.Parameters.Length == 1;
            if (!linq && !listMethod) return null;
            // (in a flow graph, a lambda argument is lowered: the original tree has it; the rest is evaluated as the flow graph has it)
            var original = _model.GetOperation(inv.Syntax) as IInvocationOperation;
            if (original != null && !SymbolEqualityComparer.Default.Equals(original.TargetMethod, m)) original = null;
            if (linq && !(m.Parameters[0].Type is INamedTypeSymbol pt && (pt.Name == "IEnumerable" || pt.Name == "IOrderedEnumerable"))) return null;
            if (linq && LazyLinqCall(inv, original, f, spec) is Term lazy) return lazy;
            var sourceOp = linq ? inv.Arguments.FirstOrDefault(a => a.Parameter.Ordinal == 0)?.Value : inv.Instance;
            if (sourceOp == null) return null;

            IOperation predicate = null;
            IParameterSymbol parameter = null;
            var lambdaCall = original ?? inv;
            var predicateArg = linq ? lambdaCall.Arguments.FirstOrDefault(a => a.Parameter.Ordinal == 1)?.Value : lambdaCall.Arguments[0].Value;
            bool takesPredicate = predicateArg != null && predicateArg.Type?.TypeKind == TypeKind.Delegate;
            if (takesPredicate)
            {
                predicate = PureLambdaBody(predicateArg, out parameter);
                if (predicate == null) return null; // (not one to inline: the library call, which may run it)
            }
            var name = m.Name;
            if (listMethod) name = name switch { "Find" => "FirstOrDefault", "Exists" => "Any", "TrueForAll" => "All", _ => name };
            if (!(name == "Count" || name == "Any" || name == "All" || name == "Contains" || name == "ElementAt" || name.StartsWith("First") ||
                  name.StartsWith("Last") || name == "FindIndex" || name == "ToArray" || name == "ToList" || name == "Sum" || name == "Min" || name == "Max")) return null;

            var seq = SequenceOf(sourceOp, f, spec);
            if (seq == null) return null;
            var n = seq.Length;
            var element = seq.ElementType;
            Term Elem(Term i) => seq.Element(i);
            Term P(Term i) => Apply(predicate, parameter, Elem(i), f);
            // facts that hold of a List or an array, and of a library collection (not of the program's own lists)
            void Fact(Term t) => AssumeSide(T.Implies(seq.Known, t));
            Term Default() => SortOf(inv.Type) == Sort.Bool ? T.False : IsFloating(inv.Type) ? Zero(SortOf(inv.Type)) : T.Int(0);

            // Sum, Min and Max (of the elements, or of a selector's values): by a running total, minimum or maximum
            if (name == "Sum" || name == "Min" || name == "Max")
            {
                if (m.Parameters.Length != (takesPredicate ? 2 : 1)) return null;
                var valueType = inv.Type;
                if (IsNullableValue(valueType) || !(IsIntegral(valueType) || IsFloating(valueType))) return null; // (nullable sums, comparers: not modeled)
                Term Value(Term i) => T.Coerce(takesPredicate ? ApplyValue(predicate, parameter, Elem(i), f) : Elem(i), SortOf(valueType));
                var sort = SortOf(valueType);
                if (IsIntegral(valueType) && sort != Sort.Int) return null; // (bit-vector integers: not modeled)
                if (IsFloating(valueType))
                {
                    // (floating point sums and NaN ordering: not modeled, the result is unknown)
                    if (name != "Sum")
                        Require(T.Implies(seq.Known, T.Lt(T.Int(0), n)), "CSV1001", inv.Syntax, $"'{inv.Syntax}': the sequence might be empty (it would throw InvalidOperationException)");
                    return Unknown(valueType, name.ToLowerInvariant());
                }
                if (name == "Sum")
                {
                    var acc = Recur("sum", n, T.Int(0), (a, j) => T.Add(a, Value(j)), seq.Known);
                    var (lo, hi) = RangeOf(valueType);
                    // checked: a partial sum out of range throws OverflowException. (As a recurrence of its own, so that
                    // the obligation is a ground term the solver unfolds, not a quantifier over the running sum.)
                    var ok = Recur("sum.ok", n, T.Int(1), (a, j) => T.Ite(T.And(T.Eq(a, T.Int(1)), T.InRange(acc(T.Add(j, T.Int(1))), lo, hi)), T.Int(1), T.Int(0)), seq.Known);
                    AssumeSide(T.Implies(seq.Known, OverIndices("forall", T.Int(0), n, j => T.Implies(T.Eq(ok(T.Add(j, T.Int(1))), T.Int(1)), T.Eq(ok(j), T.Int(1))))));
                    Require(T.Implies(seq.Known, T.Eq(ok(n), T.Int(1))), "CSV1001", inv.Syntax,
                        $"'{inv.Syntax}' might overflow (it would throw OverflowException)");
                    var r = _z3.Fresh("sum", sort);
                    Fact(T.Eq(r, acc(n)));
                    return r;
                }
                Require(T.Implies(seq.Known, T.Lt(T.Int(0), n)), "CSV1001", inv.Syntax, $"'{inv.Syntax}': the sequence might be empty (it would throw InvalidOperationException)");
                bool min = name == "Min";
                var best = Recur(name.ToLowerInvariant(), n, Value(T.Int(0)),
                    (a, j) => T.Ite(min ? T.Lt(Value(j), a) : T.Lt(a, Value(j)), Value(j), a), seq.Known);
                var result = _z3.Fresh(name.ToLowerInvariant(), sort);
                Fact(T.Eq(result, best(n)));
                Fact(T.And(OverIndices("forall", T.Int(0), n, j => min ? T.Le(result, Value(j)) : T.Le(Value(j), result)),
                           OverIndices("exists", T.Int(0), n, j => T.Eq(result, Value(j)))));
                return result;
            }

            switch (name)
            {
                case "Count" when !takesPredicate:
                {
                    var r = _z3.Fresh("count", Sort.Int);
                    AssumeSide(T.Le(T.Int(0), r));
                    Fact(T.Eq(r, n));
                    return r;
                }
                case "Any" when !takesPredicate:
                {
                    var r = _z3.Fresh("any", Sort.Bool);
                    Fact(T.Eq(r, T.Lt(T.Int(0), n)));
                    return r;
                }
                case "Any":
                {
                    var r = _z3.Fresh("any", Sort.Bool);
                    Fact(T.Eq(r, OverIndices("exists", T.Int(0), n, P)));
                    return r;
                }
                case "All":
                {
                    var r = _z3.Fresh("all", Sort.Bool);
                    Fact(T.Eq(r, OverIndices("forall", T.Int(0), n, P)));
                    return r;
                }
                case "Count":
                {
                    var r = _z3.Fresh("count", Sort.Int);
                    AssumeSide(T.And(T.Le(T.Int(0), r), T.Le(r, n)));
                    var c = Recur("count", n, T.Int(0), (a, j) => T.Add(a, T.Ite(P(j), T.Int(1), T.Int(0))), seq.Known);
                    Fact(T.And(T.Eq(r, c(n)), T.Eq(T.Eq(r, T.Int(0)), T.Not(OverIndices("exists", T.Int(0), n, P))), T.Eq(T.Eq(r, n), OverIndices("forall", T.Int(0), n, P))));
                    return r;
                }
                case "Contains" when !takesPredicate && m.Parameters.Length == 2:
                {
                    var v = T.Coerce(Eval(inv.Arguments.First(a => a.Parameter.Ordinal == 1).Value, f, spec), SortOf(element));
                    var r = _z3.Fresh("contains", Sort.Bool);
                    var epoch = _z3.Fresh("equals", Sort.Int);
                    Term Eq(Term a) => KnownEquality(element) ? T.Eq(a, v)
                        : _z3.Apply("equals:" + Resolve(element).ToDisplayString(), Sort.Bool, new[] { T.Coerce(a, Sort.Int), T.Coerce(v, Sort.Int), epoch });
                    Fact(T.Eq(r, OverIndices("exists", T.Int(0), n, i => Eq(Elem(i)))));
                    return r;
                }
                case "ElementAt" when m.Parameters.Length == 2:
                {
                    var i = T.Coerce(Eval(inv.Arguments.First(a => a.Parameter.Ordinal == 1).Value, f, spec), Sort.Int);
                    Require(T.Implies(seq.Known, T.And(T.Le(T.Int(0), i), T.Lt(i, n))), "CSV1001", inv.Syntax,
                        $"'{inv.Syntax}': the index might be out of range (it would throw ArgumentOutOfRangeException)");
                    return Elem(i);
                }
                case "First":
                case "FirstOrDefault":
                case "Last":
                case "LastOrDefault":
                case "FindIndex":
                {
                    bool first = name.StartsWith("First") || name == "FindIndex";
                    bool orDefault = name.EndsWith("OrDefault") || name == "FindIndex";
                    if (m.Parameters.Length > (takesPredicate ? (linq ? 2 : 1) : 1)) return null; // (with a default value: not modeled)
                    var found = takesPredicate ? OverIndices("exists", T.Int(0), n, P) : T.Lt(T.Int(0), n);
                    if (!orDefault)
                        Require(T.Implies(seq.Known, found), "CSV1001", inv.Syntax, $"'{inv.Syntax}' might find nothing (it would throw InvalidOperationException)");
                    var j = _z3.Fresh("at", Sort.Int);
                    // the first (or last) index whose element matches
                    var facts = new List<Term> { T.Le(T.Int(0), j), T.Lt(j, n) };
                    if (takesPredicate)
                    {
                        facts.Add(P(j));
                        facts.Add(first ? OverIndices("forall", T.Int(0), j, i => T.Not(P(i))) : OverIndices("forall", T.Add(j, T.Int(1)), n, i => T.Not(P(i))));
                    }
                    else facts.Add(T.Eq(j, first ? T.Int(0) : T.Sub(n, T.Int(1))));
                    Fact(T.Implies(found, T.And(facts.ToArray())));
                    if (!orDefault && GroupOf(Elem(j)) != null) return Elem(j); // (a group: the term its key and elements are read from)
                    var result = _z3.Fresh(name, SortOf(inv.Type));
                    var value = name == "FindIndex" ? T.Ite(found, j, T.Int(-1))
                        : orDefault ? T.Ite(found, T.Coerce(Elem(j), SortOf(inv.Type)), Default()) : T.Coerce(Elem(j), SortOf(inv.Type));
                    Fact(T.Eq(result, value));
                    return result;
                }
                case "ToArray" when !takesPredicate:
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
                case "ToList" when !takesPredicate && ListModels:
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
            return null;
        }
    }
}
