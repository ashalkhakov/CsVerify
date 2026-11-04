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
        private IOperation PureLambdaBody(IOperation arg, out IParameterSymbol parameter)
        {
            parameter = null;
            var target = (arg as IDelegateCreationOperation)?.Target as IAnonymousFunctionOperation;
            if (target == null || target.Symbol.Parameters.Length != 1 || target.Body.Operations.Length != 1 ||
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
                                                               IsNullableValue(pr.Property.ContainingType) || IsListInterface(pr.Property.ContainingType) ||
                                                               _engine.HasStub(pr.Property.GetMethod) && _engine.Stubs.IsPureMember(pr.Property.GetMethod)):
                        return null;
                }
            }
            parameter = target.Symbol.Parameters[0];
            return ret.ReturnedValue;
        }

        /// <summary>
        /// A condition on the elements of [lo, hi) as a quantifier over their index: the body is evaluated for a bound
        /// variable, without obligations (they are checked where the lambda is), its side facts quantified the same way.
        /// </summary>
        private Term OverIndices(string quantifier, Term lo, Term hi, System.Func<Term, Term> body, System.Func<Term, Term> pattern = null)
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
                    return new Term($"(forall (({name} Int)) (! {T.Implies(range, b)} :pattern ({pattern(bound)})))", Sort.Bool);
                return quantifier == "forall" ? T.Quant("forall", name, T.Implies(range, b)) : T.Quant("exists", name, T.And(range, b));
            }
            finally
            {
                _foreignSpec--;
                _codeMode = wasCode;
                _quantDepth--;
            }
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
        }

        private readonly Dictionary<string, View> _views = new Dictionary<string, View>(System.StringComparer.Ordinal);
        private int _materialized;

        /// <summary>A pure lambda's body for one element, as a value of its type (in spec mode, without obligations).</summary>
        private Term ApplyValue(IOperation body, IParameterSymbol parameter, Term element, Frame f)
        {
            var inner = f.Clone();
            inner.Vars[parameter] = element;
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

        /// <summary>A view read now: from its source as it is, with its lambda applied now.</summary>
        private Sequence Materialize(View v, Frame f)
        {
            var src = v.Inner != null ? Materialize(v.Inner, f) : ListSequence(v.Source, v.SourceType, f);
            switch (v.Kind)
            {
                case "Select":
                    return new Sequence { Length = src.Length, Element = i => ApplyValue(v.Lambda, v.Parameter, src.Element(i), f), ElementType = v.ElementType, Known = src.Known };
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
            if (!Indexable(type)) return null;
            Deref(sourceOp, x, sourceOp.Syntax);
            return ListSequence(x, type, f);
        }

        /// <summary>Select, Where, Take, Skip of what this can read: a view (read when it is enumerated); null for others.</summary>
        private Term LazyLinqCall(IInvocationOperation inv, IInvocationOperation original, Frame f, SpecEnv spec)
        {
            var m = inv.TargetMethod;
            if (!(m.Name == "Select" || m.Name == "Where" || m.Name == "Take" || m.Name == "Skip") || m.Parameters.Length != 2) return null;
            var sourceOp = inv.Arguments.First(a => a.Parameter.Ordinal == 0).Value;
            var type = Unconverted(sourceOp).Type;
            var view = new View { Kind = m.Name, ElementType = ((INamedTypeSymbol)inv.Type).TypeArguments[0] };
            if (m.Name == "Take" || m.Name == "Skip")
            {
                if (m.Parameters[1].Type.SpecialType != SpecialType.System_Int32) return null;
            }
            else
            {
                var lambdaArg = (original ?? inv).Arguments.First(a => a.Parameter.Ordinal == 1).Value;
                view.Lambda = PureLambdaBody(lambdaArg, out view.Parameter);
                if (view.Lambda == null) return null; // (Select with an index, or an impure lambda: the library's)
            }
            var x = T.Coerce(Eval(sourceOp, f, spec), Sort.Int);
            if (_views.TryGetValue(x.S, out var inner)) view.Inner = inner;
            else if (Indexable(type)) { Deref(sourceOp, x, inv.Syntax); view.Source = x; view.SourceType = type; }
            else return null;
            if (view.Kind == "Take" || view.Kind == "Skip") view.Count = T.Coerce(Eval(inv.Arguments.First(a => a.Parameter.Ordinal == 1).Value, f, spec), Sort.Int);
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
            for (var c = call; ; )
            {
                if (c == null || !IsEnumerableMethod(c.TargetMethod) || c.TargetMethod.Parameters.Length != 2) return null;
                var name = c.TargetMethod.Name;
                if (name == "Select" || name == "Where") { if (PureLambdaBody(c.Arguments.First(a => a.Parameter.Ordinal == 1).Value, out _) == null) return null; }
                else if (name != "Take" && name != "Skip") return null;
                var source = Unconverted(c.Arguments.First(a => a.Parameter.Ordinal == 0).Value);
                if (Indexable(source.Type)) break;
                c = source as IInvocationOperation;
            }
            return call.Type is INamedTypeSymbol t && t.TypeArguments.Length == 1 ? t.TypeArguments[0] : null;
        }

        /// <summary>The view a foreach over one runs over: read when the loop began.</summary>
        private Sequence ViewSequenceOf(Loop loop, Term view, Frame f)
        {
            if (f.ViewSequences.TryGetValue(loop.Id, out var known)) return (Sequence)known;
            var seq = _views.TryGetValue(view.S, out var v) ? Materialize(v, f) : null;
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
            if (linq && !(m.Parameters[0].Type is INamedTypeSymbol pt && pt.Name == "IEnumerable")) return null;
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
                  name.StartsWith("Last") || name == "FindIndex" || name == "ToArray" || name == "ToList")) return null;

            var seq = SequenceOf(sourceOp, f, spec);
            if (seq == null) return null;
            var n = seq.Length;
            var element = seq.ElementType;
            Term Elem(Term i) => seq.Element(i);
            Term P(Term i) => Apply(predicate, parameter, Elem(i), f);
            // facts that hold of a List or an array, and of a library collection (not of the program's own lists)
            void Fact(Term t) => AssumeSide(T.Implies(seq.Known, t));
            Term Default() => SortOf(inv.Type) == Sort.Bool ? T.False : IsFloating(inv.Type) ? Zero(SortOf(inv.Type)) : T.Int(0);

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
                    Fact(T.And(T.Eq(T.Eq(r, T.Int(0)), T.Not(OverIndices("exists", T.Int(0), n, P))), T.Eq(T.Eq(r, n), OverIndices("forall", T.Int(0), n, P))));
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
                    var y = new Term("y", Sort.Int);
                    var row = Pointwise("toArray", Sort.Row, T.Coerce(Elem(y), Sort.Int).S);
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
                    var y = new Term("y", Sort.Int);
                    var row = Pointwise("toList", Sort.Row, T.Coerce(Elem(y), Sort.Int).S);
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
