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
        private Term OverIndices(string quantifier, Term lo, Term hi, System.Func<Term, Term> body)
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
            var sourceOp = linq ? inv.Arguments.FirstOrDefault(a => a.Parameter.Ordinal == 0)?.Value : inv.Instance;
            if (sourceOp == null) return null;
            var sourceType = Unconverted(sourceOp).Type;
            if (!Indexable(sourceType)) return null;
            if (linq && !(m.Parameters[0].Type is INamedTypeSymbol pt && pt.Name == "IEnumerable")) return null;
            var element = ElementOf(sourceType);

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

            var x = T.Coerce(Eval(sourceOp, f, spec), Sort.Int);
            Deref(sourceOp, x, inv.Syntax);
            ListKind(x, sourceType);
            var n = ListSizeOf(x, f);
            Term Elem(Term i) => InRangeOf(ListItemOf(x, i, element, f, fresh: false), element);
            Term P(Term i) => Apply(predicate, parameter, Elem(i), f);
            // facts that hold of a List or an array, and of a library collection (not of the program's own lists)
            void Fact(Term t) => AssumeSide(ProgramImplementsListInterfaces() ? T.Implies(KnownList(x), t) : t);
            Term Default() => SortOf(inv.Type) == Sort.Bool ? T.False : IsFloating(inv.Type) ? Zero(SortOf(inv.Type)) : T.Int(0);
            var name = m.Name;
            if (listMethod) name = name switch { "Find" => "FirstOrDefault", "Exists" => "Any", "TrueForAll" => "All", _ => name };

            switch (name)
            {
                case "Count" when !takesPredicate:
                    return n;
                case "Any" when !takesPredicate:
                    return T.Lt(T.Int(0), n);
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
                    Require(T.And(T.Le(T.Int(0), i), T.Lt(i, n)), "CSV1001", inv.Syntax, $"'{inv.Syntax}': the index might be out of range (it would throw ArgumentOutOfRangeException)");
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
                        Require(found, "CSV1001", inv.Syntax, $"'{inv.Syntax}' might find nothing (it would throw InvalidOperationException)");
                    var j = _z3.Fresh("at", Sort.Int);
                    // the first (or last) index whose element matches
                    var facts = new List<Term> { T.Le(T.Int(0), j), T.Lt(j, n) };
                    if (takesPredicate)
                    {
                        facts.Add(P(j));
                        facts.Add(first ? OverIndices("forall", T.Int(0), j, i => T.Not(P(i))) : OverIndices("forall", T.Add(j, T.Int(1)), n, i => T.Not(P(i))));
                    }
                    else facts.Add(T.Eq(j, first ? T.Int(0) : T.Sub(n, T.Int(1))));
                    AssumeSide(T.Implies(found, ProgramImplementsListInterfaces() ? T.Implies(KnownList(x), T.And(facts.ToArray())) : T.And(facts.ToArray())));
                    if (name == "FindIndex") return T.Ite(found, j, T.Int(-1));
                    var value = Elem(j);
                    return orDefault ? T.Ite(found, T.Coerce(value, SortOf(inv.Type)), Default()) : T.Coerce(value, SortOf(inv.Type));
                }
                case "ToArray" when !takesPredicate:
                {
                    var arr = Unknown(inv.Type, "toArray");
                    AssumeSide(T.And(NotNull(arr), T.Eq(Len(arr), n)));
                    ListKind(arr, inv.Type);
                    NewArrayIsDistinct(arr, f);
                    var y = new Term("y", Sort.Int);
                    var row = Pointwise("toArray", Sort.Row, T.Coerce(ListItemOf(x, y, element, f, fresh: false), Sort.Int).S);
                    f.Heap = T.Store(f.Heap, arr, ProgramImplementsListInterfaces() ? T.Ite(KnownList(x), row, _z3.Fresh("toArray", Sort.Row)) : row);
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
                    var row = Pointwise("toList", Sort.Row, T.Coerce(ListItemOf(x, y, element, f, fresh: false), Sort.Int).S);
                    var known = ProgramImplementsListInterfaces() ? KnownList(x) : T.True;
                    f.Link = null; // (model maps changed outside a call's frame)
                    f.Fields[ListModel("Items")] = T.Store(FieldMap(f, ListModel("Items")), list, T.Ite(known, row, _z3.Fresh("toList", Sort.Row)));
                    f.Fields[ListModel("Size")] = T.Store(FieldMap(f, ListModel("Size")), list, n);
                    return list;
                }
            }
            return null;
        }
    }
}
