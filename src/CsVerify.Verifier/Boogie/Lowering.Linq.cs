using System;
using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.FlowAnalysis;
using Microsoft.CodeAnalysis.Operations;
using static CsVerify.Verifier.Boogie.KernelTypes;
using static CsVerify.Verifier.Boogie.KOp;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>
    /// LINQ to Objects, as its definitions in Bcl/Linq.cs say, member by member: a source the
    /// verifier indexes (an array, a List, a list interface) is a sequence, its length and its elements; Select maps
    /// them, Where filters them (a running count of the matches, and the index of each), OrderBy and ThenBy permute
    /// them in their keys' order (stably), Distinct keeps each first occurrence, Zip pairs them; Count, Sum, Max, Min,
    /// Any, All, First and Last read them, with their definitions' preconditions (CSV1001); ToArray and ToList copy them
    /// into a new object. Lambdas are inlined where they are pure (their own obligations are checked where each is
    /// verified, as a unit of its own). The running counts and permutations are maps havocked where the call is, their
    /// definitions assumed: a call in a loop gets new ones each time round. Anything else is the library's.
    /// </summary>
    internal sealed partial class Lowering
    {
        private sealed class LSeq
        {
            public KExpr Length;
            public Func<KExpr, KExpr> Elem;
            public ITypeSymbol Type;
            /// <summary>A filter's: the source index of its element i.</summary>
            public Func<KExpr, KExpr> Index;
            /// <summary>A GroupBy's groups: the call (its source, key and counts in _groupsOf).</summary>
            public IInvocationOperation Groups;
        }

        /// <summary>A GroupBy's: its source as read, its key, and how many of the source have each element's key.</summary>
        private readonly Dictionary<IInvocationOperation, (LSeq src, (IOperation, IParameterSymbol, IParameterSymbol) key, KVar count)> _groupsOf =
            new Dictionary<IInvocationOperation, (LSeq, (IOperation, IParameterSymbol, IParameterSymbol), KVar)>();

        /// <summary>
        /// A selector's parameter that is a group (q$name its value): a GroupBy's (its first element's index; its key, its
        /// count) or a GroupJoin's matches (the outer element's index; their count).
        /// </summary>
        private readonly Dictionary<IParameterSymbol, (LSeq src, (IOperation, IParameterSymbol, IParameterSymbol)? key, KVar count)> _groupParams =
            new Dictionary<IParameterSymbol, (LSeq, (IOperation, IParameterSymbol, IParameterSymbol)?, KVar)>(SymbolEqualityComparer.Default);

        /// <summary>A group's Key, Count(): their values (null for anything else; another use of a group isn't translated).</summary>
        private KExpr GroupValue(IOperation e)
        {
            if (_groupParams.Count == 0)
            {
                return null;
            }
            switch (e)
            {
                case IPropertyReferenceOperation { Property.Name: "Key", Instance: IParameterReferenceOperation p } when _groupParams.TryGetValue(p.Parameter, out var g) && g.key is var (kb, kp1, kp2):
                    return Apply((kb, kp1, kp2), g.src.Elem(new KVar("q$" + p.Parameter.Name)));
                case IInvocationOperation { TargetMethod.Name: "Count" or "LongCount", Arguments.Length: 1 } c when IsEnumerableCall(c.TargetMethod) &&
                                                                                                                      Unconverted(c.Arguments[0].Value) is IParameterReferenceOperation cp && _groupParams.TryGetValue(cp.Parameter, out var cg):
                    return Sel(cg.count, new KVar("q$" + cp.Parameter.Name));
                case IParameterReferenceOperation gp when _groupParams.ContainsKey(gp.Parameter):
                    throw new NotTranslated("a group used but for its Key and Count()");
                default:
                    return null;
            }
        }

        private static bool IsEnumerableCall(IMethodSymbol m) => m?.ContainingType?.ToDisplayString() == "System.Linq.Enumerable";

        private int _linq;

        /// <summary>A fact of the library's, assumed as mathematics where the call is.</summary>
        /// <summary>
        /// A fact of a query, assumed. Of a database query read with tracking, only where the context tracked no entity of
        /// the type before (Lowering.Ef's <see cref="_known"/>): else the rows are instances
        /// it tracks, as the program left them, not as the database matched them.
        /// </summary>
        private void LinqFact(KExpr fact, SyntaxNode at) =>
            Emit(KSpecStmt.AssumedFree(_known == null ? fact : Implies(_known, fact), at, argumentAt: at));

        /// <summary>A fact of what a query's result is (a definition, the bounds of a count or an index), whatever the rows hold.</summary>
        private void ShapeFact(KExpr fact, SyntaxNode at) => Emit(KSpecStmt.AssumedFree(fact, at, argumentAt: at));

        private string LinqMap(string type)
        {
            var name = "lq$" + _linq++;
            _p.Locals.Add(KLocal.Of(name, type));
            Emit(KHavoc.Of(name));
            return name;
        }

        private static KExpr Between(KExpr lo, KExpr i, KExpr hi) => AndAlso(Le(lo, i), Lt(i, hi));

        private KQuant Over(KExpr lo, KExpr hi, Func<KExpr, KExpr> body, bool forall = true)
        {
            var v = "lq$i" + _linq++;
            return new KQuant
            {
                Forall = forall,
                Var = v,
                Range = Between(lo, new KVar(v), hi),
                Body = body(new KVar(v)),
            };
        }

        /// <summary>A pure lambda's body (one expression, writing nothing, calling only functions), and its parameters.</summary>
        private (IOperation body, IParameterSymbol p1, IParameterSymbol p2)? PureLambda(IOperation arg)
        {
            // (a lambda made a delegate, or quoted as an expression tree, Queryable's)
            var fn = Unconverted(arg) is IDelegateCreationOperation dc ? dc.Target as IAnonymousFunctionOperation ?? LambdaOf(dc.Target) ?? LambdaBySymbol(dc.Target)
                   : Unconverted(arg) is IAnonymousFunctionOperation quoted ? quoted
                   : Unconverted(arg) is IFlowAnonymousFunctionOperation fq ? LambdaBySymbol(fq) : null;
            if (fn == null || fn.Body.Operations.Length != 1 || !(fn.Body.Operations[0] is IReturnOperation { ReturnedValue: { } body }))
            {
                return null;
            }
            foreach (var op in body.DescendantsAndSelf())
            {
                switch (op)
                {
                    case IAssignmentOperation a when a.Parent is IAnonymousObjectCreationOperation: break; // (new { x, y = e }: its members, not writes)
                    case IAssignmentOperation _: case IIncrementOrDecrementOperation _: case IObjectCreationOperation _: case IArrayCreationOperation _:
                    case IAnonymousFunctionOperation _: case IAwaitOperation _:
                        return null;
                    // (a group's count, of a parameter: GroupValue's)
                    case IInvocationOperation gc when IsEnumerableCall(gc.TargetMethod) && gc.TargetMethod.Name is "Count" or "LongCount" && gc.Arguments.Length == 1 &&
                                                      Unconverted(gc.Arguments[0].Value) is IParameterReferenceOperation gp && fn.Symbol.Parameters.Contains(gp.Parameter, SymbolEqualityComparer.Default):
                        break;
                    case IInvocationOperation inv when !(_isFunction(inv.TargetMethod.OriginalDefinition) || inv.TargetMethod.ContainingType?.ToDisplayString() == "System.Math" ||
                                                        SpecSymbols.IsSpecClass(inv.TargetMethod.ContainingType) ||
                                                        // (a string's [Pure] member with a stub, a list's Contains: as a specification reads them)
                                                        IsStub(inv.TargetMethod.OriginalDefinition) || StringEquals(inv) != null || DatabaseFunction(inv) ||
                                                        inv.Instance != null && CollectionKind(CollectionOf(inv.Instance.Type)) == "List" && inv.TargetMethod.Name == "Contains" && inv.Arguments.Length == 1):
                        return null;
                }
            }
            return (body, fn.Symbol.Parameters.ElementAtOrDefault(0), fn.Symbol.Parameters.ElementAtOrDefault(1));
        }

        /// <summary>A lambda the control flow graph has as a flow anonymous function (a query clause's): found in the method's operations by its symbol.</summary>
        private IAnonymousFunctionOperation LambdaBySymbol(IOperation target)
        {
            if (!(target is IFlowAnonymousFunctionOperation ff) || _model == null || _decl == null)
            {
                return null;
            }
            return _model.GetOperation(_decl)?.DescendantsAndSelf().OfType<IAnonymousFunctionOperation>().FirstOrDefault(a => SymbolEqualityComparer.Default.Equals(a.Symbol, ff.Symbol));
        }

        /// <summary>A lambda applied to an element (and its index): its body, its parameters bound.</summary>
        private KExpr Apply((IOperation body, IParameterSymbol p1, IParameterSymbol p2) f, KExpr x, KExpr i = null)
        {
            KExpr e = Spec(f.body, null);
            if (f.p2 != null)
            {
                e = KLet.Of("q$" + f.p2.Name, i ?? throw new NotTranslated("a lambda of an index"), e);
            }
            return KLet.Of("q$" + f.p1.Name, x, e);
        }

        private static ITypeSymbol ElementOf(ITypeSymbol t) =>
            t is IArrayTypeSymbol a ? a.ElementType : t is INamedTypeSymbol { TypeArguments.Length: >= 1 } n ? n.TypeArguments[n.TypeArguments.Length - 1] : null;

        /// <summary>A LINQ source as a sequence, read now: a query of the members here, or an array, a List, a list interface.</summary>
        private LSeq Sequence(IOperation op)
        {
            var src = Unconverted(op);
            // (a query the control flow graph captured: what it captured)
            // (and query syntax: the calls it is)
            while (src is IFlowCaptureReferenceOperation r && _captured.TryGetValue(r.Id, out var v) || src is ITranslatedQueryOperation ||
                   src is ILocalReferenceOperation lq && _lazyQueries.ContainsKey(lq.Local))
            {
                src = src is ITranslatedQueryOperation tq ? Unconverted(tq.Operation)
                    : src is ILocalReferenceOperation lazy ? Unconverted(_lazyQueries[lazy.Local])
                    : Unconverted(_captured[((IFlowCaptureReferenceOperation)src).Id]);
            }
            // (a table, as the query reads it; Queryable's operators, LINQ to Objects')
            if (TableOf(src) is DbTable table)
            {
                return ReadTable(table);
            }
            // (a context's local view: what it tracks of a type)
            if (KernelTypes.Ef != null && IsLocalView(src))
            {
                return LocalView((IPropertyReferenceOperation)Unconverted(src));
            }
            // (a compiled query's rows: a library call's)
            if (CompiledSequence(src) is LSeq compiled)
            {
                return compiled;
            }
            if (src is IInvocationOperation q && (IsEnumerableCall(q.TargetMethod) || IsQueryableMethod(q.TargetMethod)))
            {
                return Query(q);
            }
            var type = src.Type;
            var elem = ElementOf(type);
            // (a set's members, in some order: as many as its Size, each a member, no two the same)
            if (elem != null && InSubset(elem) && CollectionKind(type) == "HashSet" && IsCollection(type))
            {
                var hs = Declare("t$" + _temps++, type);
                Emit(KAssign.Of(hs, Expr(src)));
                Emit(KCheck.Of(
                    NotNull(new KVar(hs)),
                    "CSV1013",
                    src.Syntax,
                    $"'{src.Syntax}' might be null: LINQ would throw ArgumentNullException"));
                foreach (var m in ModelsOf((INamedTypeSymbol)type))
                {
                    _p.Models[m.Name] = m;
                }
                var n = Sel(SizeMap, new KVar(hs));
                var order = new KVar(LinqMap("[int]" + TypeOf(elem)));
                KExpr E(KExpr i) => Sel(order, i);
                ShapeFact(Over(KLit.Zero, n, i => Sel(ModelOf("Members", (INamedTypeSymbol)type).Name, new KVar(hs), Keyed(E(i), elem))), src.Syntax);
                ShapeFact(Over(KLit.Zero, n, i => Over(KLit.Zero, i, j => Ne(E(j), E(i)))), src.Syntax);
                return new LSeq
                {
                    Length = n,
                    Elem = E,
                    Type = elem,
                };
            }
            // (a sequence one is given, a lambda's group of a GroupJoin say: some elements, not known)
            if (elem != null && InSubset(elem) && (IsSequence(type) || IsLinqGroup(type)) && src is IParameterReferenceOperation or ILocalReferenceOperation)
            {
                var given = Expr(src);
                if (IsSequence(type))
                {
                    Emit(KCheck.Of(NotNull(given), "CSV1013", src.Syntax, $"'{src.Syntax}' might be null: LINQ would throw ArgumentNullException"));
                }
                var items = new KVar(LinqMap("[int]" + TypeOf(elem)));
                var n = Declare("t$" + _temps++, KernelTypes.Compilation.GetSpecialType(SpecialType.System_Int32));
                Emit(KHavoc.Of(n));
                ShapeFact(Le(KLit.Zero, new KVar(n)), src.Syntax);
                // (a group has one at least)
                if (IsLinqGroup(type))
                {
                    ShapeFact(Lt(KLit.Zero, new KVar(n)), src.Syntax);
                }
                return new LSeq
                {
                    Length = new KVar(n),
                    Elem = i => Sel(items, i),
                    Type = elem,
                };
            }
            if (elem == null || !InSubset(elem) || !(IsArray(type) || IsList(type) || IsCollectionInterface(type)))
            {
                throw new NotTranslated("a LINQ source of " + type + " (" + src.Kind + ")");
            }
            var t = Declare("t$" + _temps++, type);
            Emit(KAssign.Of(t, Expr(src)));
            Emit(KCheck.Of(NotNull(new KVar(t)), "CSV1013", src.Syntax, $"'{src.Syntax}' might be null: LINQ would throw ArgumentNullException"));
            var x = new KVar(t);
            if (IsArray(type))
            {
                return new LSeq
                {
                    Length = Length(x),
                    Elem = i => Sel(Elements(type), x, i),
                    Type = elem,
                };
            }
            if (IsList(type))
            {
                foreach (var m in ModelsOf((INamedTypeSymbol)type))
                {
                    _p.Models[m.Name] = m;
                }
                return new LSeq
                {
                    Length = Sel(SizeMap, x),
                    Elem = i => Sel(ModelOf("Items", (INamedTypeSymbol)type).Name, x, i),
                    Type = elem,
                };
            }
            var list = (INamedTypeSymbol)KernelTypes.Compilation.GetTypeByMetadataName("System.Collections.Generic.List`1").Construct(elem);
            foreach (var m in ModelsOf(list))
            {
                _p.Models[m.Name] = m;
            }
            _p.UsesState = true;
            return new LSeq
            {
                Length = IfcRead(x, null, elem),
                Elem = i => IfcRead(x, i, elem),
                Type = elem,
            };
        }

        /// <summary>
        /// Queries kept in a local, var q = l.Select(...): lazy, read where they're enumerated, of the state then, as LINQ
        /// to Objects runs them. Only of variables nothing assigns after, so that the query read later is the one made.
        /// </summary>
        private readonly Dictionary<ILocalSymbol, IOperation> _lazyQueries = new Dictionary<ILocalSymbol, IOperation>(SymbolEqualityComparer.Default);

        private bool LazyQuery(ILocalSymbol local, IOperation value)
        {
            var q = Unconverted(value);
            if (!(q is IInvocationOperation call && IsEnumerableCall(call.TargetMethod)) || !(IsSequence(local.Type) || local.Type is INamedTypeSymbol { Name: "IOrderedEnumerable" }))
            {
                return false;
            }
            if (_lazyQueries.ContainsKey(local) || !NeverWrittenAfter(local, q))
            {
                return false;
            }
            foreach (var op in q.DescendantsAndSelf())
            {
                if (op is ILocalReferenceOperation lr && !lr.Local.Equals(local) && !(q.Syntax.Span.Contains(lr.Local.DeclaringSyntaxReferences.FirstOrDefault()?.Span ?? default)) && !NeverWritten(lr.Local) ||
                    op is IParameterReferenceOperation pr && _assigned.ContainsKey(pr.Parameter) ||
                    op is IAnonymousFunctionOperation af && PureLambda(af) == null)
                {
                    return false;
                }
            }
            _lazyQueries[local] = q;
            return true;
        }

        /// <summary>Is the local assigned only where it is declared (by this value)?</summary>
        private bool NeverWrittenAfter(ILocalSymbol local, IOperation value) =>
            !_decl.DescendantNodes().OfType<Microsoft.CodeAnalysis.CSharp.Syntax.AssignmentExpressionSyntax>().Any(a => SymbolEqualityComparer.Default.Equals(_model.GetSymbolInfo(a.Left).Symbol, local));

        private (IOperation body, IParameterSymbol p1, IParameterSymbol p2) LambdaArg(IInvocationOperation q, int ordinal)
        {
            var arg = q.Arguments.First(a => a.Parameter.Ordinal == ordinal).Value;
            return PureLambda(arg) ?? throw new NotTranslated("a LINQ lambda that isn't pure: " + Unconverted(arg).Kind + " " + ((Unconverted(arg) as IDelegateCreationOperation)?.Target?.Kind));
        }

        /// <summary>A query: a member of Enumerable that gives a sequence.</summary>
        private LSeq Query(IInvocationOperation q)
        {
            // (what is known of a tracked query's rows is known only where its context tracked none before: _known, kept
            // from here on, for the query's facts that its consumer assumes; the statement's lowering ends it)
            bool database = KernelTypes.Ef != null && DatabaseRoot(q, out _) != null;
            var result = _dbResult;
            if (database && _inDatabase == 0)
            {
                _dbResult = q.Type;
            }
            bool untranslatable = database && TranslationChecks(q);
            if (database)
            {
                _inDatabase++;
            }
            try
            {
                if (untranslatable)
                {
                    var elem = ElementOf(q.Type);
                    if (elem == null || !InSubset(elem))
                    {
                        throw new NotTranslated("a database query's result of " + q.Type);
                    }
                    var items = new KVar(LinqMap("[int]" + TypeOf(elem)));
                    var n = Declare("t$" + _temps++, KernelTypes.Compilation.GetSpecialType(SpecialType.System_Int32));
                    Emit(KHavoc.Of(n));
                    ShapeFact(Le(KLit.Zero, new KVar(n)), q.Syntax);
                    return new LSeq
                    {
                        Length = new KVar(n),
                        Elem = i => Sel(items, i),
                        Type = elem,
                    };
                }
                return QueryCore(q);
            }
            finally
            {
                if (database)
                {
                    _inDatabase--;
                }
                _dbResult = result;
            }
        }

        private LSeq QueryCore(IInvocationOperation q)
        {
            var m = q.TargetMethod;
            var args = q.Arguments.OrderBy(a => a.Parameter.Ordinal).ToList();
            var resultElem = ElementOf(q.Type);
            // (a database's that says nothing of what it gives: some rows, of the type)
            if (KernelTypes.Ef != null && DatabaseUnknown(q))
            {
                if (resultElem == null || !InSubset(resultElem))
                {
                    throw new NotTranslated("a database query's result of " + q.Type);
                }
                var items = new KVar(LinqMap("[int]" + TypeOf(resultElem)));
                var n = Declare("t$" + _temps++, KernelTypes.Compilation.GetSpecialType(SpecialType.System_Int32));
                Emit(KHavoc.Of(n));
                ShapeFact(Le(KLit.Zero, new KVar(n)), q.Syntax);
                return new LSeq
                {
                    Length = new KVar(n),
                    Elem = i => Sel(items, i),
                    Type = resultElem,
                };
            }
            // (a lazy operator whose lambda isn't pure, of LINQ to Objects: the lambda must accept anything (it may change
            // what it is called with), what it may change changes, and what it gives isn't known)
            if (IsEnumerableCall(m) && args.Count == 2 && IsFunc(args[1].Parameter.Type) && PureLambda(args[1].Value) == null &&
                m.Name is "Where" or "Select" or "TakeWhile" or "SkipWhile" or "OrderBy" or "OrderByDescending" && resultElem != null && InSubset(resultElem))
            {
                var src = Sequence(args[0].Value);
                DelegatesHere("a library call of a delegate");
                var d = Expr(args[1].Value);
                var key = FuncKey(args[1].Parameter.Type);
                _p.DelegateKeys.Add(key);
                _p.CallsDelegates = true;
                var (lambda, quiet, free) = Handed(args[1]);
                if (!free)
                {
                    Emit(KCheck.Of(
                        new KOp("$total." + key, d),
                        "CSV1029",
                        args[1].Syntax,
                        $"'{m.Name}' may call this with anything (its query runs later), but its precondition might not hold for them all"));
                }
                if (!quiet)
                {
                    _p.HavocsAll = true;
                    Emit(new KHavocAll { Unless = new KOp("$nochange", d) });
                }
                ForgetCaptured();
                var items = new KVar(LinqMap("[int]" + TypeOf(resultElem)));
                var n = Declare("t$" + _temps++, KernelTypes.Compilation.GetSpecialType(SpecialType.System_Int32));
                Emit(KHavoc.Of(n));
                ShapeFact(Le(KLit.Zero, new KVar(n)), q.Syntax);
                if (m.Name is "Where" or "TakeWhile" or "SkipWhile")
                {
                    ShapeFact(Le(new KVar(n), src.Length), q.Syntax);
                }
                if (m.Name is "Select" or "OrderBy" or "OrderByDescending")
                {
                    ShapeFact(Eq(new KVar(n), src.Length), q.Syntax);
                }
                return new LSeq
                {
                    Length = new KVar(n),
                    Elem = i => Sel(items, i),
                    Type = resultElem,
                };
            }
            switch (m.Name)
            {
                case "Select" when args.Count == 2:
                {
                    var src = Sequence(args[0].Value);
                    var f = LambdaArg(q, 1);
                    // (of groups: the selector's parameter is one)
                    if (src.Groups != null && _groupsOf.TryGetValue(src.Groups, out var gi))
                    {
                        _groupParams[f.p1] = (gi.src, gi.key, gi.count);
                    }
                    return new LSeq
                    {
                        Length = src.Length,
                        Elem = i => Apply(f, src.Elem(i), i),
                        Type = resultElem,
                    };
                }
                // (the first n, or all but them: n clamped to [0, Count], as their definitions have it)
                case "Take" or "Skip" when args.Count == 2 && IsIntegral(args[1].Value.Type) && args[1].Value.Type.SpecialType == SpecialType.System_Int32:
                {
                    var src = Sequence(args[0].Value);
                    var n = Expr(args[1].Value);
                    var k = Declare("t$" + _temps++, args[1].Value.Type);
                    Emit(KAssign.Of(
                        k,
                        Ite(Le(n, KLit.Zero), KLit.Zero, Ite(Lt(n, src.Length), n, src.Length))));
                    var kv = new KVar(k);
                    // (a database's: by their place in its order, CSV1031)
                    DatabaseOrder(q, args[0].Value, src.Length);
                    return m.Name == "Take"
                        ? new LSeq
                        {
                            Length = kv,
                            Elem = src.Elem,
                            Type = src.Type,
                        }
                        : new LSeq
                        {
                            Length = Minus(src.Length, kv),
                            Elem = i => src.Elem(Plus(i, kv)),
                            Type = src.Type,
                        };
                }
                case "Where" when args.Count == 2:
                {
                    var src = Sequence(args[0].Value);
                    var f = LambdaArg(q, 1);
                    // (with an index: each element's place in the source)
                    if (f.p2 != null)
                    {
                        return _inDatabase > 0 ? throw new NotTranslated("Where with an index, in a database") : FilterAt(src, j => Apply(f, src.Elem(j), j), q.Syntax);
                    }
                    return Filter(src, x => Apply(f, x), q.Syntax);
                }
                // (each first occurrence of the first source's elements that the second has, or hasn't)
                case "Intersect" or "Except" when args.Count == 2 && _inDatabase == 0:
                {
                    var a = Sequence(args[0].Value);
                    var b = Sequence(args[1].Value);
                    bool keep = m.Name == "Intersect";
                    var unseen = Unseen(a.Length, (k, j) => SameValue(a.Elem(k), a.Elem(j), a.Type), q.Syntax);
                    return FilterAt(a, j => AndAlso(unseen(j),
                                                    keep ? (KExpr)new KQuantOver(this, KLit.Zero, b.Length, k => SameValue(b.Elem(k), a.Elem(j), a.Type), forall: false).Q
                                                         : Not(new KQuantOver(this, KLit.Zero, b.Length, k => SameValue(b.Elem(k), a.Elem(j), a.Type), forall: false).Q)), q.Syntax);
                }
                // (each element whose key no element before it has)
                case "DistinctBy" when args.Count == 2 && _inDatabase == 0:
                {
                    var src = Sequence(args[0].Value);
                    var f = LambdaArg(q, 1);
                    if (f.p2 != null)
                    {
                        throw new NotTranslated("DistinctBy with an index");
                    }
                    var keyType = f.body.Type;
                    return FilterAt(src, Unseen(src.Length, (k, j) => SameValue(Apply(f, src.Elem(k)), Apply(f, src.Elem(j)), keyType), q.Syntax), q.Syntax);
                }
                // (each element with its index: a tuple (Index, Item))
                case "Index" when args.Count == 1 && _inDatabase == 0 && resultElem != null && IsTuple(resultElem):
                {
                    var src = Sequence(args[0].Value);
                    return new LSeq
                    {
                        Length = src.Length,
                        Elem = i => new KOp(TupleMaker(resultElem), i, src.Elem(i)),
                        Type = resultElem,
                    };
                }
                // (the source backwards)
                case "Reverse" when args.Count == 1 && _inDatabase == 0:
                {
                    var src = Sequence(args[0].Value);
                    return new LSeq
                    {
                        Length = src.Length,
                        Elem = i => src.Elem(Minus(Minus(src.Length, KLit.One), i)),
                        Type = src.Type,
                    };
                }
                // (one more element, at the end or the start)
                case "Append" or "Prepend" when args.Count == 2 && _inDatabase == 0:
                {
                    var src = Sequence(args[0].Value);
                    var x = Operand(args[1].Value, Expr, inSpec: false);
                    bool end = m.Name == "Append";
                    return new LSeq
                    {
                        Length = Plus(src.Length, KLit.One),
                        Type = src.Type,
                        Elem = i => end ? Ite(Lt(i, src.Length), src.Elem(i), x)
                                                                : Ite(Eq(i, KLit.Zero), x, src.Elem(Minus(i, KLit.One))),
                    };
                }
                // (the last n, or all but them: n clamped to [0, Count])
                case "TakeLast" or "SkipLast" when args.Count == 2 && args[1].Value.Type.SpecialType == SpecialType.System_Int32 && _inDatabase == 0:
                {
                    var src = Sequence(args[0].Value);
                    var n = Expr(args[1].Value);
                    var k = Declare("t$" + _temps++, args[1].Value.Type);
                    Emit(KAssign.Of(
                        k,
                        Ite(Le(n, KLit.Zero), KLit.Zero, Ite(Lt(n, src.Length), n, src.Length))));
                    var kv = new KVar(k);
                    return m.Name == "TakeLast"
                        ? new LSeq
                        {
                            Length = kv,
                            Elem = i => src.Elem(Plus(Minus(src.Length, kv), i)),
                            Type = src.Type,
                        }
                        : new LSeq
                        {
                            Length = Minus(src.Length, kv),
                            Elem = src.Elem,
                            Type = src.Type,
                        };
                }
                // (up to the first element the predicate rejects, or from it on)
                case "TakeWhile" or "SkipWhile" when args.Count == 2 && _inDatabase == 0:
                {
                    var src = Sequence(args[0].Value);
                    var f = LambdaArg(q, 1);
                    if (f.p2 != null)
                    {
                        throw new NotTranslated(m.Name + " with an index");
                    }
                    var k = Declare("t$" + _temps++, KernelTypes.Compilation.GetSpecialType(SpecialType.System_Int32));
                    Emit(KHavoc.Of(k));
                    var kv = new KVar(k);
                    ShapeFact(AndAlso(Le(KLit.Zero, kv), Le(kv, src.Length)), q.Syntax);
                    ShapeFact(Over(KLit.Zero, kv, i => Apply(f, src.Elem(i))), q.Syntax);
                    ShapeFact(Implies(Lt(kv, src.Length), Not(Apply(f, src.Elem(kv)))), q.Syntax);
                    return m.Name == "TakeWhile"
                        ? new LSeq
                        {
                            Length = kv,
                            Elem = src.Elem,
                            Type = src.Type,
                        }
                        : new LSeq
                        {
                            Length = Minus(src.Length, kv),
                            Elem = i => src.Elem(Plus(i, kv)),
                            Type = src.Type,
                        };
                }
                // (the source, or one default if it's empty)
                case "DefaultIfEmpty" when args.Count == 1 && _inDatabase == 0 && Default(resultElem) is KExpr de:
                {
                    var src = Sequence(args[0].Value);
                    var empty = Eq(src.Length, KLit.Zero);
                    return new LSeq
                    {
                        Length = Ite(empty, KLit.One, src.Length),
                        Elem = i => Ite(empty, de, src.Elem(i)),
                        Type = src.Type,
                    };
                }
                case "Distinct" when args.Count == 1:
                {
                    var src = Sequence(args[0].Value);
                    // (each element's first occurrence, in order: Q.Unseen; the database's, in no order)
                    var distinct = FilterAt(src, Unseen(src.Length, (k, j) => SameValue(src.Elem(k), src.Elem(j), src.Type), q.Syntax), q.Syntax);
                    return _inDatabase > 0 ? Sort(distinct, new List<((IOperation, IParameterSymbol, IParameterSymbol), ITypeSymbol, bool)>(), q.Syntax) : distinct;
                }
                // (a.Zip(b): pairs of the elements at each index, as long as the shorter)
                case "Zip" when args.Count == 2 && resultElem != null && IsTuple(resultElem):
                {
                    var a = Sequence(args[0].Value);
                    var b = Sequence(args[1].Value);
                    return new LSeq
                    {
                        Length = Ite(Le(a.Length, b.Length), a.Length, b.Length),
                        Type = resultElem,
                        Elem = i => new KOp(TupleMaker(resultElem), a.Elem(i), b.Elem(i)),
                    };
                }
                // (the first group of a GroupBy: the source's elements of its first element's key, in order, as the element
                // selector makes them, if it has one; none: it throws)
                case "First" when args.Count == 1 && Unconverted(args[0].Value) is IInvocationOperation gb && IsEnumerableCall(gb.TargetMethod) && gb.TargetMethod.Name == "GroupBy" && _inDatabase == 0 &&
                                  (gb.Arguments.Length == 2 || gb.Arguments.Length == 3 && LambdaArg(gb, 2).p2 == null):
                {
                    var gsrc = Sequence(gb.Arguments.First(a => a.Parameter.Ordinal == 0).Value);
                    var gkey = LambdaArg(gb, 1);
                    Emit(KCheck.Of(
                        Gt(gsrc.Length, KLit.Zero),
                        "CSV1001",
                        q.Syntax,
                        "precondition 'Q.Count(source) > 0' of 'First' might not hold"));
                    var members = FilterAt(gsrc, k => SameValue(Apply(gkey, gsrc.Elem(k)), Apply(gkey, gsrc.Elem(KLit.Zero)), gkey.body.Type), q.Syntax);
                    if (gb.Arguments.Length == 2)
                    {
                        return members;
                    }
                    var es = LambdaArg(gb, 2);
                    return new LSeq
                    {
                        Length = members.Length,
                        Elem = i => Apply(es, members.Elem(i)),
                        Type = resultElem,
                    };
                }
                case "Zip" when args.Count == 3:
                {
                    var a = Sequence(args[0].Value);
                    var b = Sequence(args[1].Value);
                    var f = LambdaArg(q, 2);
                    var fx = (f.body, f.p1, (IParameterSymbol)null);
                    return new LSeq
                    {
                        Length = Ite(Le(a.Length, b.Length), a.Length, b.Length),
                        Type = resultElem,
                        Elem = i => KLet.Of("q$" + f.p2.Name, b.Elem(i), Apply(fx, a.Elem(i))),
                    };
                }
                case "OrderBy" or "OrderByDescending" or "ThenBy" or "ThenByDescending" when args.Count == 2:
                {
                    // (the keys, the first one's call innermost; a stable sort of the source by them all)
                    var keys = new List<((IOperation, IParameterSymbol, IParameterSymbol) key, ITypeSymbol type, bool down)>();
                    IInvocationOperation at = q;
                    IOperation SourceOf(IInvocationOperation x) => x.Arguments.OrderBy(a => a.Parameter.Ordinal).First().Value;
                    while (at.TargetMethod.Name.StartsWith("Then"))
                    {
                        keys.Insert(0, (LambdaArg(at, 1), at.TargetMethod.TypeArguments.Last(), at.TargetMethod.Name.EndsWith("Descending")));
                        if (!(Unconverted(SourceOf(at)) is IInvocationOperation inner && (IsEnumerableCall(inner.TargetMethod) || IsQueryableMethod(inner.TargetMethod)) &&
                              inner.TargetMethod.Name is "OrderBy" or "OrderByDescending" or "ThenBy" or "ThenByDescending"))
                        {
                            throw new NotTranslated("a ThenBy of an order not made here");
                        }
                        at = inner;
                    }
                    keys.Insert(0, (LambdaArg(at, 1), at.TargetMethod.TypeArguments.Last(), at.TargetMethod.Name.EndsWith("Descending")));
                    var src = Sequence(at.Arguments.OrderBy(a => a.Parameter.Ordinal).First().Value);
                    return Sort(src, keys, q.Syntax);
                }
                case "SelectMany" when args.Count is 2 or 3:
                {
                    var src = Sequence(args[0].Value);
                    var f = LambdaArg(q, 1);
                    if (f.p2 != null)
                    {
                        throw new NotTranslated("SelectMany with an index");
                    }
                    var r = args.Count == 3 ? LambdaArg(q, 2) : default;
                    var flat = Flatten(src, j => Inner(Apply(f, src.Elem(j)), f.body), q.Syntax, out var outer, out var within);
                    if (args.Count == 2)
                    {
                        return flat;
                    }
                    var rx = (r.body, r.p1, (IParameterSymbol)null);
                    return new LSeq
                    {
                        Length = flat.Length,
                        Type = resultElem,
                        Elem = i => KLet.Of("q$" + r.p2.Name, flat.Elem(i), Apply(rx, src.Elem(outer(i)))),
                    };
                }
                case "Join" when args.Count == 5:
                {
                    // (each pair of an outer and an inner element, in that order, whose keys agree: Q.For, Q.For, Q.If)
                    var o = Sequence(args[0].Value);
                    var inner = Sequence(args[1].Value);
                    var (okey, ikey, sel) = (LambdaArg(q, 2), LambdaArg(q, 3), LambdaArg(q, 4));
                    var pairs = Flatten(o, j => inner, q.Syntax, out var outer, out var within, whole: true);
                    var matched = FilterAt(pairs, i => JoinKeysEqual(Apply(okey, o.Elem(outer(i))), Apply(ikey, inner.Elem(within(i))), okey.body.Type), q.Syntax);
                    var sx = (sel.body, sel.p1, (IParameterSymbol)null);
                    // (the matched pair i is pair ix[i]: its outer and inner elements)
                    var joined = new LSeq
                    {
                        Length = matched.Length,
                        Type = resultElem,
                        Elem = i => KLet.Of("q$" + sel.p2.Name, inner.Elem(within(matched.Index(i))), Apply(sx, o.Elem(outer(matched.Index(i))))),
                    };
                    // (the database's: in no order of its sources', SQL Server's hash join keeping no outer row's matches together)
                    return _inDatabase > 0 ? Sort(joined, new List<((IOperation, IParameterSymbol, IParameterSymbol), ITypeSymbol, bool)>(), q.Syntax) : joined;
                }
                // (one sequence, then the other; Union: their elements' first occurrences, as Distinct of that)
                case "Concat" or "Union" when args.Count == 2:
                {
                    var a = Sequence(args[0].Value);
                    var b = Sequence(args[1].Value);
                    var both = new LSeq
                    {
                        Length = Plus(a.Length, b.Length),
                        Type = a.Type,
                        Elem = i => Ite(Lt(i, a.Length), a.Elem(i), b.Elem(Minus(i, a.Length))),
                    };
                    if (m.Name == "Concat")
                    {
                        return _inDatabase > 0 ? Sort(both, new List<((IOperation, IParameterSymbol, IParameterSymbol), ITypeSymbol, bool)>(), q.Syntax) : both;
                    }
                    var union = FilterAt(both, Unseen(both.Length, (k, j) => SameValue(both.Elem(k), both.Elem(j), both.Type), q.Syntax), q.Syntax);
                    return _inDatabase > 0 ? Sort(union, new List<((IOperation, IParameterSymbol, IParameterSymbol), ITypeSymbol, bool)>(), q.Syntax) : union;
                }
                // (groups as values, of a selector that reads their key and count: GroupValue. A database's counts are
                // bounds; LINQ to Objects' are exact: how many of the source have the key)
                case "GroupBy" when args.Count == 2 || args.Count == 3 && _inDatabase == 0 && LambdaArg(q, 2).p2 != null:
                {
                    var src = Sequence(args[0].Value);
                    var key = LambdaArg(q, 1);
                    // (a group: the index in the source of its key's first element; each key's first, in order)
                    var firsts = FilterAt(src, Unseen(src.Length, (k, j) => SameValue(Apply(key, src.Elem(k)), Apply(key, src.Elem(j)), key.body.Type), q.Syntax), q.Syntax);
                    // (how many of the source have its key: at least the one, at most all)
                    var count = new KVar(LinqMap("[int]int"));
                    ShapeFact(Over(KLit.Zero, src.Length, j => AndAlso(Le(KLit.One, Sel(count, j)), Le(Sel(count, j), src.Length))), q.Syntax);
                    if (_inDatabase == 0)
                    {
                        // (exactly: a running count of those with j's key, over the source)
                        var rc = new KVar(LinqMap("[int][int]int"));
                        KExpr R(KExpr j, KExpr k) => Sel(rc, j, k);
                        LinqFact(Over(KLit.Zero, src.Length, j => Eq(R(j, KLit.Zero), KLit.Zero)), q.Syntax);
                        LinqFact(Over(KLit.Zero, src.Length, j => Over(KLit.Zero, src.Length, k =>
                            Eq(R(j, Plus(k, KLit.One)), Plus(R(j, k), Ite(SameValue(Apply(key, src.Elem(k)), Apply(key, src.Elem(j)), key.body.Type), KLit.One, KLit.Zero))))), q.Syntax);
                        LinqFact(Over(KLit.Zero, src.Length, j => Eq(Sel(count, j), R(j, src.Length))), q.Syntax);
                    }
                    _groupsOf[q] = (src, key, count);
                    var groups = new LSeq
                    {
                        Length = firsts.Length,
                        Elem = firsts.Index,
                        Type = resultElem,
                        Groups = q,
                    };
                    // (GroupBy(key, (k, g) => ...): each group's key and itself, to the selector)
                    if (args.Count == 3)
                    {
                        var sel = LambdaArg(q, 2);
                        _groupParams[sel.p2] = (src, key, count);
                        return new LSeq
                        {
                            Length = firsts.Length,
                            Type = resultElem,
                            Elem = i => Apply(sel, Apply(key, src.Elem(firsts.Index(i))), firsts.Index(i)),
                        };
                    }
                    if (_inDatabase == 0)
                    {
                        return groups;
                    }
                    var sorted = Sort(groups, new List<((IOperation, IParameterSymbol, IParameterSymbol), ITypeSymbol, bool)>(), q.Syntax);
                    sorted.Groups = q;
                    return sorted;
                }
                // (each outer element with its matches, as the selector reads them: their count)
                case "GroupJoin" when args.Count == 5 && _inDatabase > 0:
                {
                    var o = Sequence(args[0].Value);
                    var inner = Sequence(args[1].Value);
                    var sel = LambdaArg(q, 4);
                    var count = new KVar(LinqMap("[int]int"));
                    ShapeFact(Over(KLit.Zero, o.Length, j => AndAlso(Le(KLit.Zero, Sel(count, j)), Le(Sel(count, j), inner.Length))), q.Syntax);
                    _groupParams[sel.p2] = (inner, null, count);
                    // (the selector's second parameter: the outer element's index, which its count is read at)
                    var joined = new LSeq
                    {
                        Length = o.Length,
                        Elem = i => Apply(sel, o.Elem(i), i),
                        Type = resultElem,
                    };
                    return _inDatabase > 0 ? Sort(joined, new List<((IOperation, IParameterSymbol, IParameterSymbol), ITypeSymbol, bool)>(), q.Syntax) : joined;
                }
                // (each outer element with its matches, in LINQ to Objects: how many, exactly, as the selector reads them)
                case "GroupJoin" when args.Count == 5 && _inDatabase == 0:
                {
                    var o = Sequence(args[0].Value);
                    var inner = Sequence(args[1].Value);
                    var (okey, ikey, sel) = (LambdaArg(q, 2), LambdaArg(q, 3), LambdaArg(q, 4));
                    var count = new KVar(LinqMap("[int]int"));
                    var rc = new KVar(LinqMap("[int][int]int"));
                    KExpr R(KExpr j, KExpr k) => Sel(rc, j, k);
                    LinqFact(Over(KLit.Zero, o.Length, j => Eq(R(j, KLit.Zero), KLit.Zero)), q.Syntax);
                    LinqFact(Over(KLit.Zero, o.Length, j => Over(KLit.Zero, inner.Length, k =>
                        Eq(R(j, Plus(k, KLit.One)), Plus(R(j, k), Ite(JoinKeysEqual(Apply(okey, o.Elem(j)), Apply(ikey, inner.Elem(k)), okey.body.Type), KLit.One, KLit.Zero))))), q.Syntax);
                    LinqFact(Over(KLit.Zero, o.Length, j => Eq(Sel(count, j), R(j, inner.Length))), q.Syntax);
                    ShapeFact(Over(KLit.Zero, o.Length, j => AndAlso(Le(KLit.Zero, Sel(count, j)), Le(Sel(count, j), inner.Length))), q.Syntax);
                    _groupParams[sel.p2] = (inner, null, count);
                    return new LSeq
                    {
                        Length = o.Length,
                        Elem = i => Apply(sel, o.Elem(i), i),
                        Type = resultElem,
                    };
                }
                // (RightJoin: each inner element, in order, with its matches in the outer's order, or with none (the default)
                // where it has none, as LeftJoin's the other way round)
                case "RightJoin" when args.Count == 5 && _inDatabase == 0:
                {
                    var o = Sequence(args[0].Value);
                    var inner = Sequence(args[1].Value);
                    var (okey, ikey, sel) = (LambdaArg(q, 2), LambdaArg(q, 3), LambdaArg(q, 4));
                    var none = IsNullable(sel.p1.Type) ? KLit.Null : Default(sel.p1.Type) ?? throw new NotTranslated("a RightJoin's default of " + sel.p1.Type);
                    var ext = new LSeq
                    {
                        Length = Plus(o.Length, KLit.One),
                        Type = o.Type,
                        Elem = j => Ite(Lt(j, o.Length), o.Elem(j), none),
                    };
                    var pairs = Flatten(inner, k => ext, q.Syntax, out var byInner, out var within, whole: true);
                    KExpr Match(KExpr j, KExpr k) => JoinKeysEqual(Apply(okey, o.Elem(j)), Apply(ikey, inner.Elem(k)), okey.body.Type);
                    var kept = FilterAt(pairs, i => Ite(Lt(within(i), o.Length), Match(within(i), byInner(i)),
                        Not(new KQuantOver(this, KLit.Zero, o.Length, j => Match(j, byInner(i)), forall: false).Q)), q.Syntax);
                    var sx = (sel.body, sel.p1, (IParameterSymbol)null);
                    return new LSeq
                    {
                        Length = kept.Length,
                        Type = resultElem,
                        Elem = i => KLet.Of("q$" + sel.p2.Name, inner.Elem(byInner(kept.Index(i))), Apply(sx, ext.Elem(within(kept.Index(i))))),
                    };
                }
                // (LeftJoin: each outer element, in order, with its matches in the inner's order, or with none (the
                // default) where it has none: the pairs of an outer element and an inner one, or the default after them,
                // that are kept)
                case "LeftJoin" when args.Count == 5:
                {
                    var o = Sequence(args[0].Value);
                    var inner = Sequence(args[1].Value);
                    var (okey, ikey, sel) = (LambdaArg(q, 2), LambdaArg(q, 3), LambdaArg(q, 4));
                    var none = IsNullable(sel.p2.Type) ? KLit.Null : Default(sel.p2.Type) ?? throw new NotTranslated("a LeftJoin's default of " + sel.p2.Type);
                    var ext = new LSeq
                    {
                        Length = Plus(inner.Length, KLit.One),
                        Type = inner.Type,
                        Elem = k => Ite(Lt(k, inner.Length), inner.Elem(k), none),
                    };
                    var pairs = Flatten(o, j => ext, q.Syntax, out var outer, out var within, whole: true);
                    KExpr Match(KExpr j, KExpr k) => JoinKeysEqual(Apply(okey, o.Elem(j)), Apply(ikey, inner.Elem(k)), okey.body.Type);
                    var kept = FilterAt(pairs, i => Ite(Lt(within(i), inner.Length), Match(outer(i), within(i)),
                        Not(new KQuantOver(this, KLit.Zero, inner.Length, k => Match(outer(i), k), forall: false).Q)), q.Syntax);
                    var sx = (sel.body, sel.p1, (IParameterSymbol)null);
                    var joined = new LSeq
                    {
                        Length = kept.Length,
                        Type = resultElem,
                        Elem = i => KLet.Of("q$" + sel.p2.Name, ext.Elem(within(kept.Index(i))), Apply(sx, o.Elem(outer(kept.Index(i))))),
                    };
                    return _inDatabase > 0 ? Sort(joined, new List<((IOperation, IParameterSymbol, IParameterSymbol), ITypeSymbol, bool)>(), q.Syntax) : joined;
                }
                default: throw new NotTranslated("LINQ's " + m.Name);
            }
        }

        /// <summary>A GroupBy's groups, by a loop's variable: the source read where the loop started (Map), and its key.</summary>
        private readonly Dictionary<ILocalSymbol, (string map, (IOperation, IParameterSymbol, IParameterSymbol) key, ITypeSymbol elem, string count)> _groups =
            new Dictionary<ILocalSymbol, (string, (IOperation, IParameterSymbol, IParameterSymbol), ITypeSymbol, string)>(SymbolEqualityComparer.Default);

        private static bool IsGrouping(ITypeSymbol t) => t is INamedTypeSymbol { Name: "IGrouping", Arity: 2 } g && g.ContainingNamespace?.ToDisplayString() == "System.Linq";

        /// <summary>A foreach over a query (or over a group of one): recorded, to be read where the loop starts.</summary>
        private bool QueryForEach(Microsoft.CodeAnalysis.CSharp.Syntax.CommonForEachStatementSyntax fs, IForEachLoopOperation fo, ControlFlowGraph cfg, IOperation collection)
        {
            var src = collection;
            while (src is ITranslatedQueryOperation tq)
            {
                src = Unconverted(tq.Operation);
            }
            ILocalSymbol groupOf = src is ILocalReferenceOperation gl && IsGrouping(gl.Type) ? gl.Local : null;
            // (a GroupJoin's rows, and a row's group: row.os)
            ILocalSymbol joinGroupOf = src is IPropertyReferenceOperation { Instance: ILocalReferenceOperation jr } jp && _joinRows.TryGetValue(jr.Local, out var jrow) &&
                                       jrow.members.TryGetValue(jp.Property.Name, out var jm) && jm == "group" ? jr.Local : null;
            bool joinRows = src is IInvocationOperation gjq && IsEnumerableCall(gjq.TargetMethod) && gjq.TargetMethod.Name == "GroupJoin";
            // (and a collection interface's, a variable's: read where the loop starts, as a query is)
            if (groupOf == null && joinGroupOf == null && !(src is IInvocationOperation q && IsEnumerableCall(q.TargetMethod)) &&
                !(IsCollectionInterface(src.Type) && src is IParameterReferenceOperation or ILocalReferenceOperation))
            {
                return false;
            }
            var element = fo.Locals.FirstOrDefault()?.Type;
            if (element == null || !(InSubset(element) || IsGrouping(element) || joinRows))
            {
                return false;
            }
            if (joinRows)
            {
                var members = JoinRowMembers((IInvocationOperation)src);
                foreach (var l in fo.Locals)
                {
                    _joinRows[l] = ((IInvocationOperation)src, members, null);
                    // (a row is its outer element's index)
                    if (!_p.Locals.Any(x => x.Name == Local(l)))
                    {
                        _p.Locals.Add(KLocal.Of(Local(l), "int"));
                    }
                }
            }
            var capture = cfg.Blocks.SelectMany(b => b.Operations).OfType<IFlowCaptureOperation>()
                .FirstOrDefault(c => c.Syntax == fs.Expression && c.Value is IInvocationOperation gi && gi.TargetMethod.Name == "GetEnumerator");
            var head = capture == null ? null : cfg.Blocks.FirstOrDefault(b => b.BranchValue is IInvocationOperation mn && mn.TargetMethod.Name == "MoveNext" &&
                                                                               mn.Instance is IFlowCaptureReferenceOperation r && r.Id.Equals(capture.Id));
            if (head == null)
            {
                return false;
            }
            var n = _forEachAt.Count;
            var fe = new ForEach
            {
                Head = head.Ordinal,
                Index = Declare($"fe${n}$i", _model.Compilation.GetSpecialType(SpecialType.System_Int32)),
                Type = collection.Type,
                Element = element,
                At = fs.Expression,
                Query = groupOf == null && joinGroupOf == null ? src : null,
                GroupOf = groupOf,
                JoinGroupOf = joinGroupOf,
                Mat = "fe$" + n + "$m",
                Count = Declare($"fe${n}$n", _model.Compilation.GetSpecialType(SpecialType.System_Int32)),
            };
            _p.Locals.Add(KLocal.Of(fe.Mat, "[int]" + (IsGrouping(element) || joinRows ? "int" : TypeOf(element))));
            _forEach[capture.Id] = fe;
            _forEachAt[head.Ordinal] = fe;
            foreach (var l in fo.Locals)
            {
                _forEachOf[l] = fe;
            }
            for (var region = head.EnclosingRegion; region != null; region = region.EnclosingRegion)
            {
                if (region.Kind == ControlFlowRegionKind.Try && region.EnclosingRegion?.Kind == ControlFlowRegionKind.TryAndFinally)
                {
                    _erased.Add(region.EnclosingRegion);
                    break;
                }
            }
            return true;
        }

        /// <summary>A foreach over a query starts: what it gives read now, into the loop's map (a GroupBy's: each group's first index).</summary>
        private void StartQueryLoop(ForEach fe)
        {
            var at = fe.At;
            LSeq seq;
            if (fe.GroupOf != null)
            {
                // (a group: the elements of its source, as read where the groups were, whose key is the group's)
                if (!_groups.TryGetValue(fe.GroupOf, out var g))
                {
                    throw new NotTranslated("a group not of a GroupBy read here");
                }
                var src = new LSeq
                {
                    Length = new KVar(g.count),
                    Elem = i => Sel(g.map, i),
                    Type = g.elem,
                };
                var gv = new KVar(Declare(Local(fe.GroupOf), fe.GroupOf.Type));
                seq = Filter(src, x => SameValue(Apply(g.key, x), Apply(g.key, src.Elem(gv)), g.key.Item1.Type), at);
            }
            else if (fe.JoinGroupOf != null)
            {
                // (a GroupJoin row's group: the inner elements, as read where the rows were, whose key is the row's outer element's)
                var j = _joinRows[fe.JoinGroupOf].read ?? throw new NotTranslated("a GroupJoin's group not of its rows read here");
                var rv = new KVar(Declare(Local(fe.JoinGroupOf), fe.JoinGroupOf.Type));
                var inner = new LSeq
                {
                    Length = new KVar(j.innerCount),
                    Elem = i => Sel(j.innerMap, i),
                    Type = j.innerType,
                };
                var outerElem = Sel(j.outerMap, rv);
                seq = Filter(inner, x => SameValue(Apply(j.ikey, x), Apply(j.okey, outerElem), j.okey.Item1.Type), at);
            }
            else if (Unconverted(fe.Query) is IInvocationOperation gj && gj.TargetMethod.Name == "GroupJoin" && gj.Arguments.Length == 5)
            {
                // (a GroupJoin: a row for each outer element, in order, its group the inner ones of its key; both read now)
                var args = gj.Arguments.OrderBy(a => a.Parameter.Ordinal).ToList();
                var outer = Sequence(args[0].Value);
                var innerSrc = Sequence(args[1].Value);
                var (okey, ikey) = (LambdaArg(gj, 2), LambdaArg(gj, 3));
                string Read(LSeq sq)
                {
                    var map = LinqMap("[int]" + TypeOf(sq.Type));
                    LinqFact(Over(KLit.Zero, sq.Length, i => Eq(Sel(map, i), sq.Elem(i))), at);
                    return map;
                }
                var oc = Declare("t$" + _temps++, _model.Compilation.GetSpecialType(SpecialType.System_Int32));
                Emit(KAssign.Of(oc, outer.Length));
                var ic = Declare("t$" + _temps++, _model.Compilation.GetSpecialType(SpecialType.System_Int32));
                Emit(KAssign.Of(ic, innerSrc.Length));
                var read = (outerMap: Read(outer), outerCount: oc, innerMap: Read(innerSrc), innerCount: ic, okey, ikey, outerType: outer.Type, innerType: innerSrc.Type);
                foreach (var l in _forEachOf.Where(kv => kv.Value == fe).Select(kv => kv.Key))
                {
                    _joinRows[l] = (_joinRows[l].join, _joinRows[l].members, read);
                }
                seq = new LSeq
                {
                    Length = new KVar(oc),
                    Elem = i => i,
                    Type = fe.Element,
                };
            }
            else if (Unconverted(fe.Query) is IInvocationOperation gb && gb.TargetMethod.Name == "GroupBy" && gb.Arguments.Length == 2 && IsGrouping(fe.Element))
            {
                var source = Sequence(gb.Arguments.First(a => a.Parameter.Ordinal == 0).Value);
                var key = LambdaArg(gb, 1);
                var map = LinqMap("[int]" + TypeOf(source.Type));
                var count = Declare("t$" + _temps++, _model.Compilation.GetSpecialType(SpecialType.System_Int32));
                Emit(KAssign.Of(count, source.Length));
                LinqFact(Over(KLit.Zero, new KVar(count), i => Eq(Sel(map, i), source.Elem(i))), at);
                var read = new LSeq
                {
                    Length = new KVar(count),
                    Elem = i => Sel(map, i),
                    Type = source.Type,
                };
                // (the groups in the order their keys first appear: each one's first index)
                var firsts = FilterAt(read, Unseen(read.Length, (k, j) => SameValue(Apply(key, read.Elem(k)), Apply(key, read.Elem(j)), key.body.Type), at), at);
                seq = new LSeq
                {
                    Length = firsts.Length,
                    Elem = firsts.Index,
                    Type = fe.Element,
                };
                foreach (var l in _forEachOf.Where(kv => kv.Value == fe).Select(kv => kv.Key))
                {
                    _groups[l] = (map, key, source.Type, count);
                }
            }
            else
            {
                seq = Sequence(fe.Query);
            }
            Emit(KAssign.Of(fe.Count, seq.Length));
            Emit(KHavoc.Of(fe.Mat));
            LinqFact(Over(KLit.Zero, new KVar(fe.Count), i => Eq(Sel(fe.Mat, i), seq.Elem(i))), at);
            Emit(KAssign.Of(fe.Index, KLit.Zero));
        }

        /// <summary>A GroupJoin's rows by their variable: the query, what each member of a row is (the outer element, or the group), and what was read where the loop started.</summary>
        private readonly Dictionary<ILocalSymbol, (IInvocationOperation join, Dictionary<string, string> members,
            (string outerMap, string outerCount, string innerMap, string innerCount, (IOperation, IParameterSymbol, IParameterSymbol) okey, (IOperation, IParameterSymbol, IParameterSymbol) ikey, ITypeSymbol outerType, ITypeSymbol innerType)? read)> _joinRows =
            new Dictionary<ILocalSymbol, (IInvocationOperation, Dictionary<string, string>, (string, string, string, string, (IOperation, IParameterSymbol, IParameterSymbol), (IOperation, IParameterSymbol, IParameterSymbol), ITypeSymbol, ITypeSymbol)?)>(SymbolEqualityComparer.Default);

        /// <summary>A GroupJoin's result selector, (c, os) => new { c, os }: each member of the row, "outer" or "group".</summary>
        private static Dictionary<string, string> JoinRowMembers(IInvocationOperation join)
        {
            var arg = Unconverted(join.Arguments.First(a => a.Parameter.Ordinal == 4).Value);
            if (arg is IDelegateCreationOperation dc)
            {
                arg = Unconverted(dc.Target);
            }
            if (!(arg is IAnonymousFunctionOperation f) || f.Symbol.Parameters.Length != 2 || f.Body.Operations.Length != 1 ||
                !(f.Body.Operations[0] is IReturnOperation { ReturnedValue: var rv } && Unconverted(rv) is IAnonymousObjectCreationOperation ao))
            {
                throw new NotTranslated("a GroupJoin whose result isn't an anonymous object of its row and its group");
            }
            var members = new Dictionary<string, string>();
            foreach (var init in ao.Initializers)
            {
                if (!(init is ISimpleAssignmentOperation { Target: IPropertyReferenceOperation tp, Value: var v } && Unconverted(v) is IParameterReferenceOperation pr))
                {
                    throw new NotTranslated("a GroupJoin's result member that isn't its row or its group");
                }
                members[tp.Property.Name] = SymbolEqualityComparer.Default.Equals(pr.Parameter, f.Symbol.Parameters[0]) ? "outer" : "group";
            }
            return members;
        }

        /// <summary>A GroupJoin row's outer member (row.c): the outer element at the row's index; null for anything else.</summary>
        private KExpr JoinRowMember(IPropertyReferenceOperation p)
        {
            if (!(p.Instance is ILocalReferenceOperation l) || !_joinRows.TryGetValue(l.Local, out var row) || !row.members.TryGetValue(p.Property.Name, out var kind))
            {
                return null;
            }
            if (kind != "outer")
            {
                throw new NotTranslated("a GroupJoin's group other than as a foreach's");
            }
            if (row.read == null)
            {
                throw new NotTranslated("a GroupJoin's row not read here");
            }
            return Sel(row.read.Value.outerMap, new KVar(Declare(Local(l.Local), l.Local.Type)));
        }

        /// <summary>A group's Key: its first element's key.</summary>
        private KExpr GroupKey(ILocalSymbol g)
        {
            if (!_groups.TryGetValue(g, out var info))
            {
                throw new NotTranslated("a group not of a GroupBy read here");
            }
            return Apply(info.key, Sel(info.map, new KVar(Local(g))));
        }

        /// <summary>The sequence a lambda's value is (an array, a List): its length and elements.</summary>
        private LSeq Inner(KExpr value, IOperation body)
        {
            var type = Unconverted(body).Type;
            var elem = ElementOf(type);
            if (IsArray(type))
            {
                return new LSeq
                {
                    Length = Length(value),
                    Elem = i => Sel(Elements(type), value, i),
                    Type = elem,
                };
            }
            if (IsList(type))
            {
                foreach (var m in ModelsOf((INamedTypeSymbol)type))
                {
                    _p.Models[m.Name] = m;
                }
                return new LSeq
                {
                    Length = Sel(SizeMap, value),
                    Elem = i => Sel(ModelOf("Items", (INamedTypeSymbol)type).Name, value, i),
                    Type = elem,
                };
            }
            throw new NotTranslated("an inner sequence of " + type);
        }

        /// <summary>
        /// Sequences one after another, one for each element of src: offsets o[j] (o[0] = 0, o[j + 1] = o[j] + the
        /// length of j's, never decreasing), element i at outer index out[i] and index i - o[out[i]] within it.
        /// </summary>
        /// <param name="whole">each inner sequence the same, whatever the element (a join's): its offsets are what the result is</param>
        private LSeq Flatten(LSeq src, Func<KExpr, LSeq> inner, SyntaxNode at, out Func<KExpr, KExpr> outer, out Func<KExpr, KExpr> within, bool whole = false)
        {
            var o = new KVar(LinqMap("[int]int"));
            var ov = new KVar(LinqMap("[int]int"));
            var n = src.Length;
            KExpr O(KExpr j) => Sel(o, j);
            KExpr Out(KExpr i) => Sel(ov, i);
            ShapeFact(Eq(O(KLit.Zero), KLit.Zero), at);
            var offsets = Over(KLit.Zero, n, j => AndAlso(Eq(O(Plus(j, KLit.One)), Plus(O(j), inner(j).Length)), Le(KLit.Zero, inner(j).Length)));
            if (whole)
            {
                ShapeFact(offsets, at);
            } else
            {
                LinqFact(offsets, at);
            }
            // (monotone: an offset is no more than any later one)
            ShapeFact(Over(KLit.Zero, Plus(n, KLit.One), a => Over(a, Plus(n, KLit.One), b => Le(O(a), O(b)))), at);
            ShapeFact(Over(KLit.Zero, O(n), i => AndAlso(Between(KLit.Zero, Out(i), n), AndAlso(Le(O(Out(i)), i), Lt(i, O(Plus(Out(i), KLit.One)))))), at);
            outer = Out;
            within = i => Minus(i, O(Out(i)));
            Func<KExpr, KExpr> w = within;
            return new LSeq
            {
                Length = O(n),
                Elem = i => inner(Out(i)).Elem(w(i)),
                Type = inner(KLit.Zero).Type,
            };
        }

        /// <summary>Two keys a join matches: equal, and a nullable one with a value (null matches nothing, in LINQ's Join and in SQL's).</summary>
        private KExpr JoinKeysEqual(KExpr a, KExpr b, ITypeSymbol t) =>
            IsNullableValue(t) && Scalar(Underlying(t))
                ? AndAlso(AndAlso(NotNull(a), NotNull(b)), Eq(NullableValue(a, t), NullableValue(b, t)))
                : SameValue(a, b, t);

        /// <summary>Elements equal as EqualityComparer&lt;T&gt;.Default has them: values and references, a tuple by its parts.</summary>
        private static KExpr SameValue(KExpr a, KExpr b, ITypeSymbol t)
        {
            if (IsTuple(t))
            {
                var parts = PartsOf(t);
                KExpr all = KLit.True;
                for (int k = 0; k < parts.Count; k++)
                {
                    all = AndAlso(all, SameValue(TupleItem(a, t, k), TupleItem(b, t, k), parts[k]));
                }
                return all;
            }
            if (Scalar(t) || IsClass(t) || IsInterface(t) || t.SpecialType == SpecialType.System_Object)
            {
                return Eq(a, b);
            }
            // (strings by their content, as string.Equals has them)
            if (IsString(t))
            {
                return new KOp("streq", a, b);
            }
            throw new NotTranslated("LINQ's equality of " + t);
        }

        /// <summary>
        /// Whether no element before j is the same as it (Q.Unseen: each first occurrence), as a map of its own: where it
        /// is, none before is; where it isn't, seen[j] is one before that is. Not the existential itself, inside the
        /// count's facts: each instance of that made an element the solver hadn't, whose own instances made more, so a
        /// failing proof never saturated them.
        /// </summary>
        private Func<KExpr, KExpr> Unseen(KExpr n, Func<KExpr, KExpr, KExpr> same, SyntaxNode at)
        {
            var first = new KVar(LinqMap("[int]bool"));
            var seen = new KVar(LinqMap("[int]int"));
            KExpr First(KExpr j) => Sel(first, j);
            KExpr Seen(KExpr j) => Sel(seen, j);
            LinqFact(Over(KLit.Zero, n, j => Implies(First(j), Over(KLit.Zero, j, k => Not(same(k, j))))), at);
            LinqFact(Over(KLit.Zero, n, j => Implies(Not(First(j)), AndAlso(Between(KLit.Zero, Seen(j), j), same(Seen(j), j)))), at);
            return First;
        }

        private sealed class KQuantOver
        {
            public KQuant Q;
            public KQuantOver(Lowering l, KExpr lo, KExpr hi, Func<KExpr, KExpr> body, bool forall)
            {
                Q = l.Over(lo, hi, body, forall);
            }
        }

        /// <summary>
        /// Of a filter, where at most one element matching is to be shown: two matches are at two indices, the first
        /// before the second (what its facts say; said of indices 0 and 1, for the solver to find them).
        /// </summary>
        private void AtMostOneHint(LSeq s, SyntaxNode at)
        {
            if (s.Index == null)
            {
                return;
            }
            LinqFact(Implies(Ge(s.Length, new KLit("2")), Lt(s.Index(KLit.Zero), s.Index(KLit.One))), at);
        }

        private LSeq Filter(LSeq src, Func<KExpr, KExpr> pred, SyntaxNode at) => FilterAt(src, j => pred(src.Elem(j)), at);

        /// <summary>
        /// A filter: c[j] the matches before j (c[0] = 0, one more at each j that matches), ix[i] the i-th match's index,
        /// increasing; its length c[n], its element i the source's ix[i].
        /// </summary>
        private LSeq FilterAt(LSeq src, Func<KExpr, KExpr> keep, SyntaxNode at)
        {
            var c = new KVar(LinqMap("[int]int"));
            var ix = new KVar(LinqMap("[int]int"));
            var n = src.Length;
            KExpr C(KExpr j) => Sel(c, j);
            KExpr Ix(KExpr i) => Sel(ix, i);
            ShapeFact(Eq(C(KLit.Zero), KLit.Zero), at);
            LinqFact(Over(KLit.Zero, n, j => Eq(C(Plus(j, KLit.One)), Plus(C(j), Ite(keep(j), KLit.One, KLit.Zero)))), at);
            ShapeFact(Over(KLit.Zero, Plus(n, KLit.One), j => AndAlso(Le(KLit.Zero, C(j)), Le(C(j), j))), at);
            LinqFact(Over(KLit.Zero, n, j => Implies(keep(j), Eq(Ix(C(j)), j))), at);
            LinqFact(Over(KLit.Zero, C(n), i => AndAlso(AndAlso(Between(KLit.Zero, Ix(i), n), keep(Ix(i))), Eq(C(Ix(i)), i))), at);
            // (of two indices there are: one alone would make the next, and so on without end)
            var increasing = Over(KLit.Zero, Minus(C(n), KLit.One), i => Lt(Ix(i), Ix(Plus(i, KLit.One))));
            var iv = new KVar(increasing.Var);
            increasing.Trigger = new KExpr[] { new KOp("$pattern", Ix(iv), Ix(Plus(iv, KLit.One))) };
            LinqFact(increasing, at);
            return new LSeq
            {
                Length = C(n),
                Elem = i => src.Elem(Ix(i)),
                Type = src.Type,
                Index = Ix,
            };
        }

        /// <summary>
        /// A stable sort: element i is the source's p[i], p a bijection (q its inverse), in the keys' order (the first,
        /// then the next among equal ones); keys are ordered where they are integers or chars, from the first that
        /// isn't, only those before it are.
        /// </summary>
        private LSeq Sort(LSeq src, List<((IOperation, IParameterSymbol, IParameterSymbol) key, ITypeSymbol type, bool down)> keys, SyntaxNode at)
        {
            var p = new KVar(LinqMap("[int]int"));
            var qv = new KVar(LinqMap("[int]int"));
            var n = src.Length;
            KExpr P(KExpr i) => Sel(p, i);
            KExpr Q(KExpr j) => Sel(qv, j);
            ShapeFact(Over(KLit.Zero, n, i => AndAlso(Between(KLit.Zero, P(i), n), Eq(Q(P(i)), i))), at);
            ShapeFact(Over(KLit.Zero, n, j => AndAlso(Between(KLit.Zero, Q(j), n), Eq(P(Q(j)), j))), at);
            int prefix = keys.TakeWhile(k => k.type != null && (IsIntegral(k.type) || k.type.SpecialType == SpecialType.System_Char)).Count();
            KExpr Key(int k, KExpr j) => Apply(keys[k].key, src.Elem(j));
            KExpr InOrder(KExpr a, KExpr b, int level)
            {
                if (level == prefix)
                {
                    return prefix == keys.Count ? Lt(a, b) : KLit.True;
                }
                var (x, y) = (Key(level, a), Key(level, b));
                return OrElse(keys[level].down ? Gt(x, y) : Lt(x, y), AndAlso(Eq(x, y), InOrder(a, b, level + 1)));
            }
            if (prefix > 0)
            {
                LinqFact(Over(KLit.Zero, Minus(n, KLit.One), i => InOrder(P(i), P(Plus(i, KLit.One)), 0)), at);
            }
            return new LSeq
            {
                Length = n,
                Elem = i => src.Elem(P(i)),
                Type = src.Type,
            };
        }

        /// <summary>A call of Enumerable read here (in code): a query copied (ToArray, ToList), or read (Count, Sum, Max, ...).</summary>
        /// <param name="name">the operator, where the call is another's form of it (EF's ...Async, awaited); its own by default</param>
        /// <param name="resultType">what it gives, there (the awaited task's T)</param>
        /// <summary>List's Find, FindIndex, Exists and TrueForAll of a pure lambda: the first match, its index (-1 if none), Any, All.</summary>
        private KExpr ListPredicate(IInvocationOperation call)
        {
            var at = call.Syntax;
            var s = Sequence(call.Instance);
            var f = LambdaArg(call, 0);
            var t = Declare("t$" + _temps++, call.Type);
            Emit(KHavoc.Of(t));
            var v = new KVar(t);
            KExpr P(KExpr x) => Apply(f, x);
            switch (call.TargetMethod.Name)
            {
                case "Exists":
                    ShapeFact(Eq(v, Over(KLit.Zero, s.Length, i => P(s.Elem(i)), forall: false)), at);
                    break;
                case "TrueForAll":
                    ShapeFact(Eq(v, Over(KLit.Zero, s.Length, i => P(s.Elem(i)))), at);
                    break;
                case "Find":
                {
                    if (!(Default(call.Type) is KExpr dflt))
                    {
                        throw new NotTranslated("a default of " + call.Type);
                    }
                    var m = Filter(s, P, at);
                    ShapeFact(Eq(v, Ite(Gt(m.Length, KLit.Zero), m.Elem(KLit.Zero), dflt)), at);
                    break;
                }
                default: // FindIndex
                    ShapeFact(AndAlso(Le(KLit.MinusOne, v), Lt(v, s.Length)), at);
                    ShapeFact(Ite(Eq(v, KLit.MinusOne), Over(KLit.Zero, s.Length, i => Not(P(s.Elem(i)))),
                                      AndAlso(P(s.Elem(v)), Over(KLit.Zero, v, i => Not(P(s.Elem(i)))))), at);
                    break;
            }
            return v;
        }

        private KExpr Linq(IInvocationOperation call, string name = null, ITypeSymbol resultType = null)
        {
            // (of a database query: its lambdas, the database's to evaluate)
            bool database = KernelTypes.Ef != null && DatabaseRoot(call, out _) != null;
            if (!database && name == null && ElementwiseKind(call) == "each")
            {
                return Elementwise(call);
            }
            var known = _known;
            var result = _dbResult;
            // (the query's last operator: what it gives, entities or not)
            if (database && _inDatabase == 0)
            {
                _dbResult = resultType ?? call.Type;
            }
            bool untranslatable = database && TranslationChecks(call);
            if (database)
            {
                _inDatabase++;
            }
            try
            {
                // (a query EF can't translate throws where it runs, CSV1032: what it would give isn't known)
                if (untranslatable)
                {
                    var type = resultType ?? call.Type;
                    if (!InSubset(type))
                    {
                        throw new NotTranslated("a query's result of " + type);
                    }
                    var t = Declare("t$" + _temps++, type);
                    Emit(KHavoc.Of(t));
                    return new KVar(t);
                }
                return LinqCore(call, name, resultType);
            }
            finally
            {
                if (database)
                {
                    _inDatabase--;
                }
                _known = known;
                _dbResult = result;
            }
        }

        private KExpr LinqCore(IInvocationOperation call, string name, ITypeSymbol resultType)
        {
            var m = call.TargetMethod;
            name ??= m.Name;
            var callType = resultType ?? call.Type;
            // (a CancellationToken an async form takes says nothing of what it gives)
            var args = call.Arguments.OrderBy(a => a.Parameter.Ordinal).Where(a => !IsToken(a.Parameter.Type)).ToList();
            var at = call.Syntax;
            void Need(KExpr cond, string text) => Emit(KCheck.Of(cond, "CSV1001", at, $"precondition '{text}' of '{name}' might not hold"));
            KExpr Value(KExpr v)
            {
                var t = Declare("t$" + _temps++, callType);
                Emit(KHavoc.Of(t));
                ShapeFact(Eq(new KVar(t), v), at);
                return new KVar(t);
            }
            LSeq Of(bool withPredicate)
            {
                var src = Sequence(args[0].Value);
                if (!withPredicate || args.Count == 1)
                {
                    return src;
                }
                var f = LambdaArg(call, 1);
                return Filter(src, x => Apply(f, x), at);
            }
            LSeq Mapped()
            {
                var src = Sequence(args[0].Value);
                if (args.Count == 1)
                {
                    return src;
                }
                var f = LambdaArg(call, 1);
                return new LSeq
                {
                    Length = src.Length,
                    Elem = i => Apply(f, src.Elem(i), i),
                    Type = ElementOf(callType) ?? f.body.Type,
                };
            }
            switch (name)
            {
                case "ToArray" when args.Count == 1 && IsArray(callType):
                {
                    var s = Sequence(args[0].Value);
                    var t = Declare("t$" + _temps++, callType);
                    Emit(KNew.Of(t, callType, s.Length));
                    Emit(KRow.Of(
                        Elements(callType),
                        new KVar(t),
                        MapLambda("j$: int", Ite(Between(KLit.Zero, new KVar("j$"), s.Length), s.Elem(new KVar("j$")), new KLit(Default(s.Type) is KLit d ? d.Text : "0")))));
                    return new KVar(t);
                }
                case "ToList" when args.Count == 1 && IsList(callType):
                {
                    var s = Sequence(args[0].Value);
                    var ctor = ((INamedTypeSymbol)callType).Constructors.FirstOrDefault(c => c.Parameters.Length == 0) ?? throw new NotTranslated("a List without its constructor");
                    var list = Invoke(ctor, null, new IArgumentOperation[0], at, null);
                    var t = Declare("t$" + _temps++, callType);
                    Emit(KAssign.Of(t, list));
                    var items = ModelOf("Items", (INamedTypeSymbol)callType);
                    Emit(KRow.Of(items.Name, new KVar(t), MapLambda("j$: int", s.Elem(new KVar("j$")))));
                    Emit(KRow.Of(SizeMap, new KVar(t), s.Length));
                    return new KVar(t);
                }
                case "Count" or "LongCount" when args.Count <= 2:
                    return Value(Of(true).Length);
                case "Any" when args.Count <= 2:
                    return Value(Gt(Of(true).Length, KLit.Zero));
                case "All" when args.Count == 2:
                {
                    var s = Sequence(args[0].Value);
                    var f = LambdaArg(call, 1);
                    return Value(Over(KLit.Zero, s.Length, i => Apply(f, s.Elem(i))));
                }
                // (a dictionary, of the library's: only where it throws, a key that's null or an earlier one's, as its definition says)
                case "ToDictionary" when args.Count is 2 or 3 && _inDatabase == 0 && IsCollection(callType) && LambdaArg(call, 1) is var kf && kf.p2 == null:
                {
                    var s = Sequence(args[0].Value);
                    KExpr K(KExpr i) => Apply(kf, s.Elem(i));
                    var keyType = kf.body.Type;
                    Need(Over(KLit.Zero, s.Length, i => AndAlso(IsNullable(keyType) ? NotNull(K(i)) : KLit.True,
                                                                    Not(new KQuantOver(this, KLit.Zero, i, j => SameValue(K(j), K(i), keyType), forall: false).Q))),
                         "Spec.Forall(0, Q.Count(source), i => keySelector(Q.At(source, i)) != null && Q.Unseen(Select(source, keySelector), i))");
                    var d = Declare("t$" + _temps++, callType);
                    Emit(KHavoc.Of(d));
                    ShapeFact(NotNull(new KVar(d)), at);
                    return new KVar(d);
                }
                // (two sequences of the same length, element by element the same)
                case "SequenceEqual" when args.Count == 2 && _inDatabase == 0:
                {
                    var a = Sequence(args[0].Value);
                    var b = Sequence(args[1].Value);
                    return Value(AndAlso(Eq(a.Length, b.Length), Over(KLit.Zero, a.Length, i => SameValue(a.Elem(i), b.Elem(i), a.Type))));
                }
                case "Contains" when args.Count == 2:
                {
                    var s = Sequence(args[0].Value);
                    var x = Expr(args[1].Value);
                    return Value(Over(KLit.Zero, s.Length, i => SameValue(s.Elem(i), x, s.Type), forall: false));
                }
                case "First" or "Last" or "FirstOrDefault" or "LastOrDefault" when args.Count <= 2:
                {
                    var s = Of(true);
                    AtMostOneHint(s, at);
                    DatabaseOrder(call, args[0].Value, s.Length);
                    var pos = name.StartsWith("First") ? KLit.Zero : (KExpr)Minus(s.Length, KLit.One);
                    if (!name.EndsWith("OrDefault"))
                    {
                        Need(Gt(s.Length, KLit.Zero), args.Count == 1 ? "Q.Count(source) > 0" : "a matching element");
                        return Value(s.Elem(pos));
                    }
                    if (!(Default(callType) is KExpr dflt))
                    {
                        throw new NotTranslated("a default of " + callType);
                    }
                    return Value(Ite(Gt(s.Length, KLit.Zero), s.Elem(pos), dflt));
                }
                case "Single" or "SingleOrDefault" when args.Count <= 2:
                {
                    // (one, or with OrDefault none, else InvalidOperationException: its precondition)
                    var s = Of(true);
                    AtMostOneHint(s, at);
                    var src = args.Count == 1 ? "Q.Count(source)" : "Q.Count(Where(source, predicate))";
                    if (name == "Single")
                    {
                        Need(Eq(s.Length, KLit.One), src + " == 1");
                        return Value(s.Elem(KLit.Zero));
                    }
                    Need(Le(s.Length, KLit.One), src + " <= 1");
                    if (!(Default(callType) is KExpr sd))
                    {
                        throw new NotTranslated("a default of " + callType);
                    }
                    return Value(Ite(Eq(s.Length, KLit.One), s.Elem(KLit.Zero), sd));
                }
                // (the first element whose key is least, or greatest: an integer key)
                case "MinBy" or "MaxBy" when args.Count == 2 && _inDatabase == 0 && LambdaArg(call, 1) is var by && by.p2 == null && IsIntegral(by.body.Type):
                {
                    var s = Sequence(args[0].Value);
                    Need(Gt(s.Length, KLit.Zero), "Q.Count(source) > 0");
                    var ix = Declare("t$" + _temps++, KernelTypes.Compilation.GetSpecialType(SpecialType.System_Int32));
                    Emit(KHavoc.Of(ix));
                    var iv = new KVar(ix);
                    KExpr Key(KExpr e) => Apply(by, e);
                    var better = name == "MinBy" ? "<" : ">";
                    LinqFact(AndAlso(Le(KLit.Zero, iv), Lt(iv, s.Length)), at);
                    LinqFact(Over(KLit.Zero, s.Length, i => Not(new KOp(better, Key(s.Elem(i)), Key(s.Elem(iv))))), at);
                    LinqFact(Over(KLit.Zero, iv, i => new KOp(better == "<" ? ">" : "<", Key(s.Elem(i)), Key(s.Elem(iv)))), at);
                    return Value(s.Elem(iv));
                }
                // (of doubles: Min is NaN where one is; Max passes NaNs over, NaN only where all are, as .NET compares them)
                case "Max" or "Min" when args.Count <= 2 && IsFloating(callType) && _inDatabase == 0:
                {
                    var s = Mapped();
                    Need(Gt(s.Length, KLit.Zero), "Q.Count(source) > 0");
                    var n = FloatSize(callType);
                    var r = Declare("t$" + _temps++, callType);
                    Emit(KHavoc.Of(r));
                    var rv = new KVar(r);
                    KExpr NaN(KExpr x) => new KOp("$fp.isNaN" + n, x);
                    var anyNaN = Over(KLit.Zero, s.Length, i => NaN(s.Elem(i)), forall: false);
                    var allNaN = Over(KLit.Zero, s.Length, i => NaN(s.Elem(i)));
                    LinqFact(Over(KLit.Zero, s.Length, i => Eq(s.Elem(i), rv), forall: false), at);
                    if (name == "Min")
                    {
                        LinqFact(Eq(NaN(rv), anyNaN), at);
                        LinqFact(Over(KLit.Zero, s.Length, i => OrElse(NaN(rv), new KOp("$fp.leq" + n, rv, s.Elem(i)))), at);
                    }
                    else
                    {
                        LinqFact(Eq(NaN(rv), allNaN), at);
                        LinqFact(Over(KLit.Zero, s.Length, i => OrElse(NaN(s.Elem(i)), new KOp("$fp.leq" + n, s.Elem(i), rv))), at);
                    }
                    return rv;
                }
                case "Max" or "Min" when args.Count <= 2 && IsIntegral(callType):
                {
                    var s = Mapped();
                    Need(Gt(s.Length, KLit.Zero), "Q.Count(source) > 0");
                    var r = Declare("t$" + _temps++, callType);
                    Emit(KHavoc.Of(r));
                    var rv = new KVar(r);
                    LinqFact(Over(KLit.Zero, s.Length, i => Eq(s.Elem(i), rv), forall: false), at);
                    LinqFact(Over(KLit.Zero, s.Length, i => new KOp(name == "Max" ? "<=" : ">=", s.Elem(i), rv)), at);
                    return rv;
                }
                case "Sum" when args.Count <= 2 && IsIntegral(callType):
                {
                    var s = Mapped();
                    // (every partial sum in range: .NET adds them checked)
                    var acc = new KVar(LinqMap("[int]int"));
                    KExpr A(KExpr j) => Sel(acc, j);
                    LinqFact(Eq(A(KLit.Zero), KLit.Zero), at);
                    LinqFact(Over(KLit.Zero, s.Length, j => Eq(A(Plus(j, KLit.One)), Plus(A(j), s.Elem(j)))), at);
                    var (lo, hi) = Range(callType.SpecialType);
                    Need(Over(KLit.Zero, Plus(s.Length, KLit.One), j => AndAlso(Le(Number(lo), A(j)), Le(A(j), Number(hi)))),
                         "every partial sum in range");
                    return Value(A(s.Length));
                }
                // (floating point: IEEE, added in order from 0.0, rounded at each step, as .NET adds them)
                // (a fold, as its definition is: Q.Fold(Skip(source, 1), Q.At(source, 0), func) without a seed, which
                // needs an element (CSV1001); a running accumulator, func of the one before and the element)
                case "Aggregate" when (args.Count == 2 || args.Count == 3) && Scalar(callType):
                {
                    var s = Sequence(args[0].Value);
                    var f = LambdaArg(call, args.Count - 1);
                    if (f.p2 == null)
                    {
                        throw new NotTranslated("LINQ's Aggregate of a function of one parameter");
                    }
                    KExpr seed, from;
                    if (args.Count == 2)
                    {
                        Need(Gt(s.Length, KLit.Zero), "Q.Count(source) > 0");
                        (seed, from) = (s.Elem(KLit.Zero), KLit.One);
                    }
                    else
                    {
                        (seed, from) = (Expr(args[1].Value), KLit.Zero);
                    }
                    var acc = new KVar(LinqMap("[int]" + TypeOf(callType)));
                    KExpr A(KExpr j) => Sel(acc, j);
                    LinqFact(Eq(A(from), seed), at);
                    LinqFact(Over(from, s.Length, j => Eq(A(Plus(j, KLit.One)), Apply(f, A(j), s.Elem(j)))), at);
                    return Value(A(s.Length));
                }
                case "Sum" or "Average" when args.Count <= 2 && callType.SpecialType == SpecialType.System_Double:
                {
                    var s = Mapped();
                    if (name == "Average")
                    {
                        Need(Gt(s.Length, KLit.Zero), "Q.Count(source) > 0");
                    }
                    var count = new KOp("$fp.ofReal64", new KOp("$toreal", s.Length));
                    if (s.Type.SpecialType == SpecialType.System_Double)
                    {
                        var acc = new KVar(LinqMap("[int]float53e11"));
                        KExpr A(KExpr j) => Sel(acc, j);
                        LinqFact(Eq(A(KLit.Zero), FloatLiteral(0.0, callType)), at);
                        LinqFact(Over(KLit.Zero, s.Length, j => Eq(A(Plus(j, KLit.One)), new KOp("$fp.add64", A(j), s.Elem(j)))), at);
                        return Value(name == "Sum" ? A(s.Length) : new KOp("$fp.div64", A(s.Length), count));
                    }
                    if (name == "Sum" || !IsIntegral(s.Type))
                    {
                        throw new NotTranslated("LINQ's " + name + " of " + s.Type);
                    }
                    // (an integer average: summed as long, exactly, then divided as doubles)
                    var sum = new KVar(LinqMap("[int]int"));
                    KExpr S(KExpr j) => Sel(sum, j);
                    LinqFact(Eq(S(KLit.Zero), KLit.Zero), at);
                    LinqFact(Over(KLit.Zero, s.Length, j => Eq(S(Plus(j, KLit.One)), Plus(S(j), s.Elem(j)))), at);
                    return Value(new KOp("$fp.div64", new KOp("$fp.ofReal64", new KOp("$toreal", S(s.Length))), count));
                }
                default:
                    throw new NotTranslated("LINQ's " + name);
            }
        }
    }
}
