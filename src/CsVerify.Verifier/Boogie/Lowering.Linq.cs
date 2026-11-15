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
        /// <summary>A sequence: its length, and its element at an index (a term over the index), of this type.</summary>
        private sealed class LSeq
        {
            public KExpr Length;
            public KAbs Elem;
            public ITypeSymbol Type;
            /// <summary>A filter's: the source index of its element i (a term over i).</summary>
            public KAbs Index;
            /// <summary>A GroupBy's groups: the call (its source, key and counts in _groupsOf).</summary>
            public IInvocationOperation Groups;

            /// <summary>This sequence with a free atom (an outer element's index, say) given a value.</summary>
            public LSeq With(KVar atom, KExpr value) => new LSeq
            {
                Length = Nameless.Substitute(Length, atom, value),
                Elem = Elem.With(atom, value),
                Type = Type,
                Index = Index?.With(atom, value),
                Groups = Groups,
            };
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
                    return Apply((kb, kp1, kp2), g.src.Elem.At(new KVar("q$" + p.Parameter.Name)));
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
        private void LinqFact(KExpr fact, SyntaxNode at)
        {
            var named = Named(fact);
            Emit(KSpecStmt.AssumedFree(_known == null ? named : Implies(_known, named), at, argumentAt: at));
        }

        /// <summary>A fact of what a query's result is (a definition, the bounds of a count or an index), whatever the rows hold.</summary>
        private void ShapeFact(KExpr fact, SyntaxNode at) => Emit(KSpecStmt.AssumedFree(Named(fact), at, argumentAt: at));

        private string LinqMap(string type)
        {
            var name = "lq$" + _linq++;
            _p.AddLocal(KLocal.Of(name, type));
            Emit(KHavoc.Of(name));
            return name;
        }

        private static KExpr Between(KExpr lo, KExpr i, KExpr hi) => AndAlso(Le(lo, i), Lt(i, hi));

        private int _atoms;

        /// <summary>A fresh atom: a name a binder's body is made of, then closed over (Nameless).</summary>
        private KVar Atom() => new KVar(Nameless.AtomPrefix + _atoms++);

        /// <summary>
        /// forall (or exists) i in [lo, hi): body, i an atom in it (and in the triggers'). Nameless: it is named where it
        /// leaves the lowering (Named).
        /// </summary>
        private static KNameless Over(KExpr lo, KExpr hi, KVar i, KExpr body, bool forall = true, KExpr[] trigger = null) => new KNameless
        {
            Forall = forall,
            Range = Nameless.Close(Between(lo, i, hi), i),
            Body = Nameless.Close(body, i),
            Trigger = trigger?.Select(t => Nameless.Close(t, i)).ToArray(),
        };

        private int _boundNames;

        /// <summary>A term as it leaves the lowering of queries: its quantifiers named, no index or atom left in it.</summary>
        private KExpr Named(KExpr e) => Nameless.Named(e, ref _boundNames);

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
                var i2 = Atom();
                ShapeFact(Over(KLit.Zero, n, i2, Sel(ModelOf("Members", (INamedTypeSymbol)type).Name, new KVar(hs), Keyed(Sel(order, i2), elem))), src.Syntax);
                var i3 = Atom();
                var j = Atom();
                ShapeFact(Over(KLit.Zero, n, i3, Over(KLit.Zero, i3, j, Ne(Sel(order, j), Sel(order, i3)))), src.Syntax);
                var i = Atom();
                return new LSeq
                {
                    Length = n,
                    Elem = KAbs.Of(i, Sel(order, i)),
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
                var i = Atom();
                return new LSeq
                {
                    Length = new KVar(n),
                    Elem = KAbs.Of(i, Sel(items, i)),
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
                var i = Atom();
                return new LSeq
                {
                    Length = Length(x),
                    Elem = KAbs.Of(i, Sel(Elements(type), x, i)),
                    Type = elem,
                };
            }
            if (IsList(type))
            {
                foreach (var m in ModelsOf((INamedTypeSymbol)type))
                {
                    _p.Models[m.Name] = m;
                }
                var i = Atom();
                return new LSeq
                {
                    Length = Sel(SizeMap, x),
                    Elem = KAbs.Of(i, Sel(ModelOf("Items", (INamedTypeSymbol)type).Name, x, i)),
                    Type = elem,
                };
            }
            var list = (INamedTypeSymbol)KernelTypes.Compilation.GetTypeByMetadataName("System.Collections.Generic.List`1").Construct(elem);
            foreach (var m in ModelsOf(list))
            {
                _p.Models[m.Name] = m;
            }
            _p.UsesState = true;
            var i4 = Atom();
            return new LSeq
            {
                Length = IfcRead(x, null, elem),
                Elem = KAbs.Of(i4, IfcRead(x, i4, elem)),
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
                    var i = Atom();
                    return new LSeq
                    {
                        Length = new KVar(n),
                        Elem = KAbs.Of(i, Sel(items, i)),
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
                var i = Atom();
                return new LSeq
                {
                    Length = new KVar(n),
                    Elem = KAbs.Of(i, Sel(items, i)),
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
                _p.AddDelegateKey(key);
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
                var i = Atom();
                return new LSeq
                {
                    Length = new KVar(n),
                    Elem = KAbs.Of(i, Sel(items, i)),
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
                    var i = Atom();
                    return new LSeq
                    {
                        Length = src.Length,
                        Elem = KAbs.Of(i, Apply(f, src.Elem.At(i), i)),
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
                    var i = Atom();
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
                            Elem = KAbs.Of(i, src.Elem.At(Plus(i, kv))),
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
                        var j = Atom();
                        return _inDatabase > 0 ? throw new NotTranslated("Where with an index, in a database") : FilterAt(src, KAbs.Of(j, Apply(f, src.Elem.At(j), j)), q.Syntax);
                    }
                    var x = Atom();
                    return Filter(src, KAbs.Of(x, Apply(f, x)), q.Syntax);
                }
                // (each first occurrence of the first source's elements that the second has, or hasn't)
                case "Intersect" or "Except" when args.Count == 2 && _inDatabase == 0:
                {
                    var a = Sequence(args[0].Value);
                    var b = Sequence(args[1].Value);
                    bool keep = m.Name == "Intersect";
                    var earlier = Atom();
                    var later = Atom();
                    var same = KAbs.Of(earlier, later, SameValue(a.Elem.At(earlier), a.Elem.At(later), a.Type));
                    var unseen = Unseen(a.Length, same, q.Syntax);
                    var j2 = Atom();
                    var k2 = Atom();
                    var k3 = Atom();
                    return FilterAt(a, KAbs.Of(j2, AndAlso(unseen.At(j2),
                                                    keep ? (KExpr)Over(KLit.Zero, b.Length, k2, SameValue(b.Elem.At(k2), a.Elem.At(j2), a.Type), forall: false)
                                                         : Not(Over(KLit.Zero, b.Length, k3, SameValue(b.Elem.At(k3), a.Elem.At(j2), a.Type), forall: false)))), q.Syntax);
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
                    var earlier = Atom();
                    var later = Atom();
                    var sameKey = KAbs.Of(earlier, later, SameValue(Apply(f, src.Elem.At(earlier)), Apply(f, src.Elem.At(later)), keyType));
                    return FilterAt(src, Unseen(src.Length, sameKey, q.Syntax), q.Syntax);
                }
                // (each element with its index: a tuple (Index, Item))
                case "Index" when args.Count == 1 && _inDatabase == 0 && resultElem != null && IsTuple(resultElem):
                {
                    var src = Sequence(args[0].Value);
                    var i = Atom();
                    return new LSeq
                    {
                        Length = src.Length,
                        Elem = KAbs.Of(i, new KOp(TupleMaker(resultElem), i, src.Elem.At(i))),
                        Type = resultElem,
                    };
                }
                // (the source backwards)
                case "Reverse" when args.Count == 1 && _inDatabase == 0:
                {
                    var src = Sequence(args[0].Value);
                    var i = Atom();
                    return new LSeq
                    {
                        Length = src.Length,
                        Elem = KAbs.Of(i, src.Elem.At(Minus(Minus(src.Length, KLit.One), i))),
                        Type = src.Type,
                    };
                }
                // (one more element, at the end or the start)
                case "Append" or "Prepend" when args.Count == 2 && _inDatabase == 0:
                {
                    var src = Sequence(args[0].Value);
                    var x = Operand(args[1].Value, LowerMode.Code);
                    bool end = m.Name == "Append";
                    var i = Atom();
                    return new LSeq
                    {
                        Length = Plus(src.Length, KLit.One),
                        Type = src.Type,
                        Elem = KAbs.Of(i, end ? Ite(Lt(i, src.Length), src.Elem.At(i), x)
                                                                : Ite(Eq(i, KLit.Zero), x, src.Elem.At(Minus(i, KLit.One)))),
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
                    var i = Atom();
                    return m.Name == "TakeLast"
                        ? new LSeq
                        {
                            Length = kv,
                            Elem = KAbs.Of(i, src.Elem.At(Plus(Minus(src.Length, kv), i))),
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
                    var i2 = Atom();
                    ShapeFact(Over(KLit.Zero, kv, i2, Apply(f, src.Elem.At(i2))), q.Syntax);
                    ShapeFact(Implies(Lt(kv, src.Length), Not(Apply(f, src.Elem.At(kv)))), q.Syntax);
                    var i = Atom();
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
                            Elem = KAbs.Of(i, src.Elem.At(Plus(i, kv))),
                            Type = src.Type,
                        };
                }
                // (the source, or one default if it's empty)
                case "DefaultIfEmpty" when args.Count == 1 && _inDatabase == 0 && Default(resultElem) is KExpr de:
                {
                    var src = Sequence(args[0].Value);
                    var empty = Eq(src.Length, KLit.Zero);
                    var i = Atom();
                    return new LSeq
                    {
                        Length = Ite(empty, KLit.One, src.Length),
                        Elem = KAbs.Of(i, Ite(empty, de, src.Elem.At(i))),
                        Type = src.Type,
                    };
                }
                case "Distinct" when args.Count == 1:
                {
                    var src = Sequence(args[0].Value);
                    // (each element's first occurrence, in order: Q.Unseen; the database's, in no order)
                    var earlier = Atom();
                    var later = Atom();
                    var same = KAbs.Of(earlier, later, SameValue(src.Elem.At(earlier), src.Elem.At(later), src.Type));
                    var distinct = FilterAt(src, Unseen(src.Length, same, q.Syntax), q.Syntax);
                    return _inDatabase > 0 ? Sort(distinct, new List<((IOperation, IParameterSymbol, IParameterSymbol), ITypeSymbol, bool)>(), q.Syntax) : distinct;
                }
                // (a.Zip(b): pairs of the elements at each index, as long as the shorter)
                case "Zip" when args.Count == 2 && resultElem != null && IsTuple(resultElem):
                {
                    var a = Sequence(args[0].Value);
                    var b = Sequence(args[1].Value);
                    var i = Atom();
                    return new LSeq
                    {
                        Length = Ite(Le(a.Length, b.Length), a.Length, b.Length),
                        Type = resultElem,
                        Elem = KAbs.Of(i, new KOp(TupleMaker(resultElem), a.Elem.At(i), b.Elem.At(i))),
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
                    var k = Atom();
                    var members = FilterAt(gsrc, KAbs.Of(k, SameValue(Apply(gkey, gsrc.Elem.At(k)), Apply(gkey, gsrc.Elem.At(KLit.Zero)), gkey.body.Type)), q.Syntax);
                    if (gb.Arguments.Length == 2)
                    {
                        return members;
                    }
                    var es = LambdaArg(gb, 2);
                    var i = Atom();
                    return new LSeq
                    {
                        Length = members.Length,
                        Elem = KAbs.Of(i, Apply(es, members.Elem.At(i))),
                        Type = resultElem,
                    };
                }
                case "Zip" when args.Count == 3:
                {
                    var a = Sequence(args[0].Value);
                    var b = Sequence(args[1].Value);
                    var f = LambdaArg(q, 2);
                    var fx = (f.body, f.p1, (IParameterSymbol)null);
                    var i = Atom();
                    return new LSeq
                    {
                        Length = Ite(Le(a.Length, b.Length), a.Length, b.Length),
                        Type = resultElem,
                        Elem = KAbs.Of(i, KLet.Of("q$" + f.p2.Name, b.Elem.At(i), Apply(fx, a.Elem.At(i)))),
                    };
                }
                case "OrderBy" or "OrderByDescending" or "ThenBy" or "ThenByDescending" when args.Count == 2:
                {
                    // (the keys, the first one's call innermost; a stable sort of the source by them all)
                    var keys = new List<((IOperation, IParameterSymbol, IParameterSymbol) key, ITypeSymbol type, bool down)>();
                    IInvocationOperation at = q;
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
                    var each = Atom();
                    var flat = Flatten(src, each, Inner(Apply(f, src.Elem.At(each)), f.body), q.Syntax, out var outer, out var within);
                    if (args.Count == 2)
                    {
                        return flat;
                    }
                    var rx = (r.body, r.p1, (IParameterSymbol)null);
                    var i = Atom();
                    return new LSeq
                    {
                        Length = flat.Length,
                        Type = resultElem,
                        Elem = KAbs.Of(i, KLet.Of("q$" + r.p2.Name, flat.Elem.At(i), Apply(rx, src.Elem.At(outer.At(i))))),
                    };
                }
                case "Join" when args.Count == 5:
                {
                    // (each pair of an outer and an inner element, in that order, whose keys agree: Q.For, Q.For, Q.If)
                    var o = Sequence(args[0].Value);
                    var inner = Sequence(args[1].Value);
                    var (okey, ikey, sel) = (LambdaArg(q, 2), LambdaArg(q, 3), LambdaArg(q, 4));
                    var pairs = Flatten(o, Atom(), inner, q.Syntax, out var outer, out var within, whole: true);
                    var i2 = Atom();
                    var matched = FilterAt(pairs, KAbs.Of(i2, JoinKeysEqual(Apply(okey, o.Elem.At(outer.At(i2))), Apply(ikey, inner.Elem.At(within.At(i2))), okey.body.Type)), q.Syntax);
                    var sx = (sel.body, sel.p1, (IParameterSymbol)null);
                    // (the matched pair i is pair ix[i]: its outer and inner elements)
                    var i = Atom();
                    var joined = new LSeq
                    {
                        Length = matched.Length,
                        Type = resultElem,
                        Elem = KAbs.Of(i, KLet.Of("q$" + sel.p2.Name, inner.Elem.At(within.At(matched.Index.At(i))), Apply(sx, o.Elem.At(outer.At(matched.Index.At(i)))))),
                    };
                    // (the database's: in no order of its sources', SQL Server's hash join keeping no outer row's matches together)
                    return _inDatabase > 0 ? Sort(joined, new List<((IOperation, IParameterSymbol, IParameterSymbol), ITypeSymbol, bool)>(), q.Syntax) : joined;
                }
                // (one sequence, then the other; Union: their elements' first occurrences, as Distinct of that)
                case "Concat" or "Union" when args.Count == 2:
                {
                    var a = Sequence(args[0].Value);
                    var b = Sequence(args[1].Value);
                    var i = Atom();
                    var both = new LSeq
                    {
                        Length = Plus(a.Length, b.Length),
                        Type = a.Type,
                        Elem = KAbs.Of(i, Ite(Lt(i, a.Length), a.Elem.At(i), b.Elem.At(Minus(i, a.Length)))),
                    };
                    if (m.Name == "Concat")
                    {
                        return _inDatabase > 0 ? Sort(both, new List<((IOperation, IParameterSymbol, IParameterSymbol), ITypeSymbol, bool)>(), q.Syntax) : both;
                    }
                    var earlier = Atom();
                    var later = Atom();
                    var same = KAbs.Of(earlier, later, SameValue(both.Elem.At(earlier), both.Elem.At(later), both.Type));
                    var union = FilterAt(both, Unseen(both.Length, same, q.Syntax), q.Syntax);
                    return _inDatabase > 0 ? Sort(union, new List<((IOperation, IParameterSymbol, IParameterSymbol), ITypeSymbol, bool)>(), q.Syntax) : union;
                }
                // (groups as values, of a selector that reads their key and count: GroupValue. A database's counts are
                // bounds; LINQ to Objects' are exact: how many of the source have the key)
                case "GroupBy" when args.Count == 2 || args.Count == 3 && _inDatabase == 0 && LambdaArg(q, 2).p2 != null:
                {
                    var src = Sequence(args[0].Value);
                    var key = LambdaArg(q, 1);
                    // (a group: the index in the source of its key's first element; each key's first, in order)
                    var earlier = Atom();
                    var later = Atom();
                    var sameKey = KAbs.Of(earlier, later, SameValue(Apply(key, src.Elem.At(earlier)), Apply(key, src.Elem.At(later)), key.body.Type));
                    var firsts = FilterAt(src, Unseen(src.Length, sameKey, q.Syntax), q.Syntax);
                    // (how many of the source have its key: at least the one, at most all)
                    var count = new KVar(LinqMap("[int]int"));
                    var j2 = Atom();
                    ShapeFact(Over(KLit.Zero, src.Length, j2, AndAlso(Le(KLit.One, Sel(count, j2)), Le(Sel(count, j2), src.Length))), q.Syntax);
                    if (_inDatabase == 0)
                    {
                        // (exactly: a running count of those with j's key, over the source)
                        var rc = new KVar(LinqMap("[int][int]int"));
                        var j3 = Atom();
                        LinqFact(Over(KLit.Zero, src.Length, j3, Eq(Sel(rc, j3, KLit.Zero), KLit.Zero)), q.Syntax);
                        var j4 = Atom();
                        var k = Atom();
                        LinqFact(Over(KLit.Zero, src.Length, j4, Over(KLit.Zero, src.Length, k, Eq(Sel(rc, j4, Plus(k, KLit.One)), Plus(Sel(rc, j4, k), Ite(SameValue(Apply(key, src.Elem.At(k)), Apply(key, src.Elem.At(j4)), key.body.Type), KLit.One, KLit.Zero))))), q.Syntax);
                        var j = Atom();
                        LinqFact(Over(KLit.Zero, src.Length, j, Eq(Sel(count, j), Sel(rc, j, src.Length))), q.Syntax);
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
                        var i = Atom();
                        return new LSeq
                        {
                            Length = firsts.Length,
                            Type = resultElem,
                            Elem = KAbs.Of(i, Apply(sel, Apply(key, src.Elem.At(firsts.Index.At(i))), firsts.Index.At(i))),
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
                    var j = Atom();
                    ShapeFact(Over(KLit.Zero, o.Length, j, AndAlso(Le(KLit.Zero, Sel(count, j)), Le(Sel(count, j), inner.Length))), q.Syntax);
                    _groupParams[sel.p2] = (inner, null, count);
                    // (the selector's second parameter: the outer element's index, which its count is read at)
                    var i = Atom();
                    var joined = new LSeq
                    {
                        Length = o.Length,
                        Elem = KAbs.Of(i, Apply(sel, o.Elem.At(i), i)),
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
                    var j2 = Atom();
                    LinqFact(Over(KLit.Zero, o.Length, j2, Eq(Sel(rc, j2, KLit.Zero), KLit.Zero)), q.Syntax);
                    var j3 = Atom();
                    var k = Atom();
                    LinqFact(Over(KLit.Zero, o.Length, j3, Over(KLit.Zero, inner.Length, k, Eq(Sel(rc, j3, Plus(k, KLit.One)), Plus(Sel(rc, j3, k), Ite(JoinKeysEqual(Apply(okey, o.Elem.At(j3)), Apply(ikey, inner.Elem.At(k)), okey.body.Type), KLit.One, KLit.Zero))))), q.Syntax);
                    var j4 = Atom();
                    LinqFact(Over(KLit.Zero, o.Length, j4, Eq(Sel(count, j4), Sel(rc, j4, inner.Length))), q.Syntax);
                    var j = Atom();
                    ShapeFact(Over(KLit.Zero, o.Length, j, AndAlso(Le(KLit.Zero, Sel(count, j)), Le(Sel(count, j), inner.Length))), q.Syntax);
                    _groupParams[sel.p2] = (inner, null, count);
                    var i = Atom();
                    return new LSeq
                    {
                        Length = o.Length,
                        Elem = KAbs.Of(i, Apply(sel, o.Elem.At(i), i)),
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
                    var j2 = Atom();
                    var ext = new LSeq
                    {
                        Length = Plus(o.Length, KLit.One),
                        Type = o.Type,
                        Elem = KAbs.Of(j2, Ite(Lt(j2, o.Length), o.Elem.At(j2), none)),
                    };
                    var pairs = Flatten(inner, Atom(), ext, q.Syntax, out var byInner, out var within, whole: true);
                    var i2 = Atom();
                    var j = Atom();
                    var kept = FilterAt(pairs, KAbs.Of(i2, Ite(Lt(within.At(i2), o.Length), KeysMatch(within.At(i2), byInner.At(i2), okey, o, ikey, inner),
                        Not(Over(KLit.Zero, o.Length, j, KeysMatch(j, byInner.At(i2), okey, o, ikey, inner), forall: false)))), q.Syntax);
                    var sx = (sel.body, sel.p1, (IParameterSymbol)null);
                    var i = Atom();
                    return new LSeq
                    {
                        Length = kept.Length,
                        Type = resultElem,
                        Elem = KAbs.Of(i, KLet.Of("q$" + sel.p2.Name, inner.Elem.At(byInner.At(kept.Index.At(i))), Apply(sx, ext.Elem.At(within.At(kept.Index.At(i)))))),
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
                    var k2 = Atom();
                    var ext = new LSeq
                    {
                        Length = Plus(inner.Length, KLit.One),
                        Type = inner.Type,
                        Elem = KAbs.Of(k2, Ite(Lt(k2, inner.Length), inner.Elem.At(k2), none)),
                    };
                    var pairs = Flatten(o, Atom(), ext, q.Syntax, out var outer, out var within, whole: true);
                    var i2 = Atom();
                    var k = Atom();
                    var kept = FilterAt(pairs, KAbs.Of(i2, Ite(Lt(within.At(i2), inner.Length), KeysMatch(outer.At(i2), within.At(i2), okey, o, ikey, inner),
                        Not(Over(KLit.Zero, inner.Length, k, KeysMatch(outer.At(i2), k, okey, o, ikey, inner), forall: false)))), q.Syntax);
                    var sx = (sel.body, sel.p1, (IParameterSymbol)null);
                    var i = Atom();
                    var joined = new LSeq
                    {
                        Length = kept.Length,
                        Type = resultElem,
                        Elem = KAbs.Of(i, KLet.Of("q$" + sel.p2.Name, ext.Elem.At(within.At(kept.Index.At(i))), Apply(sx, o.Elem.At(outer.At(kept.Index.At(i)))))),
                    };
                    return _inDatabase > 0 ? Sort(joined, new List<((IOperation, IParameterSymbol, IParameterSymbol), ITypeSymbol, bool)>(), q.Syntax) : joined;
                }
                default: throw new NotTranslated("LINQ's " + m.Name);
            }
        }

        private KExpr KeysMatch(KExpr j, KExpr k, (IOperation body, IParameterSymbol p1, IParameterSymbol p2) okey, LSeq o, (IOperation body, IParameterSymbol p1, IParameterSymbol p2) ikey, LSeq inner) => JoinKeysEqual(Apply(okey, o.Elem.At(j)), Apply(ikey, inner.Elem.At(k)), okey.body.Type);

        private IOperation SourceOf(IInvocationOperation x) => x.Arguments.OrderBy(a => a.Parameter.Ordinal).First().Value;

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
                        _p.AddLocal(KLocal.Of(Local(l), "int"));
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
            _p.AddLocal(KLocal.Of(fe.Mat, "[int]" + (IsGrouping(element) || joinRows ? "int" : TypeOf(element))));
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
                var i = Atom();
                var src = new LSeq
                {
                    Length = new KVar(g.count),
                    Elem = KAbs.Of(i, Sel(g.map, i)),
                    Type = g.elem,
                };
                var gv = new KVar(Declare(Local(fe.GroupOf), fe.GroupOf.Type));
                var x = Atom();
                seq = Filter(src, KAbs.Of(x, SameValue(Apply(g.key, x), Apply(g.key, src.Elem.At(gv)), g.key.Item1.Type)), at);
            }
            else if (fe.JoinGroupOf != null)
            {
                // (a GroupJoin row's group: the inner elements, as read where the rows were, whose key is the row's outer element's)
                var j = _joinRows[fe.JoinGroupOf].read ?? throw new NotTranslated("a GroupJoin's group not of its rows read here");
                var rv = new KVar(Declare(Local(fe.JoinGroupOf), fe.JoinGroupOf.Type));
                var i = Atom();
                var inner = new LSeq
                {
                    Length = new KVar(j.innerCount),
                    Elem = KAbs.Of(i, Sel(j.innerMap, i)),
                    Type = j.innerType,
                };
                var outerElem = Sel(j.outerMap, rv);
                var x = Atom();
                seq = Filter(inner, KAbs.Of(x, SameValue(Apply(j.ikey, x), Apply(j.okey, outerElem), j.okey.Item1.Type)), at);
            }
            else if (Unconverted(fe.Query) is IInvocationOperation gj && gj.TargetMethod.Name == "GroupJoin" && gj.Arguments.Length == 5)
            {
                // (a GroupJoin: a row for each outer element, in order, its group the inner ones of its key; both read now)
                var args = gj.Arguments.OrderBy(a => a.Parameter.Ordinal).ToList();
                var outer = Sequence(args[0].Value);
                var innerSrc = Sequence(args[1].Value);
                var (okey, ikey) = (LambdaArg(gj, 2), LambdaArg(gj, 3));
                var oc = Declare("t$" + _temps++, _model.Compilation.GetSpecialType(SpecialType.System_Int32));
                Emit(KAssign.Of(oc, outer.Length));
                var ic = Declare("t$" + _temps++, _model.Compilation.GetSpecialType(SpecialType.System_Int32));
                Emit(KAssign.Of(ic, innerSrc.Length));
                var read = (outerMap: ReadIntoMap(outer, at), outerCount: oc, innerMap: ReadIntoMap(innerSrc, at), innerCount: ic, okey, ikey, outerType: outer.Type, innerType: innerSrc.Type);
                foreach (var l in _forEachOf.Where(kv => kv.Value == fe).Select(kv => kv.Key))
                {
                    _joinRows[l] = (_joinRows[l].join, _joinRows[l].members, read);
                }
                var i = Atom();
                seq = new LSeq
                {
                    Length = new KVar(oc),
                    Elem = KAbs.Of(i, i),
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
                var i2 = Atom();
                LinqFact(Over(KLit.Zero, new KVar(count), i2, Eq(Sel(map, i2), source.Elem.At(i2))), at);
                var i = Atom();
                var read = new LSeq
                {
                    Length = new KVar(count),
                    Elem = KAbs.Of(i, Sel(map, i)),
                    Type = source.Type,
                };
                // (the groups in the order their keys first appear: each one's first index)
                var earlier = Atom();
                var later = Atom();
                var sameKey = KAbs.Of(earlier, later, SameValue(Apply(key, read.Elem.At(earlier)), Apply(key, read.Elem.At(later)), key.body.Type));
                var firsts = FilterAt(read, Unseen(read.Length, sameKey, at), at);
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
            var i3 = Atom();
            LinqFact(Over(KLit.Zero, new KVar(fe.Count), i3, Eq(Sel(fe.Mat, i3), seq.Elem.At(i3))), at);
            Emit(KAssign.Of(fe.Index, KLit.Zero));
        }

        private string ReadIntoMap(LSeq sq, SyntaxNode at)
        {
            var map = LinqMap("[int]" + TypeOf(sq.Type));
            var i = Atom();
            LinqFact(Over(KLit.Zero, sq.Length, i, Eq(Sel(map, i), sq.Elem.At(i))), at);
            return map;
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
                var i = Atom();
                return new LSeq
                {
                    Length = Length(value),
                    Elem = KAbs.Of(i, Sel(Elements(type), value, i)),
                    Type = elem,
                };
            }
            if (IsList(type))
            {
                foreach (var m in ModelsOf((INamedTypeSymbol)type))
                {
                    _p.Models[m.Name] = m;
                }
                var i = Atom();
                return new LSeq
                {
                    Length = Sel(SizeMap, value),
                    Elem = KAbs.Of(i, Sel(ModelOf("Items", (INamedTypeSymbol)type).Name, value, i)),
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
        private LSeq Flatten(LSeq src, KVar outerIndex, LSeq inner, SyntaxNode at, out KAbs outer, out KAbs within, bool whole = false)
        {
            var o = new KVar(LinqMap("[int]int"));
            var ov = new KVar(LinqMap("[int]int"));
            var n = src.Length;
            ShapeFact(Eq(Sel(o, KLit.Zero), KLit.Zero), at);
            var j = Atom();
            var length = inner.With(outerIndex, j).Length;
            var offsets = Over(KLit.Zero, n, j, AndAlso(Eq(Sel(o, Plus(j, KLit.One)), Plus(Sel(o, j), length)), Le(KLit.Zero, length)));
            if (whole)
            {
                ShapeFact(offsets, at);
            } else
            {
                LinqFact(offsets, at);
            }
            // (monotone: an offset is no more than any later one)
            var a = Atom();
            var b = Atom();
            ShapeFact(Over(KLit.Zero, Plus(n, KLit.One), a, Over(a, Plus(n, KLit.One), b, Le(Sel(o, a), Sel(o, b)))), at);
            var i2 = Atom();
            ShapeFact(Over(KLit.Zero, Sel(o, n), i2, AndAlso(Between(KLit.Zero, Sel(ov, i2), n), AndAlso(Le(Sel(o, Sel(ov, i2)), i2), Lt(i2, Sel(o, Plus(Sel(ov, i2), KLit.One)))))), at);
            var i = Atom();
            outer = KAbs.Of(i, Sel(ov, i));
            within = KAbs.Of(i, Minus(i, Sel(o, Sel(ov, i))));
            var element = inner.With(outerIndex, outer.At(i)).Elem.At(within.At(i));
            return new LSeq
            {
                Length = Sel(o, n),
                Elem = KAbs.Of(i, element),
                Type = inner.Type,
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
        /// <summary>
        /// Of n elements, those no earlier one is the same as (same: a term over two indices, the earlier first): first[j]
        /// where none before j is, seen[j] one before it that is where not. Its value: first, over the index.
        /// </summary>
        private KAbs Unseen(KExpr n, KAbs same, SyntaxNode at)
        {
            var first = new KVar(LinqMap("[int]bool"));
            var seen = new KVar(LinqMap("[int]int"));
            var j2 = Atom();
            var k = Atom();
            LinqFact(Over(KLit.Zero, n, j2, Implies(Sel(first, j2), Over(KLit.Zero, j2, k, Not(same.At(k, j2))))), at);
            var j3 = Atom();
            LinqFact(Over(KLit.Zero, n, j3, Implies(Not(Sel(first, j3)), AndAlso(Between(KLit.Zero, Sel(seen, j3), j3), same.At(Sel(seen, j3), j3)))), at);
            var j = Atom();
            return KAbs.Of(j, Sel(first, j));
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
            LinqFact(Implies(Ge(s.Length, new KLit("2")), Lt(s.Index.At(KLit.Zero), s.Index.At(KLit.One))), at);
        }

        /// <summary>A filter by a predicate of the elements (a term over the element).</summary>
        private LSeq Filter(LSeq src, KAbs pred, SyntaxNode at)
        {
            var j = Atom();
            return FilterAt(src, KAbs.Of(j, pred.At(src.Elem.At(j))), at);
        }

        /// <summary>
        /// A filter: c[j] the matches before j (c[0] = 0, one more at each j that matches), ix[i] the i-th match's index,
        /// increasing; its length c[n], its element i the source's ix[i].
        /// </summary>
        private LSeq FilterAt(LSeq src, KAbs keep, SyntaxNode at)
        {
            var c = new KVar(LinqMap("[int]int"));
            var ix = new KVar(LinqMap("[int]int"));
            var n = src.Length;
            ShapeFact(Eq(Sel(c, KLit.Zero), KLit.Zero), at);
            var j2 = Atom();
            LinqFact(Over(KLit.Zero, n, j2, Eq(Sel(c, Plus(j2, KLit.One)), Plus(Sel(c, j2), Ite(keep.At(j2), KLit.One, KLit.Zero)))), at);
            var j3 = Atom();
            ShapeFact(Over(KLit.Zero, Plus(n, KLit.One), j3, AndAlso(Le(KLit.Zero, Sel(c, j3)), Le(Sel(c, j3), j3))), at);
            var j = Atom();
            LinqFact(Over(KLit.Zero, n, j, Implies(keep.At(j), Eq(Sel(ix, Sel(c, j)), j))), at);
            var i2 = Atom();
            LinqFact(Over(KLit.Zero, Sel(c, n), i2, AndAlso(AndAlso(Between(KLit.Zero, Sel(ix, i2), n), keep.At(Sel(ix, i2))), Eq(Sel(c, Sel(ix, i2)), i2))), at);
            // (of two indices there are: one alone would make the next, and so on without end)
            var i3 = Atom();
            var pattern = new KOp("$pattern", Sel(ix, i3), Sel(ix, Plus(i3, KLit.One)));
            var increasing = Over(KLit.Zero, Minus(Sel(c, n), KLit.One), i3, Lt(Sel(ix, i3), Sel(ix, Plus(i3, KLit.One))), trigger: new KExpr[] { pattern });
            LinqFact(increasing, at);
            var i4 = Atom();
            var i = Atom();
            return new LSeq
            {
                Length = Sel(c, n),
                Elem = KAbs.Of(i4, src.Elem.At(Sel(ix, i4))),
                Type = src.Type,
                Index = KAbs.Of(i, Sel(ix, i)),
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
            var i2 = Atom();
            ShapeFact(Over(KLit.Zero, n, i2, AndAlso(Between(KLit.Zero, Sel(p, i2), n), Eq(Sel(qv, Sel(p, i2)), i2))), at);
            var j = Atom();
            ShapeFact(Over(KLit.Zero, n, j, AndAlso(Between(KLit.Zero, Sel(qv, j), n), Eq(Sel(p, Sel(qv, j)), j))), at);
            int prefix = keys.TakeWhile(k => k.type != null && (IsIntegral(k.type) || k.type.SpecialType == SpecialType.System_Char)).Count();
            if (prefix > 0)
            {
                var i = Atom();
                LinqFact(Over(KLit.Zero, Minus(n, KLit.One), i, InOrder(Sel(p, i), Sel(p, Plus(i, KLit.One)), 0, prefix, keys, src)), at);
            }
            var i3 = Atom();
            return new LSeq
            {
                Length = n,
                Elem = KAbs.Of(i3, src.Elem.At(Sel(p, i3))),
                Type = src.Type,
            };
        }

        private KExpr InOrder(KExpr a, KExpr b, int level, int prefix, List<((IOperation, IParameterSymbol, IParameterSymbol) key, ITypeSymbol type, bool down)> keys, LSeq src)
        {
            if (level == prefix)
            {
                return prefix == keys.Count ? Lt(a, b) : KLit.True;
            }
            var (x, y) = (Apply(keys[level].key, src.Elem.At(a)), Apply(keys[level].key, src.Elem.At(b)));
            return OrElse(keys[level].down ? Gt(x, y) : Lt(x, y), AndAlso(Eq(x, y), InOrder(a, b, level + 1, prefix, keys, src)));
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
            switch (call.TargetMethod.Name)
            {
                case "Exists":
                    var i2 = Atom();
                    ShapeFact(Eq(v, Over(KLit.Zero, s.Length, i2, Apply(f, s.Elem.At(i2)), forall: false)), at);
                    break;
                case "TrueForAll":
                    var i3 = Atom();
                    ShapeFact(Eq(v, Over(KLit.Zero, s.Length, i3, Apply(f, s.Elem.At(i3)))), at);
                    break;
                case "Find":
                {
                    if (!(Default(call.Type) is KExpr dflt))
                    {
                        throw new NotTranslated("a default of " + call.Type);
                    }
                    var x = Atom();
                    var m = Filter(s, KAbs.Of(x, Apply(f, x)), at);
                    ShapeFact(Eq(v, Ite(Gt(m.Length, KLit.Zero), m.Elem.At(KLit.Zero), dflt)), at);
                    break;
                }
                default: // FindIndex
                    ShapeFact(AndAlso(Le(KLit.MinusOne, v), Lt(v, s.Length)), at);
                    var i4 = Atom();
                    var i = Atom();
                    ShapeFact(Ite(Eq(v, KLit.MinusOne), Over(KLit.Zero, s.Length, i4, Not(Apply(f, s.Elem.At(i4)))),
                                      AndAlso(Apply(f, s.Elem.At(v)), Over(KLit.Zero, v, i, Not(Apply(f, s.Elem.At(i)))))), at);
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
                return Named(Elementwise(call));
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
                return Named(LinqCore(call, name, resultType));
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
                        MapLambda("j$: int", Ite(Between(KLit.Zero, new KVar("j$"), s.Length), s.Elem.At(new KVar("j$")), new KLit(Default(s.Type) is KLit d ? d.Text : "0")))));
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
                    Emit(KRow.Of(items.Name, new KVar(t), MapLambda("j$: int", s.Elem.At(new KVar("j$")))));
                    Emit(KRow.Of(SizeMap, new KVar(t), s.Length));
                    return new KVar(t);
                }
                case "Count" or "LongCount" when args.Count <= 2:
                    return LinqValue(FilteredSequence(true, args, call, at).Length, callType, at);
                case "Any" when args.Count <= 2:
                    return LinqValue(Gt(FilteredSequence(true, args, call, at).Length, KLit.Zero), callType, at);
                case "All" when args.Count == 2:
                {
                    var s = Sequence(args[0].Value);
                    var f = LambdaArg(call, 1);
                    var i = Atom();
                    return LinqValue(Over(KLit.Zero, s.Length, i, Apply(f, s.Elem.At(i))), callType, at);
                }
                // (a dictionary, of the library's: only where it throws, a key that's null or an earlier one's, as its definition says)
                case "ToDictionary" when args.Count is 2 or 3 && _inDatabase == 0 && IsCollection(callType) && LambdaArg(call, 1) is var kf && kf.p2 == null:
                {
                    var s = Sequence(args[0].Value);
                    var keyType = kf.body.Type;
                    var i = Atom();
                    var j = Atom();
                    CheckPrecondition(Over(KLit.Zero, s.Length, i, AndAlso(IsNullable(keyType) ? NotNull(Apply(kf, s.Elem.At(i))) : KLit.True,
                                                                    Not(Over(KLit.Zero, i, j, SameValue(Apply(kf, s.Elem.At(j)), Apply(kf, s.Elem.At(i)), keyType), forall: false)))), "Spec.Forall(0, Q.Count(source), i => keySelector(Q.At(source, i)) != null && Q.Unseen(Select(source, keySelector), i))", at, name);
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
                    var i = Atom();
                    return LinqValue(AndAlso(Eq(a.Length, b.Length), Over(KLit.Zero, a.Length, i, SameValue(a.Elem.At(i), b.Elem.At(i), a.Type))), callType, at);
                }
                case "Contains" when args.Count == 2:
                {
                    var s = Sequence(args[0].Value);
                    var x = Expr(args[1].Value);
                    var i = Atom();
                    return LinqValue(Over(KLit.Zero, s.Length, i, SameValue(s.Elem.At(i), x, s.Type), forall: false), callType, at);
                }
                case "First" or "Last" or "FirstOrDefault" or "LastOrDefault" when args.Count <= 2:
                {
                    var s = FilteredSequence(true, args, call, at);
                    AtMostOneHint(s, at);
                    DatabaseOrder(call, args[0].Value, s.Length);
                    var pos = name.StartsWith("First") ? KLit.Zero : (KExpr)Minus(s.Length, KLit.One);
                    if (!name.EndsWith("OrDefault"))
                    {
                        CheckPrecondition(Gt(s.Length, KLit.Zero), args.Count == 1 ? "Q.Count(source) > 0" : "a matching element", at, name);
                        return LinqValue(s.Elem.At(pos), callType, at);
                    }
                    if (!(Default(callType) is KExpr dflt))
                    {
                        throw new NotTranslated("a default of " + callType);
                    }
                    return LinqValue(Ite(Gt(s.Length, KLit.Zero), s.Elem.At(pos), dflt), callType, at);
                }
                case "Single" or "SingleOrDefault" when args.Count <= 2:
                {
                    // (one, or with OrDefault none, else InvalidOperationException: its precondition)
                    var s = FilteredSequence(true, args, call, at);
                    AtMostOneHint(s, at);
                    var src = args.Count == 1 ? "Q.Count(source)" : "Q.Count(Where(source, predicate))";
                    if (name == "Single")
                    {
                        CheckPrecondition(Eq(s.Length, KLit.One), src + " == 1", at, name);
                        return LinqValue(s.Elem.At(KLit.Zero), callType, at);
                    }
                    CheckPrecondition(Le(s.Length, KLit.One), src + " <= 1", at, name);
                    if (!(Default(callType) is KExpr sd))
                    {
                        throw new NotTranslated("a default of " + callType);
                    }
                    return LinqValue(Ite(Eq(s.Length, KLit.One), s.Elem.At(KLit.Zero), sd), callType, at);
                }
                // (the first element whose key is least, or greatest: an integer key)
                case "MinBy" or "MaxBy" when args.Count == 2 && _inDatabase == 0 && LambdaArg(call, 1) is var by && by.p2 == null && IsIntegral(by.body.Type):
                {
                    var s = Sequence(args[0].Value);
                    CheckPrecondition(Gt(s.Length, KLit.Zero), "Q.Count(source) > 0", at, name);
                    var ix = Declare("t$" + _temps++, KernelTypes.Compilation.GetSpecialType(SpecialType.System_Int32));
                    Emit(KHavoc.Of(ix));
                    var iv = new KVar(ix);
                    var better = name == "MinBy" ? "<" : ">";
                    LinqFact(AndAlso(Le(KLit.Zero, iv), Lt(iv, s.Length)), at);
                    var i2 = Atom();
                    LinqFact(Over(KLit.Zero, s.Length, i2, Not(new KOp(better, Apply(by, s.Elem.At(i2)), Apply(by, s.Elem.At(iv))))), at);
                    var i = Atom();
                    LinqFact(Over(KLit.Zero, iv, i, new KOp(better == "<" ? ">" : "<", Apply(by, s.Elem.At(i)), Apply(by, s.Elem.At(iv)))), at);
                    return LinqValue(s.Elem.At(iv), callType, at);
                }
                // (of doubles: Min is NaN where one is; Max passes NaNs over, NaN only where all are, as .NET compares them)
                case "Max" or "Min" when args.Count <= 2 && IsFloating(callType) && _inDatabase == 0:
                {
                    var s = MappedSequence(args, call, callType);
                    CheckPrecondition(Gt(s.Length, KLit.Zero), "Q.Count(source) > 0", at, name);
                    var n = FloatSize(callType);
                    var r = Declare("t$" + _temps++, callType);
                    Emit(KHavoc.Of(r));
                    var rv = new KVar(r);
                    var i2 = Atom();
                    var anyNaN = Over(KLit.Zero, s.Length, i2, IsNaN(s.Elem.At(i2), n), forall: false);
                    var i3 = Atom();
                    var allNaN = Over(KLit.Zero, s.Length, i3, IsNaN(s.Elem.At(i3), n));
                    var i4 = Atom();
                    LinqFact(Over(KLit.Zero, s.Length, i4, Eq(s.Elem.At(i4), rv), forall: false), at);
                    if (name == "Min")
                    {
                        LinqFact(Eq(IsNaN(rv, n), anyNaN), at);
                        var i = Atom();
                        LinqFact(Over(KLit.Zero, s.Length, i, OrElse(IsNaN(rv, n), new KOp("$fp.leq" + n, rv, s.Elem.At(i)))), at);
                    }
                    else
                    {
                        LinqFact(Eq(IsNaN(rv, n), allNaN), at);
                        var i = Atom();
                        LinqFact(Over(KLit.Zero, s.Length, i, OrElse(IsNaN(s.Elem.At(i), n), new KOp("$fp.leq" + n, s.Elem.At(i), rv))), at);
                    }
                    return rv;
                }
                case "Max" or "Min" when args.Count <= 2 && IsIntegral(callType):
                {
                    var s = MappedSequence(args, call, callType);
                    CheckPrecondition(Gt(s.Length, KLit.Zero), "Q.Count(source) > 0", at, name);
                    var r = Declare("t$" + _temps++, callType);
                    Emit(KHavoc.Of(r));
                    var rv = new KVar(r);
                    var i2 = Atom();
                    LinqFact(Over(KLit.Zero, s.Length, i2, Eq(s.Elem.At(i2), rv), forall: false), at);
                    var i = Atom();
                    LinqFact(Over(KLit.Zero, s.Length, i, new KOp(name == "Max" ? "<=" : ">=", s.Elem.At(i), rv)), at);
                    return rv;
                }
                case "Sum" when args.Count <= 2 && IsIntegral(callType):
                {
                    var s = MappedSequence(args, call, callType);
                    // (every partial sum in range: .NET adds them checked)
                    var acc = new KVar(LinqMap("[int]int"));
                    LinqFact(Eq(Sel(acc, KLit.Zero), KLit.Zero), at);
                    var j2 = Atom();
                    LinqFact(Over(KLit.Zero, s.Length, j2, Eq(Sel(acc, Plus(j2, KLit.One)), Plus(Sel(acc, j2), s.Elem.At(j2)))), at);
                    var (lo, hi) = Range(callType.SpecialType);
                    var j = Atom();
                    CheckPrecondition(Over(KLit.Zero, Plus(s.Length, KLit.One), j, AndAlso(Le(Number(lo), Sel(acc, j)), Le(Sel(acc, j), Number(hi)))), "every partial sum in range", at, name);
                    return LinqValue(Sel(acc, s.Length), callType, at);
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
                        CheckPrecondition(Gt(s.Length, KLit.Zero), "Q.Count(source) > 0", at, name);
                        (seed, from) = (s.Elem.At(KLit.Zero), KLit.One);
                    }
                    else
                    {
                        (seed, from) = (Expr(args[1].Value), KLit.Zero);
                    }
                    var acc = new KVar(LinqMap("[int]" + TypeOf(callType)));
                    LinqFact(Eq(Sel(acc, from), seed), at);
                    var j = Atom();
                    LinqFact(Over(from, s.Length, j, Eq(Sel(acc, Plus(j, KLit.One)), Apply(f, Sel(acc, j), s.Elem.At(j)))), at);
                    return LinqValue(Sel(acc, s.Length), callType, at);
                }
                case "Sum" or "Average" when args.Count <= 2 && callType.SpecialType == SpecialType.System_Double:
                {
                    var s = MappedSequence(args, call, callType);
                    if (name == "Average")
                    {
                        CheckPrecondition(Gt(s.Length, KLit.Zero), "Q.Count(source) > 0", at, name);
                    }
                    var count = new KOp("$fp.ofReal64", new KOp("$toreal", s.Length));
                    if (s.Type.SpecialType == SpecialType.System_Double)
                    {
                        var acc = new KVar(LinqMap("[int]float53e11"));
                        LinqFact(Eq(Sel(acc, KLit.Zero), FloatLiteral(0.0, callType)), at);
                        var j = Atom();
                        LinqFact(Over(KLit.Zero, s.Length, j, Eq(Sel(acc, Plus(j, KLit.One)), new KOp("$fp.add64", Sel(acc, j), s.Elem.At(j)))), at);
                        return LinqValue(name == "Sum" ? Sel(acc, s.Length) : new KOp("$fp.div64", Sel(acc, s.Length), count), callType, at);
                    }
                    if (name == "Sum" || !IsIntegral(s.Type))
                    {
                        throw new NotTranslated("LINQ's " + name + " of " + s.Type);
                    }
                    // (an integer average: summed as long, exactly, then divided as doubles)
                    var sum = new KVar(LinqMap("[int]int"));
                    LinqFact(Eq(Sel(sum, KLit.Zero), KLit.Zero), at);
                    var j2 = Atom();
                    LinqFact(Over(KLit.Zero, s.Length, j2, Eq(Sel(sum, Plus(j2, KLit.One)), Plus(Sel(sum, j2), s.Elem.At(j2)))), at);
                    return LinqValue(new KOp("$fp.div64", new KOp("$fp.ofReal64", new KOp("$toreal", Sel(sum, s.Length))), count), callType, at);
                }
                default:
                    throw new NotTranslated("LINQ's " + name);
            }
        }

        private KExpr IsNaN(KExpr x, string n) => new KOp("$fp.isNaN" + n, x);

        private LSeq MappedSequence(List<IArgumentOperation> args, IInvocationOperation call, ITypeSymbol callType)
        {
            var src = Sequence(args[0].Value);
            if (args.Count == 1)
            {
                return src;
            }
            var f = LambdaArg(call, 1);
            var i = Atom();
            return new LSeq
            {
                Length = src.Length,
                Elem = KAbs.Of(i, Apply(f, src.Elem.At(i), i)),
                Type = ElementOf(callType) ?? f.body.Type,
            };
        }

        private LSeq FilteredSequence(bool withPredicate, List<IArgumentOperation> args, IInvocationOperation call, SyntaxNode at)
        {
            var src = Sequence(args[0].Value);
            if (!withPredicate || args.Count == 1)
            {
                return src;
            }
            var f = LambdaArg(call, 1);
            var x = Atom();
            return Filter(src, KAbs.Of(x, Apply(f, x)), at);
        }

        private KExpr LinqValue(KExpr v, ITypeSymbol callType, SyntaxNode at)
        {
            var t = Declare("t$" + _temps++, callType);
            Emit(KHavoc.Of(t));
            ShapeFact(Eq(new KVar(t), v), at);
            return new KVar(t);
        }

        private void CheckPrecondition(KExpr cond, string text, SyntaxNode at, string name) => Emit(KCheck.Of(Named(cond), "CSV1001", at, $"precondition '{text}' of '{name}' might not hold"));
    }
}
