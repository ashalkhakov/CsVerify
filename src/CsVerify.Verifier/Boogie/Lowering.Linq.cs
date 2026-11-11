using System;
using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.FlowAnalysis;
using Microsoft.CodeAnalysis.Operations;
using static CsVerify.Verifier.Boogie.KernelTypes;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>
    /// LINQ to Objects, as CsVerify's engine reads it from its definitions (Bcl/Linq.cs), member by member: a source the
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
        }

        private static bool IsEnumerableCall(IMethodSymbol m) => m?.ContainingType?.ToDisplayString() == "System.Linq.Enumerable";

        private int _linq;

        /// <summary>A fact of the library's, assumed as mathematics where the call is.</summary>
        private void LinqFact(KExpr fact, SyntaxNode at) => Emit(new KSpecStmt { Spec = fact, Assume = true, Free = true, At = at, ArgumentAt = at });

        private string LinqMap(string type)
        {
            var name = "lq$" + _linq++;
            _p.Locals.Add(new KLocal { Name = name, Raw = type });
            Emit(new KHavoc { Var = name });
            return name;
        }

        private static KExpr Between(KExpr lo, KExpr i, KExpr hi) => new KOp("&&", new KOp("<=", lo, i), new KOp("<", i, hi));

        private KQuant Over(KExpr lo, KExpr hi, Func<KExpr, KExpr> body, bool forall = true)
        {
            var v = "lq$i" + _linq++;
            return new KQuant { Forall = forall, Var = v, Range = Between(lo, new KVar(v), hi), Body = body(new KVar(v)) };
        }

        /// <summary>A pure lambda's body (one expression, writing nothing, calling only functions), and its parameters.</summary>
        private (IOperation body, IParameterSymbol p1, IParameterSymbol p2)? PureLambda(IOperation arg)
        {
            var fn = Unconverted(arg) is IDelegateCreationOperation dc ? dc.Target as IAnonymousFunctionOperation ?? LambdaOf(dc.Target) ?? LambdaBySymbol(dc.Target) : null;
            if (fn == null || fn.Body.Operations.Length != 1 || !(fn.Body.Operations[0] is IReturnOperation { ReturnedValue: { } body })) return null;
            foreach (var op in body.DescendantsAndSelf())
                switch (op)
                {
                    case IAssignmentOperation a when a.Parent is IAnonymousObjectCreationOperation: break; // (new { x, y = e }: its members, not writes)
                    case IAssignmentOperation _: case IIncrementOrDecrementOperation _: case IObjectCreationOperation _: case IArrayCreationOperation _:
                    case IAnonymousFunctionOperation _: case IAwaitOperation _:
                        return null;
                    case IInvocationOperation inv when !(_isFunction(inv.TargetMethod.OriginalDefinition) || inv.TargetMethod.ContainingType?.ToDisplayString() == "System.Math" ||
                                                        SpecSymbols.IsSpecClass(inv.TargetMethod.ContainingType)):
                        return null;
                }
            return (body, fn.Symbol.Parameters.ElementAtOrDefault(0), fn.Symbol.Parameters.ElementAtOrDefault(1));
        }

        /// <summary>A lambda the control flow graph has as a flow anonymous function (a query clause's): found in the method's operations by its symbol.</summary>
        private IAnonymousFunctionOperation LambdaBySymbol(IOperation target)
        {
            if (!(target is IFlowAnonymousFunctionOperation ff) || _model == null || _decl == null) return null;
            return _model.GetOperation(_decl)?.DescendantsAndSelf().OfType<IAnonymousFunctionOperation>().FirstOrDefault(a => SymbolEqualityComparer.Default.Equals(a.Symbol, ff.Symbol));
        }

        /// <summary>A lambda applied to an element (and its index): its body, its parameters bound.</summary>
        private KExpr Apply((IOperation body, IParameterSymbol p1, IParameterSymbol p2) f, KExpr x, KExpr i = null)
        {
            KExpr e = Spec(f.body, null);
            if (f.p2 != null) e = new KLet { Var = "q$" + f.p2.Name, Value = i ?? throw new NotTranslated("a lambda of an index"), Body = e };
            return new KLet { Var = "q$" + f.p1.Name, Value = x, Body = e };
        }

        private static ITypeSymbol ElementOf(ITypeSymbol t) =>
            t is IArrayTypeSymbol a ? a.ElementType : t is INamedTypeSymbol { TypeArguments.Length: >= 1 } n ? n.TypeArguments[n.TypeArguments.Length - 1] : null;

        /// <summary>A LINQ source as a sequence, read now: a query of the members here, or an array, a List, a list interface.</summary>
        private LSeq Sequence(IOperation op)
        {
            var src = Unconverted(op);
            // (a query the control flow graph captured: what it captured)
            // (and query syntax: the calls it is)
            while (src is IFlowCaptureReferenceOperation r && _captured.TryGetValue(r.Id, out var v) || src is ITranslatedQueryOperation)
                src = src is ITranslatedQueryOperation tq ? Unconverted(tq.Operation) : Unconverted(_captured[((IFlowCaptureReferenceOperation)src).Id]);
            if (src is IInvocationOperation q && IsEnumerableCall(q.TargetMethod)) return Query(q);
            var type = src.Type;
            var elem = ElementOf(type);
            if (elem == null || !InSubset(elem) || !(IsArray(type) || IsList(type) || IsCollectionInterface(type)))
                throw new NotTranslated("a LINQ source of " + type + " (" + src.Kind + ")");
            var t = Declare("t$" + _temps++, type);
            Emit(new KAssign { Var = t, Value = Expr(src) });
            Emit(new KCheck { Cond = new KOp("!=", new KVar(t), new KLit("null")), Id = "CSV1013", At = src.Syntax, Message = $"'{src.Syntax}' might be null: LINQ would throw ArgumentNullException" });
            var x = new KVar(t);
            if (IsArray(type)) return new LSeq { Length = new KOp("len", x), Elem = i => new KOp("sel", new KVar(Elements(type)), x, i), Type = elem };
            if (IsList(type))
            {
                foreach (var m in ModelsOf((INamedTypeSymbol)type)) _p.Models[m.Name] = m;
                return new LSeq { Length = new KOp("sel", new KVar(SizeMap), x), Elem = i => new KOp("sel", new KVar(ModelOf("Items", (INamedTypeSymbol)type).Name), x, i), Type = elem };
            }
            var list = (INamedTypeSymbol)KernelTypes.Compilation.GetTypeByMetadataName("System.Collections.Generic.List`1").Construct(elem);
            foreach (var m in ModelsOf(list)) _p.Models[m.Name] = m;
            _p.UsesState = true;
            return new LSeq { Length = IfcRead(x, null, elem), Elem = i => IfcRead(x, i, elem), Type = elem };
        }

        private (IOperation body, IParameterSymbol p1, IParameterSymbol p2) LambdaArg(IInvocationOperation q, int ordinal)
        {
            var arg = q.Arguments.First(a => a.Parameter.Ordinal == ordinal).Value;
            return PureLambda(arg) ?? throw new NotTranslated("a LINQ lambda that isn't pure: " + Unconverted(arg).Kind + " " + ((Unconverted(arg) as IDelegateCreationOperation)?.Target?.Kind));
        }

        /// <summary>A query: a member of Enumerable that gives a sequence.</summary>
        private LSeq Query(IInvocationOperation q)
        {
            var m = q.TargetMethod;
            var args = q.Arguments.OrderBy(a => a.Parameter.Ordinal).ToList();
            var resultElem = ElementOf(q.Type);
            switch (m.Name)
            {
                case "Select" when args.Count == 2:
                {
                    var src = Sequence(args[0].Value);
                    var f = LambdaArg(q, 1);
                    return new LSeq { Length = src.Length, Elem = i => Apply(f, src.Elem(i), i), Type = resultElem };
                }
                case "Where" when args.Count == 2:
                {
                    var src = Sequence(args[0].Value);
                    var f = LambdaArg(q, 1);
                    if (f.p2 != null) throw new NotTranslated("Where with an index");
                    return Filter(src, x => Apply(f, x), q.Syntax);
                }
                case "Distinct" when args.Count == 1:
                {
                    var src = Sequence(args[0].Value);
                    // (each element's first occurrence, in order: Q.Unseen)
                    return FilterAt(src, j => new KOp("!", new KQuantOver(this, new KLit("0"), j, k => SameValue(src.Elem(k), src.Elem(j), src.Type), forall: false).Q), q.Syntax);
                }
                case "Zip" when args.Count == 3:
                {
                    var a = Sequence(args[0].Value);
                    var b = Sequence(args[1].Value);
                    var f = LambdaArg(q, 2);
                    var fx = (f.body, f.p1, (IParameterSymbol)null);
                    return new LSeq
                    {
                        Length = new KOp("ite", new KOp("<=", a.Length, b.Length), a.Length, b.Length), Type = resultElem,
                        Elem = i => new KLet { Var = "q$" + f.p2.Name, Value = b.Elem(i), Body = Apply(fx, a.Elem(i)) },
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
                        if (!(Unconverted(SourceOf(at)) is IInvocationOperation inner && IsEnumerableCall(inner.TargetMethod) && inner.TargetMethod.Name is "OrderBy" or "OrderByDescending" or "ThenBy" or "ThenByDescending"))
                            throw new NotTranslated("a ThenBy of an order not made here");
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
                    if (f.p2 != null) throw new NotTranslated("SelectMany with an index");
                    var r = args.Count == 3 ? LambdaArg(q, 2) : default;
                    var flat = Flatten(src, j => Inner(Apply(f, src.Elem(j)), f.body), q.Syntax, out var outer, out var within);
                    if (args.Count == 2) return flat;
                    var rx = (r.body, r.p1, (IParameterSymbol)null);
                    return new LSeq { Length = flat.Length, Type = resultElem,
                                      Elem = i => new KLet { Var = "q$" + r.p2.Name, Value = flat.Elem(i), Body = Apply(rx, src.Elem(outer(i))) } };
                }
                case "Join" when args.Count == 5:
                {
                    // (each pair of an outer and an inner element, in that order, whose keys agree: Q.For, Q.For, Q.If)
                    var o = Sequence(args[0].Value);
                    var inner = Sequence(args[1].Value);
                    var (okey, ikey, sel) = (LambdaArg(q, 2), LambdaArg(q, 3), LambdaArg(q, 4));
                    var pairs = Flatten(o, j => inner, q.Syntax, out var outer, out var within);
                    var matched = FilterAt(pairs, i => SameValue(Apply(okey, o.Elem(outer(i))), Apply(ikey, inner.Elem(within(i))), okey.body.Type), q.Syntax);
                    var sx = (sel.body, sel.p1, (IParameterSymbol)null);
                    // (the matched pair i is pair ix[i]: its outer and inner elements)
                    return new LSeq
                    {
                        Length = matched.Length, Type = resultElem,
                        Elem = i => new KLet { Var = "q$" + sel.p2.Name, Value = inner.Elem(within(matched.Index(i))), Body = Apply(sx, o.Elem(outer(matched.Index(i)))) },
                    };
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
            while (src is ITranslatedQueryOperation tq) src = Unconverted(tq.Operation);
            ILocalSymbol groupOf = src is ILocalReferenceOperation gl && IsGrouping(gl.Type) ? gl.Local : null;
            if (groupOf == null && !(src is IInvocationOperation q && IsEnumerableCall(q.TargetMethod))) return false;
            var element = fo.Locals.FirstOrDefault()?.Type;
            if (element == null || !(InSubset(element) || IsGrouping(element))) return false;
            var capture = cfg.Blocks.SelectMany(b => b.Operations).OfType<IFlowCaptureOperation>()
                .FirstOrDefault(c => c.Syntax == fs.Expression && c.Value is IInvocationOperation gi && gi.TargetMethod.Name == "GetEnumerator");
            var head = capture == null ? null : cfg.Blocks.FirstOrDefault(b => b.BranchValue is IInvocationOperation mn && mn.TargetMethod.Name == "MoveNext" &&
                                                                               mn.Instance is IFlowCaptureReferenceOperation r && r.Id.Equals(capture.Id));
            if (head == null) return false;
            var n = _forEachAt.Count;
            var fe = new ForEach
            {
                Head = head.Ordinal, Index = Declare($"fe${n}$i", _model.Compilation.GetSpecialType(SpecialType.System_Int32)),
                Type = collection.Type, Element = element, At = fs.Expression, Query = groupOf == null ? src : null, GroupOf = groupOf,
                Mat = "fe$" + n + "$m", Count = Declare($"fe${n}$n", _model.Compilation.GetSpecialType(SpecialType.System_Int32)),
            };
            _p.Locals.Add(new KLocal { Name = fe.Mat, Raw = "[int]" + (IsGrouping(element) ? "int" : TypeOf(element)) });
            _forEach[capture.Id] = fe;
            _forEachAt[head.Ordinal] = fe;
            foreach (var l in fo.Locals) _forEachOf[l] = fe;
            for (var region = head.EnclosingRegion; region != null; region = region.EnclosingRegion)
                if (region.Kind == ControlFlowRegionKind.Try && region.EnclosingRegion?.Kind == ControlFlowRegionKind.TryAndFinally)
                {
                    _erased.Add(region.EnclosingRegion);
                    break;
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
                if (!_groups.TryGetValue(fe.GroupOf, out var g)) throw new NotTranslated("a group not of a GroupBy read here");
                var src = new LSeq { Length = new KVar(g.count), Elem = i => new KOp("sel", new KVar(g.map), i), Type = g.elem };
                var gv = new KVar(Declare(Local(fe.GroupOf), fe.GroupOf.Type));
                seq = Filter(src, x => SameValue(Apply(g.key, x), Apply(g.key, src.Elem(gv)), g.key.Item1.Type), at);
            }
            else if (Unconverted(fe.Query) is IInvocationOperation gb && gb.TargetMethod.Name == "GroupBy" && gb.Arguments.Length == 2 && IsGrouping(fe.Element))
            {
                var source = Sequence(gb.Arguments.First(a => a.Parameter.Ordinal == 0).Value);
                var key = LambdaArg(gb, 1);
                var map = LinqMap("[int]" + TypeOf(source.Type));
                var count = Declare("t$" + _temps++, _model.Compilation.GetSpecialType(SpecialType.System_Int32));
                Emit(new KAssign { Var = count, Value = source.Length });
                LinqFact(Over(new KLit("0"), new KVar(count), i => new KOp("==", new KOp("sel", new KVar(map), i), source.Elem(i))), at);
                var read = new LSeq { Length = new KVar(count), Elem = i => new KOp("sel", new KVar(map), i), Type = source.Type };
                // (the groups in the order their keys first appear: each one's first index)
                var firsts = FilterAt(read, j => new KOp("!", Over(new KLit("0"), j, k => SameValue(Apply(key, read.Elem(k)), Apply(key, read.Elem(j)), key.body.Type), forall: false)), at);
                seq = new LSeq { Length = firsts.Length, Elem = firsts.Index, Type = fe.Element };
                foreach (var l in _forEachOf.Where(kv => kv.Value == fe).Select(kv => kv.Key)) _groups[l] = (map, key, source.Type, count);
            }
            else seq = Sequence(fe.Query);
            Emit(new KAssign { Var = fe.Count, Value = seq.Length });
            Emit(new KHavoc { Var = fe.Mat });
            LinqFact(Over(new KLit("0"), new KVar(fe.Count), i => new KOp("==", new KOp("sel", new KVar(fe.Mat), i), seq.Elem(i))), at);
            Emit(new KAssign { Var = fe.Index, Value = new KLit("0") });
        }

        /// <summary>A group's Key: its first element's key.</summary>
        private KExpr GroupKey(ILocalSymbol g)
        {
            if (!_groups.TryGetValue(g, out var info)) throw new NotTranslated("a group not of a GroupBy read here");
            return Apply(info.key, new KOp("sel", new KVar(info.map), new KVar(Local(g))));
        }

        /// <summary>The sequence a lambda's value is (an array, a List): its length and elements.</summary>
        private LSeq Inner(KExpr value, IOperation body)
        {
            var type = Unconverted(body).Type;
            var elem = ElementOf(type);
            if (IsArray(type)) return new LSeq { Length = new KOp("len", value), Elem = i => new KOp("sel", new KVar(Elements(type)), value, i), Type = elem };
            if (IsList(type))
            {
                foreach (var m in ModelsOf((INamedTypeSymbol)type)) _p.Models[m.Name] = m;
                return new LSeq { Length = new KOp("sel", new KVar(SizeMap), value), Elem = i => new KOp("sel", new KVar(ModelOf("Items", (INamedTypeSymbol)type).Name), value, i), Type = elem };
            }
            throw new NotTranslated("an inner sequence of " + type);
        }

        /// <summary>
        /// Sequences one after another, one for each element of src: offsets o[j] (o[0] = 0, o[j + 1] = o[j] + the
        /// length of j's, never decreasing), element i at outer index out[i] and index i - o[out[i]] within it.
        /// </summary>
        private LSeq Flatten(LSeq src, Func<KExpr, LSeq> inner, SyntaxNode at, out Func<KExpr, KExpr> outer, out Func<KExpr, KExpr> within)
        {
            var o = new KVar(LinqMap("[int]int"));
            var ov = new KVar(LinqMap("[int]int"));
            var n = src.Length;
            KExpr O(KExpr j) => new KOp("sel", o, j);
            KExpr Out(KExpr i) => new KOp("sel", ov, i);
            LinqFact(new KOp("==", O(new KLit("0")), new KLit("0")), at);
            LinqFact(Over(new KLit("0"), n, j => new KOp("&&", new KOp("==", O(new KOp("+", j, new KLit("1"))), new KOp("+", O(j), inner(j).Length)), new KOp("<=", new KLit("0"), inner(j).Length))), at);
            // (monotone: an offset is no more than any later one)
            LinqFact(Over(new KLit("0"), new KOp("+", n, new KLit("1")), a => Over(a, new KOp("+", n, new KLit("1")), b => new KOp("<=", O(a), O(b)))), at);
            LinqFact(Over(new KLit("0"), O(n), i => new KOp("&&", Between(new KLit("0"), Out(i), n), new KOp("&&", new KOp("<=", O(Out(i)), i), new KOp("<", i, O(new KOp("+", Out(i), new KLit("1"))))))), at);
            outer = Out;
            within = i => new KOp("-", i, O(Out(i)));
            Func<KExpr, KExpr> w = within;
            return new LSeq { Length = O(n), Elem = i => inner(Out(i)).Elem(w(i)), Type = inner(new KLit("0")).Type };
        }

        /// <summary>Elements equal as EqualityComparer&lt;T&gt;.Default has them: values and references, a tuple by its parts.</summary>
        private static KExpr SameValue(KExpr a, KExpr b, ITypeSymbol t)
        {
            if (IsTuple(t))
            {
                var parts = PartsOf(t);
                KExpr all = new KLit("true");
                for (int k = 0; k < parts.Count; k++) all = new KOp("&&", all, SameValue(TupleItem(a, t, k), TupleItem(b, t, k), parts[k]));
                return all;
            }
            if (Scalar(t) || IsClass(t) || IsInterface(t) || t.SpecialType == SpecialType.System_Object) return new KOp("==", a, b);
            // (strings by their content, as string.Equals has them)
            if (IsString(t)) return new KOp("streq", a, b);
            throw new NotTranslated("LINQ's equality of " + t);
        }

        private sealed class KQuantOver
        {
            public KQuant Q;
            public KQuantOver(Lowering l, KExpr lo, KExpr hi, Func<KExpr, KExpr> body, bool forall) { Q = l.Over(lo, hi, body, forall); }
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
            KExpr C(KExpr j) => new KOp("sel", c, j);
            KExpr Ix(KExpr i) => new KOp("sel", ix, i);
            LinqFact(new KOp("==", C(new KLit("0")), new KLit("0")), at);
            LinqFact(Over(new KLit("0"), n, j => new KOp("==", C(new KOp("+", j, new KLit("1"))), new KOp("+", C(j), new KOp("ite", keep(j), new KLit("1"), new KLit("0"))))), at);
            LinqFact(Over(new KLit("0"), new KOp("+", n, new KLit("1")), j => new KOp("&&", new KOp("<=", new KLit("0"), C(j)), new KOp("<=", C(j), j))), at);
            LinqFact(Over(new KLit("0"), n, j => new KOp("==>", keep(j), new KOp("==", Ix(C(j)), j))), at);
            LinqFact(Over(new KLit("0"), C(n), i => new KOp("&&", new KOp("&&", Between(new KLit("0"), Ix(i), n), keep(Ix(i))), new KOp("==", C(Ix(i)), i))), at);
            LinqFact(Over(new KLit("0"), new KOp("-", C(n), new KLit("1")), i => new KOp("<", Ix(i), Ix(new KOp("+", i, new KLit("1"))))), at);
            return new LSeq { Length = C(n), Elem = i => src.Elem(Ix(i)), Type = src.Type, Index = Ix };
        }

        /// <summary>
        /// A stable sort: element i is the source's p[i], p a bijection (q its inverse), in the keys' order (the first,
        /// then the next among equal ones); keys are ordered where they are integers or chars, from the first that
        /// isn't, only those before it are (as CsVerify's engine has it).
        /// </summary>
        private LSeq Sort(LSeq src, List<((IOperation, IParameterSymbol, IParameterSymbol) key, ITypeSymbol type, bool down)> keys, SyntaxNode at)
        {
            var p = new KVar(LinqMap("[int]int"));
            var qv = new KVar(LinqMap("[int]int"));
            var n = src.Length;
            KExpr P(KExpr i) => new KOp("sel", p, i);
            KExpr Q(KExpr j) => new KOp("sel", qv, j);
            LinqFact(Over(new KLit("0"), n, i => new KOp("&&", Between(new KLit("0"), P(i), n), new KOp("==", Q(P(i)), i))), at);
            LinqFact(Over(new KLit("0"), n, j => new KOp("&&", Between(new KLit("0"), Q(j), n), new KOp("==", P(Q(j)), j))), at);
            int prefix = keys.TakeWhile(k => k.type != null && (IsIntegral(k.type) || k.type.SpecialType == SpecialType.System_Char)).Count();
            KExpr Key(int k, KExpr j) => Apply(keys[k].key, src.Elem(j));
            KExpr InOrder(KExpr a, KExpr b, int level)
            {
                if (level == prefix) return prefix == keys.Count ? new KOp("<", a, b) : new KLit("true");
                var (x, y) = (Key(level, a), Key(level, b));
                return new KOp("||", keys[level].down ? new KOp(">", x, y) : new KOp("<", x, y), new KOp("&&", new KOp("==", x, y), InOrder(a, b, level + 1)));
            }
            if (prefix > 0) LinqFact(Over(new KLit("0"), new KOp("-", n, new KLit("1")), i => InOrder(P(i), P(new KOp("+", i, new KLit("1"))), 0)), at);
            return new LSeq { Length = n, Elem = i => src.Elem(P(i)), Type = src.Type };
        }

        /// <summary>A call of Enumerable read here (in code): a query copied (ToArray, ToList), or read (Count, Sum, Max, ...).</summary>
        private KExpr Linq(IInvocationOperation call)
        {
            var m = call.TargetMethod;
            var args = call.Arguments.OrderBy(a => a.Parameter.Ordinal).ToList();
            var at = call.Syntax;
            void Need(KExpr cond, string text) => Emit(new KCheck { Cond = cond, Id = "CSV1001", At = at, Message = $"precondition '{text}' of '{m.Name}' might not hold" });
            KExpr Value(KExpr v)
            {
                var t = Declare("t$" + _temps++, call.Type);
                Emit(new KHavoc { Var = t });
                LinqFact(new KOp("==", new KVar(t), v), at);
                return new KVar(t);
            }
            LSeq Of(bool withPredicate)
            {
                var src = Sequence(args[0].Value);
                if (!withPredicate || args.Count == 1) return src;
                var f = LambdaArg(call, 1);
                return Filter(src, x => Apply(f, x), at);
            }
            LSeq Mapped()
            {
                var src = Sequence(args[0].Value);
                if (args.Count == 1) return src;
                var f = LambdaArg(call, 1);
                return new LSeq { Length = src.Length, Elem = i => Apply(f, src.Elem(i), i), Type = ElementOf(call.Type) ?? f.body.Type };
            }
            switch (m.Name)
            {
                case "ToArray" when args.Count == 1 && IsArray(call.Type):
                {
                    var s = Sequence(args[0].Value);
                    var t = Declare("t$" + _temps++, call.Type);
                    Emit(new KNew { Var = t, ArrayType = call.Type, Size = s.Length });
                    Emit(new KRow { Map = Elements(call.Type), Ref = new KVar(t),
                                    Value = new KOp("lambda", new KLit("j$: int"), new KOp("ite", Between(new KLit("0"), new KVar("j$"), s.Length), s.Elem(new KVar("j$")), new KLit(Default(s.Type) is KLit d ? d.Text : "0"))) });
                    return new KVar(t);
                }
                case "ToList" when args.Count == 1 && IsList(call.Type):
                {
                    var s = Sequence(args[0].Value);
                    var ctor = ((INamedTypeSymbol)call.Type).Constructors.FirstOrDefault(c => c.Parameters.Length == 0) ?? throw new NotTranslated("a List without its constructor");
                    var list = Invoke(ctor, null, new IArgumentOperation[0], at, null);
                    var t = Declare("t$" + _temps++, call.Type);
                    Emit(new KAssign { Var = t, Value = list });
                    var items = ModelOf("Items", (INamedTypeSymbol)call.Type);
                    Emit(new KRow { Map = items.Name, Ref = new KVar(t), Value = new KOp("lambda", new KLit("j$: int"), s.Elem(new KVar("j$"))) });
                    Emit(new KRow { Map = SizeMap, Ref = new KVar(t), Value = s.Length });
                    return new KVar(t);
                }
                case "Count" or "LongCount" when args.Count <= 2:
                    return Value(Of(true).Length);
                case "Any" when args.Count <= 2:
                    return Value(new KOp(">", Of(true).Length, new KLit("0")));
                case "All" when args.Count == 2:
                {
                    var s = Sequence(args[0].Value);
                    var f = LambdaArg(call, 1);
                    return Value(Over(new KLit("0"), s.Length, i => Apply(f, s.Elem(i))));
                }
                case "Contains" when args.Count == 2:
                {
                    var s = Sequence(args[0].Value);
                    var x = Expr(args[1].Value);
                    return Value(Over(new KLit("0"), s.Length, i => SameValue(s.Elem(i), x, s.Type), forall: false));
                }
                case "First" or "Last" or "FirstOrDefault" or "LastOrDefault" when args.Count <= 2:
                {
                    var s = Of(true);
                    var pos = m.Name.StartsWith("First") ? new KLit("0") : (KExpr)new KOp("-", s.Length, new KLit("1"));
                    if (!m.Name.EndsWith("OrDefault"))
                    {
                        Need(new KOp(">", s.Length, new KLit("0")), args.Count == 1 ? "Q.Count(source) > 0" : "a matching element");
                        return Value(s.Elem(pos));
                    }
                    if (!(Default(call.Type) is KExpr dflt)) throw new NotTranslated("a default of " + call.Type);
                    return Value(new KOp("ite", new KOp(">", s.Length, new KLit("0")), s.Elem(pos), dflt));
                }
                case "Max" or "Min" when args.Count <= 2 && IsIntegral(call.Type):
                {
                    var s = Mapped();
                    Need(new KOp(">", s.Length, new KLit("0")), "Q.Count(source) > 0");
                    var r = Declare("t$" + _temps++, call.Type);
                    Emit(new KHavoc { Var = r });
                    var rv = new KVar(r);
                    LinqFact(Over(new KLit("0"), s.Length, i => new KOp("==", s.Elem(i), rv), forall: false), at);
                    LinqFact(Over(new KLit("0"), s.Length, i => new KOp(m.Name == "Max" ? "<=" : ">=", s.Elem(i), rv)), at);
                    return rv;
                }
                case "Sum" when args.Count <= 2 && IsIntegral(call.Type):
                {
                    var s = Mapped();
                    // (every partial sum in range: .NET adds them checked)
                    var acc = new KVar(LinqMap("[int]int"));
                    KExpr A(KExpr j) => new KOp("sel", acc, j);
                    LinqFact(new KOp("==", A(new KLit("0")), new KLit("0")), at);
                    LinqFact(Over(new KLit("0"), s.Length, j => new KOp("==", A(new KOp("+", j, new KLit("1"))), new KOp("+", A(j), s.Elem(j)))), at);
                    var (lo, hi) = Range(call.Type.SpecialType);
                    Need(Over(new KLit("0"), new KOp("+", s.Length, new KLit("1")), j => new KOp("&&", new KOp("<=", Number(lo), A(j)), new KOp("<=", A(j), Number(hi)))),
                         "every partial sum in range");
                    return Value(A(s.Length));
                }
                // (floating point: IEEE, added in order from 0.0, rounded at each step, as .NET adds them)
                case "Sum" or "Average" when args.Count <= 2 && call.Type.SpecialType == SpecialType.System_Double:
                {
                    var s = Mapped();
                    if (m.Name == "Average") Need(new KOp(">", s.Length, new KLit("0")), "Q.Count(source) > 0");
                    var count = new KOp("$fp.ofReal64", new KOp("$toreal", s.Length));
                    if (s.Type.SpecialType == SpecialType.System_Double)
                    {
                        var acc = new KVar(LinqMap("[int]float53e11"));
                        KExpr A(KExpr j) => new KOp("sel", acc, j);
                        LinqFact(new KOp("==", A(new KLit("0")), FloatLiteral(0.0, call.Type)), at);
                        LinqFact(Over(new KLit("0"), s.Length, j => new KOp("==", A(new KOp("+", j, new KLit("1"))), new KOp("$fp.add64", A(j), s.Elem(j)))), at);
                        return Value(m.Name == "Sum" ? A(s.Length) : new KOp("$fp.div64", A(s.Length), count));
                    }
                    if (m.Name == "Sum" || !IsIntegral(s.Type)) throw new NotTranslated("LINQ's " + m.Name + " of " + s.Type);
                    // (an integer average: summed as long, exactly, then divided as doubles)
                    var sum = new KVar(LinqMap("[int]int"));
                    KExpr S(KExpr j) => new KOp("sel", sum, j);
                    LinqFact(new KOp("==", S(new KLit("0")), new KLit("0")), at);
                    LinqFact(Over(new KLit("0"), s.Length, j => new KOp("==", S(new KOp("+", j, new KLit("1"))), new KOp("+", S(j), s.Elem(j)))), at);
                    return Value(new KOp("$fp.div64", new KOp("$fp.ofReal64", new KOp("$toreal", S(s.Length))), count));
                }
                default:
                    throw new NotTranslated("LINQ's " + m.Name);
            }
        }
    }
}
