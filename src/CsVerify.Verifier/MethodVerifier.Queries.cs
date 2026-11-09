using System;
using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// LINQ, read from its definitions: each System.Linq.Enumerable member (and List's predicate methods) is defined
    /// by a [Comprehensions] method of the Spec library (Bcl/Linq.cs), written with CsVerify.Q, and a call is read by
    /// running that definition here, symbolically, on what the call was given.
    ///
    /// A definition's comprehension (Q.For, Q.If, Q.Yield) is put into the normal form of Cheney, Lindley and Wadler's
    /// "A Practical Theory of Language-Integrated Query" (ICFP 2013): a source is never itself a comprehension
    /// (for-yield, for-for, for-if), and conditions in a row are one (if-if); their union rule, which reorders, is not
    /// used, so the order is LINQ to Objects'. The normal form, "for each x1 of s1, each x2 of s2(x1), ..., if c, yield
    /// v", is compiled into the primitives (MethodVerifier.Linq): sources one after another for each For, a filter for
    /// the If, and the yielded values. Lengths, elements, ranges, folds, sorts and groups are the primitives' own.
    ///
    /// A member returning a sequence is a query: its result is a term standing for the call, read (its definition
    /// run) when it is enumerated, on its sources and its lambdas' captures as they are then. Any other member is read
    /// at the call: its Spec.Requires are proved there (the member throws where they do not hold), and its value is
    /// its body's. Lambdas are inlined where they are pure (PureLambdaBody); with another, or a source the verifier
    /// cannot read, the call is a library call without a contract, as is a query whose definition this cannot read
    /// (a sequence made anew for each element: groups read inside another lambda).
    /// </summary>
    internal sealed partial class MethodVerifier
    {
        // ------------------------------------------------------------------ query values

        /// <summary>A query, as its definition gives it: compiled (once) into a Sequence when it is read.</summary>
        private abstract class Qry
        {
            public Sequence Compiled;
            public ITypeSymbol ElementType;
        }

        /// <summary>A sequence of its own: a source, a range, a scan, a group.</summary>
        private sealed class QSeq : Qry { public Func<Sequence> Make; }

        private sealed class QSort : Qry
        {
            public Qry Source;
            public List<(Func<Term, Term> key, ITypeSymbol type, bool down)> Keys;
        }

        private sealed class QFor : Qry
        {
            public Qry Source;
            public Func<Term, Qry> Body;
        }

        private sealed class QIf : Qry
        {
            public Term Condition;
            public Qry Then;
        }

        /// <summary>One value, evaluated when it is read (not where only the comprehension's shape or condition is).</summary>
        private sealed class QYield : Qry
        {
            public Func<Term> Make;
            private Term _value;
            public Term Value => _value ??= Make();
        }

        private sealed class QEmpty : Qry { }

        /// <summary>A definition this cannot read (the call is then the library's).</summary>
        private sealed class NotQuery : Exception
        {
            public NotQuery(string why) : base(why) { }
        }

        /// <summary>Where a definition runs: its type parameters as the call has them, its equality epoch, its groups.</summary>
        private sealed class QueryContext
        {
            public Dictionary<ITypeSymbol, ITypeSymbol> Instantiation;
            public Term Epoch;
            public int Id;
            public List<Term> Known = new List<Term>();
            public List<Term> Requires = new List<Term>();
        }

        /// <summary>A query call's result: its definition and what it was called with (lambdas not yet bound to a state).</summary>
        private sealed class LazyQuery
        {
            public IMethodSymbol Definition;
            public List<(IParameterSymbol parameter, object value)> Args; // a Term, or a Lambda
            public Dictionary<ITypeSymbol, ITypeSymbol> Instantiation;
        }

        /// <summary>A lambda argument: its pure body and parameters, and the state its captures are read in.</summary>
        private sealed class Lambda
        {
            public IOperation Body;
            public IParameterSymbol P1, P2;
            public Frame Frame;
            /// <summary>A lambda of a query on a database: evaluated as the database does (see InDatabase).</summary>
            public bool Database;
        }

        /// <summary>A Q.Group site: each group is (site key), its elements what the definition gives for its key.</summary>
        private sealed class GroupFamily
        {
            public Func<Term, Qry> ElementsOf;
        }

        private readonly Dictionary<string, LazyQuery> _lazy = new Dictionary<string, LazyQuery>(StringComparer.Ordinal);
        private readonly Dictionary<string, Lambda> _lambdas = new Dictionary<string, Lambda>(StringComparer.Ordinal);
        private readonly Dictionary<string, Qry> _queries = new Dictionary<string, Qry>(StringComparer.Ordinal);
        private readonly Dictionary<string, ITypeSymbol> _sourceTypes = new Dictionary<string, ITypeSymbol>(StringComparer.Ordinal);
        private readonly Dictionary<string, GroupFamily> _groupFamilies = new Dictionary<string, GroupFamily>(StringComparer.Ordinal);
        private readonly Stack<QueryContext> _queryContexts = new Stack<QueryContext>();
        private int _queryIds, _boundCompile;
        private readonly Dictionary<Qry, Func<Term, Term>> _seen = new Dictionary<Qry, Func<Term, Term>>();
        private readonly HashSet<string> _nonNegative = new HashSet<string>(StringComparer.Ordinal); // (lengths)

        /// <summary>A sequence made for each element of another (its source read at a bound index) must have no axioms.</summary>
        private void BoundCompileCheck()
        {
            if (_boundCompile > 0) throw new NotQuery("a sequence made anew for each element");
        }

        private QueryContext NewContext(Dictionary<ITypeSymbol, ITypeSymbol> instantiation) => new QueryContext
        {
            Instantiation = instantiation ?? new Dictionary<ITypeSymbol, ITypeSymbol>(SymbolEqualityComparer.Default),
            Epoch = _z3.Fresh("equals", Sort.Int),
            Id = _queryIds++,
        };

        /// <summary>Runs definition code in its context: in spec mode, without obligations of ours.</summary>
        private R InContext<R>(QueryContext ctx, Func<R> fn)
        {
            _queryContexts.Push(ctx);
            _instantiations.Push(ctx.Instantiation);
            _equalityEpochs.Push(ctx.Epoch);
            bool wasCode = _codeMode;
            _codeMode = false;
            _foreignSpec++;
            try { return fn(); }
            finally
            {
                _foreignSpec--;
                _codeMode = wasCode;
                _equalityEpochs.Pop();
                _instantiations.Pop();
                _queryContexts.Pop();
            }
        }

        /// <summary>Reads a query, or gives the fallback where its definition cannot be read (state as it was).</summary>
        private R Guarded<R>(Func<R> fn, R fallback)
        {
            int facts = _quantFacts.Count, boundCompile = _boundCompile;
            try { return fn(); }
            catch (NotQuery why)
            {
                if (System.Environment.GetEnvironmentVariable("CSVERIFY_TRACE") != null) System.Console.Error.WriteLine("not a query: " + why.Message);
                while (_quantFacts.Count > facts) _quantFacts.Pop();
                _boundCompile = boundCompile;
                return fallback;
            }
        }

        private Term QueryTerm(Qry q)
        {
            var t = _z3.Fresh("query", Sort.Int);
            _queries[t.S] = q;
            return t;
        }

        private static bool IsSequenceType(ITypeSymbol t) =>
            t is INamedTypeSymbol n && (n.Name == "IEnumerable" || n.Name == "IOrderedEnumerable") && n.TypeArguments.Length == 1;

        private ITypeSymbol ElementTypeOf(ITypeSymbol t) =>
            Resolve(t) is INamedTypeSymbol n && n.TypeArguments.Length >= 1 ? Resolve(n.TypeArguments[n.TypeArguments.Length - 1]) : null;

        // ------------------------------------------------------------------ calls

        /// <summary>The LINQ calls read from their definitions (and ToList and ToArray); null for others.</summary>
        private Term LinqCall(IInvocationOperation inv, Frame f, SpecEnv spec)
        {
            // (in a lambda a definition applies, g => g.Count(): read there too)
            if (!_codeMode && _queryContexts.Count == 0) return null;
            if (_queryContexts.Count == 0) TranslationChecks(inv);
            var outer = _queryResult;
            if (_queryContexts.Count == 0) { _queryResult = inv.Type; _queryRun++; }
            try
            {
                if ((IsEnumerableMethod(inv.TargetMethod) || IsEfAsyncQuery(inv.TargetMethod)) && Copying(inv, f, spec) is Term copy) return copy;
                return QueryCall(inv, f, spec);
            }
            finally { _queryResult = outer; }
        }

        private Dictionary<ITypeSymbol, ITypeSymbol> DefinitionInstantiation(IMethodSymbol definition, IMethodSymbol called)
        {
            var map = new Dictionary<ITypeSymbol, ITypeSymbol>(SymbolEqualityComparer.Default);
            foreach (var (p, a) in definition.TypeParameters.Zip(called.TypeArguments, (p, a) => (p, a))) map[p] = Resolve(a);
            if (called.ContainingType is INamedTypeSymbol ct)
                foreach (var (p, a) in definition.ContainingType.TypeParameters.Zip(ct.TypeArguments, (p, a) => (p, a))) map[p] = Resolve(a);
            return map;
        }

        /// <summary>
        /// A call to a member with a definition: its arguments as the definition takes them (the receiver first), the
        /// lambdas checked pure and the sources readable; then a query term (for a member returning a sequence) or the
        /// definition's value.
        /// </summary>
        private Term QueryCall(IInvocationOperation inv, Frame f, SpecEnv spec)
        {
            var m = inv.TargetMethod;
            var definition = _engine.Stubs.QueryOf(m) ?? _engine.Stubs.QueryOf(EnumerableTwin(m));
            if (definition == null) return null;
            var original = _model.GetOperation(inv.Syntax) as IInvocationOperation;
            if (original != null && !SymbolEqualityComparer.Default.Equals(original.TargetMethod, m)) original = null;
            // (a query clause's call is found in its query's translation, its clause's syntax being no invocation)
            if (original == null && inv.Syntax.AncestorsAndSelf().OfType<Microsoft.CodeAnalysis.CSharp.Syntax.QueryExpressionSyntax>().LastOrDefault() is { } query)
                original = _model.GetOperation(query)?.DescendantsAndSelf().OfType<IInvocationOperation>()
                    .FirstOrDefault(c => c.Syntax == inv.Syntax && SymbolEqualityComparer.Default.Equals(c.TargetMethod, m));
            bool receiver = ContractStubs.TakesReceiver(definition);
            IOperation ArgOf(IInvocationOperation call, int k) =>
                receiver && k == 0 ? call.Instance : call.Arguments.FirstOrDefault(a => a.Parameter.Ordinal == k - (receiver ? 1 : 0))?.Value;
            // the lambdas first (making a delegate does nothing): each must be one to inline
            var lambdas = new Dictionary<int, Lambda>();
            for (int k = 0; k < definition.Parameters.Length; k++)
                if (definition.Parameters[k].Type.TypeKind == TypeKind.Delegate)
                {
                    var body = PureLambdaBody(ArgOf(original ?? inv, k), out var p1, out var p2, pair: true);
                    if (body == null) return null; // (not one to inline: the library call, which may run it)
                    lambdas[k] = new Lambda { Body = body, P1 = p1, P2 = p2 };
                }
            var args = new List<(IParameterSymbol, object)>();
            for (int k = 0; k < definition.Parameters.Length; k++)
            {
                var p = definition.Parameters[k];
                if (lambdas.TryGetValue(k, out var lambda)) { args.Add((p, lambda)); continue; }
                var op = ArgOf(inv, k);
                if (op == null) return null;
                var x = Eval(op, f, spec);
                if (IsSequenceType(p.Type) || receiver && k == 0)
                {
                    // a source: a query, a group, or what the verifier indexes
                    var type = Unconverted(op).Type;
                    x = T.Coerce(x, Sort.Int);
                    if (Indexable(type))
                    {
                        Deref(op, x, inv.Syntax);
                        _sourceTypes[x.S] = type;
                    }
                    else if (!_lazy.ContainsKey(x.S) && !_queries.ContainsKey(x.S) && GroupOf(x) == null && !_tables.ContainsKey(x.S)) return null; // (_queries: GroupJoin's matches)
                }
                args.Add((p, x));
            }
            // a query on a database: its lambdas are the database's to evaluate
            bool database = args.Any(a => a.Item2 is Term t && IsDatabaseQuery(t));
            if (database)
            {
                // (what compares values for equality is the database's: strings by collation, rows by every column)
                if (ComparesByEquality(definition)) return null;
                foreach (var l in lambdas.Values) l.Database = true;
                if (_codeMode && _queryContexts.Count == 0) DatabaseQueryChecks(inv, original ?? inv, definition, args, lambdas, f);
                // (First(p) as Where(p).First(): the rows filtered once, where the definition would filter them twice)
                if (FilteredFirst(definition, m, args) is (IMethodSymbol plain, List<(IParameterSymbol, object)> filtered))
                {
                    definition = plain;
                    args = filtered;
                }
            }
            var instantiation = DefinitionInstantiation(definition, m);
            if (!_codeMode && !IsSequenceType(definition.ReturnType))
            {
                // inside a definition (a lambda it applies): its value here. One that may throw is not read: a lambda
                // runs where .NET runs it (Count of a GroupJoin runs its selector, of an array's Select not), which
                // the definitions do not say, so its precondition could not be checked where it applies
                var outer = _queryContexts.Peek();
                var inner = NewContext(instantiation);
                var value = InContext(inner, () => RunDefinition(definition, args, f).value);
                if (inner.Requires.Any(r => r != T.True)) throw new NotQuery("a lambda's call that may throw: " + inv.Syntax);
                outer.Known.AddRange(inner.Known);
                return value ?? throw new NotQuery("a member without a value");
            }
            if (IsSequenceType(definition.ReturnType))
            {
                var result = _z3.Fresh("query", Sort.Int);
                AssumeSide(NotNull(result));
                _lazy[result.S] = new LazyQuery { Definition = definition, Args = args, Instantiation = instantiation };
                if (database) _databaseQueries.Add(result.S);
                Assumed(m.OriginalDefinition.ToDisplayString());
                return result;
            }
            return Guarded(() => EagerCall(inv, definition, args, instantiation, f), null);
        }

        /// <summary>A member read at its call: its precondition proved, its value (and its Ensures) assumed where it holds.</summary>
        private Term EagerCall(IInvocationOperation inv, IMethodSymbol definition, List<(IParameterSymbol, object)> args,
                               Dictionary<ITypeSymbol, ITypeSymbol> instantiation, Frame f)
        {
            var ctx = NewContext(instantiation);
            var (pre, known, result, facts, requiresText) = InContext(ctx, () =>
            {
                var (value, ensures, texts) = RunDefinition(definition, args, f);
                var k = T.And(ctx.Known.ToArray());
                var p = T.And(ctx.Requires.ToArray());
                Term r;
                if (value == null)
                {
                    // (a member with a precondition only: its value the library's, not null where it says so)
                    r = Unknown(inv.Type, definition.Name);
                    if (IsNonNullableReturn(inv.TargetMethod)) AssumeSide(NotNull(r));
                }
                else if (k == T.True) r = T.Coerce(value, SortOf(inv.Type));
                else
                {
                    r = Unknown(inv.Type, definition.Name);
                    AssumeSide(T.Implies(T.And(k, p), T.Eq(r, T.Coerce(value, SortOf(inv.Type)))));
                }
                var fs = ensures.Select(e => e(r)).ToList();
                return (p, k, r, fs, texts);
            });
            if (pre != T.True)
                Require(T.Implies(known, pre), "CSV1001", inv.Syntax,
                        $"'{inv.Syntax}' might throw: its precondition ({string.Join(", ", requiresText)}) might not hold");
            foreach (var fact in facts) AssumeSide(T.Implies(T.And(known, pre), fact));
            Assumed(inv.TargetMethod.OriginalDefinition.ToDisplayString());
            return result;
        }

        /// <summary>
        /// Runs a definition (in a query context) on its arguments, in the state f: its value (null where its body
        /// throws: a member whose value is not defined), its Ensures (of a result), the text of its Requires (which
        /// go into the context, as they hold of where it is called).
        /// </summary>
        private (Term value, List<Func<Term, Term>> ensures, List<string> requires) RunDefinition(IMethodSymbol definition, List<(IParameterSymbol p, object v)> args, Frame f)
        {
            var decl = definition.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() as MethodDeclarationSyntax
                       ?? throw new NotQuery("no definition");
            var model = _engine.ModelOf(decl.SyntaxTree);
            if (!(model.GetOperation(decl) is IMethodBodyOperation body)) throw new NotQuery("no body");
            var block = body.BlockBody ?? body.ExpressionBody;
            var frame = f.Clone();
            var spec = new SpecEnv { Old = _entry };
            foreach (var (p, v) in args)
            {
                if (v is Lambda l)
                {
                    var t = _z3.Fresh("lambda", Sort.Int);
                    _lambdas[t.S] = new Lambda { Body = l.Body, P1 = l.P1, P2 = l.P2, Frame = f, Database = l.Database };
                    frame.Vars[p] = t;
                }
                else if (v is Term x && (IsSequenceType(p.Type) || ContractStubs.TakesReceiver(definition) && p.Ordinal == 0))
                    frame.Vars[p] = QueryTerm(QryOf(x, null, f)); // (one query for the parameter: its every use is the same sequence)
                else frame.Vars[p] = (Term)v;
            }
            var ctx = _queryContexts.Peek();
            Term value = null;
            var ensures = new List<Func<Term, Term>>();
            var texts = new List<string>();
            foreach (var op in block.Operations)
            {
                switch (op)
                {
                    case IVariableDeclarationGroupOperation group:
                        foreach (var d in group.Declarations.SelectMany(g => g.Declarators))
                            frame.Vars[d.Symbol] = d.Initializer != null ? Eval(d.Initializer.Value, frame, spec) : Unknown(d.Symbol.Type);
                        break;
                    case IExpressionStatementOperation { Operation: IInvocationOperation c } when SpecSymbols.IsSpecClass(c.TargetMethod.ContainingType) && c.TargetMethod.Name == "Requires":
                        ctx.Requires.Add(AsBool(Eval(c.Arguments[0].Value, frame, spec)));
                        texts.Add(c.Arguments[0].Value.Syntax.ToString());
                        break;
                    case IExpressionStatementOperation { Operation: IInvocationOperation c } when SpecSymbols.IsSpecClass(c.TargetMethod.ContainingType) && c.TargetMethod.Name == "Ensures":
                    {
                        var fn = StubLambda(c.Arguments[0].Value);
                        var fr = frame;
                        ensures.Add(r => { var inner = fr.Clone(); inner.Vars[fn.Symbol.Parameters[0]] = r; return AsBool(Eval(LambdaResult(fn), inner, spec)); });
                        break;
                    }
                    case IReturnOperation r:
                        value = Eval(r.ReturnedValue, frame, spec);
                        return (value, ensures, texts);
                    case IThrowOperation _:
                        return (null, ensures, texts);
                    default:
                        throw new NotQuery("a statement a definition may not have: " + op.Syntax);
                }
            }
            return (value, ensures, texts);
        }

        private static IAnonymousFunctionOperation StubLambda(IOperation arg) =>
            (arg as IDelegateCreationOperation)?.Target as IAnonymousFunctionOperation ?? throw new NotQuery("not a lambda: " + arg.Syntax);

        private static IOperation LambdaResult(IAnonymousFunctionOperation fn) =>
            fn.Body.Operations.OfType<IReturnOperation>().FirstOrDefault()?.ReturnedValue ?? throw new NotQuery("a lambda that is not an expression");

        /// <summary>A lambda argument applied to elements (spec mode): a value of its body's type.</summary>
        private Term ApplyLambda(Lambda l, Term a, Term b = null)
        {
            var r = l.Database ? InDatabase(() => ApplyValue(l.Body, l.P1, a, l.Frame, l.P2, b)) : ApplyValue(l.Body, l.P1, a, l.Frame, l.P2, b);
            var type = Unconverted(l.Body).Type;
            if (Indexable(type)) _sourceTypes[T.Coerce(r, Sort.Int).S] = type; // (SelectMany's inner sequences)
            return r;
        }

        /// <summary>The query a term stands for: a definition's, a call's, a group's, or a source the verifier indexes.</summary>
        private Qry QryOf(Term t, ITypeSymbol type, Frame f)
        {
            t = T.Coerce(t, Sort.Int);
            if (_queries.TryGetValue(t.S, out var q)) return q;
            if (_lazy.TryGetValue(t.S, out var lazy))
            {
                // a query call: its definition run now, on its sources and its lambdas' captures as they are now
                var ctx = NewContext(lazy.Instantiation);
                var value = InContext(ctx, () => RunDefinition(lazy.Definition, lazy.Args, f).value);
                return InContext(ctx, () => QryOf(value ?? throw new NotQuery("a query without a definition"), null, f));
            }
            if (GroupOf(t) is (GroupFamily family, Term key)) return family.ElementsOf(key);
            if (_tables.TryGetValue(t.S, out var table)) return new QSeq { Make = () => TableSequence(table, f), ElementType = table.Entity.Type };
            if (!(_sourceTypes.TryGetValue(t.S, out var st) && Indexable(st))) st = type;
            if (st != null && Indexable(st))
                return new QSeq { Make = () => ListSequence(t, st, f), ElementType = ElementOf(st) };
            throw new NotQuery("a source the verifier does not read");
        }

        // ------------------------------------------------------------------ Q, and lambdas, inside definitions

        /// <summary>Inside a definition: Q's operations, the lambdas' calls, and other definitions' members.</summary>
        private Term QueryOperation(IInvocationOperation inv, Frame f, SpecEnv spec)
        {
            if (_queryContexts.Count == 0) return null;
            var m = inv.TargetMethod;
            if (m.MethodKind == MethodKind.DelegateInvoke && inv.Instance != null &&
                _lambdas.TryGetValue(T.Coerce(Eval(inv.Instance, f, spec), Sort.Int).S, out var lambda))
            {
                var a = inv.Arguments.Select(x => Eval(x.Value, f, spec)).ToList();
                return ApplyLambda(lambda, a[0], a.Count > 1 ? a[1] : null);
            }
            if (SpecSymbols.HasAttribute(m.ContainingType, "ComprehensionsAttribute"))
            {
                // another member's definition (Count(source, p) is Q.Count(Where(source, p))): run here, its Requires too
                var args = m.OriginalDefinition.Parameters.Select(p => (p, (object)Eval(inv.Arguments.First(a => a.Parameter.Ordinal == p.Ordinal).Value, f, spec))).ToList();
                var map = DefinitionInstantiation(m.OriginalDefinition, m);
                var ctx = _queryContexts.Peek();
                var inner = NewContext(map);
                var value = InContext(inner, () => RunDefinition(m.OriginalDefinition, args, f).value);
                ctx.Requires.AddRange(inner.Requires);
                ctx.Known.AddRange(inner.Known);
                return value ?? throw new NotQuery("a member without a value");
            }
            if (!SpecSymbols.IsCsVerifyType(m.ContainingType, "Q")) return null;
            return QOperation(inv, f, spec);
        }

        private Term QOperation(IInvocationOperation inv, Frame f, SpecEnv spec)
        {
            var m = inv.TargetMethod;
            var ctx = _queryContexts.Peek();
            IOperation Op(int k) => inv.Arguments.First(a => a.Parameter.Ordinal == k).Value;
            Term A(int k) => Eval(Op(k), f, spec);
            Qry S(int k) => QryOf(A(k), Unconverted(Op(k)).Type, f);
            var element = ElementTypeOf(m.ReturnType);
            Func<Term, Qry> Body(int k)
            {
                var fn = StubLambda(Op(k));
                var result = LambdaResult(fn);
                return e => InContext(ctx, () =>
                {
                    var inner = f.Clone();
                    inner.Vars[fn.Symbol.Parameters[0]] = e;
                    return QryOf(Eval(result, inner, spec), Unconverted(result).Type, f);
                });
            }
            Sequence Read(Qry q)
            {
                var s = Compile(q);
                ctx.Known.Add(s.Known);
                return s;
            }
            switch (m.Name)
            {
                case "For":
                    return QueryTerm(new QFor { Source = S(0), Body = Body(1), ElementType = element });
                case "If":
                    return QueryTerm(new QIf { Condition = AsBool(A(0)), Then = S(1), ElementType = element });
                case "Yield":
                {
                    var op = Op(0);
                    return QueryTerm(new QYield { Make = () => InContext(ctx, () => Eval(op, f, spec)), ElementType = element });
                }
                case "Empty":
                    return QueryTerm(new QEmpty { ElementType = element });
                case "Range":
                {
                    var lo = T.Coerce(A(0), Sort.Int);
                    var hi = T.Coerce(A(1), Sort.Int);
                    // (from 0 to a count: as many as the count, each its index)
                    bool fromZero = lo.S == "0";
                    var length = fromZero && _nonNegative.Contains(hi.S) ? hi : T.Ite(T.Lt(lo, hi), T.Sub(hi, lo), T.Int(0));
                    return QueryTerm(new QSeq
                    {
                        ElementType = element,
                        Make = () => new Sequence { Length = length, Element = i => fromZero ? i : T.Add(lo, i), ElementType = element },
                    });
                }
                case "Count":
                {
                    var n = Read(S(0)).Length;
                    _nonNegative.Add(n.S);
                    return n;
                }
                case "At":
                {
                    var s = Read(S(0));
                    return T.Coerce(s.Element(T.Coerce(A(1), Sort.Int)), SortOf(Resolve(inv.Type)));
                }
                case "Unseen":
                {
                    // none before it equal: for keys compared as SMT values, a running set of those seen (one store a
                    // step, no quantifier inside); for others, a quantifier over the earlier ones
                    var q = S(0);
                    var s = Read(q);
                    var j = T.Coerce(A(1), Sort.Int);
                    var t = Resolve(m.TypeArguments[0]);
                    if (!KnownEquality(t))
                    {
                        var relation = "equals:" + t.ToDisplayString();
                        return OverIndices("forall", T.Int(0), j, i => T.Not(_z3.Apply(relation, Sort.Bool,
                            new[] { T.Coerce(s.Element(i), Sort.Int), T.Coerce(s.Element(j), Sort.Int), ctx.Epoch })));
                    }
                    if (!_seen.TryGetValue(q, out var seen))
                    {
                        BoundCompileCheck();
                        var name = "seen#" + _materialized++;
                        Term Seen(Term i) => _z3.Apply(name, Sort.Row, new[] { i });
                        AssumeSide(T.Implies(s.Known, T.And(T.Eq(Seen(T.Int(0)), T.ZeroRow()),
                            OverIndices("forall", T.Int(0), s.Length, i => T.Eq(Seen(T.Add(i, T.Int(1))), T.Store(Seen(i), T.Coerce(s.Element(i), Sort.Int), T.Int(1))),
                                        pattern: i => Seen(T.Add(i, T.Int(1))), pattern2: Seen))));
                        _seen[q] = seen = Seen;
                    }
                    return T.Eq(T.Select(seen(j), T.Coerce(s.Element(j), Sort.Int), Sort.Int), T.Int(0));
                }
                case "Fold":
                case "Scan":
                {
                    var s = Read(S(0));
                    var accType = Resolve(m.TypeArguments[1]);
                    var accSort = SortOf(accType);
                    // the accumulator in its own sort: an integer or a flag, or a float (IEEE, as the steps round)
                    if (accSort != Sort.Int && accSort != Sort.Bool && accSort != Sort.F32 && accSort != Sort.F64) throw new NotQuery("a fold of " + accType);
                    var runSort = accSort == Sort.Bool ? Sort.Int : accSort;
                    var seed = A(1);
                    var elementSort = SortOf(Resolve(m.TypeArguments[0]));
                    Func<Term, Term, Term> Step;
                    if ((Op(2) as IDelegateCreationOperation)?.Target is IAnonymousFunctionOperation fn)
                    {
                        var result = LambdaResult(fn);
                        Step = (acc, x) => InContext(ctx, () =>
                        {
                            var inner = f.Clone();
                            inner.Vars[fn.Symbol.Parameters[0]] = T.Coerce(acc, accSort);
                            inner.Vars[fn.Symbol.Parameters[1]] = T.Coerce(x, elementSort);
                            return T.Coerce(Eval(result, inner, spec), runSort);
                        });
                    }
                    else if (_lambdas.TryGetValue(T.Coerce(A(2), Sort.Int).S, out var given) && given.P2 != null)
                        // the program's own lambda, passed on (Aggregate's func)
                        Step = (acc, x) => T.Coerce(ApplyLambda(given, T.Coerce(acc, accSort), T.Coerce(x, elementSort)), runSort);
                    else throw new NotQuery("a fold by what is not a lambda");
                    var run = Recur(m.Name.ToLowerInvariant(), s.Length, T.Coerce(seed, runSort), (a, j) => Step(a, s.Element(j)), s.Known, runSort);
                    if (m.Name == "Fold") return T.Coerce(run(s.Length), accSort);
                    var scanned = new Sequence { Length = s.Length, Element = j => T.Coerce(run(T.Add(j, T.Int(1))), accSort), ElementType = accType, Known = s.Known };
                    return QueryTerm(new QSeq { Make = () => scanned, ElementType = accType });
                }
                case "Sort":
                case "ThenSort":
                {
                    var source = S(0);
                    if (!_lambdas.TryGetValue(T.Coerce(A(1), Sort.Int).S, out var key)) throw new NotQuery("a sort by a key that is not a lambda");
                    if (!(Op(2).ConstantValue is { HasValue: true, Value: bool down })) throw new NotQuery("a sort's direction is not a constant");
                    var entry = ((Func<Term, Term>)(e => ApplyLambda(key, e)), Resolve(m.TypeArguments[1]), down);
                    if (m.Name == "Sort") return QueryTerm(new QSort { Source = source, Keys = new List<(Func<Term, Term>, ITypeSymbol, bool)> { entry }, ElementType = element });
                    if (!(source is QSort sorted)) throw new NotQuery("ThenBy of what is not a sort");
                    return QueryTerm(new QSort { Source = sorted.Source, Keys = sorted.Keys.Concat(new[] { entry }).ToList(), ElementType = element });
                }
                case "Group":
                {
                    // a group: (site key), the site this Q.Group in this run of its definition
                    var key = A(0);
                    var elementsOf = Body(1);
                    var name = $"group#{ctx.Id}#{inv.Syntax.SpanStart}";
                    var g = _z3.Apply(name, Sort.Int, new[] { T.Coerce(key, Sort.Int) });
                    var head = g.S.Substring(1, g.S.IndexOf(' ') - 1);
                    // groups are objects: not null (one axiom for the site, not a fact at each read)
                    _z3.AssumeOnce(head, () =>
                    {
                        var k = _z3.FreshName("key");
                        return new Term($"(forall (({k} Int)) (! (not (= ({head} {k}) 0)) :pattern (({head} {k}))))", Sort.Bool);
                    });
                    _groupFamilies[head] = new GroupFamily { ElementsOf = elementsOf };
                    return g;
                }
            }
            throw new NotQuery("Q." + m.Name);
        }

        // ------------------------------------------------------------------ compiling

        private Sequence Empty(ITypeSymbol elementType) =>
            new Sequence { Length = T.Int(0), Element = _ => T.Int(0), ElementType = elementType };

        private static Q2 Expect<Q2>(Qry q) where Q2 : Qry =>
            q as Q2 ?? throw new NotQuery("a comprehension whose shape is not the same for every element");

        /// <summary>A query's sequence (once for each query value).</summary>
        private Sequence Compile(Qry q)
        {
            if (q.Compiled != null) return q.Compiled;
            Sequence s;
            switch (q)
            {
                case QSeq x: s = x.Make(); break;
                case QSort x: s = SortSequence(Compile(x.Source), x.Keys, x.ElementType); break;
                case QYield y: s = new Sequence { Length = T.Int(1), Element = _ => y.Value, ElementType = q.ElementType }; break;
                case QEmpty _: s = Empty(q.ElementType); break;
                case QIf c:
                {
                    var then = Compile(c.Then);
                    s = new Sequence { Length = T.Ite(c.Condition, then.Length, T.Int(0)), Element = then.Element, ElementType = q.ElementType, Known = then.Known };
                    break;
                }
                case QFor x: s = CompileFor(x); break;
                default: throw new NotQuery("a query");
            }
            return q.Compiled = s;
        }

        /// <summary>A For: its source normalised (never a comprehension), then each element's rest of the comprehension.</summary>
        private Sequence CompileFor(QFor q)
        {
            var source = q.Source;
            var body = q.Body;
            while (true)
            {
                switch (source)
                {
                    case QYield y: // for-yield
                        return Compile(body(y.Value));
                    case QEmpty _:
                        return Empty(q.ElementType);
                    case QIf c: // for-if
                        return Compile(new QIf { Condition = c.Condition, Then = new QFor { Source = c.Then, Body = body, ElementType = q.ElementType }, ElementType = q.ElementType });
                    case QFor inner: // for-for
                    {
                        var b1 = inner.Body;
                        var b2 = body;
                        source = inner.Source;
                        body = x => new QFor { Source = b1(x), Body = b2, ElementType = q.ElementType };
                        continue;
                    }
                }
                break;
            }
            var d = Compile(source);
            return CompileDomain(d.Length, i => body(d.Element(i)), d.Known, q.ElementType);
        }

        /// <summary>
        /// The rest of a comprehension at a probe index: its shape, which is the same at every index. What reading it
        /// says of the probe is dropped (the probe is no index); what it says of anything else is kept.
        /// </summary>
        private Qry Probe(Func<Term, Qry> rest, out Term probe)
        {
            probe = _z3.Fresh("probe", Sort.Int);
            int facts = _quantFacts.Count;
            _quantFacts.Push(new List<Term>());
            try { return rest(probe); }
            finally
            {
                var collected = _quantFacts.Count > facts ? _quantFacts.Pop() : new List<Term>();
                while (_quantFacts.Count > facts) _quantFacts.Pop();
                var p = probe.S;
                foreach (var fact in collected.Where(x => !x.S.Contains(p))) AssumeSide(fact);
            }
        }

        /// <summary>
        /// The sequence of indices 0..length, each with the rest of its comprehension: a yield is the sequence of the
        /// values; an If filters the indices (conditions in a row are one); a For flattens (each index's source one
        /// after another), its own source normalised first; a bare sequence is its elements.
        /// </summary>
        private Sequence CompileDomain(Term length, Func<Term, Qry> rest, Term known, ITypeSymbol elementType)
        {
            while (true)
            {
                var shape = Probe(rest, out _);
                var r0 = rest;
                switch (shape)
                {
                    case QYield _:
                        return new Sequence { Length = length, Element = i => Expect<QYield>(r0(i)).Value, ElementType = elementType, Known = known };
                    case QEmpty _:
                        return Empty(elementType);
                    case QIf _:
                    {
                        Term Condition(Term i)
                        {
                            var r = r0(i);
                            var c = T.True;
                            while (r is QIf x) { c = T.And(c, x.Condition); r = x.Then; }
                            return c;
                        }
                        Qry Then(Term i)
                        {
                            var r = r0(i);
                            while (r is QIf x) r = x.Then;
                            return r;
                        }
                        var indices = new Sequence { Length = length, Element = i => i, Known = known };
                        var kept = Filter(indices, Condition, null, out var index);
                        length = kept.Length;
                        rest = k => Then(index(k));
                        continue;
                    }
                    case QFor first:
                    {
                        switch (first.Source)
                        {
                            case QYield _:
                                rest = i => { var x = Expect<QFor>(r0(i)); return x.Body(Expect<QYield>(x.Source).Value); };
                                continue;
                            case QEmpty _:
                                return Empty(elementType);
                            case QIf _:
                                rest = i =>
                                {
                                    var x = Expect<QFor>(r0(i));
                                    var c = Expect<QIf>(x.Source);
                                    return new QIf { Condition = c.Condition, Then = new QFor { Source = c.Then, Body = x.Body, ElementType = x.ElementType }, ElementType = x.ElementType };
                                };
                                continue;
                            case QFor _:
                                rest = i =>
                                {
                                    var x = Expect<QFor>(r0(i));
                                    var y = Expect<QFor>(x.Source);
                                    return new QFor { Source = y.Source, Body = e => new QFor { Source = y.Body(e), Body = x.Body, ElementType = x.ElementType }, ElementType = x.ElementType };
                                };
                                continue;
                        }
                        // each index's source, one after another. The same source for every index (Join's inner) is
                        // compiled once; one made for each index must be one without axioms (a lambda's list).
                        Qry SourceAt(Term i) => Expect<QFor>(r0(i)).Source;
                        var once = Probe(SourceAt, out _);
                        var again = Probe(SourceAt, out _);
                        Func<Term, Sequence> inner;
                        if (ReferenceEquals(once, again))
                        {
                            var closed = Compile(once);
                            inner = _ => closed;
                        }
                        else
                            inner = i =>
                            {
                                _boundCompile++;
                                try { return Compile(SourceAt(i)); }
                                finally { _boundCompile--; }
                            };
                        var indices = new Sequence { Length = length, Element = i => i, Known = known };
                        var allKnown = T.And(known, OverIndices("forall", T.Int(0), length, j => inner(j).Known));
                        var flat = Flatten(indices, inner, elementType, allKnown, out var outer, out var within);
                        rest = k => Expect<QFor>(r0(outer(k))).Body(inner(outer(k)).Element(within(k)));
                        length = flat.Length;
                        known = flat.Known;
                        continue;
                    }
                    default:
                        // a sequence as a For's body: its elements
                        rest = i => new QFor { Source = r0(i), Body = y => new QYield { Make = () => y, ElementType = elementType }, ElementType = elementType };
                        continue;
                }
            }
        }

        // ------------------------------------------------------------------ reading queries from outside

        /// <summary>
        /// The sequence a term stands for (a query call's, a group's, a source the verifier indexes), read now: its
        /// elements re-enter its definitions when they are read. Null where it cannot be read.
        /// </summary>
        private Sequence SequenceOfTerm(Term x, ITypeSymbol type, Frame f)
        {
            x = T.Coerce(x, Sort.Int);
            if (!(_lazy.ContainsKey(x.S) || _queries.ContainsKey(x.S) || GroupOf(x) != null || _tables.ContainsKey(x.S) || type != null && Indexable(type))) return null;
            var ctx = NewContext(null);
            return Guarded(() =>
            {
                var s = InContext(ctx, () => Compile(QryOf(x, type, f)));
                return new Sequence
                {
                    Length = s.Length, ElementType = s.ElementType, Known = s.Known,
                    Element = i => Guarded(() => InContext(ctx, () => s.Element(i)), (Term)_z3.Fresh("element", Sort.Int)),
                };
            }, null);
        }

        /// <summary>A group term's family and key, if it is one.</summary>
        private (GroupFamily family, Term key)? GroupOf(Term t)
        {
            if (!t.S.StartsWith("(", StringComparison.Ordinal)) return null;
            int space = t.S.IndexOf(' ');
            if (space < 0) return null;
            var head = t.S.Substring(1, space - 1);
            if (!_groupFamilies.TryGetValue(head, out var family)) return null;
            return (family, new Term(t.S.Substring(space + 1, t.S.Length - space - 2), Sort.Int));
        }

        /// <summary>IGrouping.Key of a group a definition made.</summary>
        private Term GroupKey(IPropertyReferenceOperation pr, Frame f, SpecEnv spec)
        {
            if (pr.Instance == null || pr.Property.Name != "Key" || pr.Property.ContainingType?.Name != "IGrouping") return null;
            var x = T.Coerce(Eval(pr.Instance, f, spec), Sort.Int);
            return GroupOf(x) is (GroupFamily, Term key) ? T.Coerce(key, SortOf(pr.Type)) : null;
        }

        /// <summary>
        /// A foreach's collection that is a query this can read (a call with a definition, its lambdas pure, its
        /// sources read too), or a group: its element type; else null.
        /// </summary>
        private ITypeSymbol ViewForEachElement(IOperation collection)
        {
            var op = Unconverted(collection);
            var call = ViewCall(op);
            if (call == null && Unconverted(_model.GetOperation(op.Syntax) ?? op) is IPropertyReferenceOperation { Property.ContainingType.IsAnonymousType: true } && IsSequenceType(op.Type))
                return ((INamedTypeSymbol)op.Type).TypeArguments[0]; // (GroupJoin's matches carried in new { x, ys }: read if a query)
            if (call == null && op.Type is INamedTypeSymbol grouping && grouping.Name == "IGrouping" && grouping.TypeArguments.Length == 2)
                return grouping.TypeArguments[1]; // (a group: read if it is one a definition made)
            if (!ReadableView(call)) return null;
            return call.Type is INamedTypeSymbol t && t.TypeArguments.Length == 1 ? t.TypeArguments[0] : null;
        }

        /// <summary>Is this call a query QueryCall reads, over sources it reads (as the syntax shows)?</summary>
        private bool ReadableView(IInvocationOperation c)
        {
            var definition = c == null ? null : _engine.Stubs.QueryOf(c.TargetMethod);
            if (definition == null || !IsSequenceType(definition.ReturnType)) return false;
            bool receiver = ContractStubs.TakesReceiver(definition);
            for (int k = 0; k < definition.Parameters.Length; k++)
            {
                var p = definition.Parameters[k];
                var op = receiver && k == 0 ? c.Instance : c.Arguments.FirstOrDefault(a => a.Parameter.Ordinal == k - (receiver ? 1 : 0))?.Value;
                if (op == null) return false;
                if (p.Type.TypeKind == TypeKind.Delegate && PureLambdaBody(op, out _, out _, pair: true) == null) return false;
                if (IsSequenceType(p.Type) || receiver && k == 0)
                {
                    var s = Unconverted(op);
                    if (!(Indexable(s.Type) || ReadableView(ViewCall(s)))) return false;
                }
            }
            return true;
        }

        /// <summary>The call an operation is (query syntax: the last call of its translation).</summary>
        private IInvocationOperation ViewCall(IOperation op)
        {
            var o = _model.GetOperation(op.Syntax) ?? op;
            if (o is ITranslatedQueryOperation tq) o = tq.Operation;
            return o as IInvocationOperation ?? op as IInvocationOperation;
        }

        /// <summary>The query a foreach over one runs over: read when the loop began.</summary>
        private Sequence ViewSequenceOf(Loop loop, Term view, Frame f)
        {
            if (f.ViewSequences.TryGetValue(loop.Id, out var known)) return (Sequence)known;
            var seq = SequenceOfTerm(view, null, f);
            f.ViewSequences[loop.Id] = seq;
            return seq;
        }
    }
}
