using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.FlowAnalysis;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// What a delegate without a contract (a Func, an Action, a delegate type with no [ContractClassFor]) accepts and
    /// gives, as Dafny's <c>f.requires</c> and <c>f.ensures</c>: <c>Spec.Pre(f, x)</c> and <c>Spec.Post(f, x, r)</c>,
    /// functions of the delegate value and its arguments, the same in every state; <c>Spec.Total(f)</c> is Spec.Pre
    /// for every argument.
    /// <list type="bullet">
    /// <item>A call <c>f(x)</c> proves <c>Spec.Pre(f, x)</c> and gives a result r with <c>Spec.Post(f, x, r)</c>.</item>
    /// <item>No delegate is taken to be total: what one from a parameter, a field or a call accepts is what a
    /// specification says, and nothing otherwise, as in ATS.</item>
    /// <item>A lambda made a delegate defines them: its Spec.Pre is its own Spec.Requires (total without one, since its
    /// body is proved for every argument), and its Spec.Post implies what it ensures and, for an expression, its value.
    /// Both are taken only as far as they depend on its parameters and on captured variables that never change; a
    /// precondition that depends on more can't be a Spec.Pre, so it is reported (CSV1029). A method group made one
    /// gives its method's contract the same way.</item>
    /// <item>A delegate handed to a library (Task.Run, List.ForEach, a query) may be called with anything, so it must
    /// be total (CSV1029).</item>
    /// <item>A lambda knows the preconditions of the method it is in that are of what never changes (Spec.Total of a
    /// parameter never assigned): they held when it was made and still do.</item>
    /// </list>
    /// </summary>
    internal sealed partial class MethodVerifier
    {
        /// <summary>A delegate type whose calls have no contract of their own: Spec.Pre and Spec.Post speak of them.</summary>
        private bool IsPlainDelegate(ITypeSymbol t) =>
            t is INamedTypeSymbol { TypeKind: TypeKind.Delegate } d && d.DelegateInvokeMethod != null && !_engine.HasDelegateContract(d);

        private (Term[] args, Term result) DelegateSignature(INamedTypeSymbol type, IReadOnlyList<Term> args, Term result)
        {
            var invoke = type.DelegateInvokeMethod;
            var a = invoke.Parameters.Select((p, i) => T.Coerce(args[i], SortOf(p.Type))).ToArray();
            var r = invoke.ReturnsVoid || result == null ? null : T.Coerce(result, SortOf(invoke.ReturnType));
            return (a, r);
        }

        private Term PreOf(INamedTypeSymbol type, Term d, IReadOnlyList<Term> args)
        {
            var (a, _) = DelegateSignature(type, args, null);
            return _z3.Apply("cv_pre", Sort.Bool, new[] { T.Coerce(d, Sort.Int) }.Concat(a).ToArray());
        }

        private Term PostOf(INamedTypeSymbol type, Term d, IReadOnlyList<Term> args, Term result)
        {
            var (a, r) = DelegateSignature(type, args, result);
            var all = new[] { T.Coerce(d, Sort.Int) }.Concat(a);
            if (r != null) all = all.Append(r);
            return _z3.Apply("cv_post", Sort.Bool, all.ToArray());
        }

        /// <summary>The delegate accepts any arguments: its Spec.Pre holds for all of them.</summary>
        private Term TotalOf(INamedTypeSymbol type, Term d)
        {
            var invoke = type.DelegateInvokeMethod;
            var sorts = invoke.Parameters.Select(p => SortOf(p.Type)).ToArray();
            var key = "total:" + string.Join(",", sorts);
            _z3.AssumeOnce(key, () =>
            {
                var dv = new Term(_z3.FreshName("d"), Sort.Int);
                var xs = sorts.Select(s => new Term(_z3.FreshName("x"), s)).ToArray();
                var total = _z3.Apply("cv_total" + sorts.Length, Sort.Bool, new[] { dv });
                var pre = _z3.Apply("cv_pre", Sort.Bool, new[] { dv }.Concat(xs).ToArray());
                var forward = Forall(new[] { dv }.Concat(xs).ToArray(), T.Implies(total, pre), pre);
                // and back: Spec.Pre at a witness the function picks for d (if it holds there, it holds everywhere)
                var witness = sorts.Select((s, i) => _z3.Apply("cv_witness" + sorts.Length + "_" + i, s, new[] { dv })).ToArray();
                var back = Forall(new[] { dv }, T.Implies(_z3.Apply("cv_pre", Sort.Bool, new[] { dv }.Concat(witness).ToArray()), total), total);
                return T.And(forward, back);
            });
            return _z3.Apply("cv_total" + sorts.Length, Sort.Bool, new[] { T.Coerce(d, Sort.Int) });
        }

        private static Term Forall(IReadOnlyList<Term> vars, Term body, Term pattern) =>
            vars.Count == 0 ? body
            : new Term($"(forall ({string.Join(" ", vars.Select(v => $"({v.S} {T.SortName(v.Sort)})"))}) (! {body.S} :pattern ({pattern.S})))", Sort.Bool);

        /// <summary>The precondition a lambda or method group made a delegate has (its own, for a lambda).</summary>
        private IReadOnlyList<IOperation> DelegateRequires(IOperation target) => target switch
        {
            IAnonymousFunctionOperation fn => _engine.ContractOf(fn.Symbol).OwnRequires,
            IFlowAnonymousFunctionOperation ffn => _engine.ContractOf(ffn.Symbol).OwnRequires,
            IMethodReferenceOperation mr => _engine.ContractOf(mr.Method).Requires,
            _ => new IOperation[0],
        };

        private static IMethodSymbol DelegateTarget(IOperation target) => target switch
        {
            IAnonymousFunctionOperation fn => fn.Symbol,
            IFlowAnonymousFunctionOperation ffn => ffn.Symbol,
            IMethodReferenceOperation mr => mr.Method,
            _ => null,
        };

        // ---- the hook: every delegate value the method computes

        private void DelegateValue(IOperation op, Term t, Frame f)
        {
            // (in a callee's contract, its parameters are the arguments: what they are is the caller's to say)
            if (_foreignSpec > 0 || !(op is IDelegateCreationOperation dc) || !(op.Type is INamedTypeSymbol type) || !IsPlainDelegate(type)) return;
            DelegateMade(dc, type, t, f);
        }

        /// <summary>
        /// A delegate handed to a library: the library's call of it must be allowed. What the library passes it is
        /// known for some members, and then only that must be accepted; otherwise it may pass anything, so the delegate
        /// must be total (proved, not just a lambda without a precondition: one whose precondition always holds is too).
        /// <list type="bullet">
        /// <item>A stub that says what it needs of the delegate (its Spec.Requires name it in Spec.Pre or Spec.Total)
        /// has that proved where it is called, as all its preconditions are.</item>
        /// <item>The members that call it on the elements of a list or an array, and on nothing else, before they return
        /// (List.ForEach, Exists, Find..., Array.ForEach..., and the LINQ members that aren't lazy: Any, All, Count,
        /// First, Sum...): Spec.Pre for each element, when the delegate is a lambda or method group that changes
        /// neither the list nor any array (so the elements it is given are those there now).</item>
        /// <item>Parallel.For(from, to, body): Spec.Pre(body, i) for each i in [from, to).</item>
        /// </list>
        /// </summary>
        private void HandedToLibrary(IMethodSymbol m, IEnumerable<IArgumentOperation> args, Frame f, SpecEnv spec, IOperation instance = null)
        {
            if (!_codeMode || _foreignSpec > 0 || m.DeclaringSyntaxReferences.Length > 0 || m.MethodKind == MethodKind.DelegateInvoke) return;
            var callee = _engine.ContractOf(m);
            var argList = args.ToList();
            foreach (var a in argList)
            {
                if (!(a.Parameter?.Type is INamedTypeSymbol type) || !IsPlainDelegate(type)) continue;
                if (callee.IsStub && StubSpeaksOf(callee, a.Parameter.Name)) continue;
                var value = Unconverted(a.Value);
                bool made = value is IDelegateCreationOperation;
                if (made && DelegateRequires(((IDelegateCreationOperation)value).Target).Count == 0) continue; // (total: its body is proved for anything)
                var known = made || value is ILocalReferenceOperation || value is IParameterReferenceOperation || value is IFieldReferenceOperation;
                if (!known)
                {
                    Prove(T.False, "CSV1029", a.Syntax, $"'{m.Name}' may call '{a.Value.Syntax}' with any arguments, but it isn't known to accept them all: keep it in a local said to be Spec.Total");
                    continue;
                }
                var d = Eval(a.Value, f, spec);
                // Parallel.For(from, to, body): body(i) for each i from 'from' up to 'to', whatever body does
                if (m.ContainingType?.ToDisplayString() == "System.Threading.Tasks.Parallel" && m.Name == "For" && a.Parameter.Ordinal == 2 &&
                    type.DelegateInvokeMethod.Parameters.Length == 1 && type.DelegateInvokeMethod.Parameters[0].Type.SpecialType == SpecialType.System_Int32 &&
                    argList.FirstOrDefault(x => x.Parameter?.Ordinal == 0) is IArgumentOperation fromArg && argList.FirstOrDefault(x => x.Parameter?.Ordinal == 1) is IArgumentOperation toArg)
                {
                    var lo = T.Coerce(Eval(fromArg.Value, f, spec), Sort.Int);
                    var hi = T.Coerce(Eval(toArg.Value, f, spec), Sort.Int);
                    var k = new Term(_z3.FreshName("i"), Sort.Int);
                    Prove(T.Quant("forall", k.S, T.Implies(T.And(T.Le(lo, k), T.Lt(k, hi)), PreOf(type, d, new[] { k }))), "CSV1001", a.Syntax,
                        $"'{m.Name}' calls this with each index from {fromArg.Value.Syntax} up to {toArg.Value.Syntax}, but it might not accept them all");
                    continue;
                }
                if (made && EachElement(m, a, argList, instance, f, spec) is (Term length, System.Func<Term, Term> element, Term listKnown))
                {
                    var i = new Term(_z3.FreshName("i"), Sort.Int);
                    // (facts of the element, its range, are of the bound index: hypotheses inside, not facts outside)
                    _quantDepth++;
                    _quantFacts.Push(new List<Term>());
                    Term pre;
                    List<Term> facts;
                    try { pre = PreOf(type, d, new[] { element(i) }); }
                    finally { facts = _quantFacts.Pop(); _quantDepth--; }
                    foreach (var plain in facts.Where(x => !x.S.Contains(i.S))) AssumeSide(plain);
                    var each = T.Quant("forall", i.S, T.Implies(T.And(new[] { listKnown, T.Le(T.Int(0), i), T.Lt(i, length) }.Concat(facts.Where(x => x.S.Contains(i.S))).ToArray()), pre));
                    Prove(each, "CSV1001", a.Syntax, $"'{m.Name}' calls this with each element, but it might not accept them all (its Spec.Requires)");
                    continue;
                }
                Prove(TotalOf(type, d), "CSV1029", a.Syntax, made
                    ? $"'{m.Name}' may call this with any arguments, but its precondition might not hold for them all"
                    : $"'{m.Name}' may call '{a.Value.Syntax}' with any arguments, but it isn't known to accept them all: say so with Spec.Requires(Spec.Total({a.Value.Syntax}))");
            }
        }

        // ---- library members that change nothing they are given: a call changes only what the code it runs does

        private static readonly HashSet<string> ReadOnlyCollectionMembers = new HashSet<string>
        {
            "Exists", "TrueForAll", "Find", "FindIndex", "FindLast", "FindLastIndex", "FindAll", "ConvertAll", "ForEach",
            "Contains", "IndexOf", "LastIndexOf",
        };

        /// <summary>
        /// A library member that writes nothing it is given, nor any state of the program's: every LINQ member (they
        /// read their sources, and make what they return), and the List and Array members that only look. What a call
        /// of one changes is what the program code it runs changes, its delegates' included.
        /// </summary>
        private static bool ReadsOnly(IMethodSymbol m)
        {
            var owner = (m.ReducedFrom ?? m).ContainingType?.OriginalDefinition.ToDisplayString();
            return owner == "System.Linq.Enumerable"
                || owner == "System.Collections.Generic.List<T>" && !m.IsStatic && ReadOnlyCollectionMembers.Contains(m.Name)
                || owner == "System.Array" && m.IsStatic && ReadOnlyCollectionMembers.Contains(m.Name);
        }

        /// <summary>A delegate argument whose code is in sight (a lambda, a method group) and writes no arrays.</summary>
        private bool WritesNoArrays(IOperation value) =>
            Unconverted(value) is IDelegateCreationOperation dc && DelegateTarget(dc.Target) is IMethodSymbol fn && !_engine.MayWriteHeap(fn);

        /// <summary>A delegate argument whose code is in sight and writes no field nor model state.</summary>
        private bool WritesNoFields(IOperation value)
        {
            if (!(Unconverted(value) is IDelegateCreationOperation dc) || !(DelegateTarget(dc.Target) is IMethodSymbol fn)) return false;
            if (fn.MethodKind != MethodKind.AnonymousFunction)
            {
                var (fields, all) = _engine.Fields.WritesOf(fn);
                return !all && fields.Count == 0;
            }
            // a lambda: its own code, looked at here (its effects are counted with its method's, not on their own)
            var syntax = fn.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax();
            var model = syntax == null ? null : _engine.Compilation.GetSemanticModel(syntax.SyntaxTree);
            var body = model?.GetOperation(syntax);
            if (body == null) return false;
            foreach (var op in body.DescendantsAndSelf())
            {
                if (SpecSymbols.EnclosingSpecCall(op.Syntax, model) != null) continue;
                switch (op)
                {
                    case IAssignmentOperation a when !(a.Target is ILocalReferenceOperation || a.Target is IParameterReferenceOperation && ((IParameterReferenceOperation)a.Target).Parameter.RefKind == RefKind.None):
                    case IIncrementOrDecrementOperation inc when !(inc.Target is ILocalReferenceOperation || inc.Target is IParameterReferenceOperation):
                    case IDeconstructionAssignmentOperation _:
                    case IObjectCreationOperation _:
                        return false;
                    case IArgumentOperation arg when arg.Parameter?.RefKind != RefKind.None && arg.Parameter?.RefKind != RefKind.In:
                        return false;
                    case IInvocationOperation inv when !(SpecSymbols.IsSpecClass(inv.TargetMethod.ContainingType) || _engine.ContractOf(inv.TargetMethod).IsPure ||
                                                         inv.TargetMethod.DeclaringSyntaxReferences.Length > 0 && inv.TargetMethod.MethodKind != MethodKind.AnonymousFunction &&
                                                         inv.TargetMethod.MethodKind != MethodKind.LocalFunction && _engine.Fields.WritesOf(inv.TargetMethod) is var w && !w.all && w.fields.Count == 0):
                        return false;
                }
            }
            return true;
        }

        /// <summary>Does this call of a library member keep the arrays as they are: it reads only, and runs nothing that writes one?</summary>
        private bool KeepsArrays(IInvocationOperation inv) => ReadsOnly(inv.TargetMethod) && !_engine.Fields.RunsOtherCodeAt(inv, WritesNoArrays);

        /// <summary>And the fields and model state (a list's elements)?</summary>
        private bool KeepsFields(IInvocationOperation inv) => ReadsOnly(inv.TargetMethod) && !_engine.Fields.RunsOtherCodeAt(inv, WritesNoFields);

        /// <summary>Does the stub's precondition say what the delegate parameter must accept?</summary>
        private static bool StubSpeaksOf(Contract stub, string parameter) =>
            stub.Requires.Any(r => r.DescendantsAndSelf().OfType<IInvocationOperation>().Any(i =>
                SpecSymbols.IsSpecClass(i.TargetMethod.ContainingType) && (i.TargetMethod.Name == "Pre" || i.TargetMethod.Name == "Total") &&
                i.Arguments.Length > 0 && Unconverted(i.Arguments[0].Value) is IParameterReferenceOperation p && p.Parameter.Name == parameter));

        private static readonly HashSet<string> EagerEnumerable = new HashSet<string>
        {
            "Any", "All", "Count", "LongCount", "First", "FirstOrDefault", "Last", "LastOrDefault", "Single", "SingleOrDefault",
            "Sum", "Min", "Max", "Average", "ToDictionary",
        };

        private static readonly HashSet<string> ElementwiseCollection = new HashSet<string>
        {
            "ForEach", "Exists", "TrueForAll", "Find", "FindIndex", "FindLast", "FindLastIndex", "FindAll", "RemoveAll", "ConvertAll",
        };

        /// <summary>
        /// If the library calls this delegate with the elements of a list or array, and nothing else, before it returns:
        /// that sequence (its length, its element at an index, when that is what it is).
        /// </summary>
        private (Term, System.Func<Term, Term>, Term)? EachElement(IMethodSymbol m, IArgumentOperation a, List<IArgumentOperation> args, IOperation instance, Frame f, SpecEnv spec)
        {
            var type = (INamedTypeSymbol)a.Parameter.Type;
            if (type.DelegateInvokeMethod.Parameters.Length != 1) return null;
            var owner = m.ContainingType?.OriginalDefinition.ToDisplayString();
            IOperation source;
            if (owner == "System.Linq.Enumerable" && EagerEnumerable.Contains(m.Name) && a.Parameter.Ordinal == 1)
                source = args.FirstOrDefault(x => x.Parameter?.Ordinal == 0)?.Value;
            else if (owner == "System.Array" && ElementwiseCollection.Contains(m.Name) && m.IsStatic)
                source = args.FirstOrDefault(x => x.Parameter?.Ordinal == 0)?.Value;
            else if (owner == "System.Collections.Generic.List<T>" && ElementwiseCollection.Contains(m.Name) && !m.IsStatic)
                source = instance;
            else return null;
            source = Unconverted(source);
            // (read again here: only what reading twice can't change)
            if (!(source is ILocalReferenceOperation || source is IParameterReferenceOperation || source is IFieldReferenceOperation)) return null;
            var sourceType = source.Type;
            bool array = sourceType is IArrayTypeSymbol, list = IsListType(sourceType);
            if (!array && !list) return null;
            if (!SymbolEqualityComparer.Default.Equals(ElementOf(sourceType), type.DelegateInvokeMethod.Parameters[0].Type)) return null;
            // (it changes neither the list nor an array: the elements it is called with are those there now)
            var fn = DelegateTarget(((IDelegateCreationOperation)Unconverted(a.Value)).Target);
            if (fn == null || _engine.MayTouchArrays(fn) && array) return null;
            if (list && !WritesNoFields(a.Value)) return null; // (nor the list's model state)
            var seq = ListSequence(T.Coerce(Eval(source, f, spec), Sort.Int), sourceType, f);
            return (seq.Length, seq.Element, seq.Known);
        }

        /// <summary>A lambda knows what the method it is in requires of what never changes: Spec.Total(g) of a parameter g never assigned.</summary>
        private void EnclosingFacts(Frame f, SpecEnv spec)
        {
            if (_method.MethodKind != MethodKind.AnonymousFunction && _method.MethodKind != MethodKind.LocalFunction) return;
            var outer = _contract.Declaration?.Ancestors().OfType<BaseMethodDeclarationSyntax>().FirstOrDefault();
            if (outer == null || !(_model.GetDeclaredSymbol(outer) is IMethodSymbol enclosing)) return;
            var none = new HashSet<ISymbol>(SymbolEqualityComparer.Default);
            foreach (var req in _engine.ContractOf(enclosing).Requires)
                if (req.DescendantsAndSelf().OfType<IInvocationOperation>().Any(i => SpecSymbols.IsSpecClass(i.TargetMethod.ContainingType) && (i.TargetMethod.Name == "Pre" || i.TargetMethod.Name == "Total")) &&
                    Steady(req, none, _method))
                    _z3.Assume(AsBool(EvalSpec(req, f, spec)));
        }

        // ---- a lambda or method group made a delegate: its Spec.Pre and Spec.Post

        private void DelegateMade(IDelegateCreationOperation dc, INamedTypeSymbol type, Term d, Frame f)
        {
            var fn = DelegateTarget(dc.Target);
            if (fn == null) return;
            var c = _engine.ContractOf(fn);
            var requires = DelegateRequires(dc.Target);
            var ps = type.DelegateInvokeMethod.Parameters.Length == fn.Parameters.Length ? fn.Parameters : default;
            if (ps.IsDefault) return;
            var own = new HashSet<ISymbol>(ps, SymbolEqualityComparer.Default);
            if (requires.Count == 0) AssumeSide(TotalOf(type, d)); // (its body is proved for any arguments)
            else if (requires.All(r => Steady(r, own, fn)))
            {
                var xs = Bound(ps);
                var pre = PreOf(type, d, xs);
                var given = Closed(ps, xs, f, inner => T.And(requires.Select(r => AsBool(EvalForeignSpec(r, inner, new SpecEnv { Old = inner }))).ToArray()));
                AssumeSide(Forall(xs, T.Eq(pre, given), pre));
            }
            else if (_codeMode && _foreignSpec == 0)
                Report("CSV1029", dc.Syntax, $"the precondition of what is made a '{type.Name}' here depends on state that may change, so it can't be its Spec.Pre: " +
                                             "make it depend only on the parameters and captured variables that never change, or use a delegate type with a contract", isError: true);

            // what it gives: its postconditions, and an expression's value
            var invoke = type.DelegateInvokeMethod;
            var facts = new List<(IReadOnlyList<Term> xs, Term r, Term fact)>();
            foreach (var post in c.Ensures)
            {
                var ownR = new HashSet<ISymbol>(own, SymbolEqualityComparer.Default);
                if (post.ResultParameter != null) ownR.Add(post.ResultParameter);
                if (post.Guard != null || !Steady(post.Expr, ownR, fn)) continue;
                var xs = Bound(ps);
                var r = invoke.ReturnsVoid ? null : new Term(_z3.FreshName("r"), SortOf(invoke.ReturnType));
                var fact = Closed(ps, xs, f, inner => AsBool(EvalForeignSpec(post.Expr, inner, new SpecEnv { Old = inner, Result = r, ResultParameter = post.ResultParameter })));
                facts.Add((xs, r, fact));
            }
            if (!invoke.ReturnsVoid && ValueOf(fn) is IOperation body && Steady(body, own, fn))
            {
                var xs = Bound(ps);
                var r = new Term(_z3.FreshName("r"), SortOf(invoke.ReturnType));
                var value = Closed(ps, xs, f, inner => EvalSpec(body, inner, null));
                facts.Add((xs, r, T.Eq(r, T.Coerce(value, r.Sort))));
            }
            foreach (var (xs, r, fact) in facts)
            {
                var post = PostOf(type, d, xs, r);
                var vars = r == null ? xs.ToArray() : xs.Append(r).ToArray();
                AssumeSide(Forall(vars, T.Implies(T.And(post, PreOf(type, d, xs)), fact), post));
            }
        }

        private Term[] Bound(IReadOnlyList<IParameterSymbol> ps) => ps.Select(p => new Term(_z3.FreshName(p.Name), SortOf(p.Type))).ToArray();

        /// <summary>Evaluates a condition of the parameters, bound to <paramref name="xs"/>, with the captured variables as they are now.</summary>
        private Term Closed(IReadOnlyList<IParameterSymbol> ps, IReadOnlyList<Term> xs, Frame f, System.Func<Frame, Term> eval)
        {
            var inner = f.Clone();
            for (int i = 0; i < ps.Count; i++) inner.Vars[ps[i]] = xs[i];
            _quantDepth++;
            _quantFacts.Push(new List<Term>());
            _obligations.Push(new List<Obligation>()); // (well-definedness is the lambda's own to prove)
            try
            {
                var t = eval(inner);
                var collected = _quantFacts.Pop();
                return T.And(collected.Append(t).ToArray());
            }
            finally { _obligations.Pop(); _quantDepth--; }
        }

        /// <summary>A lambda's value as one expression (<c>x => x + 1</c>, or a block that only returns one), if it is one.</summary>
        private IOperation ValueOf(IMethodSymbol fn)
        {
            if (fn.MethodKind != MethodKind.AnonymousFunction || !(fn.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() is AnonymousFunctionExpressionSyntax syntax)) return null;
            var model = _engine.ContractOf(fn).Model;
            if (model == null) return null;
            if (syntax.ExpressionBody != null) return model.GetOperation(syntax.ExpressionBody);
            var rest = syntax.Block?.Statements.Where(s => !(s is ExpressionStatementSyntax es && es.Expression is InvocationExpressionSyntax inv &&
                                                             model.GetSymbolInfo(inv).Symbol is IMethodSymbol m && SpecSymbols.IsSpecClass(m.ContainingType))).ToList();
            return rest?.Count == 1 && rest[0] is ReturnStatementSyntax ret && ret.Expression != null ? model.GetOperation(ret.Expression) : null;
        }

        /// <summary>
        /// Does this depend only on <paramref name="own"/> parameters, constants, and captured variables that are never
        /// written after they're declared, through arithmetic, comparisons, Spec.Pre/Post and static [Pure] functions of values?
        /// </summary>
        private bool Steady(IOperation op, ISet<ISymbol> own, IMethodSymbol fn)
        {
            if (op == null) return false;
            if (op.ConstantValue.HasValue) return true;
            switch (op)
            {
                case IParameterReferenceOperation p:
                    return own.Contains(p.Parameter) || !SymbolEqualityComparer.Default.Equals(p.Parameter.ContainingSymbol, fn) && p.Parameter.RefKind == RefKind.None && NeverWritten(p.Parameter);
                case ILocalReferenceOperation l:
                    return !SymbolEqualityComparer.Default.Equals(l.Local.ContainingSymbol, fn) && l.Local.RefKind == RefKind.None && NeverWritten(l.Local);
                case IBinaryOperation _:
                case IUnaryOperation _:
                case IConversionOperation _:
                case IParenthesizedOperation _:
                case IConditionalOperation _:
                    return op.ChildOperations.All(ch => Steady(ch, own, fn));
                case IInvocationOperation inv when SpecSymbols.IsSpecClass(inv.TargetMethod.ContainingType) && (inv.TargetMethod.Name == "Pre" || inv.TargetMethod.Name == "Post" || inv.TargetMethod.Name == "Total"):
                    return inv.Arguments.All(a => Steady(a.Value, own, fn));
                case IInvocationOperation inv when inv.Instance == null && _engine.ContractOf(inv.TargetMethod).IsPure &&
                                                   inv.TargetMethod.Parameters.All(p => p.Type.IsValueType) && inv.TargetMethod.ReturnType.IsValueType:
                    return inv.Arguments.All(a => Steady(a.Value, own, fn));
                default:
                    return false;
            }
        }

        /// <summary>A local or parameter assigned nowhere after its declaration (nor passed by ref or out).</summary>
        private bool NeverWritten(ISymbol s)
        {
            var owner = s.ContainingSymbol?.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax();
            if (owner == null) return false;
            var model = _engine.Compilation.GetSemanticModel(owner.SyntaxTree);
            foreach (var id in owner.DescendantNodes().OfType<IdentifierNameSyntax>())
            {
                if (id.Identifier.Text != s.Name || !SymbolEqualityComparer.Default.Equals(model.GetSymbolInfo(id).Symbol, s)) continue;
                SyntaxNode e = id;
                while (e.Parent is ParenthesizedExpressionSyntax) e = e.Parent;
                if (e.Parent is AssignmentExpressionSyntax a && a.Left == e) return false;
                if (e.Parent is PrefixUnaryExpressionSyntax || e.Parent is PostfixUnaryExpressionSyntax pu && !pu.IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.SuppressNullableWarningExpression)) return false;
                if (e.Parent is ArgumentSyntax arg && !arg.RefKindKeyword.IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.None)) return false;
            }
            return true;
        }

        // ---- a call of a delegate

        private void DelegateCalled(IInvocationOperation inv, Term receiver, Term[] args)
        {
            if (!(inv.TargetMethod.ContainingType is INamedTypeSymbol type) || inv.TargetMethod.MethodKind != MethodKind.DelegateInvoke || !IsPlainDelegate(type) || receiver == null) return;
            Require(PreOf(type, receiver, args), "CSV1001", inv.Syntax,
                $"'{inv.Instance?.Syntax}' might not accept these arguments: say what it accepts with Spec.Requires(Spec.Pre({inv.Instance?.Syntax}, ...))");
        }

        private void DelegateGave(IInvocationOperation inv, Term receiver, Term[] args, Term result)
        {
            if (!(inv.TargetMethod.ContainingType is INamedTypeSymbol type) || inv.TargetMethod.MethodKind != MethodKind.DelegateInvoke || !IsPlainDelegate(type) || receiver == null) return;
            _z3.Assume(PostOf(type, receiver, args, inv.TargetMethod.ReturnsVoid ? null : result));
        }
    }
}
