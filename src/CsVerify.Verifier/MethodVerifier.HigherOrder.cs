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

        /// <summary>A delegate handed to a library, which may call it with anything: it must be total.</summary>
        private void HandedToLibrary(IMethodSymbol m, IEnumerable<IArgumentOperation> args, Frame f, SpecEnv spec)
        {
            if (!_codeMode || _foreignSpec > 0 || m.DeclaringSyntaxReferences.Length > 0 || m.MethodKind == MethodKind.DelegateInvoke) return;
            foreach (var a in args)
            {
                if (!(a.Parameter?.Type is INamedTypeSymbol type) || !IsPlainDelegate(type)) continue;
                var value = Unconverted(a.Value);
                if (value is IDelegateCreationOperation made)
                {
                    if (DelegateRequires(made.Target).Count > 0)
                        Report("CSV1029", a.Syntax, $"'{m.Name}' may call what it is given here with any arguments, but this requires something of them: drop the precondition, or check it inside", isError: true);
                    continue;
                }
                var known = value is ILocalReferenceOperation || value is IParameterReferenceOperation || value is IFieldReferenceOperation;
                Prove(known ? TotalOf(type, Eval(a.Value, f, spec)) : T.False, "CSV1029", a.Syntax,
                    $"'{m.Name}' may call '{a.Value.Syntax}' with any arguments, but it isn't known to accept them all: say so with Spec.Requires(Spec.Total({a.Value.Syntax}))");
            }
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
