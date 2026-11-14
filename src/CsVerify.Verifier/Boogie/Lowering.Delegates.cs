using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.FlowAnalysis;
using Microsoft.CodeAnalysis.Operations;
using static CsVerify.Verifier.Boogie.KernelTypes;
using static CsVerify.Verifier.Boogie.KOp;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>Delegates: lambdas and method groups made into delegates, their calls, what they capture and write.</summary>
    internal sealed partial class Lowering
    {
        private static AnonymousFunctionExpressionSyntax LambdaSyntax(IArgumentOperation a) =>
            (a.Syntax as ArgumentSyntax)?.Expression as AnonymousFunctionExpressionSyntax ?? a.Value.Syntax as AnonymousFunctionExpressionSyntax;

        /// <summary>Locals that lambdas and local functions here write: unknown after every call that may run one.</summary>
        private HashSet<ISymbol> _capturedWrites;

        private HashSet<ISymbol> CapturedWrites()
        {
            if (_capturedWrites != null)
            {
                return _capturedWrites;
            }
            _capturedWrites = new HashSet<ISymbol>(SymbolEqualityComparer.Default);
            foreach (var fn in _decl.DescendantNodes().Where(n => n is AnonymousFunctionExpressionSyntax || n is LocalFunctionStatementSyntax))
            {
                foreach (var id in fn.DescendantNodes().OfType<IdentifierNameSyntax>())
                {
                    SyntaxNode e = id;
                    while (e.Parent is ParenthesizedExpressionSyntax)
                    {
                        e = e.Parent;
                    }
                    // (++x, --x, x++, x--: not -x, !x, x!)
                    bool written = e.Parent is AssignmentExpressionSyntax a && a.Left == e ||
                                   e.Parent is PrefixUnaryExpressionSyntax pre && pre.Kind() is Microsoft.CodeAnalysis.CSharp.SyntaxKind.PreIncrementExpression or Microsoft.CodeAnalysis.CSharp.SyntaxKind.PreDecrementExpression ||
                                   e.Parent is PostfixUnaryExpressionSyntax pu && !pu.IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.SuppressNullableWarningExpression) ||
                                   e.Parent is ArgumentSyntax arg && !arg.RefKindKeyword.IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.None);
                    if (written && _model.GetSymbolInfo(id).Symbol is ISymbol s && s is ILocalSymbol or IParameterSymbol { RefKind: RefKind.None } &&
                        SymbolEqualityComparer.Default.Equals(s.ContainingSymbol, s is IParameterSymbol ? _m : s.ContainingSymbol) &&
                        !fn.Span.Contains(s.DeclaringSyntaxReferences.FirstOrDefault()?.Span ?? default))
                    {
                        _capturedWrites.Add(s);
                    }
                }
            }
            return _capturedWrites;
        }

        /// <summary>After a call that may run a lambda that writes locals: those locals are unknown.</summary>
        private void ForgetCaptured()
        {
            foreach (var s in CapturedWrites())
            {
                var type = s is IParameterSymbol ps ? ps.Type : ((ILocalSymbol)s).Type;
                if (!InSubset(type))
                {
                    throw new NotTranslated("a lambda that writes a variable of " + type);
                }
                Emit(KHavoc.Of(s is IParameterSymbol p ? _assigned[p] : Declare(Local(s), type)));
            }
        }

        /// <summary>A lambda, as written (the control-flow graph has its own operation for it).</summary>
        private IAnonymousFunctionOperation LambdaOf(IOperation target) => target switch
        {
            IAnonymousFunctionOperation af => af,
            IFlowAnonymousFunctionOperation ff => ff.Symbol.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() is SyntaxNode syn ? _model.GetOperation(syn) as IAnonymousFunctionOperation : null,
            _ => null,
        };

        private bool Contracted(ITypeSymbol t) =>
            t is INamedTypeSymbol { TypeKind: TypeKind.Delegate } d && d.DelegateInvokeMethod != null && IsDelegate(d) && _contractOf?.Invoke(d.DelegateInvokeMethod) is Contract c && c.OfDelegate;

        private void DelegatesHere(string what)
        {
            // (under Spec.Modifies, its frame is checked as for any write: a call of one that may change anything breaks it)
            if (_p.UsesPerm)
            {
                throw new NotTranslated(what + " with permissions");
            }
        }

        /// <summary>Does the lambda read a variable of the method's that holds permissions (a view, a share, a package)?</summary>
        private bool CapturesPermissions(IAnonymousFunctionOperation af) =>
            af.Body.DescendantsAndSelf().Any(o => (o is ILocalReferenceOperation l && !SymbolEqualityComparer.Default.Equals(l.Local.ContainingSymbol, af.Symbol) ? l.Local.Type :
                                                   o is IParameterReferenceOperation p && !SymbolEqualityComparer.Default.Equals(p.Parameter.ContainingSymbol, af.Symbol) ? p.Parameter.Type : null)
                                                  is ITypeSymbol t && (IsView(t) || IsMemView(t) || IsShare(t) || IsPackage(t)));

        private KExpr DelegateCall(IInvocationOperation call)
        {
            if (!IsFunc(call.Instance?.Type))
            {
                throw new NotTranslated("a call of a delegate of " + call.Instance?.Type);
            }
            var throwsTo = _cfgBlock != null ? ThrowTarget(_cfgBlock.EnclosingRegion) : null;
            var values = Operands(new[] { call.Instance }.Concat(call.Arguments.OrderBy(a => a.Parameter.Ordinal).Select(a => a.Value)).ToArray());
            var key = FuncKey(call.Instance.Type);
            _p.AddDelegateKey(key);
            _p.CallsDelegates = true;
            var result = call.TargetMethod.ReturnsVoid ? null : Declare("t$" + _temps++, call.TargetMethod.ReturnType);
            // (under Spec.Modifies: what it may change must be in the frame; one that changes nothing is, any other may not be, CSV1017)
            if (_contract.Modifies != null)
            {
                Emit(KCheck.Of(
                    new KOp("$nochange", values[0]),
                    "CSV1017",
                    call.Syntax,
                    $"'{call.Syntax}' calls a delegate that may write anything, which Spec.Modifies doesn't allow (say what it may change with Spec.ChangesNothing)"));
            }
            // (holding permissions: a delegate without a contract is given none, so it may only be one that changes nothing)
            else if (_p.UsesPerm)
            {
                Emit(KCheck.Of(
                    new KOp("$nochange", values[0]),
                    "CSV1016",
                    call.Syntax,
                    $"'{call.Syntax}' calls a delegate that may write anything, which this method's permissions don't allow (say it changes nothing with Spec.ChangesNothing)"));
            }
            Emit(new KInvoke
            {
                Result = result,
                Delegate = values[0],
                Args = values.Skip(1).ToArray(),
                Key = key,
                At = call.Syntax,
                DelegateAt = call.Instance.Syntax,
            });
            // (where exceptions are seen: it may throw, anything)
            if (throwsTo != null)
            {
                Emit(new KFork
                {
                    Overflow = KLit.False,
                    Target = throwsTo,
                    Exception = null,
                });
            }
            ForgetCaptured();
            return result == null ? null : new KVar(result);
        }

        /// <summary>
        /// A lambda made a Func or an Action: what it accepts is its Spec.Requires, what it gives its postconditions and an
        /// expression's value, as far as they depend on its parameters and what never changes (the rest left out); it
        /// changes nothing if it writes nothing. Its body is verified on its own.
        /// </summary>
        private KExpr Lambda(IDelegateCreationOperation dc, IAnonymousFunctionOperation af)
        {
            // (made, it changes nothing: under Spec.Modifies, and holding permissions, too; but one that captures a view, a
            // share or a package would hold its permissions twice)
            if (_p.UsesPerm && CapturesPermissions(af))
            {
                throw new NotTranslated("a lambda that captures a view, a share or a package");
            }
            var fn = af.Symbol;
            var c = _contractOf?.Invoke(fn) ?? throw new NotTranslated("a lambda without its contract");
            var own = new HashSet<ISymbol>(fn.Parameters, SymbolEqualityComparer.Default);
            var key = FuncKey(dc.Type);
            _p.AddDelegateKey(key);
            var invoke = ((INamedTypeSymbol)dc.Type).DelegateInvokeMethod;
            var t = Declare("t$" + _temps++, dc.Type);
            var lam = new KLambda
            {
                Var = t,
                Key = key,
                ResultType = invoke.ReturnsVoid ? null : TypeOf(invoke.ReturnType),
                NoChange = WritesNothing(af),
                Steady = true,
            };
            foreach (var p in fn.Parameters)
            {
                lam.AddParam(("q$" + p.Name, TypeOf(p.Type)));
            }
            if (!c.OwnRequires.All(r => Steady(r, own)))
            {
                // (one that reads state says what with its own Spec.Reads: its precondition is of the state it's made in,
                // and holds while what it reads stays as it is; what the precondition reads must be in that frame)
                var objects = new List<IOperation>();
                if (c.Reads == null || !Steady(c.Reads, own) || !c.OwnRequires.All(r => StateRead(r, own, objects)))
                {
                    Emit(KCheck.Of(
                        KLit.False,
                        "CSV1029",
                        notAssumedAfter: true,
                        at: dc.Syntax,
                        message: $"the precondition of what is made a '{dc.Type.Name}' here depends on state that may change: " +
                                               "say what it reads with Spec.Reads(...) in the lambda (fields and array cells of the objects it names), or use a delegate type with a contract"));
                    Emit(new KNewObj
                    {
                        Var = t,
                        Type = dc.Type,
                        At = dc.Syntax,
                        Args = new KExpr[0],
                        ArgsAt = new SyntaxNode[0],
                    });
                    return new KVar(t);
                }
                lam.Steady = false;
                var frame = Spec(c.Reads, null);
                lam.PreS = AndAll(c.OwnRequires.Select(r => Spec(r, null)));
                lam.Reads = frame;
                foreach (var o in objects)
                {
                    Emit(KCheck.Of(
                        Forall(lam.Params, Sel(frame, Spec(o, null))),
                        "CSV1029",
                        notAssumedAfter: true,
                        at: o.Syntax,
                        message: $"the precondition reads '{o.Syntax}', which isn't in its Spec.Reads"));
                }
                // (what it gives, where it changes nothing and reads only its frame: of the state it's made in, as its precondition)
                if (lam.NoChange)
                {
                    foreach (var post in c.Ensures.Where(e => e.Guard == null))
                    {
                        var mine = new HashSet<ISymbol>(own, SymbolEqualityComparer.Default);
                        if (post.ResultParameter != null)
                        {
                            mine.Add(post.ResultParameter);
                        }
                        var read = new List<IOperation>();
                        var postBody = Unconverted(post.Expr);
                        if (postBody is IDelegateCreationOperation pd)
                        {
                            postBody = Unconverted(pd.Target);
                        }
                        if (postBody is IAnonymousFunctionOperation pf && pf.Body.Operations.Length == 1 && pf.Body.Operations[0] is IReturnOperation { ReturnedValue: { } pv })
                        {
                            postBody = pv;
                            foreach (var x in pf.Symbol.Parameters)
                            {
                                mine.Add(x);
                            }
                        }
                        if (!StateRead(postBody, mine, read))
                        {
                            continue;
                        }
                        if (!read.All(o => objects.Any(x => x.Syntax.IsEquivalentTo(o.Syntax))))
                        {
                            continue;
                        }
                        lam.AddPostS(Spec(post.Expr, post.ResultParameter));
                    }
                }
            }
            else if (c.OwnRequires.Count > 0)
            {
                lam.Pre = AndAll(c.OwnRequires.Select(r => Spec(r, null)));
            }
            if (c.Modifies != null && Steady(c.Modifies, own))
            {
                lam.Changes = Spec(c.Modifies, null);
                lam.NoChange = false;
            }
            foreach (var post in c.Ensures.Where(e => e.Guard == null && lam.Steady))
            {
                var mine = new HashSet<ISymbol>(own, SymbolEqualityComparer.Default);
                if (post.ResultParameter != null)
                {
                    mine.Add(post.ResultParameter);
                }
                if (!Steady(post.Expr, mine))
                {
                    continue;
                }
                lam.AddPost(Spec(post.Expr, post.ResultParameter));
            }
            // (of Spec.Reads, changing nothing: the value it returns, where its body is specifications and a return, of its frame)
            if (!lam.Steady && lam.NoChange && lam.Reads != null && !invoke.ReturnsVoid && fn.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() is AnonymousFunctionExpressionSyntax lfn)
            {
                var returned = ReturnedOf(lfn);
                var frameObjects = new List<IOperation>();
                foreach (var r in c.OwnRequires)
                {
                    StateRead(r, own, frameObjects);
                }
                var valueRead = new List<IOperation>();
                if (returned != null && _model.GetOperation(returned) is IOperation rv && StateRead(rv, own, valueRead) && valueRead.All(o => frameObjects.Any(x => x.Syntax.IsEquivalentTo(o.Syntax))))
                {
                    try
                    {
                        lam.AddPostS(Eq(new KVar("result"), Spec(rv, null)));
                    }
                    catch (NotTranslated) { }
                }
            }
            // (an expression's value)
            if (lam.Steady && !invoke.ReturnsVoid && fn.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() is AnonymousFunctionExpressionSyntax sfn && ReturnedOf(sfn) is ExpressionSyntax body &&
                _model.GetOperation(body) is IOperation value && Steady(value, own))
            {
                try
                {
                    lam.AddPost(Eq(new KVar("result"), Spec(value, null)));
                }
                catch (NotTranslated) { }
            }
            Emit(lam);
            return new KVar(t);
        }

        /// <summary>What a lambda returns, where its body is that expression, or specifications and a return of it; null otherwise.</summary>
        private static ExpressionSyntax ReturnedOf(AnonymousFunctionExpressionSyntax f)
        {
            if (f.ExpressionBody is ExpressionSyntax e)
            {
                return e;
            }
            if (f.Block is BlockSyntax b && b.Statements.Count > 0 && b.Statements.Last() is ReturnStatementSyntax { Expression: { } r } &&
                b.Statements.Take(b.Statements.Count - 1).All(st => st is ExpressionStatementSyntax es && es.Expression is InvocationExpressionSyntax si && si.Expression.ToString().StartsWith("Spec.")))
            {
                return r;
            }
            return null;
        }

        /// <summary>
        /// A static method made a Func or an Action: what it accepts is its precondition, what it gives its
        /// postconditions, as far as they're steady; it changes nothing if it's [Pure].
        /// </summary>
        private KExpr MethodGroup(IDelegateCreationOperation dc, IMethodSymbol fn, IOperation instance)
        {
            // (holding permissions: of an [Owned] object, the delegate would need its view, which it isn't given)
            if (_p.UsesPerm && (instance != null && IsOwnedClass(instance.Type) || fn.Parameters.Any(p => IsView(p.Type) || IsShare(p.Type) || IsPackage(p.Type))))
            {
                throw new NotTranslated("a method group of an [Owned] object's, or of views, with permissions");
            }
            var c = _contractOf?.Invoke(fn) ?? throw new NotTranslated("a method group without its contract");
            var invoke = ((INamedTypeSymbol)dc.Type).DelegateInvokeMethod;
            if (invoke.Parameters.Length != fn.Parameters.Length || fn.Parameters.Any(p => p.RefKind != RefKind.None))
            {
                throw new NotTranslated("a method group of another shape");
            }
            if (c.Modifies != null || c.Reads != null)
            {
                throw new NotTranslated("a method group with Spec.Modifies or Spec.Reads");
            }
            // (a generic method's, Id<int>: its contract is of the definition's parameters, boxes where they're of a T)
            var def = fn.OriginalDefinition;
            var own = new HashSet<ISymbol>(def.Parameters, SymbolEqualityComparer.Default);
            if (!c.Requires.All(r => Steady(r, own)))
            {
                throw new NotTranslated("a method group whose precondition depends on state");
            }
            // (o.M: o evaluated once, where the delegate is made (null throws), the method's this)
            string receiver = null;
            if (instance != null)
            {
                receiver = Declare("t$" + _temps++, instance.Type);
                Emit(KAssign.Of(receiver, Expr(instance)));
                Emit(KCheck.Of(NotNull(new KVar(receiver)), "CSV1013", instance.Syntax, $"'{instance.Syntax}' might be null in '{dc.Syntax}'"));
            }
            var key = FuncKey(dc.Type);
            _p.AddDelegateKey(key);
            var t = Declare("t$" + _temps++, dc.Type);
            var lam = new KLambda
            {
                Var = t,
                Key = key,
                ResultType = invoke.ReturnsVoid ? null : TypeOf(invoke.ReturnType),
                NoChange = c.IsPure,
                Steady = true,
            };
            if (receiver != null)
            {
                lam.Rename["this"] = new KVar(receiver);
            }
            foreach (var p in fn.Parameters)
            {
                lam.AddParam(("q$" + p.Name, TypeOf(p.Type)));
                lam.Rename[Local(p)] = Box(new KVar("q$" + p.Name), def.Parameters[p.Ordinal].Type, p.Type);
            }
            if (!fn.ReturnsVoid)
            {
                lam.Rename["result"] = Box(new KVar("q$r"), def.ReturnType, fn.ReturnType);
            }
            if (c.Requires.Count > 0)
            {
                lam.Pre = AndAll(c.Requires.Select(r => Spec(r, null)));
            }
            foreach (var post in c.Ensures.Where(e => e.Guard == null))
            {
                var mine = new HashSet<ISymbol>(own, SymbolEqualityComparer.Default);
                if (post.ResultParameter != null)
                {
                    mine.Add(post.ResultParameter);
                }
                if (Steady(post.Expr, mine))
                {
                    lam.AddPost(Spec(post.Expr, post.ResultParameter));
                }
            }
            Emit(lam);
            return new KVar(t);
        }

        /// <summary>
        /// A method's contract against a delegate type's, where both depend only on their parameters (and the method's
        /// this, the receiver): that it accepts every argument the type does, and gives what the type says there. Null
        /// where either depends on more.
        /// </summary>
        private (KExpr accepts, KExpr gives)? Refines(IMethodSymbol m, IMethodSymbol invoke, KExpr receiver)
        {
            var mc = _contractOf?.Invoke(m.OriginalDefinition);
            var dc = _contractOf?.Invoke(invoke);
            if (mc == null || dc == null || m.IsGenericMethod || m.Parameters.Length != invoke.Parameters.Length || m.Parameters.Any(p => p.RefKind != RefKind.None) ||
                mc.Modifies != null || mc.Reads != null)
            {
                return null;
            }
            var vars = invoke.Parameters.Select((p, k) => ("q$" + k, TypeOf(p.Type))).ToList();
            var withResult = invoke.ReturnsVoid ? vars : vars.Append(("r$", TypeOf(invoke.ReturnType))).ToList();
            var dPre = dc.Requires.Select(r => ContractPart(r, null, receiver)).ToList();
            var mPre = mc.Requires.Select(r => ContractPart(r, null, receiver)).ToList();
            var mPost = mc.Ensures.Where(e => e.Guard == null).Select(e => ContractPart(e.Expr, e.ResultParameter, receiver)).ToList();
            var dPost = dc.Ensures.Where(e => e.Guard == null).Select(e => ContractPart(e.Expr, e.ResultParameter, receiver)).ToList();
            if (dPre.Concat(mPre).Concat(mPost).Concat(dPost).Any(x => x == null))
            {
                return null;
            }
            return (Forall(vars, Implies(AndAll(dPre), AndAll(mPre))),
                    Forall(withResult, Implies(AndAlso(AndAlso(AndAll(dPre), AndAll(mPre)), AndAll(mPost)), AndAll(dPost))));
        }

        // (each contract's parameters, by position, to the bound variables; its result to r$; the method's this to the receiver)
        private KExpr ContractPart(IOperation op, IParameterSymbol result, KExpr receiver)
        {
            var own = new HashSet<ISymbol>(op.DescendantsAndSelf().OfType<IParameterReferenceOperation>().Select(p => p.Parameter), SymbolEqualityComparer.Default);
            if (!Steady(op, own))
            {
                return null;
            }
            var given = own.OfType<IParameterSymbol>().Where(p => !SymbolEqualityComparer.Default.Equals(p, result)).ToDictionary(p => Local(p), p => (KExpr)new KVar("q$" + p.Ordinal));
            given["result"] = new KVar("r$");
            if (receiver != null)
            {
                given["this"] = receiver;
            }
            // (a contract of code's reads, an element or a call, isn't compared: its well-definedness is Checks')
            var spec = Spec(op, result);
            return spec.IsMath() ? spec.Rewrite(x => x is KVar v && given.TryGetValue(v.Name, out var value) ? value : null) : null;
        }

        /// <summary>For every value of these variables (none: the body itself).</summary>
        private static KExpr Forall(List<(string name, string type)> vars, KExpr body)
        {
            for (int k = vars.Count - 1; k >= 0; k--)
            {
                body = KQuant.ForAll(vars[k].name, vars[k].type, body);
            }
            return body;
        }

        /// <summary>
        /// Of state that a frame can say: fields and array cells of steady objects (each added to <paramref name="objects"/>),
        /// array lengths, and what's steady.
        /// </summary>
        private bool StateRead(IOperation op, ISet<ISymbol> own, List<IOperation> objects)
        {
            if (op == null)
            {
                return false;
            }
            if (op.ConstantValue.HasValue)
            {
                return true;
            }
            switch (op)
            {
                case IFieldReferenceOperation fr when !fr.Field.IsStatic && fr.Instance != null:
                    objects.Add(fr.Instance);
                    return StateRead(fr.Instance, own, objects);
                case IArrayElementReferenceOperation ae:
                    objects.Add(ae.ArrayReference);
                    return StateRead(ae.ArrayReference, own, objects) && ae.Indices.All(i => StateRead(i, own, objects));
                case IPropertyReferenceOperation len when len.Property.Name == "Length" && len.Instance?.Type is IArrayTypeSymbol:
                    return StateRead(len.Instance, own, objects);
                case IBinaryOperation _: case IUnaryOperation _: case IConversionOperation _: case IParenthesizedOperation _: case IConditionalOperation _:
                    return op.ChildOperations.All(ch => StateRead(ch, own, objects));
                default:
                    return Steady(op, own);
            }
        }

        /// <summary>A local or parameter assigned nowhere after its declaration (nor passed by ref or out).</summary>
        private bool NeverWritten(ISymbol s) => NeverWrittenIn(s.ContainingSymbol?.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax(), s);

        /// <summary>Assigned nowhere in this code (nor passed by ref or out).</summary>
        private bool NeverWrittenIn(SyntaxNode owner, ISymbol s)
        {
            if (owner == null)
            {
                return false;
            }
            var model = (_model?.Compilation ?? KernelTypes.Compilation).GetSemanticModel(owner.SyntaxTree);
            foreach (var id in owner.DescendantNodes().OfType<IdentifierNameSyntax>())
            {
                if (id.Identifier.Text != s.Name || !SymbolEqualityComparer.Default.Equals(model.GetSymbolInfo(id).Symbol, s))
                {
                    continue;
                }
                SyntaxNode e = id;
                while (e.Parent is ParenthesizedExpressionSyntax)
                {
                    e = e.Parent;
                }
                if (e.Parent is AssignmentExpressionSyntax a && a.Left == e)
                {
                    return false;
                }
                if (e.Parent is PrefixUnaryExpressionSyntax || e.Parent is PostfixUnaryExpressionSyntax pu && !pu.IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.SuppressNullableWarningExpression))
                {
                    return false;
                }
                if (e.Parent is ArgumentSyntax arg && !arg.RefKindKeyword.IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.None))
                {
                    return false;
                }
            }
            return true;
        }

        /// <summary>A lambda that writes no field, array cell or captured variable, makes no object and calls only what's [Pure].</summary>
        private bool WritesNothing(IAnonymousFunctionOperation af)
        {
            foreach (var op in af.Body.DescendantsAndSelf())
            {
                if (InSpec(op.Syntax))
                {
                    continue;
                }
                switch (op)
                {
                    case IAssignmentOperation a when a.Target is ILocalReferenceOperation l && !SymbolEqualityComparer.Default.Equals(l.Local.ContainingSymbol, af.Symbol):
                    case IIncrementOrDecrementOperation i when i.Target is ILocalReferenceOperation il && !SymbolEqualityComparer.Default.Equals(il.Local.ContainingSymbol, af.Symbol):
                        return false; // (a captured variable: what it writes, every call forgets)
                    case IAssignmentOperation a when !(a.Target is ILocalReferenceOperation || a.Target is IParameterReferenceOperation { Parameter.RefKind: RefKind.None }):
                    case IIncrementOrDecrementOperation i when !(i.Target is ILocalReferenceOperation || i.Target is IParameterReferenceOperation):
                    case IDeconstructionAssignmentOperation _:
                    case IObjectCreationOperation _:
                    case IArrayCreationOperation _:
                        return false;
                    case IArgumentOperation arg when arg.Parameter?.RefKind != RefKind.None && arg.Parameter?.RefKind != RefKind.In:
                        return false;
                    case IInvocationOperation inv when !(SpecSymbols.IsSpecClass(inv.TargetMethod.ContainingType) || _contractOf?.Invoke(inv.TargetMethod) is Contract ic && ic.IsPure):
                        return false;
                }
            }
            return true;
        }
    }
}
