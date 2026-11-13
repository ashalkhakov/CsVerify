using System;
using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.FlowAnalysis;
using Microsoft.CodeAnalysis.Operations;
using static CsVerify.Verifier.Boogie.KernelTypes;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>Statements and assignment: each operation of a block, writes to locals, parameters, fields, cells and struct members.</summary>
    internal sealed partial class Lowering
    {
        private readonly Dictionary<IParameterSymbol, string> _assigned = new Dictionary<IParameterSymbol, string>(SymbolEqualityComparer.Default);

        /// <summary>The by-value parameters the body writes (not views, shares or packages, nor one a lambda captures).</summary>
        private List<IParameterSymbol> AssignedParameters(ControlFlowGraph cfg)
        {
            var found = new List<IParameterSymbol>();
            // (a target the flow graph captured, as x = new C { ... }'s: the variable it is)
            var captures = cfg.Blocks.SelectMany(b => b.Operations).SelectMany(o => o.DescendantsAndSelf()).OfType<IFlowCaptureOperation>().GroupBy(c => c.Id).ToDictionary(g => g.Key, g => g.First().Value);
            void Target(IOperation t)
            {
                if (Unconverted(t) is IFlowCaptureReferenceOperation fc && captures.TryGetValue(fc.Id, out var captured)) t = captured;
                if (Unconverted(t) is IParameterReferenceOperation { Parameter: var p } && p.RefKind == RefKind.None && !found.Contains(p, SymbolEqualityComparer.Default))
                {
                    if (!InSubset(p.Type) || IsView(p.Type) || IsShare(p.Type) || IsPackage(p.Type)) throw new NotTranslated("an assignment to a parameter of " + p.Type);
                    found.Add(p);
                }
            }
            var ops = cfg.Blocks.SelectMany(b => b.Operations.Concat(b.BranchValue == null ? new IOperation[0] : new[] { b.BranchValue })).SelectMany(o => o.DescendantsAndSelf()).ToList();
            foreach (var o in ops)
                switch (o)
                {
                    case IAssignmentOperation a when !(a is IDeconstructionAssignmentOperation): Target(a.Target); break;
                    case IIncrementOrDecrementOperation i: Target(i.Target); break;
                    case IDeconstructionAssignmentOperation d when d.Target is ITupleOperation tt: foreach (var e in tt.Elements) Target(e); break;
                    case IArgumentOperation { Parameter.RefKind: RefKind.Ref or RefKind.Out } arg: Target(arg.Value); break;
                    // (a struct's method that writes its receiver: the parameter it's called on)
                    case IInvocationOperation { Instance: { } wi } wc when WritesStructThis(wc.TargetMethod): Target(wi); break;
                }
            // (one a lambda or local function writes: assigned too, and forgotten after each call that may run it, as a
            // local it writes is; a lambda that reads one reads its own input, the value when it runs)
            foreach (var p in CapturedWrites().OfType<IParameterSymbol>())
                if (!found.Contains(p, SymbolEqualityComparer.Default))
                {
                    if (!InSubset(p.Type) || IsView(p.Type) || IsShare(p.Type) || IsPackage(p.Type)) throw new NotTranslated("an assignment to a parameter of " + p.Type);
                    found.Add(p);
                }
            return found;
        }

        /// <summary>The locals a deconstruction declares or writes, in order (null for a discard); null if it is anything else.</summary>
        private static ITypeSymbol dc_Type(IDeconstructionAssignmentOperation d) => Unconverted(d.Value) is ITupleOperation t && t.Type == null ? d.Target.Type : d.Value.Type;

        /// <summary>A deconstruction's target whose parts are variables or constants: a[i], o.f, x, _.</summary>
        private static bool SimpleTarget(IOperation t) => t switch
        {
            IDiscardOperation or ILocalReferenceOperation or IParameterReferenceOperation => true,
            IArrayElementReferenceOperation ae => ae.Indices.Length == 1 && Plain(ae.ArrayReference) && Plain(ae.Indices[0]),
            IFieldReferenceOperation fr => fr.Instance == null || Plain(fr.Instance),
            _ => false,
        };

        private static bool Plain(IOperation o) => Unconverted(o) is ILocalReferenceOperation or IParameterReferenceOperation or IInstanceReferenceOperation || o.ConstantValue.HasValue ||
            // (an index of them, i * 2 + 1: arithmetic, which reads nothing else)
            Unconverted(o) is IBinaryOperation { OperatorMethod: null, OperatorKind: BinaryOperatorKind.Add or BinaryOperatorKind.Subtract or BinaryOperatorKind.Multiply } b &&
            IsIntegral(b.Type) && Plain(b.LeftOperand) && Plain(b.RightOperand);

        private static List<ILocalSymbol> DeconstructedLocals(IOperation target)
        {
            if (target is IDeclarationExpressionOperation de) target = de.Expression;
            if (!(target is ITupleOperation tuple)) return null;
            var parts = new List<ILocalSymbol>();
            foreach (var e in tuple.Elements)
                switch (e)
                {
                    case ILocalReferenceOperation l: parts.Add(l.Local); break;
                    case IDeclarationExpressionOperation { Expression: ILocalReferenceOperation dl }: parts.Add(dl.Local); break;
                    case IDiscardOperation: parts.Add(null); break;
                    default: return null;
                }
            return parts;
        }

        /// <summary>
        /// A constructor's start: the field initializers of its class, in order (its fields are their defaults before,
        /// as the caller makes them). One that chains to another (this(...), or base(...) of a class not object) isn't
        /// translated yet.
        /// </summary>
        private void Initializers()
        {
            if (_decl is ConstructorDeclarationSyntax { Initializer: { } chained } && chained.ThisOrBaseKeyword.IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.ThisKeyword))
                return; // (this(...): the constructor it calls runs them, called on this as base(...) is)
            _block = new KBlock { Label = "init", Ordinal = -1, Jump = new KGoto("b0") };
            _p.Blocks.Add(_block);
            foreach (var member in _m.ContainingType.GetMembers().Where(x => !x.IsStatic && (x is IFieldSymbol || x is IPropertySymbol)))
                foreach (var syntax in member.DeclaringSyntaxReferences.Select(r => r.GetSyntax()))
                {
                    var init = (SyntaxNode)(syntax as VariableDeclaratorSyntax)?.Initializer ?? (syntax as PropertyDeclarationSyntax)?.Initializer;
                    if (init == null) continue;
                    if (IsLockObject(member)) continue; // (a lock's object: no state of the kernel's)
                    if (!IsField(member)) throw new NotTranslated("an initializer of " + member.Name);
                    if (init.SyntaxTree != _decl.SyntaxTree) throw new NotTranslated("an initializer in another file");
                    if (!(_model.GetOperation(init) is ISymbolInitializerOperation op)) throw new NotTranslated("the initializer of " + member.Name);
                    var value = Expr(op.Value);
                    _p.Fields.Add(member.OriginalDefinition);
                    Emit(new KFieldStore { Field = member.OriginalDefinition, Instance = new KVar("this"), Value = value, OnThis = true, At = init, InstanceAt = init });
                }
        }

        private void Statement(IOperation op)
        {
            if (op is IExpressionStatementOperation es) op = es.Operation;
            if (op is IFlowCaptureOperation spec && InSpec(spec.Value.Syntax)) return;
            switch (op)
            {
                // (an iterator's yield return: its value evaluated, then the caller's code runs until the next MoveNext,
                // which may change anything)
                case IReturnOperation { Kind: OperationKind.YieldReturn } yr:
                    if (yr.ReturnedValue != null) Emit(new KAssign { Var = Declare("t$" + _temps++, yr.ReturnedValue.Type), Value = Expr(yr.ReturnedValue) });
                    CallersRun();
                    return;
                // (an interface's task as a statement: it runs on, alongside the rest of this method, never awaited)
                case IInvocationOperation bareTask when IsTaskMethod(bareTask.TargetMethod) && bareTask.TargetMethod.IsAbstract && !_awaiting:
                    { InterfaceTaskStatement(bareTask); return; }
                // (Task.Run(...) as a statement: it runs on, alongside the rest of this method, never awaited)
                case IInvocationOperation bare when IsTaskRun(bare, out var brun, out var blam):
                    Detach(brun, blam, kept: false);
                    return;
                case IInvocationOperation baseCall when baseCall.TargetMethod.MethodKind == MethodKind.Constructor &&
                                                        baseCall.TargetMethod.ContainingType.SpecialType == SpecialType.System_Object:
                    return; // (object's constructor does nothing)
                // (a context's base, DbContext(options): nothing the kernel keeps; a new context is new where it's made)
                case IInvocationOperation efBase when efBase.TargetMethod.MethodKind == MethodKind.Constructor && _p.IsCtor && KernelTypes.Ef != null &&
                                                      efBase.TargetMethod.ContainingType?.ToDisplayString() == "Microsoft.EntityFrameworkCore.DbContext" && efBase.Instance is IInstanceReferenceOperation:
                    return;
                // (a library exception's base(...): its arguments evaluated; its state isn't the kernel's)
                case IInvocationOperation excBase when excBase.TargetMethod.MethodKind == MethodKind.Constructor && _p.IsCtor &&
                                                       IsLibraryException(excBase.TargetMethod.ContainingType) && excBase.Instance is IInstanceReferenceOperation:
                    foreach (var a in excBase.Arguments.Where(a => InSubset(a.Value.Type) && !(a.Value is IInterpolatedStringOperation))) Expr(a.Value);
                    return;
                case IInvocationOperation chain when chain.TargetMethod.MethodKind == MethodKind.Constructor && _p.IsCtor &&
                                                     (chain.Instance is IInstanceReferenceOperation ||
                                                      chain.Instance is IFlowCaptureReferenceOperation cr && _captured.TryGetValue(cr.Id, out var cv) && cv is IInstanceReferenceOperation):
                    { ConstructorChain(chain); return; }
                case IInvocationOperation own when SpecSymbols.IsCsVerifyType(own.TargetMethod.ContainingType, "Own"):
                    Own(own);
                    return;
                // (var (a, b) = p: a package taken apart, or a data value's fields; the views that come out are in hand)
                // (var (a, b) = t, of a tuple: each element; of a tuple written here, (x, y), each value)
                case IDeconstructionAssignmentOperation tdc when IsTuple(dc_Type(tdc)) && DeconstructedLocals(tdc.Target) is List<ILocalSymbol> tparts:
                    { TupleDeconstruction(tdc, tparts); return; }
                // ((a[i], a[j]) = (a[j], a[i]), of a tuple: each value read first, then each target written, as C# does where the
                // targets' parts are variables that the values don't change)
                case IDeconstructionAssignmentOperation gdc when IsTuple(dc_Type(gdc)) && gdc.Target is ITupleOperation gt && gt.Elements.All(SimpleTarget):
                    { TupleSwap(gdc, gt); return; }
                case IDeconstructionAssignmentOperation dc when IsData(dc.Value.Type) && DeconstructedLocals(dc.Target) is List<ILocalSymbol> parts:
                    { DataDeconstruction(dc, parts); return; }
                case IInvocationOperation inv when SpecSymbols.IsSpecClass(inv.TargetMethod.ContainingType):
                    switch (inv.TargetMethod.Name)
                    {
                        case "Requires": case "Ensures": case "Invariant": case "Decreases": case "Modifies": case "EnsuresOnThrow": case "Reads": return; // (the contract; the loop heads)
                        case "Fold": case "Unfold":
                        {
                            var whole = SpecArgument(inv);
                            if (!(Spec(whole, null) is KInst instance)) throw new NotTranslated("Spec." + inv.TargetMethod.Name + " of what isn't a predicate instance");
                            Emit(new KFold { Inst = instance, Unfold = inv.TargetMethod.Name == "Unfold", At = inv.Syntax, InstAt = whole.Syntax });
                            return;
                        }
                        case "Assert": case "Assume":
                            Emit(new KSpecStmt { Spec = Spec(SpecArgument(inv), null), Assume = inv.TargetMethod.Name == "Assume", At = inv.Syntax, ArgumentAt = inv.Arguments[0].Syntax });
                            return;
                        default: throw new NotTranslated("Spec." + inv.TargetMethod.Name);
                    }
                case IInvocationOperation { TargetMethod.Name: "Start", Instance: ILocalReferenceOperation sl, Arguments.Length: 0 } when _threads.TryGetValue(sl.Local, out var startedLambda):
                    Start(sl.Local, StartedCall(startedLambda), thread: true, at: op.Syntax, lambda: startedLambda);
                    return;
                case IInvocationOperation { TargetMethod.Name: "Join", Instance: ILocalReferenceOperation jl, Arguments.Length: 0 } when _tasks.TryGetValue(jl.Local, out var joined):
                    JoinOf(joined);
                    Emit(new KAssign { Var = joined.Awaited, Value = new KLit("true") });
                    var jk = new KAwait();
                    if (!_opaque) foreach (var l in Confined()) jk.Keep.Add(Declare(Local(l), l.Type));
                    _p.Awaits = true;
                    _p.CallsDelegates = true;
                    Emit(jk);
                    return;
                case IInvocationOperation call:
                    Call(call);
                    return;
                case IAwaitOperation aw:
                    Await(aw);
                    return;
                case ISimpleAssignmentOperation st when st.Target is ILocalReferenceOperation { Local: var tl } && IsTaskLike(tl.Type) &&
                                                        Unconverted(st.Value) is IInvocationOperation started && started.TargetMethod.IsAsync && started.TargetMethod.DeclaringSyntaxReferences.Length > 0:
                    Start(tl, started);
                    return;
                // (a task from code that isn't an async method here, a delegate's, an interface's or a method's of the program
                // that isn't async: its call, then a task of code of its own, running alongside until it's awaited)
                case ISimpleAssignmentOperation other when other.Target is ILocalReferenceOperation { Local: var ol } && IsTaskLike(ol.Type) && !_tasks.ContainsKey(ol) &&
                                                           Unconverted(other.Value) is IInvocationOperation oc && !oc.TargetMethod.IsAsync &&
                                                           (oc.TargetMethod.MethodKind == MethodKind.DelegateInvoke || oc.TargetMethod.DeclaringSyntaxReferences.Length > 0):
                    if (IsTaskMethod(oc.TargetMethod)) StartedTaskCall(oc);
                    else Expr(oc);
                    Start(ol, null, at: oc.Syntax);
                    return;
                // (an enumerator of a collection, var e = l.GetEnumerator(): its collection and version, as a foreach's)
                case ISimpleAssignmentOperation en when en.Target is ILocalReferenceOperation { Local: var enl } && Unconverted(en.Value) is IInvocationOperation { TargetMethod.Name: "GetEnumerator", Instance: { } ec } &&
                                                        IsCollection(ec.Type) && ((INamedTypeSymbol)ec.Type).TypeArguments.Length >= 1 && !_enumerators.ContainsKey(enl):
                {
                    var coll = Expr(Unconverted(ec));
                    Emit(new KCheck { Cond = new KOp("!=", coll, new KLit("null")), Id = "CSV1013", At = ec.Syntax, Message = $"'{ec.Syntax}' might be null in '{en.Value.Syntax}'" });
                    foreach (var model in ModelsOf((INamedTypeSymbol)ec.Type)) _p.Models[model.Name] = model;
                    var held = Declare("en$" + _enumerators.Count + "$c", ec.Type);
                    var version = Declare("en$" + _enumerators.Count + "$v", _model.Compilation.GetSpecialType(SpecialType.System_Int32));
                    Emit(new KAssign { Var = held, Value = coll });
                    Emit(new KAssign { Var = version, Value = new KOp("sel", new KVar(VersionMap), coll) });
                    _enumerators[enl] = (held, version, (INamedTypeSymbol)ec.Type);
                    return;
                }
                // (a query kept in a local: read where it's enumerated)
                case ISimpleAssignmentOperation lq when lq.Target is ILocalReferenceOperation { Local: var lql } && LazyQuery(lql, lq.Value):
                    return;
                // (tasks started in a batch, ts = xs.Select(x => F(x)).ToArray(): they run alongside until Task.WhenAll(ts))
                case ISimpleAssignmentOperation bt when bt.Target is ILocalReferenceOperation { Local: var btl } && TaskBatch(bt.Value) is (IInvocationOperation bsel, IOperation bsrc, AnonymousFunctionExpressionSyntax blam):
                    StartBatch(btl, bsel, bsrc, blam);
                    return;
                // (a task local stored in a field: reported where it's started, CSV1901; the field is the library's)
                case ISimpleAssignmentOperation ts when ts.Target is IFieldReferenceOperation && IsTaskLike(ts.Target.Type) && Unconverted(ts.Value) is ILocalReferenceOperation { Local: var tsl } && _misused.Contains(tsl):
                    return;
                // (a thread made background: nothing the kernel keeps)
                case ISimpleAssignmentOperation bg when bg.Target is IPropertyReferenceOperation { Property.Name: "IsBackground", Instance: ILocalReferenceOperation { Local: var bgl } } && _threads.ContainsKey(bgl):
                    Expr(bg.Value);
                    return;
                // (Task.Run(...) kept in a field or discarded: it runs on, alongside the rest of this method)
                case ISimpleAssignmentOperation kr when kr.Target is IDiscardOperation or IFieldReferenceOperation && IsTaskLike(kr.Target.Type) && IsTaskRun(kr.Value, out var krun, out var klam):
                    if (kr.Target is IFieldReferenceOperation { Instance: { } ki } && !(ki is IInstanceReferenceOperation)) Expr(ki);
                    Detach(krun, klam, kept: true);
                    return;
                // (Task.Run(() => F(...)): a task of the call, proved where it starts; of any other lambda, a task of code verified on its own)
                case ISimpleAssignmentOperation run when run.Target is ILocalReferenceOperation { Local: var rl } && IsTaskLike(rl.Type) &&
                                                         Unconverted(run.Value) is IInvocationOperation tr && tr.TargetMethod.ContainingType?.ToDisplayString() == "System.Threading.Tasks.Task" &&
                                                         tr.TargetMethod.Name == "Run" && tr.Arguments.Length == 1 && LambdaSyntax(tr.Arguments[0]) is AnonymousFunctionExpressionSyntax runLambda:
                    Start(rl, StartedCall(runLambda), at: tr.Syntax, lambda: runLambda);
                    return;
                // (new Thread(() => F(...)): started by Start, finished by Join)
                case ISimpleAssignmentOperation th when th.Target is ILocalReferenceOperation { Local: var thl } && thl.Type.OriginalDefinition.ToDisplayString(SymbolDisplayFormat.FullyQualifiedFormat) == "global::System.Threading.Thread" &&
                                                        Unconverted(th.Value) is IObjectCreationOperation tc && tc.Arguments.Length == 1 && LambdaSyntax(tc.Arguments[0]) is AnonymousFunctionExpressionSyntax thLambda:
                    if (_threads.ContainsKey(thl)) throw new NotTranslated("a thread local assigned again");
                    _threads[thl] = thLambda;
                    return;
                // (a lock's object made in a constructor, new object() or a library semaphore: no state of the kernel's; its arguments read)
                case ISimpleAssignmentOperation lk when lk.Target is IFieldReferenceOperation { Field: var lkf, Instance: IInstanceReferenceOperation } && IsLockObject(lkf) && _p.IsCtor &&
                                                        Unconverted(lk.Value) is IObjectCreationOperation { Initializer: null } lc && lc.Arguments.All(x => Scalar(x.Value.Type) && x.Parameter.RefKind == RefKind.None):
                    foreach (var x in lc.Arguments.OrderBy(x => x.Parameter.Ordinal)) Expr(x.Value);
                    return;
                // (a lock's object given to a constructor, a lock wrapper's releaser's: kept, no state of the kernel's)
                case ISimpleAssignmentOperation lg when lg.Target is IFieldReferenceOperation { Field: var lgf, Instance: IInstanceReferenceOperation } && IsLockObject(lgf) && _p.IsCtor &&
                                                        Unconverted(lg.Value) is IParameterReferenceOperation or ILocalReferenceOperation:
                    Expr(lg.Value);
                    return;
                // (EF's Entry(o).State = s, of a state known here: no value to read)
                case ISimpleAssignmentOperation efs when efs.Value.ConstantValue.HasValue && efs.Value.ConstantValue.Value is int && TrackerAssign(efs.Target, null):
                    return;
                case ISimpleAssignmentOperation rb when rb.IsRef && rb.Target is ILocalReferenceOperation { Local: { RefKind: not RefKind.None } rbl }:
                    BindRef(rbl, rb.Value, rb.Syntax);
                    return;
                case ISimpleAssignmentOperation a:
                    Assign(a.Target, Expr(a.Value));
                    return;
                case ICompoundAssignmentOperation ca:
                {
                    var v = Operands(ca.Target, ca.Value);
                    Assign(ca.Target, IsBitwise(ca.OperatorKind) && IsIntegral(ca.Type) ? Bitwise(ca.OperatorKind, v[0], v[1], ca.Type, inSpec: false)
                                                                                         : Arith(Op(ca.OperatorKind), v[0], v[1], ca.Type, ca.Syntax, ca.IsChecked));
                    return;
                }
                case IIncrementOrDecrementOperation id:
                    Assign(id.Target, Arith(id.Kind == OperationKind.Increment ? "+" : "-", Expr(id.Target), new KLit("1"), id.Type, id.Syntax, id.IsChecked));
                    return;
                case IFlowCaptureOperation qe when _forEach.TryGetValue(qe.Id, out var qf) && (qf.Query != null || qf.GroupOf != null || qf.JoinGroupOf != null):
                    StartQueryLoop(qf);
                    return;
                case IFlowCaptureOperation ae when _asyncEach.ContainsKey(ae.Id):
                    AsyncStream((IInvocationOperation)ae.Value);
                    return;
                case IFlowCaptureOperation en when _forEach.TryGetValue(en.Id, out var fe):
                {
                    // the collection, evaluated once (a null one throws), and the index at its start
                    var coll = Expr(fe.Of ?? Unconverted(((IInvocationOperation)en.Value).Instance ?? ((IInvocationOperation)en.Value).Arguments[0].Value));
                    Emit(new KAssign { Var = fe.Array, Value = coll });
                    Emit(new KAssign { Var = fe.Index, Value = new KLit("0") });
                    // (its length, read once: where a null one throws)
                    if (fe.Collection != null || fe.Opaque)
                        Emit(new KCheck { Cond = new KOp("!=", new KVar(fe.Array), new KLit("null")), Id = "CSV1013", At = fe.At, Message = $"'{fe.At}' might be null in '{fe.At}'" });
                    if (fe.Opaque) return;
                    if (fe.Version != null) Emit(new KAssign { Var = fe.Version, Value = new KOp("sel", new KVar(VersionMap), new KVar(fe.Array)) });
                    if (fe.Size0 != null)
                    {
                        Emit(new KAssign { Var = fe.Size0, Value = LengthOf(fe) });
                        // (its Count, an int)
                        Emit(new KAssume { Cond = new KOp("<=", new KVar(fe.Size0), new KLit("2147483647")) });
                    }
                    else if (fe.Collection == null) Emit(new KAssign { Var = Declare(fe.Array.Replace("$a", "$n"), _model.Compilation.GetSpecialType(SpecialType.System_Int32)), Value = new KLen { String = fe.String, Array = new KVar(fe.Array), At = fe.At, ArrayAt = fe.At } });
                    return;
                }
                case IFlowCaptureOperation lk when Unconverted(lk.Value) is IFieldReferenceOperation { Field: var lf } lkf && IsLockObject(lf):
                    _captured[lk.Id] = Unconverted(lk.Value);
                    // (a lock's object: no value of the kernel's; another object's lock field is read of it, which mustn't be null)
                    if (!lf.IsStatic && !(lkf.Instance is IInstanceReferenceOperation) && lkf.Instance != null && InSubset(lkf.Instance.Type))
                        Emit(new KCheck { Cond = new KOp("!=", Expr(lkf.Instance), new KLit("null")), Id = "CSV1013", At = lkf.Syntax,
                                          Message = $"'{lkf.Instance.Syntax}' might be null in '{lkf.Syntax}'" });
                    return;
                case IFlowCaptureOperation wa when Unconverted(wa.Value) is IInvocationOperation wc && wc.TargetMethod.IsAsync && wc.TargetMethod.DeclaringSyntaxReferences.Length > 0 &&
                                                   wc.Syntax.Parent is ArgumentSyntax { Parent.Parent: InvocationExpressionSyntax { Parent: AwaitExpressionSyntax } wi } &&
                                                   wi.Expression.ToString().EndsWith("WhenAll"):
                    StartCaptured(wa.Id, wc);
                    return;
                // (this, captured as the receiver of a this(...) or base(...) whose arguments branch: nothing to evaluate)
                case IFlowCaptureOperation ft when ft.Value is IInstanceReferenceOperation && _p.IsCtor:
                    _captured[ft.Id] = ft.Value;
                    return;
                // (a collection's element captured as what an assignment writes, d[k] = c ? a : b: written by its setter
                // there, of its receiver and index as they are then, which the value doesn't change)
                case IFlowCaptureOperation fx when fx.Value is IPropertyReferenceOperation { Property.IsIndexer: true } ix && IsCollection(ix.Instance?.Type) &&
                                                   ix.Syntax.Parent is AssignmentExpressionSyntax { RawKind: (int)SyntaxKind.SimpleAssignmentExpression } xa && xa.Left == ix.Syntax &&
                                                   Steady(ix.Instance, xa.Right) && ix.Arguments.All(a => Steady(a.Value, xa.Right)):
                    _captured[fx.Id] = fx.Value;
                    _lvalues[fx.Id] = ix;
                    return;
                case IFlowCaptureOperation fc:
                    _captured[fc.Id] = fc.Value;
                    // (a field captured as what an assignment writes, x.f = c ? a : b: its object, kept)
                    if (fc.Value is IFieldReferenceOperation { Field.IsStatic: false } cf &&
                        cf.Instance is ILocalReferenceOperation or IParameterReferenceOperation or IInstanceReferenceOperation)
                        _lvalues[fc.Id] = cf;
                    var value = Expr(fc.Value);
                    Emit(new KAssign { Var = Capture(fc.Id, fc.Value.Type), Value = value });
                    return;
                // (new C(...); as a statement: made, its constructor run, the object not kept)
                case IObjectCreationOperation made when InSubset(made.Type):
                    Expr(made);
                    return;
                default:
                    throw new NotTranslated(op.Kind.ToString());
            }
        }

        private void InterfaceTaskStatement(IInvocationOperation bareTask)
        {
            StartedTaskCall(bareTask);
            _opaque = true;
            var t = new Task { Method = bareTask.TargetMethod, At = bareTask.Syntax, Thread = true, RunAt = bareTask.Syntax,
                               Awaited = Declare($"aw$d{_detached.Count}", _model.Compilation.GetSpecialType(SpecialType.System_Boolean)) };
            Emit(new KAssign { Var = t.Awaited, Value = new KLit("false") });
            _detached.Add(t);
            return;
        }

        private void ConstructorChain(IInvocationOperation chain)
        {
            // base(...): the base class's constructor, on this object
            var ctor = chain.TargetMethod.OriginalDefinition;
            // (an implicit one of a class without field initializers does nothing)
            if (ctor.IsImplicitlyDeclared && !ctor.ContainingType.GetMembers().Any(x => !x.IsStatic && x.DeclaringSyntaxReferences.Any(r =>
                    r.GetSyntax() is VariableDeclaratorSyntax { Initializer: not null } || r.GetSyntax() is PropertyDeclarationSyntax { Initializer: not null }))) return;
            if (!_isProcedure(ctor)) throw new NotTranslated("a call of " + ctor.ContainingType.Name + "'s constructor");
            _p.Calls.Add(ctor);
            var ordered = chain.Arguments.OrderBy(a => a.Parameter.Ordinal).ToList();
            var args = Operands(ordered.Select(a => a.Value).ToArray());
            Emit(new KCall { Callee = ctor, Receiver = new KVar("this"), ReceiverIsThis = true, Args = args, ArgsAt = ordered.Select(a => a.Value.Syntax).ToArray(), At = chain.Syntax });
            return;
        }

        private void TupleDeconstruction(IDeconstructionAssignmentOperation tdc, List<ILocalSymbol> tparts)
        {
            var items = Unconverted(tdc.Value) is ITupleOperation lit && lit.Elements.Length == tparts.Count ? lit.Elements.Select(x => Expr(x)).ToList() : null;
            KExpr whole = null;
            if (items == null)
            {
                var w = Declare("t$" + _temps++, tdc.Value.Type);
                Emit(new KAssign { Var = w, Value = Expr(tdc.Value) });
                whole = new KVar(w);
            }
            // (all read before any is assigned: (a, b) = (b, a))
            var temps = new List<string>();
            for (int k = 0; k < tparts.Count; k++)
            {
                if (tparts[k] == null) { temps.Add(null); continue; }
                var t = Declare("t$" + _temps++, tparts[k].Type);
                Emit(new KAssign { Var = t, Value = items != null ? items[k] : TupleItem(whole, tdc.Value.Type, k) });
                temps.Add(t);
            }
            for (int k = 0; k < tparts.Count; k++)
                if (tparts[k] != null) Emit(new KAssign { Var = Declare(Local(tparts[k]), tparts[k].Type), Value = new KVar(temps[k]) });
            return;
        }

        private void TupleSwap(IDeconstructionAssignmentOperation gdc, ITupleOperation gt)
        {
            var items = Unconverted(gdc.Value) is ITupleOperation lit && lit.Elements.Length == gt.Elements.Length ? lit.Elements.Select(x => Expr(x)).ToList() : null;
            KExpr whole = null;
            if (items == null)
            {
                var w = Declare("t$" + _temps++, gdc.Value.Type);
                Emit(new KAssign { Var = w, Value = Expr(gdc.Value) });
                whole = new KVar(w);
            }
            var temps = new List<string>();
            for (int k = 0; k < gt.Elements.Length; k++)
            {
                if (gt.Elements[k] is IDiscardOperation) { temps.Add(null); continue; }
                var t = Declare("t$" + _temps++, gt.Elements[k].Type);
                Emit(new KAssign { Var = t, Value = items != null ? items[k] : TupleItem(whole, gdc.Value.Type, k) });
                temps.Add(t);
            }
            for (int k = 0; k < gt.Elements.Length; k++)
                if (temps[k] != null) Assign(gt.Elements[k], new KVar(temps[k]));
            return;
        }

        private void DataDeconstruction(IDeconstructionAssignmentOperation dc, List<ILocalSymbol> parts)
        {
            var fields = KernelTypes.Data.Fields((INamedTypeSymbol)dc.Value.Type);
            if (fields.Count != parts.Count) throw new NotTranslated("a deconstruction of another shape");
            if (IsPackage(dc.Value.Type)) CheckPackage(dc.Value.Type);
            Data(dc.Value.Type);
            var whole = Declare("t$" + _temps++, dc.Value.Type);
            Emit(new KAssign { Var = whole, Value = Expr(dc.Value) });
            for (int k = 0; k < parts.Count; k++)
            {
                if (parts[k] == null) continue;
                var field = fields[k];
                KExpr read = new KDataField { Function = FieldFunction(field), Value = new KVar(whole), At = dc.Value.Syntax, ValueAt = dc.Value.Syntax, Struct = dc.Value.Type.IsValueType };
                read = Unbox(read, field.OriginalDefinition.Type, parts[k].Type);
                var local = Declare(Local(parts[k]), parts[k].Type);
                Emit(new KAssign { Var = local, Value = read });
                if (IsView(parts[k].Type)) Emit(new KOwn { Kind = "unpack", Obj = new KVar(local), Type = ViewOf(parts[k].Type), At = dc.Syntax });
                else if (IsRef(parts[k].Type) && NotNullable(field.Type)) Emit(new KAssume { Cond = new KOp("!=", new KVar(local), new KLit("null")) });
                if (HasInvariants(parts[k].Type)) AssumeValid(new KVar(local), parts[k].Type);
            }
            return;
        }

        /// <summary>A value defined where cond holds: in code, checked there (id); in a specification, needed for it to be well-defined.</summary>
        private KExpr Defined(KExpr cond, KExpr value, string id, SyntaxNode at, string message, bool inSpec)
        {
            if (inSpec) return new KOp("$need", cond, value);
            Emit(new KCheck { Cond = cond, Id = id, At = at, Message = message });
            return value;
        }

        /// <summary>A rectangular array's cell: each index within its dimension (CSV1003).</summary>
        private KExpr MultiIndices(KExpr a, List<KExpr> ix, SyntaxNode at, KExpr cell, bool inSpec)
        {
            KExpr all = new KLit("true");
            for (int d = 0; d < ix.Count; d++)
            {
                var within = new KOp("&&", new KOp("<=", new KLit("0"), ix[d]), new KOp("<", ix[d], new KOp("$dim", a, new KLit(d.ToString()))));
                // (null first: a null array's check is its own)
                var cond = new KOp("||", new KOp("==", a, new KLit("null")), within);
                if (inSpec) all = new KOp("&&", all, cond);
                else Emit(new KCheck { Cond = cond, Id = "CSV1003", At = at, Message = $"index {d} in '{at}' might be out of range" });
            }
            return inSpec ? new KOp("$need", all, cell) : cell;
        }

        /// <summary>A member of a struct value (a field, an auto-property): the value, and the member's element; else null.</summary>
        private static (IOperation, int)? StructMember(IOperation e) => e switch
        {
            IFieldReferenceOperation { Instance: { Type: var t } i } f when IsStruct(t) && StructIndex(t, f.Field) is int k && k >= 0 => (i, k),
            IPropertyReferenceOperation { Instance: { Type: var t } i, Arguments.Length: 0 } p when IsStruct(t) && StructIndex(t, p.Property) is int k && k >= 0 => (i, k),
            _ => null,
        };

        /// <summary>A struct's member written: the value it's in made anew, of the others and this one, and written where it is.</summary>
        private void StructWrite(IOperation whole, int k, KExpr value)
        {
            var was = Expr(whole);
            var parts = StructFields(whole.Type).Select((f, j) => j == k ? value : TupleItem(was, whole.Type, j)).ToArray();
            var now = new KOp(TupleMaker(whole.Type), parts);
            switch (whole)
            {
                case IInstanceReferenceOperation when _p.StructThis: Emit(new KAssign { Var = "this", Value = now }); return;
                case IInstanceReferenceOperation:
                    Emit(new KCheck { Cond = new KLit("false"), Id = "CSV1901", At = whole.Syntax.Parent ?? whole.Syntax, NotAssumedAfter = true,
                                      Message = $"a struct's method that writes its own members is not supported: make it return a new value" });
                    return;
                case IFlowCaptureReferenceOperation c: Emit(new KAssign { Var = Capture(c.Id, c.Type), Value = now }); return;
                // (a struct in a class's field isn't written in place)
                case IFieldReferenceOperation or IPropertyReferenceOperation when StructMember(whole) is null:
                    Emit(new KCheck { Cond = new KLit("false"), Id = "CSV1901", At = whole.Syntax.Parent ?? whole.Syntax, NotAssumedAfter = true,
                                      Message = $"writing a member of the struct in '{whole.Syntax}' in place is not supported: assign the whole struct" });
                    return;
                case IParameterReferenceOperation { Parameter.RefKind: RefKind.None } p when !_assigned.ContainsKey(p.Parameter): throw new NotTranslated("a struct parameter written");
                default: Assign(whole, now); return;
            }
        }

        private void Assign(IOperation target, KExpr value)
        {
            if (StructMember(target) is (IOperation sw, int sk)) { StructWrite(sw, sk, value); return; }
            if (SpanAssign(target, value)) return;
            // (EF's Entry(o).State = s)
            if (TrackerAssign(target, value)) return;
            // (l[i] = v through IList: by what the object is)
            if (IfcIndexerWrite(target, value)) return;
            if (target is ILocalReferenceOperation { Local: var rw } && _refAlias.TryGetValue(rw, out var wa))
            {
                if (wa.Var != null) Emit(new KAssign { Var = wa.Var, Value = value });
                else
                {
                    HeldCell(wa.Array, target.Syntax, write: true);
                    Emit(new KStore { Array = wa.Array, Index = wa.Index, Value = value, ArrayType = wa.ArrayType, At = target.Syntax, ArrayAt = target.Syntax });
                }
                return;
            }
            switch (target)
            {
                // (a view moved from one variable to another: its permission is its object's, so it goes along; the
                // linearity analyzer sees that the variable it overwrites held none)
                case ILocalReferenceOperation l when IsView(l.Local.Type) && l.Local.RefKind == RefKind.None:
                    Emit(new KAssign { Var = Declare(Local(l.Local), l.Local.Type), Value = value });
                    return;
                case ILocalReferenceOperation l when IsView(l.Local.Type) || IsShare(l.Local.Type):
                    throw new NotTranslated("a view moved from one variable to another");
                case ILocalReferenceOperation l when InSubset(l.Local.Type) && l.Local.RefKind == RefKind.None:
                {
                    // (a local of non-nullable type: each write is checked, so it stays not null)
                    bool nonNull = IsNullable(l.Local.Type) && NotNullable(l.Local.Type);
                    Emit(new KAssign { Var = Declare(Local(l.Local), l.Local.Type), Value = value,
                                       NotNullAt = nonNull ? l.Syntax.Parent ?? l.Syntax : null, NotNullName = l.Local.Name });
                    return;
                }
                // (a list's indexer: its stub's setter)
                case IPropertyReferenceOperation ls when IsCollection(ls.Instance?.Type) && ls.Property.SetMethod != null:
                    Invoke(ls.Property.SetMethod, ls.Instance, ls.Arguments, ls.Syntax, value);
                    return;
                // (a library object's indexer or property set, ConcurrentDictionary's d[k] = v: its receiver not null; what it
                // changes isn't the program's, so nothing known changes; reading it back is a library's read, not known)
                case IPropertyReferenceOperation lps when lps.Property.DeclaringSyntaxReferences.Length == 0 && lps.Property.SetMethod != null && lps.Instance != null &&
                                                         IsLibraryObject(lps.Instance.Type) && !IsCollection(lps.Instance.Type) && InSubset(lps.Instance.Type) &&
                                                         !(_contractOf?.Invoke(lps.Property.SetMethod) is Contract lpc && lpc.IsStub) && KernelTypes.MayWriteHeap != null && !KernelTypes.MayWriteHeap(lps.Property.SetMethod) &&
                                                         lps.Arguments.All(a => InSubset(a.Value.Type)):
                {
                    var recv = Expr(Unconverted(lps.Instance));
                    Emit(new KCheck { Cond = new KOp("!=", recv, new KLit("null")), Id = "CSV1013", At = lps.Instance.Syntax, Message = $"'{lps.Instance.Syntax}' might be null in '{lps.Syntax}'" });
                    foreach (var a in lps.Arguments.OrderBy(a => a.Parameter.Ordinal)) Expr(a.Value);
                    return;
                }
                // (a computed property: its setter, called with the value)
                case IPropertyReferenceOperation sp when IsComputed(sp.Property) && sp.Property.SetMethod != null:
                    Invoke(sp.Property.SetMethod, sp.Instance, sp.Arguments, sp.Syntax, value);
                    return;
                // (a static readonly field the kernel doesn't have, set where it's initialized: its value, not kept)
                case IFieldReferenceOperation { Field: { IsStatic: true, IsReadOnly: true } srw } when StaticReadonly(srw) != null:
                    return;
                case IFieldReferenceOperation _: case IPropertyReferenceOperation _:
                {
                    var (field, instance, onThis, instanceAt) = FieldOf(target);
                    if (SpecSymbols.IsOwnsField(field))
                        Emit(new KCheck { Cond = new KLit("false"), Id = "CSV1016", At = target.Syntax, NotAssumedAfter = true,
                                          Message = $"'{target.Syntax}': an [Owns] field changes hands only through Own.Take and Own.Give" });
                    if (Atomics.IsAtomic(field) && !(_p.IsCtor && onThis) && !(target.Syntax.Parent is InitializerExpressionSyntax)) value = AtomicWrite(field, instance, onThis, value, target.Syntax);
                    // (a generic class's field of T holds a box: Box<int>'s Item, written an int)
                    Emit(new KFieldStore { Field = field, Instance = instance, OnThis = onThis, Value = Box(value, FieldType(field), target.Type), At = target.Syntax, InstanceAt = instanceAt });
                    // (an entity's column written: modified, for a context tracking it unchanged)
                    TrackerFieldWrite(field, instance, target.Syntax);
                    return;
                }
                case IArrayElementReferenceOperation me when IsMultiArray(me.ArrayReference.Type) && me.Indices.Length == ((IArrayTypeSymbol)me.ArrayReference.Type).Rank:
                {
                    var v = Operands(new[] { me.ArrayReference }.Concat(me.Indices).ToArray());
                    var ix = v.Skip(1).ToList();
                    MultiIndices(v[0], ix, me.Syntax, null, inSpec: false);
                    Emit(new KStore { Unchecked = true, Array = v[0], Index = CellOf(ix), Value = value, ArrayType = me.ArrayReference.Type, At = me.Syntax, ArrayAt = me.ArrayReference.Syntax });
                    return;
                }
                case IArrayElementReferenceOperation e when IsArray(e.ArrayReference.Type) && e.Indices.Length == 1:
                {
                    var v = Operands(e.ArrayReference, e.Indices[0]);
                    HeldCell(v[0], e.Syntax, write: true);
                    Emit(new KStore { Array = v[0], Index = v[1], Value = value, ArrayType = e.ArrayReference.Type, At = e.Syntax, ArrayAt = e.ArrayReference.Syntax });
                    return;
                }
                case IParameterReferenceOperation p when p.Parameter.RefKind is RefKind.Ref or RefKind.Out && InSubset(p.Parameter.Type) && !IsShare(p.Parameter.Type):
                {
                    Emit(new KAssign { Var = Local(p.Parameter), Value = value });
                    return;
                }
                case IParameterReferenceOperation ap when _assigned.TryGetValue(ap.Parameter, out var apLocal):
                    Emit(new KAssign { Var = apLocal, Value = value });
                    return;
                case IParameterReferenceOperation: throw new NotTranslated("an assignment to a parameter");
                case IFlowCaptureReferenceOperation cr when _lvalues.TryGetValue(cr.Id, out var lv):
                    Assign(lv, value);
                    return;
                // (a target the flow graph captured before a value that branches, x = c ? a : b: the variable, or a cell of
                // variables, itself)
                case IFlowCaptureReferenceOperation tc when _captured.TryGetValue(tc.Id, out var tv) && SimpleTarget(tv) && !(tv is IDiscardOperation):
                    Assign(tv, value);
                    return;
                default: throw new NotTranslated("an assignment to " + target.Kind + " '" + target.Syntax + "'");
            }
        }

        private void Branch(BasicBlock b)
        {
            var fall = b.FallThroughSuccessor;
            string then = $"b{b.Ordinal}$then", otherwise = $"b{b.Ordinal}$else";
            if (b.ConditionalSuccessor != null)
            {
                bool inSpec = InSpec(b.BranchValue?.Syntax);
                KExpr cond = null;
                if (!inSpec)
                {
                    // (evaluated once, here: each way assumes it, or its negation)
                    var c = Expr(b.BranchValue);
                    var name = Declare($"g${b.Ordinal}", _model.Compilation.GetSpecialType(SpecialType.System_Boolean));
                    Emit(new KAssign { Var = name, Value = c });
                    cond = b.ConditionKind == ControlFlowConditionKind.WhenTrue ? new KVar(name) : new KOp("!", new KVar(name));
                }
                _block.Jump = new KGoto(then, otherwise);
                var thenBlock = new KBlock { Label = then, Ordinal = b.Ordinal };
                var elseBlock = new KBlock { Label = otherwise, Ordinal = b.Ordinal };
                if (cond != null)
                {
                    thenBlock.Stmts.Add(new KAssume { Cond = cond });
                    elseBlock.Stmts.Add(new KAssume { Cond = new KOp("!", cond) });
                }
                thenBlock.Jump = Edge(b, b.ConditionalSuccessor);
                elseBlock.Jump = Edge(b, fall);
                Next(b, b.ConditionalSuccessor.Destination, thenBlock);
                Next(b, fall?.Destination, elseBlock);
                // (the C# condition is true on the then edge when it jumps on true)
                if (b.ConditionKind == ControlFlowConditionKind.WhenTrue) FlagTakenOn(b, thenBlock, elseBlock);
                else FlagTakenOn(b, elseBlock, thenBlock);
                if (b.ConditionalSuccessor.Destination?.Kind == BasicBlockKind.Exit) TasksAwaited(thenBlock);
                if (fall?.Destination?.Kind == BasicBlockKind.Exit) TasksAwaited(elseBlock);
                _p.Blocks.Add(thenBlock);
                _p.Blocks.Add(elseBlock);
                return;
            }
            if (fall?.Semantics == ControlFlowBranchSemantics.Return && b.BranchValue != null)
                Emit(new KAssign { Var = "result", Value = Expr(b.BranchValue) });
            else if (fall?.Semantics == ControlFlowBranchSemantics.Throw || fall?.Semantics == ControlFlowBranchSemantics.Rethrow)
            {
                // (a path that throws need not meet the postcondition: it ends, or, where exceptions are seen, goes to the
                // handlers; a rethrow, past this try's)
                // (the throw the compiler adds to a switch expression, for a value no arm matches: the switch must cover
                // every value it gets, a failure the program didn't write)
                if (fall.Semantics == ControlFlowBranchSemantics.Throw && b.BranchValue?.Syntax is Microsoft.CodeAnalysis.CSharp.Syntax.SwitchExpressionSyntax missed &&
                    !InSpec(missed) && !(_p.Ghost || _contract.IsPure || _contract.IsLemma))
                {
                    Emit(new KCheck { Cond = new KLit("false"), Id = "CSV1022", At = missed,
                                      Message = $"switch expression '{missed.GoverningExpression} switch' might not cover every value: it would throw SwitchExpressionException" });
                    _block.Jump = new KStop();
                    return;
                }
                var target = ThrowTarget(b.EnclosingRegion);
                // (a proof may not escape its obligations by throwing)
                if (_p.Ghost || _contract.IsPure || _contract.IsLemma)
                    Emit(new KCheck { Cond = new KLit("false"), Id = "CSV1011", At = b.BranchValue?.Syntax ?? b.Operations.LastOrDefault()?.Syntax ?? _decl,
                                      Message = "a lemma or [Pure] function must not throw" });
                if (fall.Semantics == ControlFlowBranchSemantics.Throw && b.BranchValue != null)
                    Emit(new KThrow { Value = Expr(b.BranchValue), Seen = target != null, At = b.BranchValue.Syntax });
                _block.Jump = target == null ? new KStop() : new KGoto(target);
                return;
            }
            // (a return: every task it started was awaited, else a failure in it would be lost; through a finally, once it's run)
            if (fall?.Destination?.Kind == BasicBlockKind.Exit && !fall.FinallyRegions.Any(f => !_erased.Contains(f.EnclosingRegion))) TasksAwaited(_block);
            // (a constructor's end: the invariants of its object's locks hold, before anyone can take them)
            // (a static constructor's: its type's static locks')
            if (fall?.Destination?.Kind == BasicBlockKind.Exit && (_p.IsCtor || _m.MethodKind == MethodKind.StaticConstructor) && KernelTypes.Locks != null)
                foreach (var (lockField, invariant) in KernelTypes.Locks.InvariantsIn(_m.ContainingType).Where(x => x.lockField.IsStatic == _m.IsStatic))
                    Emit(new KCheck { Cond = InvariantCall(invariant, _m.IsStatic ? null : new KVar("this")), Id = "CSV1024", At = _decl,
                                      Message = $"the constructor might not establish the invariant of lock '{lockField.Name}'" });
            // (the end of a finally: on to where whatever ran it was going)
            if (fall?.Semantics == ControlFlowBranchSemantics.StructuredExceptionHandling && FinallyOf(b.EnclosingRegion) is ControlFlowRegion fin)
            {
                _finEnds.Add((fin, _block));
                return;
            }
            _block.Jump = Edge(b, fall);
            Next(b, fall?.Destination, _block);
        }

        /// <summary>An edge back to a foreach's head: the next element.</summary>
        private void Next(BasicBlock from, BasicBlock to, KBlock edge)
        {
            if (to != null && _forEachAt.TryGetValue(to.Ordinal, out var fe) && from.Ordinal >= fe.Head)
                edge.Stmts.Add(new KAssign { Var = fe.Index, Value = new KOp("+", new KVar(fe.Index), new KLit("1")) });
        }

        private readonly Dictionary<CaptureId, IOperation> _lvalues = new Dictionary<CaptureId, IOperation>();
    }
}
