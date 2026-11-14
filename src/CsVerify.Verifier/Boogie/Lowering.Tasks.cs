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
using static CsVerify.Verifier.Boogie.KOp;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>async, tasks and threads: awaits, tasks started and joined, Task.Run, WhenAll, threads, what stays confined.</summary>
    internal sealed partial class Lowering
    {
        private bool Concurrent => KernelTypes.Started != null && KernelTypes.Started.RunsAlongside(_m) && !_p.Ghost;

        /// <summary>
        /// A field used by code that runs alongside other code: it never changes, a lock guards it (StaticChecks checks that), or its object is in hand (a confined local's, or the one a constructor is
        /// building); otherwise another could be writing it (CSV1027).
        /// </summary>
        /// <summary>Is a task this method started still running here? (null: none is started)</summary>
        /// <summary>Tasks started here that nothing in this method awaits: kept elsewhere, discarded, or never looked at again.</summary>
        private readonly List<Task> _detached = new List<Task>();

        private IEnumerable<Task> AllTasks() => _tasks.Values.Concat(_startedCaptures.Values).Concat(_detached);

        /// <summary>That some task is not yet awaited (null: there are none).</summary>
        private KExpr Running()
        {
            var running = AllTasks().Select(t => Not(new KVar(t.Awaited))).ToList();
            return running.Count == 0 ? null : OrAny(running);
        }

        /// <summary>Running alongside other code here: always (a method that runs concurrently), or while a task it started does.</summary>
        private KExpr Alongside(KExpr inHand) => Concurrent ? inHand : Running() is KExpr r ? OrElse(Not(r), inHand) : null;

        // ------------------------------------------------------------------ async

        private bool _awaiting;
        /// <summary>The call being lowered is a task's or thread's start (1): it returns at its join.</summary>
        private int _phase;
        /// <summary>
        /// await t: other code may run, so what the method doesn't hold is forgotten (all but its confined locals'
        /// objects). An awaited async method of the program is a call, its contract of the task's result; a library's
        /// Task.Yield, Task.Delay, Task.CompletedTask gives nothing. ConfigureAwait is seen through. In three parts: what
        /// is awaited, lowered up to the await (Awaiting); other code running (OthersRun); what comes after it (here).
        /// </summary>
        private KExpr Await(IAwaitOperation aw)
        {
            if (_p.Ghost || _contract.IsPure || _contract.IsLemma)
            {
                throw new NotTranslated("an await in a proof");
            }
            var op = aw.Operation;
            while (op is IInvocationOperation ca && ca.TargetMethod.Name == "ConfigureAwait" && ca.Instance != null)
            {
                op = ca.Instance;
            }
            // (a task of a nullable type, checked not null: the task)
            if (op is IConversionOperation { IsImplicit: true } nc && IsGivenTask(nc.Operand.Type))
            {
                op = nc.Operand;
            }
            var awaited = Awaiting(op, aw);
            OthersRun(aw);
            var value = awaited.ValueAfter != null ? awaited.ValueAfter() : awaited.Value;
            // (where exceptions are seen: a library's await may throw, a cancellation say; not an async method of the
            // program's, whose call says how it throws, nor what says so itself)
            if (!(op is IInvocationOperation call && IsTaskMethod(call.TargetMethod) && call.TargetMethod.DeclaringSyntaxReferences.Length > 0) && !awaited.ThrowsAlready &&
                _cfgBlock != null && ThrowTarget(_cfgBlock.EnclosingRegion) is string target)
            {
                Emit(new KFork
                {
                    Overflow = KLit.False,
                    Target = target,
                    Exception = null,
                });
            }
            awaited.After?.Invoke();
            if (awaited.Gate != null)
            {
                Take(awaited.Gate, aw.Syntax, awaited.GateOwner);
            }
            return value;
        }

        /// <summary>What is awaited, lowered up to the await: what it gives, and what it needs once the others have run.</summary>
        private sealed class Awaited
        {
            /// <summary>Its value (null: none, or not used).</summary>
            public KExpr Value;
            /// <summary>Its value, read once the others have run (an EF query's, the tracker's), in place of Value.</summary>
            public System.Func<KExpr> ValueAfter;
            /// <summary>What's made of what it gave, once the others have run (Task.WhenAll's array, which nobody else has).</summary>
            public System.Action After;
            /// <summary>A gate it takes (a semaphore's, a lock wrapper's), and whose.</summary>
            public IFieldSymbol Gate;
            public KExpr GateOwner;
            /// <summary>Its way of throwing is made already, or is its own (the tracker's): no other.</summary>
            public bool ThrowsAlready;
        }

        /// <summary>What gives nothing and needs nothing after.</summary>
        private static Awaited Nothing => new Awaited();

        /// <summary>What is awaited: a task started here and kept in a local, a call, a property, a task one is given.</summary>
        private Awaited Awaiting(IOperation op, IAwaitOperation aw) => op switch
        {
            ILocalReferenceOperation tl when _tasks.TryGetValue(tl.Local, out var task) => AwaitedTask(task),
            IInvocationOperation call => AwaitedCall(call, aw),
            IPropertyReferenceOperation { Property.Name: "CompletedTask" } done when done.Property.ContainingType?.ToDisplayString() == "System.Threading.Tasks.Task" => Nothing,
            // (a task one is given: other code runs meanwhile; what it gives isn't known)
            IParameterReferenceOperation or ILocalReferenceOperation when IsGivenTask(op.Type) && !(op is ILocalReferenceOperation gl && _tasks.ContainsKey(gl.Local)) =>
                new Awaited { Value = Unknown(op, op.Type is INamedTypeSymbol { Arity: 1 } gt ? gt.TypeArguments[0] : null, notNull: false) },
            _ => throw new NotTranslated("an await of " + op.Syntax),
        };

        /// <summary>A task started here, kept in a local: its join (a task that failed gives nothing back: the way it throws leaves before it).</summary>
        private Awaited AwaitedTask(Task task)
        {
            bool forked = false;
            if (_cfgBlock != null && ThrowTarget(_cfgBlock.EnclosingRegion) is string failed)
            {
                // (awaited all the same: its failure is seen)
                Emit(KAssign.Of(task.Awaited, KLit.True));
                Emit(new KFork
                {
                    Overflow = KLit.False,
                    Target = failed,
                    Exception = null,
                });
                forked = true;
            }
            JoinOf(task);
            Emit(KAssign.Of(task.Awaited, KLit.True));
            return new Awaited
            {
                Value = task.Result == null ? null : new KVar(task.Result),
                ThrowsAlready = forked,
            };
        }

        /// <summary>A value nothing is known of but its type's (not null, where it says so): what a task one is given gives.</summary>
        private KExpr Unknown(IOperation of, ITypeSymbol type, bool notNull)
        {
            if (of != null)
            {
                Expr(of);
            }
            if (type == null)
            {
                return null;
            }
            var r = Declare("t$" + _temps++, type);
            Emit(KHavoc.Of(r));
            if (notNull && IsNullable(type) && NotNullable(type))
            {
                Emit(KAssume.Of(NotNull(new KVar(r))));
            }
            return new KVar(r);
        }

        /// <summary>What awaiting a call is, by what it calls.</summary>
        private Awaited AwaitedCall(IInvocationOperation op, IAwaitOperation aw)
        {
            switch (op)
            {
                case IInvocationOperation all when all.TargetMethod.ContainingType?.ToDisplayString() == "System.Threading.Tasks.Task" && all.TargetMethod.Name == "WhenAll":
                    return AwaitedWhenAll(all, aw);
                // (Task.Run(lambda) awaited where it starts: its code verified on its own, other code running meanwhile, as at
                // any await; what it gives not known. Not where the lambda writes this method's locals or parameters)
                case IInvocationOperation run when run.TargetMethod.ContainingType?.ToDisplayString() == "System.Threading.Tasks.Task" && run.TargetMethod.Name == "Run" &&
                                                   run.Arguments.Length == 1 && LambdaSyntax(run.Arguments[0]) is AnonymousFunctionExpressionSyntax awaitedLambda && !WritesOutside(awaitedLambda) &&
                                                   // (not one call, proved where it starts, nor in a method with permissions: a task as Start has it)
                                                   StartedCall(awaitedLambda) == null && !Permissions(_m):
                    if (op.Type is INamedTypeSymbol { Arity: 1 } && aw.Type != null && aw.Type.SpecialType != SpecialType.System_Void)
                    {
                        if (!InSubset(aw.Type))
                        {
                            throw new NotTranslated("Task.Run of " + aw.Type);
                        }
                        return new Awaited { Value = Unknown(null, aw.Type, notNull: true) };
                    }
                    return Nothing;
                // (a library member with an async stub, awaited: its stub's contract, of what the task gives)
                case IInvocationOperation las when las.TargetMethod.DeclaringSyntaxReferences.Length == 0 && KernelTypes.AsyncStub?.Invoke(las.TargetMethod.OriginalDefinition) == true &&
                                                   LibraryStub(las.TargetMethod.OriginalDefinition):
                    return new Awaited { Value = AwaitedCallOf(las) };
                // (a method of the program's that isn't async but gives a task, awaited: its call, a procedure's, then the
                // task it gave awaited as one is given: what it gives not known)
                case IInvocationOperation pt when pt.TargetMethod.DeclaringSyntaxReferences.Length > 0 && !pt.TargetMethod.IsAsync && !pt.TargetMethod.IsAbstract &&
                                                  IsTaskLike(pt.TargetMethod.ReturnType) && _isProcedure(pt.TargetMethod):
                {
                    Expr(pt);
                    if (pt.Type is INamedTypeSymbol { Arity: 1 } ptt && aw.Type != null && aw.Type.SpecialType != SpecialType.System_Void)
                    {
                        if (!InSubset(ptt.TypeArguments[0]))
                        {
                            throw new NotTranslated("an await of a task of " + ptt.TypeArguments[0]);
                        }
                        return new Awaited { Value = Unknown(null, ptt.TypeArguments[0], notNull: true) };
                    }
                    return Nothing;
                }
                // (Task.Run(() => F(...)) awaited where it starts: the call, as if awaited itself)
                case IInvocationOperation run1 when run1.TargetMethod.ContainingType?.ToDisplayString() == "System.Threading.Tasks.Task" && run1.TargetMethod.Name == "Run" &&
                                                    run1.Arguments.Length == 1 && LambdaSyntax(run1.Arguments[0]) is AnonymousFunctionExpressionSyntax oneCall && StartedCall(oneCall) is IInvocationOperation theCall:
                {
                    var value = AwaitedCallOf(theCall);
                    return new Awaited { Value = aw.Type == null || aw.Type.SpecialType == SpecialType.System_Void ? null : value };
                }
                // (EF's tracker's ...Async operations: read after the others have run, as a query is; they say how they throw)
                case IInvocationOperation eft when _failed != null && eft.TargetMethod.Name.EndsWith("Async") &&
                                                   (IsEfMethod(eft.TargetMethod) || KernelTypes.Ef.IsContextType(eft.TargetMethod.ContainingType) || IsTransactionType(eft.TargetMethod.ContainingType) ||
                                                    eft.TargetMethod.Name == "DisposeAsync" && eft.Instance != null && IsTransactionType(TrackerReceiverOf(eft.Instance)?.Type) ||
                                                    eft.TargetMethod.Name == "CreateDbContextAsync" && eft.Instance != null && IsEfFactory(Unconverted(eft.Instance).Type)) &&
                                                   (EfAsyncTwin(eft.TargetMethod) == null || eft.TargetMethod.Name.StartsWith("Execute")):
                    return new Awaited
                    {
                        ThrowsAlready = true,
                        ValueAfter = () =>
                        {
                            var (handled, tv) = TrackerCall(eft, awaited: true);
                            if (!handled)
                            {
                                throw new NotTranslated("an await of " + eft.Syntax);
                            }
                            return tv;
                        },
                    };
                // (an EF query operator's ...Async form, awaited where it's called: the operator's value, read after the others have run)
                case IInvocationOperation efq when EfAsyncTwin(efq.TargetMethod) is string && efq.Type is INamedTypeSymbol { Arity: 1 }:
                    return new Awaited
                    {
                        ValueAfter = () =>
                        {
                            _tableReads = null;
                            return Linq(efq, EfAsyncTwin(efq.TargetMethod), ((INamedTypeSymbol)efq.Type).TypeArguments[0]);
                        },
                    };
                // (a library's lock wrapper, awaited: its lock taken)
                case IInvocationOperation libw when libw.TargetMethod.DeclaringSyntaxReferences.Length == 0 && KernelTypes.Locks?.Acquires(libw.TargetMethod) == true:
                    LockReceiver(libw.Instance);
                    return new Awaited { Gate = WrapperGate(libw, acquiring: true) };
                case IInvocationOperation call when IsTaskMethod(call.TargetMethod) && call.TargetMethod.DeclaringSyntaxReferences.Length > 0:
                {
                    var value = AwaitedCallOf(call);
                    // (a lock wrapper's [Acquires], awaited: its gate is taken, as WaitAsync's is)
                    return new Awaited
                    {
                        Value = value,
                        Gate = WrapperGate(call, acquiring: true),
                    };
                }
                // (in a lock wrapper itself, its semaphore is its callers' to hold: waiting on it here changes nothing the kernel knows of)
                case IInvocationOperation wait when IsSemaphore(wait.TargetMethod.ContainingType) && wait.TargetMethod.Name == "WaitAsync" && wait.Arguments.All(a => IsToken(a.Value.Type)) && InWrapper:
                    if (wait.Instance != null)
                    {
                        Expr(Unconverted(wait.Instance));
                    }
                    foreach (var a in wait.Arguments)
                    {
                        Expr(a.Value);
                    }
                    return Nothing;
                case IInvocationOperation wait when IsSemaphore(wait.TargetMethod.ContainingType) && wait.TargetMethod.Name == "WaitAsync" && wait.Arguments.All(a => IsToken(a.Value.Type)):
                {
                    var gate = GateOf(wait);
                    return new Awaited
                    {
                        Gate = gate,
                        GateOwner = _gateOwner,
                    };
                }
                // (a wait with a timeout: it may not take the gate, so nothing is held after; what it gives is unknown)
                case IInvocationOperation timed when IsSemaphore(timed.TargetMethod.ContainingType) && timed.TargetMethod.Name == "WaitAsync" && timed.Arguments.Any(a => !IsToken(a.Value.Type)) && InSubset(aw.Type ?? timed.Type):
                    if (timed.Instance != null)
                    {
                        Expr(Unconverted(timed.Instance));
                    }
                    foreach (var a in timed.Arguments)
                    {
                        if (InSubset(a.Value.Type))
                        {
                            Expr(a.Value);
                        }
                    }
                    return new Awaited { Value = aw.Type != null && aw.Type.SpecialType != SpecialType.System_Void ? Unknown(null, aw.Type, notNull: false) : null };
                case IInvocationOperation lib when lib.TargetMethod.ContainingType?.ToDisplayString() == "System.Threading.Tasks.Task" && lib.TargetMethod.Name is "Yield" or "Delay":
                    foreach (var a in lib.Arguments.Select(x => x.Value))
                    {
                        if (InSubset(a.Type))
                        {
                            Expr(a);
                        }
                        else if (!(Unconverted(a) is IParameterReferenceOperation or ILocalReferenceOperation))
                        {
                            throw new NotTranslated("an argument of " + lib.TargetMethod.Name);
                        }
                    }
                    return Nothing;
                // (await using's IAsyncDisposable.DisposeAsync of a class's object: that class's code, its contract a library
                // interface's, so what it does isn't known: anything, as for Dispose)
                case IInvocationOperation da when da.TargetMethod.Name == "DisposeAsync" && da.TargetMethod.ContainingType?.ToDisplayString() == "System.IAsyncDisposable" &&
                                                  da.Instance != null && IsClass(Unconverted(da.Instance).Type):
                    DelegatesHere("a call of DisposeAsync");
                    if (_cfgBlock != null && ThrowTarget(_cfgBlock.EnclosingRegion) != null)
                    {
                        throw new NotTranslated("a call of DisposeAsync where exceptions are seen");
                    }
                    Expr(Unconverted(da.Instance));
                    _p.HavocsAll = true;
                    Emit(new KHavocAll());
                    return Nothing;
                // (a task a delegate gives: its call, then as a task one is given)
                case IInvocationOperation dt when dt.TargetMethod.MethodKind == MethodKind.DelegateInvoke && IsGivenTask(dt.Type):
                    return new Awaited { Value = Unknown(dt, dt.Type is INamedTypeSymbol { Arity: 1 } dtt ? dtt.TypeArguments[0] : null, notNull: true) };
                // (await foreach's next round: whether there's another isn't known; it may throw, as any library await)
                case IInvocationOperation mna when mna.TargetMethod.Name == "MoveNextAsync" && mna.Instance is IFlowCaptureReferenceOperation mc && _asyncEach.ContainsKey(mc.Id):
                    return new Awaited { Value = Unknown(null, _model.Compilation.GetSpecialType(SpecialType.System_Boolean), notNull: false) };
                // (a library's task or value task without a stub (a channel's ReadAsync): its receiver not null; other code
                // runs meanwhile, as at any await; what it gives isn't known (not null where its type says so); it may throw)
                case IInvocationOperation la when la.TargetMethod.DeclaringSyntaxReferences.Length == 0 && IsTaskLike(la.Type) && !SpecSymbols.IsSpecClass(la.TargetMethod.ContainingType) &&
                                                  !(_contractOf?.Invoke(la.TargetMethod) is Contract lac && (lac.IsStub || lac.HasSource)) &&
                                                  la.Arguments.All(a => a.Parameter.RefKind == RefKind.None && (InSubset(a.Value.Type) || IsToken(a.Value.Type)) && !IsDelegate(a.Parameter.Type)) &&
                                                  (la.Instance == null || InSubset(la.Instance.Type) || IsLibraryObject(la.Instance.Type)):
                {
                    if (la.Instance != null)
                    {
                        var recv = Expr(Unconverted(la.Instance));
                        if (!la.Instance.Type.IsValueType)
                        {
                            Emit(KCheck.Of(NotNull(recv), "CSV1013", la.Instance.Syntax, $"'{la.Instance.Syntax}' might be null in '{la.Syntax}'"));
                        }
                    }
                    foreach (var a in la.Arguments.OrderBy(a => a.Parameter.Ordinal))
                    {
                        Expr(a.Value);
                    }
                    if (la.Type is INamedTypeSymbol { Arity: 1 } lt)
                    {
                        if (!InSubset(lt.TypeArguments[0]))
                        {
                            throw new NotTranslated("an await of " + lt);
                        }
                        return new Awaited { Value = Unknown(null, lt.TypeArguments[0], notNull: true) };
                    }
                    return Nothing;
                }
                default: throw new NotTranslated("an await of " + op.Syntax);
            }
        }

        /// <summary>An awaited call: lowered as one, where its await is.</summary>
        private KExpr AwaitedCallOf(IInvocationOperation call)
        {
            _awaiting = true;
            try
            {
                return Call(call);
            }
            finally
            {
                _awaiting = false;
            }
        }

        /// <summary>
        /// Task.WhenAll(...): every one started before any is joined (those written in it start here, the others already
        /// run), then all joined; its value, where it's used, an array of what each gives, in order.
        /// </summary>
        private Awaited AwaitedWhenAll(IInvocationOperation all, IAwaitOperation aw)
        {
            var inlineStarts = new List<Task>();
            var joins = new List<Task>();
            var order = new List<Task>();
            foreach (var a in all.Arguments.SelectMany(x => x.Value is IArrayCreationOperation ac ? ac.Initializer?.ElementValues.AsEnumerable() ?? new IOperation[0]
                                                          : x.Value is ICollectionExpressionOperation ce ? ce.Elements.AsEnumerable() : new[] { x.Value }))
            {
                if (Unconverted(a is IFlowCaptureReferenceOperation wc && _captured.TryGetValue(wc.Id, out var wv) ? wv : a) is ILocalReferenceOperation wl &&
                    _tasks.TryGetValue(wl.Local, out var wt))
                {
                    joins.Add(wt);
                    order.Add(wt);
                }
                else if (a is IFlowCaptureReferenceOperation wr && _startedCaptures.TryGetValue(wr.Id, out var wst))
                {
                    joins.Add(wst);
                    order.Add(wst);
                }
                // (a batch of tasks: all joined; how many, and what they give, isn't known)
                else if (Unconverted(a is IFlowCaptureReferenceOperation bc && _captured.TryGetValue(bc.Id, out var bv) ? bv : a) is ILocalReferenceOperation bl && _batches.TryGetValue(bl.Local, out var batch))
                {
                    Emit(KAssign.Of(batch.Awaited, KLit.True));
                    order.Add(null);
                }
                // (a call written in it: started with the others, joined with them)
                else if (Unconverted(a) is IInvocationOperation inline && inline.TargetMethod.IsAsync && inline.TargetMethod.DeclaringSyntaxReferences.Length > 0)
                {
                    var started = StartInline(inline);
                    started.Effects = EffectsOfCall(inline);
                    foreach (var o in inlineStarts)
                    {
                        WarnIfMayRace(inline.Syntax, started.Effects, o.Effects, KLit.False);
                    }
                    foreach (var o in _tasks.Values.Where(t => t.Effects != null))
                    {
                        WarnIfMayRace(inline.Syntax, started.Effects, o.Effects, new KVar(o.Awaited));
                    }
                    inlineStarts.Add(started);
                    order.Add(started);
                }
                // (Task.Run(lambda) written in it: started with the others, as a Task.Run in a variable is)
                else if (Unconverted(a) is IInvocationOperation trn && trn.TargetMethod.ContainingType?.ToDisplayString() == "System.Threading.Tasks.Task" && trn.TargetMethod.Name == "Run" &&
                         trn.Arguments.Length == 1 && LambdaSyntax(trn.Arguments[0]) is AnonymousFunctionExpressionSyntax rlam)
                {
                    var started = RunInline(trn, rlam);
                    foreach (var o in inlineStarts)
                    {
                        WarnIfMayRace(trn.Syntax, started.Effects, o.Effects, KLit.False);
                    }
                    foreach (var o in _tasks.Values.Where(t => t.Effects != null))
                    {
                        WarnIfMayRace(trn.Syntax, started.Effects, o.Effects, new KVar(o.Awaited));
                    }
                    inlineStarts.Add(started);
                    order.Add(started);
                }
                // (a task one is given, a library's: other code runs meanwhile, as awaiting it does, and nothing is known of it)
                else if (Unconverted(a is IFlowCaptureReferenceOperation gc && _captured.TryGetValue(gc.Id, out var gv) ? gv : a) is var given &&
                         (given is ILocalReferenceOperation gl && !StartedByProgram(gl.Local) || given is IParameterReferenceOperation) && IsGivenTask(given.Type))
                {
                    Expr(given);
                }
                else
                {
                    throw new NotTranslated("Task.WhenAll of a task not started here");
                }
            }
            foreach (var t in joins)
            {
                JoinOf(t);
                Emit(KAssign.Of(t.Awaited, KLit.True));
            }
            foreach (var t in inlineStarts)
            {
                JoinOf(t);
            }
            bool used = !(aw.Parent is IExpressionStatementOperation || aw.Parent == null);
            if (used && aw.Type is IArrayTypeSymbol rat)
            {
                if (!InSubset(rat))
                {
                    throw new NotTranslated("Task.WhenAll's results of " + rat.ElementType);
                }
                var arr = Declare("t$" + _temps++, rat);
                // (of a batch: as many as it has, what each gave not known)
                if (order.Contains(null))
                {
                    var n = Declare("t$" + _temps++, _model.Compilation.GetSpecialType(SpecialType.System_Int32));
                    Emit(KHavoc.Of(n));
                    Emit(KAssume.Of(Le(KLit.Zero, new KVar(n))));
                    var barr = Declare("t$" + _temps++, rat);
                    var map = Elements(rat);
                    return new Awaited
                    {
                        Value = new KVar(barr),
                        After = () =>
                        {
                            Emit(KNew.Of(barr, rat, new KVar(n)));
                            Emit(KRow.Of(map, new KVar(barr), new KVar(LinqMap("[int]" + ElementValue(map)))));
                        },
                    };
                }
                var elements = order.Select(t =>
                {
                    if (t.Result != null)
                    {
                        return (KExpr)new KVar(t.Result);
                    }
                    var u = Declare("t$" + _temps++, rat.ElementType);
                    Emit(KHavoc.Of(u));
                    return new KVar(u);
                }).ToArray();
                return new Awaited
                {
                    Value = new KVar(arr),
                    After = () => Emit(KNew.Of(arr, rat, new KLit(order.Count.ToString()), elements: elements)),
                };
            }
            if (used)
            {
                throw new NotTranslated("Task.WhenAll's value");
            }
            return Nothing;
        }

        /// <summary>
        /// At an await, other code runs: the method awaits (its effects so marked), what it doesn't hold is forgotten
        /// (KAwait), but what a gate held here guards, which nobody else can have, and the confined locals' objects.
        /// </summary>
        private void OthersRun(IAwaitOperation aw)
        {
            _p.Awaits = true;
            _p.CallsDelegates = true;
            // (what a gate held here guards stays, as nobody else can have it)
            var kept = new List<(ISymbol field, string var, KExpr owner)>();
            var heldHere = GatesHeld(aw.Syntax).Distinct<IFieldSymbol>(SymbolEqualityComparer.Default).Select(g => (g, (KExpr)(g.IsStatic ? null : new KVar("this")))).ToList();
            heldHere.AddRange(OthersGatesHeld(aw.Syntax));
            foreach (var (g, owner) in heldHere)
            {
                foreach (var f in KernelTypes.Locks.GuardedBy(g).Where(f => f.IsStatic == g.IsStatic && IsField(f)))
                {
                    var t = Declare("t$" + _temps++, FieldType(f));
                    _p.AddField(f.OriginalDefinition);
                    var read = new KField
                    {
                        Field = f.OriginalDefinition,
                        Instance = f.IsStatic ? null : owner,
                        OnThis = owner is KVar { Name: "this" },
                        NoNull = true,
                        At = aw.Syntax,
                        InstanceAt = aw.Syntax,
                    };
                    Emit(KAssign.Of(t, read));
                    kept.Add((f.OriginalDefinition, t, f.IsStatic ? null : owner));
                }
            }
            var keep = new KAwait();
            if (!_opaque)
            {
                foreach (var l in Confined())
                {
                    keep.AddKeep(Declare(Local(l), l.Type));
                }
            }
            var unshared = UnsharedBefore();
            Emit(keep);
            UnsharedAfter(unshared);
            foreach (var (f, t, owner) in kept)
            {
                var read = new KField
                {
                    Field = f,
                    Instance = owner,
                    OnThis = owner is KVar { Name: "this" },
                    NoNull = true,
                    At = aw.Syntax,
                    InstanceAt = aw.Syntax,
                };
                Emit(KAssume.Of(Eq(read, new KVar(t))));
            }
            ForgetCaptured();
        }

        /// <summary>A task started and kept in a local, awaited later: whether it has been, and its result.</summary>
        private sealed class Task
        {
            public IMethodSymbol Method;
            public string Awaited, Result;
            public SyntaxNode At;
            /// <summary>A thread, or a task of code of its own: not reported if never finished.</summary>
            public bool Thread;
            /// <summary>Its call's start, where it's in two phases (a callee of permissions); and whether its join has been.</summary>
            public KCall StartCall;
            /// <summary>What it may race on, with what runs alongside it (null: not told).</summary>
            public Effects Effects;
            /// <summary>What its postcondition reads but it doesn't give back: forgotten at its join.</summary>
            public List<System.Action> Forget;
            /// <summary>A thread's (not a Task.Run's), and where a Task.Run or a thread was started.</summary>
            public bool RealThread;
            public SyntaxNode RunAt;
            /// <summary>The locals of this method its code writes, while it runs.</summary>
            public HashSet<ILocalSymbol> Shared = new HashSet<ILocalSymbol>(SymbolEqualityComparer.Default);
            /// <summary>Kept somewhere else (a field, a discard): this method needn't await it.</summary>
            public bool Kept;

            public bool AddShared(ILocalSymbol shared) => Shared.Add(shared);
        }

        private readonly Dictionary<ILocalSymbol, Task> _tasks = new Dictionary<ILocalSymbol, Task>(SymbolEqualityComparer.Default);

        /// <summary>
        /// var t = F(...): F's precondition is checked here, and what it gives is the task's result, known once it's
        /// awaited; t is used only by await t, Task.WhenAll and t.Result, and never assigned again.
        /// </summary>
        /// <summary>
        /// A started task's postcondition is of the state when it ends, and by the await others may have changed what it
        /// doesn't give back: so it may read only what never changes and what it gives back, to its left
        /// (CSV1016, at the start). Spec.Old is of the start, which is known.
        /// </summary>
        private List<IOperation> GivesBack(IInvocationOperation call)
        {
            var unkept = new List<IOperation>();
            if (!(_contractOf?.Invoke(call.TargetMethod.OriginalDefinition) is Contract c))
            {
                return unkept;
            }
            var given = new HashSet<ISymbol>(SymbolEqualityComparer.Default);
            IOperation read = null;
            foreach (var e in c.Ensures)
            {
                WalkArguments(e.Expr, call, given, ref read, unkept);
            }
            if (read != null)
            {
                Emit(KCheck.Of(
                    KLit.False,
                    "CSV1016",
                    call.Syntax,
                    notAssumedAfter: true,
                    message: $"the postcondition of the task started here reads '{read.Syntax}', which it doesn't give back (no Spec.Acc for it to its left): by the time it is awaited, others may have changed it. Give it back, or await the call at once"));
            }
            return unkept;
        }

        private void WalkArguments(IOperation o, IInvocationOperation call, HashSet<ISymbol> given, ref IOperation read, List<IOperation> unkept)
        {
            if (o == null)
            {
                return;
            }
            switch (o)
            {
                case IInvocationOperation inv when SpecSymbols.IsSpecClass(inv.TargetMethod.ContainingType) && inv.TargetMethod.Name is "Acc" or "AccRead":
                    if (inv.Arguments.Length > 0 && RootSymbol(inv.Arguments.OrderBy(a => a.Parameter.Ordinal).First().Value, call) is ISymbol g)
                    {
                        given.Add(g);
                    }
                    return;
                case IInvocationOperation old when SpecSymbols.IsSpecClass(old.TargetMethod.ContainingType) && old.TargetMethod.Name == "Old":
                    return;
                case IBinaryOperation { OperatorKind: BinaryOperatorKind.ConditionalAnd or BinaryOperatorKind.And } and:
                    WalkArguments(and.LeftOperand, call, given, ref read, unkept);
                    WalkArguments(and.RightOperand, call, given, ref read, unkept);
                    return;
                case IArrayElementReferenceOperation ae:
                    if (!(RootSymbol(ae.ArrayReference, call) is ISymbol ar && given.Contains(ar)))
                    {
                        read ??= o;
                        unkept.Add(o);
                        return;
                    }
                    foreach (var x in ae.Indices)
                    {
                        WalkArguments(x, call, given, ref read, unkept);
                    }
                    return;
                case IFieldReferenceOperation f when !f.Field.IsReadOnly && !f.Field.IsConst:
                    if (f.Instance == null || !(RootSymbol(f.Instance, call) is ISymbol fr && given.Contains(fr)))
                    {
                        read ??= o;
                        unkept.Add(o);
                        return;
                    }
                    return;
            }
            foreach (var ch in o.ChildOperations)
            {
                WalkArguments(ch, call, given, ref read, unkept);
            }
        }

        private ISymbol RootSymbol(IOperation o, IInvocationOperation call) => Unconverted(o) switch { IParameterReferenceOperation p => p.Parameter, IInstanceReferenceOperation _ => call.TargetMethod.ContainingType, _ => null };

        /// <summary>
        /// What a started task's postcondition reads but doesn't give back, as the caller's: forgotten where the task is
        /// joined (it may have changed since the task finished). An array's elements, a
        /// field of an object, of a parameter the caller passes a local or a parameter for; else the call isn't translated.
        /// </summary>
        private List<System.Action> Unkept(IInvocationOperation call, List<IOperation> reads)
        {
            var forget = new List<System.Action>();
            foreach (var r in reads)
            {
                // (a static field: forgotten itself)
                if (r is IFieldReferenceOperation { Field: { IsStatic: true } sf } && IsField(sf))
                {
                    var field = sf.OriginalDefinition;
                    _p.AddField(field);
                    forget.Add(() =>
                    {
                        var v = Declare("t$" + _temps++, sf.Type);
                        Emit(KHavoc.Of(v));
                        Emit(new KFieldStore
                        {
                            Field = field,
                            Instance = null,
                            Value = new KVar(v),
                            At = call.Syntax,
                            InstanceAt = call.Syntax,
                        });
                    });
                    continue;
                }
                var root = r is IArrayElementReferenceOperation ae ? ae.ArrayReference : (r as IFieldReferenceOperation)?.Instance;
                var arg = root == null ? null : ArgumentOf(root, call);
                if (!(Unconverted(arg) is ILocalReferenceOperation || Unconverted(arg) is IParameterReferenceOperation))
                {
                    throw new NotTranslated("a started task's postcondition reading what it doesn't give back, of an argument that isn't a variable");
                }
                var target = Expr(Unconverted(arg));
                if (r is IArrayElementReferenceOperation ar && IsArray(ar.ArrayReference.Type))
                {
                    var map = Elements(ar.ArrayReference.Type);
                    forget.Add(() =>
                    {
                        var fresh = new KVar(LinqMap("[int]" + ElementValue(map)));
                        Emit(KRow.Of(map, target, fresh));
                    });
                }
                else if (r is IFieldReferenceOperation fr && IsField(fr.Field))
                {
                    var field = fr.Field.OriginalDefinition;
                    _p.AddField(field);
                    forget.Add(() =>
                    {
                        var v = Declare("t$" + _temps++, fr.Field.Type);
                        Emit(KHavoc.Of(v));
                        Emit(KRow.Of(FieldMap(field), target, new KVar(v)));
                    });
                }
                else
                {
                    throw new NotTranslated("a started task's postcondition reading what it doesn't give back: " + r.Syntax);
                }
            }
            return forget;
        }

        private IOperation ArgumentOf(IOperation root, IInvocationOperation call) => Unconverted(root) is IParameterReferenceOperation p && p.Parameter.ContainingSymbol is IMethodSymbol pm &&
                                           SymbolEqualityComparer.Default.Equals(pm.OriginalDefinition, call.TargetMethod.OriginalDefinition)
            ? call.Arguments.FirstOrDefault(a => a.Parameter?.Ordinal == p.Parameter.Ordinal)?.Value : null;

        /// <summary>A started method that relies on its caller holding a gate: it would run alongside this code (CSV1023).</summary>
        private void StartedUnderGate(IInvocationOperation call)
        {
            if (call?.TargetMethod != null && call.TargetMethod.IsAsync && KernelTypes.Locks?.GuardOf(call.TargetMethod) is IFieldSymbol held && KernelTypes.Locks.IsSemaphore(held))
            {
                Emit(KCheck.Of(
                    KLit.False,
                    "CSV1023",
                    call.Syntax,
                    notAssumedAfter: true,
                    message: $"'{call.TargetMethod.Name}' relies on holding '{held.Name}', but its task isn't awaited here: it would run alongside this code"));
            }
        }

        private void Start(ILocalSymbol local, IInvocationOperation call, bool thread = false, SyntaxNode at = null, AnonymousFunctionExpressionSyntax lambda = null)
        {
            if (_tasks.ContainsKey(local))
            {
                Misused(at ?? call?.Syntax ?? _decl, local, "assigned again");
            }
            if (!thread)
            {
                StartedUnderGate(call);
            }
            // (what a task can't be given as it starts, views lent or its [Owned] receiver's: CSV1901)
            if (!thread && call != null && call.TargetMethod.IsAsync &&
                (call.Arguments.Any(a => SpecSymbols.IsLinear(a.Parameter?.Type) || a.Parameter?.RefKind != RefKind.None) || !call.TargetMethod.IsStatic && SpecSymbols.IsOwned(call.TargetMethod.ContainingType)))
            {
                Emit(KCheck.Of(
                    KLit.False,
                    "CSV1901",
                    call.Syntax,
                    notAssumedAfter: true,
                    message: $"'{call.TargetMethod.Name}' is async and is not awaited at once: it would run interleaved with this method, each changing what the other relies on (write 'await' at the call)"));
            }
            // (what it may race on: a Task.Run's or a thread's code, with this method's
            // alongside; an async method's, with the others')
            Effects effects = null;
            if (lambda != null)
            {
                effects = call != null ? EffectsOfCall(call, capturing: true) : EffectsOfDelegate(lambda);
                if (effects != null)
                {
                    RacesAtStart(at, effects, local.Name, call != null ? null : lambda, alongside: true);
                }
                // (a thread never joined goes on running after this method)
                if (thread && !_decl.DescendantNodes().OfType<InvocationExpressionSyntax>().Any(j => j.Expression is MemberAccessExpressionSyntax jm && jm.Name.Identifier.Text == "Join" &&
                                                                                                   SymbolEqualityComparer.Default.Equals(_model.GetSymbolInfo(jm.Expression).Symbol, local)))
                {
                    Detached(at, effects);
                }
            }
            else if (call != null && call.TargetMethod.IsAsync && call.TargetMethod.DeclaringSyntaxReferences.Length > 0)
            {
                effects = EffectsOfCall(call);
                RacesAtStart(call.Syntax, effects, local.Name, null, alongside: false);
            }
            foreach (var id in _decl.DescendantNodes().OfType<IdentifierNameSyntax>().Where(i => i.Identifier.Text == local.Name && SymbolEqualityComparer.Default.Equals(_model.GetSymbolInfo(i).Symbol, local)))
            {
                SyntaxNode e = id;
                while (e.Parent is ParenthesizedExpressionSyntax)
                {
                    e = e.Parent;
                }
                bool ok = thread ? e.Parent is MemberAccessExpressionSyntax tm && (tm.Name.Identifier.Text is "Start" or "Join" || tm.Name.Identifier.Text == "IsBackground" && tm.Parent is AssignmentExpressionSyntax tma && tma.Left == tm) ||
                                   e.Parent is VariableDeclaratorSyntax || e is VariableDeclaratorSyntax
                        : e.Parent is AwaitExpressionSyntax || e.Parent is MemberAccessExpressionSyntax ma && (ma.Name.Identifier.Text == "Result" || ma.Name.Identifier.Text == "Wait" && call == null ||
                                                                                                                 ma.Name.Identifier.Text == "ConfigureAwait" && ma.Parent?.Parent is AwaitExpressionSyntax) ||
                          // (a Task.Run's kept in a field: whoever has it awaits it)
                          lambda != null && e.Parent is AssignmentExpressionSyntax kasg && kasg.Right == e && _model.GetSymbolInfo(kasg.Left).Symbol is IFieldSymbol ||
                          e.Parent is ArgumentSyntax arg && arg.Parent?.Parent is InvocationExpressionSyntax wa && wa.Expression.ToString().EndsWith("WhenAll");
                if (!ok || id.Ancestors().Any(a => a is AnonymousFunctionExpressionSyntax || a is LocalFunctionStatementSyntax))
                {
                    Misused(id, local, "used otherwise than awaited (returned, stored, waited on or captured)");
                }
            }
            KExpr result = null;
            KCall started = null;
            List<System.Action> forget = null;
            if (call != null)
            {
                // (a callee of permissions: its start gives them, its join takes back what it gives; else the call at once)
                bool twoPhase = Permissions(call.TargetMethod);
                if (twoPhase)
                {
                    forget = Unkept(call, GivesBack(call));
                }
                _awaiting = true;
                _phase = twoPhase ? 1 : 0;
                try
                {
                    result = Call(call);
                }
                finally
                {
                    _awaiting = false;
                    _phase = 0;
                }
                if (twoPhase)
                {
                    started = _block.Stmts.OfType<KCall>().Last();
                }
            }
            // (of code of its own: what it gives isn't known, and it may reach anything, a confined local's object too)
            if (call == null && local.Type is INamedTypeSymbol { Arity: 1 } tt && InSubset(tt.TypeArguments[0]))
            {
                var unknown = Declare("t$" + _temps++, tt.TypeArguments[0]);
                Emit(KHavoc.Of(unknown));
                // (not null, where the code it runs doesn't return that)
                if (IsNullable(tt.TypeArguments[0]) && NotNullable(tt.TypeArguments[0]))
                {
                    Emit(KAssume.Of(NotNull(new KVar(unknown))));
                }
                result = new KVar(unknown);
            }
            if (call == null)
            {
                _opaque = true;
            }
            var task = new Task
            {
                Method = call?.TargetMethod,
                At = call?.Syntax,
                Result = (result as KVar)?.Name,
                Thread = thread || call == null,
                StartCall = started,
                Effects = effects,
                RealThread = thread,
                RunAt = at,
                Forget = forget,
                Awaited = Declare($"aw${_tasks.Count}", _model.Compilation.GetSpecialType(SpecialType.System_Boolean)),
            };
            if (result != null && task.Result == null)
            {
                task.Result = Declare("t$" + _temps++, Returns(call.TargetMethod));
                Emit(KAssign.Of(task.Result, result));
            }
            // (started in a loop: the one it started last time round must have been awaited, CSV1026; none was before the first)
            if (!thread && _cfgBlock != null && _p.LoopBodies.Any(lb => lb.Key <= _cfgBlock.Ordinal && _cfgBlock.Ordinal <= lb.Value))
            {
                _awaitedAtEntry.Add((task.Awaited, _cfgBlock.Ordinal, at ?? call.Syntax, call?.TargetMethod.Name ?? "Run"));
            }
            Emit(KAssign.Of(task.Awaited, KLit.False));
            // (the locals its code writes, which it captured: changed by it, whenever, while it runs)
            if (lambda != null && call == null)
            {
                foreach (var w in lambda.DescendantNodes().OfType<AssignmentExpressionSyntax>().Select(x => x.Left).Concat(lambda.DescendantNodes().OfType<PostfixUnaryExpressionSyntax>().Select(x => x.Operand))
                             .Concat(lambda.DescendantNodes().OfType<PrefixUnaryExpressionSyntax>().Select(x => x.Operand)))
                {
                    if (_model.GetSymbolInfo(w).Symbol is ILocalSymbol cl && !lambda.Span.Contains(cl.DeclaringSyntaxReferences.FirstOrDefault()?.Span ?? default) && InSubset(cl.Type))
                    {
                        task.AddShared(cl);
                    }
                }
            }
            // (kept in a field: whoever has it awaits it)
            task.Kept = lambda != null && _decl.DescendantNodes().OfType<AssignmentExpressionSyntax>().Any(a => _model.GetSymbolInfo(a.Left).Symbol is IFieldSymbol &&
                                                                                                               SymbolEqualityComparer.Default.Equals(_model.GetSymbolInfo(a.Right).Symbol, local));
            _tasks[local] = task;
        }

        private readonly HashSet<ILocalSymbol> _misused = new HashSet<ILocalSymbol>(SymbolEqualityComparer.Default);

        /// <summary>
        /// A task local used otherwise than awaited, or assigned again: not supported (CSV1901),
        /// since what runs alongside, and till when, can't be told; once for each.
        /// </summary>
        private void Misused(SyntaxNode at, ILocalSymbol local, string how)
        {
            if (!_misused.Add(local))
            {
                return;
            }
            Emit(KCheck.Of(
                KLit.False,
                "CSV1901",
                at,
                notAssumedAfter: true,
                message: $"the task in '{local.Name}' is {how}, which is not supported: await it where it is used"));
        }

        /// <summary>A task of code of its own was started: no object is in hand from then on.</summary>
        private bool _opaque;

        /// <summary>A callee whose contract names permissions: started, it runs in two phases.</summary>
        private bool Permissions(IMethodSymbol callee) =>
            _contractOf?.Invoke(callee) is Contract c && (c.Requires.Any(HasAtoms) || c.Ensures.Any(e => HasAtoms(e.Expr)));

        /// <summary>A task's join: where its call returns what its postconditions give, once.</summary>
        private void JoinOf(Task t)
        {
            if (t.StartCall == null)
            {
                return;
            }
            var st = t.StartCall;
            // (a task awaited in one place only: joined there; one awaited in more, joined where it wasn't yet)
            if (t.Awaited == null || _cfgBlock == null || !AwaitedInPlaces(t))
            {
                Join(st, t);
                t.StartCall = null;
                return;
            }
            // (once, on each path: where an earlier await joined it already (its awaited flag), nothing is given back again)
            var n = _joins++;
            var (join, skip, after) = (KBlock.Of($"b{_cfgBlock.Ordinal}$j{n}", _cfgBlock.Ordinal),
                                       KBlock.Of($"b{_cfgBlock.Ordinal}$j{n}$no", _cfgBlock.Ordinal),
                                       KBlock.Of($"b{_cfgBlock.Ordinal}$j{n}$after", _cfgBlock.Ordinal));
            _block.Jump = new KGoto(join.Label, skip.Label);
            _p.AddBlock(join);
            _p.AddBlock(skip);
            _p.AddBlock(after);
            _block = join;
            Emit(KAssume.Of(Not(new KVar(t.Awaited))));
            Join(st, t);
            join.Jump = new KGoto(after.Label);
            _block = skip;
            Emit(KAssume.Of(new KVar(t.Awaited)));
            skip.Jump = new KGoto(after.Label);
            _block = after;
        }

        private void Join(KCall st, Task t)
        {
            Emit(KCall.JoinOf(st));
            if (t.Forget != null)
            {
                foreach (var f in t.Forget)
                {
                    f();
                }
            }
        }

        private int _joins;

        /// <summary>Whether a task's variable is used in more than one place (each of which may await it).</summary>
        private bool AwaitedInPlaces(Task t)
        {
            var local = _tasks.FirstOrDefault(e => e.Value == t).Key;
            var member = t.At?.AncestorsAndSelf().FirstOrDefault(a => a is MemberDeclarationSyntax);
            return local == null || member == null ||
                   member.DescendantNodes().OfType<IdentifierNameSyntax>().Count(i => i.Identifier.ValueText == local.Name) > 1;
        }

        /// <summary>The tasks Task.WhenAll's arguments start, each as its own task.</summary>
        private readonly Dictionary<CaptureId, Task> _startedCaptures = new Dictionary<CaptureId, Task>();

        /// <summary>Is a task local given a task of the program's (a call of its own method) anywhere: one it started, not one it's given?</summary>
        private bool StartedByProgram(ILocalSymbol local) =>
            _decl.DescendantNodes().Any(n => (n is VariableDeclaratorSyntax v && SymbolEqualityComparer.Default.Equals(_model.GetDeclaredSymbol(v), local) ? v.Initializer?.Value
                                              : n is AssignmentExpressionSyntax a && SymbolEqualityComparer.Default.Equals(_model.GetSymbolInfo(a.Left).Symbol, local) ? a.Right : null) is ExpressionSyntax value &&
                                             value.DescendantNodesAndSelf().OfType<InvocationExpressionSyntax>().Any(i => _model.GetSymbolInfo(i).Symbol is IMethodSymbol im && im.DeclaringSyntaxReferences.Length > 0));

        /// <summary>Does the lambda assign a local or parameter declared outside it?</summary>
        private bool WritesOutside(AnonymousFunctionExpressionSyntax lambda)
        {
            foreach (var n in lambda.Body.DescendantNodesAndSelf())
            {
                ExpressionSyntax target = n switch
                {
                    AssignmentExpressionSyntax a => a.Left,
                    PrefixUnaryExpressionSyntax { RawKind: (int)Microsoft.CodeAnalysis.CSharp.SyntaxKind.PreIncrementExpression or (int)Microsoft.CodeAnalysis.CSharp.SyntaxKind.PreDecrementExpression } pu => pu.Operand,
                    PostfixUnaryExpressionSyntax { RawKind: (int)Microsoft.CodeAnalysis.CSharp.SyntaxKind.PostIncrementExpression or (int)Microsoft.CodeAnalysis.CSharp.SyntaxKind.PostDecrementExpression } po => po.Operand,
                    ArgumentSyntax { RefKindKeyword.RawKind: not 0 } ra => ra.Expression,
                    _ => null,
                };
                if (target != null && _model.GetSymbolInfo(target).Symbol is ISymbol s && (s is ILocalSymbol || s is IParameterSymbol) &&
                    !s.DeclaringSyntaxReferences.Any(r => lambda.Span.Contains(r.Span)))
                {
                    return true;
                }
            }
            return false;
        }

        /// <summary>
        /// Task.Run(lambda) where it is awaited with others (Task.WhenAll): of one call, that call, its precondition proved
        /// where it starts (in two phases, a callee of permissions); of any other lambda, code verified on its own, which
        /// may reach anything. What it may race on is what its code uses.
        /// </summary>
        private Task RunInline(IInvocationOperation run, AnonymousFunctionExpressionSyntax lambda)
        {
            var call = StartedCall(lambda);
            var effects = call != null ? EffectsOfCall(call, capturing: true) : EffectsOfDelegate(lambda);
            if (call == null && WritesOutside(lambda))
            {
                throw new NotTranslated("a Task.Run whose lambda writes this method's variables");
            }
            // (code of its own: Task.Run calls it with no arguments, so what it requires must hold here, CSV1029)
            if (call == null)
            {
                RunsWithNoArguments(run);
            }
            Task t;
            if (call != null)
            {
                t = StartInline(call);
            }
            else
            {
                _opaque = true;
                t = new Task
                {
                    At = run.Syntax,
                    Thread = true,
                    RunAt = run.Syntax,
                };
                if (run.Type is INamedTypeSymbol { Arity: 1 } rt && InSubset(rt.TypeArguments[0]))
                {
                    var u = Declare("t$" + _temps++, rt.TypeArguments[0]);
                    Emit(KHavoc.Of(u));
                    if (IsNullable(rt.TypeArguments[0]) && NotNullable(rt.TypeArguments[0]))
                    {
                        Emit(KAssume.Of(NotNull(new KVar(u))));
                    }
                    t.Result = u;
                }
            }
            t.Effects = effects;
            t.RunAt = run.Syntax;
            return t;
        }

        /// <summary>
        /// Task.Run(lambda) that this method doesn't await: it runs alongside the rest of the method, and after it; kept
        /// (stored, discarded), whoever has it awaits it; else it's never awaited (CSV1026).
        /// </summary>
        private void Detach(IInvocationOperation run, AnonymousFunctionExpressionSyntax lambda, bool kept)
        {
            var t = RunInline(run, lambda);
            foreach (var o in AllTasks().Where(x => x.Effects != null))
            {
                WarnIfMayRace(run.Syntax, t.Effects, o.Effects, new KVar(o.Awaited));
            }
            Detached(run.Syntax, t.Effects);
            t.Kept = kept;
            t.Awaited = Declare($"aw$d{_detached.Count}", _model.Compilation.GetSpecialType(SpecialType.System_Boolean));
            Emit(KAssign.Of(t.Awaited, KLit.False));
            _detached.Add(t);
        }

        private static bool IsTaskRun(IOperation op, out IInvocationOperation run, out AnonymousFunctionExpressionSyntax lambda)
        {
            run = Unconverted(op) as IInvocationOperation;
            lambda = run != null && run.TargetMethod.ContainingType?.ToDisplayString() == "System.Threading.Tasks.Task" && run.TargetMethod.Name == "Run" && run.Arguments.Length == 1
                ? LambdaSyntax(run.Arguments[0]) : null;
            return lambda != null;
        }

        /// <summary>
        /// A call of a task member (an interface's, or one returned as it is made) that isn't awaited at once: its precondition proved here; its code runs
        /// alongside from here on, so nothing of what it gives is known (not where its contract says something of it:
        /// not translated). The task itself: a reference, not null.
        /// </summary>
        private KExpr StartedTaskCall(IInvocationOperation call)
        {
            if (_contractOf?.Invoke(call.TargetMethod.OriginalDefinition) is Contract c && c.Ensures.Count > 0)
            {
                throw new NotTranslated("a task with a postcondition that isn't awaited at once: " + call.TargetMethod.Name);
            }
            _awaiting = true;
            try
            {
                Call(call);
            }
            finally
            {
                _awaiting = false;
            }
            var t = Declare("t$" + _temps++, call.Type);
            Emit(KHavoc.Of(t));
            Emit(KAssume.Of(NotNull(new KVar(t))));
            return new KVar(t);
        }

        /// <summary>Batches of tasks started here, by the local that holds them.</summary>
        private readonly Dictionary<ILocalSymbol, Task> _batches = new Dictionary<ILocalSymbol, Task>(SymbolEqualityComparer.Default);

        /// <summary>xs.Select(x => F(x)).ToArray() (or ToList), F's a task: the Select, its source, its lambda.</summary>
        private (IInvocationOperation, IOperation, AnonymousFunctionExpressionSyntax)? TaskBatch(IOperation value)
        {
            if (!(Unconverted(value) is IInvocationOperation to && IsEnumerableCall(to.TargetMethod) && to.TargetMethod.Name is "ToArray" or "ToList" && to.Arguments.Length == 1))
            {
                return null;
            }
            if (!(Unconverted(to.Arguments[0].Value) is IInvocationOperation sel && IsEnumerableCall(sel.TargetMethod) && sel.TargetMethod.Name == "Select" && sel.Arguments.Length == 2))
            {
                return null;
            }
            if (!(ElementOf(to.Type) is ITypeSymbol e && IsTaskLike(e)))
            {
                return null;
            }
            var lam = LambdaSyntax(sel.Arguments.First(a => a.Parameter.Ordinal == 1));
            return lam == null ? null : (sel, sel.Arguments.First(a => a.Parameter.Ordinal == 0).Value, lam);
        }

        /// <summary>
        /// A batch of tasks, each of the lambda's call on an element: they run alongside from here on (what they may race
        /// on is the lambda's code's, which is verified on its own), until Task.WhenAll of the local, the only use it may
        /// have. Nothing's known of how many there are, or what they give.
        /// </summary>
        private void StartBatch(ILocalSymbol local, IInvocationOperation select, IOperation source, AnonymousFunctionExpressionSyntax lambda)
        {
            if (_batches.ContainsKey(local) || _tasks.ContainsKey(local))
            {
                throw new NotTranslated("a batch of tasks assigned again");
            }
            foreach (var id in _decl.DescendantNodes().OfType<IdentifierNameSyntax>().Where(i => i.Identifier.Text == local.Name && SymbolEqualityComparer.Default.Equals(_model.GetSymbolInfo(i).Symbol, local)))
            {
                if (!(id.Parent is ArgumentSyntax { Parent.Parent: InvocationExpressionSyntax wa } && wa.Expression.ToString().EndsWith("WhenAll")) || id.Ancestors().Any(a => a is AnonymousFunctionExpressionSyntax))
                {
                    throw new NotTranslated("a batch of tasks used otherwise than by Task.WhenAll: " + local.Name);
                }
            }
            var src = Expr(Unconverted(source));
            Emit(KCheck.Of(NotNull(src), "CSV1013", source.Syntax, $"'{source.Syntax}' might be null: LINQ would throw ArgumentNullException"));
            Expr(select.Arguments.First(a => a.Parameter.Ordinal == 1).Value);
            var effects = EffectsOfDelegate(lambda);
            foreach (var o in AllTasks().Where(x => x.Effects != null))
            {
                WarnIfMayRace(select.Syntax, effects, o.Effects, new KVar(o.Awaited));
            }
            // (two of the batch run at once too)
            WarnIfMayRace(select.Syntax, effects, effects, KLit.False);
            _opaque = true;
            var t = new Task
            {
                At = select.Syntax,
                Thread = true,
                RunAt = select.Syntax,
                Effects = effects,
                Awaited = Declare($"aw$b{_batches.Count}", _model.Compilation.GetSpecialType(SpecialType.System_Boolean)),
            };
            Emit(KAssign.Of(t.Awaited, KLit.False));
            _batches[local] = t;
            _detached.Add(t);
        }

        /// <summary>Task.Run(lambda), of a lambda with a precondition: Task.Run calls it with no arguments, so its precondition must hold where it starts (CSV1029).</summary>
        private void RunsWithNoArguments(IInvocationOperation run)
        {
            var arg = run.Arguments[0];
            if (!(Unconverted(arg.Value) is IDelegateCreationOperation dc) || !(LambdaOf(dc.Target) is IAnonymousFunctionOperation af) ||
                !(_contractOf?.Invoke(af.Symbol) is Contract lc) || lc.OwnRequires.Count == 0 || !IsFunc(dc.Type))
            {
                return;
            }
            var d = Expr(arg.Value);
            var key = FuncKey(dc.Type);
            _p.AddDelegateKey(key);
            Emit(KCheck.Of(
                new KOp("$pre." + key, d),
                "CSV1029",
                arg.Syntax,
                "Task.Run calls this with no arguments, but its precondition might not hold here"));
        }

        private Task StartInline(IInvocationOperation call)
        {
            bool twoPhase = Permissions(call.TargetMethod);
            _awaiting = true;
            _phase = twoPhase ? 1 : 0;
            KExpr result;
            try
            {
                result = Call(call);
            }
            finally
            {
                _awaiting = false;
                _phase = 0;
            }
            return new Task
            {
                Method = call.TargetMethod,
                At = call.Syntax,
                Result = (result as KVar)?.Name,
                StartCall = twoPhase ? _block.Stmts.OfType<KCall>().Last() : null,
            };
        }

        private void StartCaptured(CaptureId id, IInvocationOperation call)
        {
            StartedUnderGate(call);
            bool twoPhase = Permissions(call.TargetMethod);
            _awaiting = true;
            _phase = twoPhase ? 1 : 0;
            KExpr result;
            try
            {
                result = Call(call);
            }
            finally
            {
                _awaiting = false;
                _phase = 0;
            }
            var task = new Task
            {
                Method = call.TargetMethod,
                At = call.Syntax,
                Result = (result as KVar)?.Name,
                StartCall = twoPhase ? _block.Stmts.OfType<KCall>().Last() : null,
                Awaited = Declare($"aw${_tasks.Count + _startedCaptures.Count}", _model.Compilation.GetSpecialType(SpecialType.System_Boolean)),
            };
            Emit(KAssign.Of(task.Awaited, KLit.False));
            _startedCaptures[id] = task;
        }

        private readonly Dictionary<ILocalSymbol, AnonymousFunctionExpressionSyntax> _threads = new Dictionary<ILocalSymbol, AnonymousFunctionExpressionSyntax>(SymbolEqualityComparer.Default);

        /// <summary>The one call a started lambda is, with values that don't change (proved where it starts); null for any other lambda.</summary>
        private IInvocationOperation StartedCall(AnonymousFunctionExpressionSyntax lambda)
        {
            var call = KernelTypes.Started?.CallOf(lambda);
            if (call == null)
            {
                // (code of its own, verified on its own: what it may change, anything; an async one's too, its task
                // unwrapped by Task.Run)
                return null;
            }
            return _model.GetOperation(call) as IInvocationOperation ?? throw new NotTranslated("a started call without its operation");
        }

        private void TasksAwaited(KBlock at)
        {
            // (a thread needn't be joined: nothing is lost if it isn't; a task, a Task.Run's too, must be awaited)
            foreach (var t in AllTasks().Where(t => !t.RealThread && !t.Kept))
            {
                at.AddStmt(KCheck.Of(
                    new KVar(t.Awaited),
                    "CSV1026",
                    t.RunAt ?? t.At,
                    notAssumedAfter: true,
                    message: $"the task of '{t.Method?.Name ?? "Run"}' might not be awaited on every path: a failure in it would be lost"));
            }
        }

        private int _keeps;

        /// <summary>The awaited flags of tasks started in loops: true at the method's entry.</summary>
        private readonly List<(string flag, int block, SyntaxNode at, string name)> _awaitedAtEntry = new List<(string, int, SyntaxNode, string)>();

        /// <summary>Between two statements, while a task started here may still be running: other code may change what the method doesn't hold.</summary>
        private void Alongside()
        {
            _p.Awaits = true;
            _p.CallsDelegates = true;
            var running = OrAny(AllTasks().Select(t => (KExpr)Not(new KVar(t.Awaited))));
            var k = new KAwait { When = running };
            if (!_opaque)
            {
                foreach (var l in Confined())
                {
                    k.AddKeep(Declare(Local(l), l.Type));
                }
            }
            Emit(k);
            // (a local a running task's code writes: what it is now isn't known, unless the task is done)
            foreach (var t in _tasks.Values.Where(t => t.Shared.Count > 0))
            {
                foreach (var l in t.Shared)
                {
                    var v = Declare(Local(l), l.Type);
                    var h = Declare("t$" + _temps++, l.Type);
                    Emit(KHavoc.Of(h));
                    Emit(KAssign.Of(v, Ite(new KVar(t.Awaited), new KVar(v), new KVar(h))));
                }
            }
        }

        /// <summary>t.Result: of a task that has finished (else it blocks, CSV1026).</summary>
        private KExpr ResultOf(Task task, SyntaxNode at)
        {
            Emit(KCheck.Of(
                new KVar(task.Awaited),
                "CSV1026",
                at,
                notAssumedAfter: true,
                message: $"the task of '{task.Method?.Name ?? "Run"}' might not have finished: reading Result blocks until it does, and that can deadlock (await it first)"));
            return task.Result == null ? throw new NotTranslated("the Result of a task of nothing") : new KVar(task.Result);
        }

        private List<ILocalSymbol> _confined;

        /// <summary>
        /// The locals that only ever hold objects the method made itself, used only in ways that can't hand them to other
        /// code: no code that runs at an await can reach their objects.
        /// </summary>
        private List<ILocalSymbol> Confined()
        {
            if (_confined != null)
            {
                return _confined;
            }
            _confined = new List<ILocalSymbol>();
            if (_decl == null)
            {
                return _confined;
            }
            var locals = _decl.DescendantNodes().OfType<VariableDeclaratorSyntax>().Select(d => _model.GetDeclaredSymbol(d) as ILocalSymbol).Where(l => l != null).ToList();
            foreach (var l in locals.Where(l => IsClass(l.Type) || IsArray(l.Type) || IsCollection(l.Type)))
            {
                bool ok = true;
                foreach (var d in l.DeclaringSyntaxReferences.Select(r => r.GetSyntax()).OfType<VariableDeclaratorSyntax>())
                {
                    if (d.Initializer != null && !Fresh(d.Initializer.Value))
                    {
                        ok = false;
                    }
                }
                foreach (var id in _decl.DescendantNodes().OfType<IdentifierNameSyntax>().Where(i => i.Identifier.Text == l.Name && SymbolEqualityComparer.Default.Equals(_model.GetSymbolInfo(i).Symbol, l)))
                {
                    if (id.Ancestors().Any(a => a is AnonymousFunctionExpressionSyntax || a is LocalFunctionStatementSyntax))
                    {
                        ok = false;
                        break;
                    }
                    switch (id.Parent)
                    {
                        case MemberAccessExpressionSyntax ma when ma.Expression == id && _model.GetSymbolInfo(ma.Name).Symbol is IFieldSymbol or IPropertySymbol: continue;
                        // (a collection's own member, of its stub, handed nothing that runs code or is another confined object)
                        case MemberAccessExpressionSyntax cm when cm.Expression == id && IsCollection(l.Type) && cm.Parent is InvocationExpressionSyntax ci &&
                                                                 _model.GetSymbolInfo(ci).Symbol is IMethodSymbol cms && SymbolEqualityComparer.Default.Equals(cms.ContainingType.OriginalDefinition, l.Type.OriginalDefinition) &&
                                                                 ci.ArgumentList.Arguments.All(a => _model.GetTypeInfo(a.Expression).Type is ITypeSymbol at && (Scalar(at) || IsString(at))): continue;
                        case ElementAccessExpressionSyntax ea when ea.Expression == id: continue;
                        case BinaryExpressionSyntax be when (be.IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.EqualsExpression) || be.IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.NotEqualsExpression)) &&
                                                          (be.Left.IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.NullLiteralExpression) || be.Right.IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.NullLiteralExpression)): continue;
                        case AssignmentExpressionSyntax asg when asg.Left == id && Fresh(asg.Right): continue;
                        case ArgumentSyntax arg when InSpec(arg): continue;
                        case ReturnStatementSyntax _: continue;
                        default:
                            ok = false;
                            break;
                    }
                    if (!ok)
                    {
                        break;
                    }
                }
                if (ok)
                {
                    _confined.Add(l);
                }
            }
            return _confined;
        }

        /// <summary>A new array, or a new object of a program class whose construction doesn't let it out (it calls nothing, and uses this only for its fields).</summary>
        private bool Fresh(ExpressionSyntax e)
        {
            if (e is ArrayCreationExpressionSyntax || e is ImplicitArrayCreationExpressionSyntax)
            {
                return true;
            }
            // (a new collection, empty or of a capacity)
            if (e is BaseObjectCreationExpressionSyntax nc && _model.GetTypeInfo(nc).Type is ITypeSymbol nt && IsCollection(nt) && nc.Initializer == null &&
                (nc.ArgumentList == null || nc.ArgumentList.Arguments.All(a => Scalar(_model.GetTypeInfo(a.Expression).Type))))
            {
                return true;
            }
            if (!(e is BaseObjectCreationExpressionSyntax oc) || !(_model.GetSymbolInfo(oc).Symbol is IMethodSymbol ctor) || !IsClass(ctor.ContainingType))
            {
                return false;
            }
            if (ctor.ContainingType.BaseType?.SpecialType != SpecialType.System_Object)
            {
                return false;
            }
            var code = ctor.DeclaringSyntaxReferences.Select(r => r.GetSyntax())
                .Concat(ctor.ContainingType.GetMembers().Where(m => !m.IsStatic).SelectMany(m => m.DeclaringSyntaxReferences).Select(r => r.GetSyntax()).OfType<VariableDeclaratorSyntax>());
            foreach (var n in code.SelectMany(c => c.DescendantNodesAndSelf()))
            {
                if (n is InvocationExpressionSyntax inv && !(inv.Expression.ToString() is "nameof") && !inv.Expression.ToString().StartsWith("Spec."))
                {
                    return false;
                }
                if (n is ThisExpressionSyntax t && !(t.Parent is MemberAccessExpressionSyntax))
                {
                    return false;
                }
            }
            return true;
        }
    }
}
