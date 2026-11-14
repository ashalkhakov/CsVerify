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
    /// <summary>
    /// Pass 1: a method's control-flow graph (Roslyn's lowering of C#) to a kernel procedure. Each block is a block, its
    /// operations kernel statements; what C# means is kept in typed nodes (arithmetic in its context, conversions,
    /// array reads and lengths, functions' calls in specifications) for Checks to make obligations of. Specifications
    /// are read whole from the operations the source has, and what the graph lowers their arguments to is left out:
    /// they never run. Throws <see cref="NotTranslated"/> at anything outside the subset.
    /// <para>
    /// This file: the pass's state, its entry points (Lower, Signature's helpers) and Run, which walks the graph. The rest,
    /// by construct: Modes (how the method is encoded, decided first), Contracts, Statements, Expressions, Specs,
    /// Patterns, Data (records, structs, tuples, nullable values), Floats, Calls, Refs, Delegates, Loops, ForEach,
    /// Exceptions, Tasks, Locks, Atomics, Ownership, MemLive (Mem's views), Spans, Ifc (collection interfaces), Linq,
    /// Ef and EfTracker, Races, Causes (the library report).
    /// </para>
    /// </summary>
    internal sealed partial class Lowering
    {
        private readonly IMethodSymbol _m;
        private readonly Contract _contract;
        private readonly SyntaxNode _decl;
        private readonly SemanticModel _model;
        private readonly Func<IMethodSymbol, bool> _isProcedure, _isFunction;
        private readonly Func<string, string> _literal;
        private readonly Func<IMethodSymbol, Contract> _contractOf;
        private readonly KProcedure _p;
        private KBlock _block;
        private int _temps;
        private bool _contractOnly;

        private Lowering(IMethodSymbol m, Contract contract, SyntaxNode decl, SemanticModel model, MethodResult result,
                         Func<IMethodSymbol, bool> isProcedure, Func<IMethodSymbol, bool> isFunction, Func<string, string> literal, Func<IMethodSymbol, Contract> contractOf)
        {
            _m = m; _contract = contract; _decl = decl; _model = model; _isProcedure = isProcedure; _isFunction = isFunction;
            _literal = literal; _contractOf = contractOf;
            _p = new KProcedure
            {
                Method = IsCollection(m.ContainingType) ? m : m.OriginalDefinition,
                Contract = contract,
                Result = result,
                Name = Name(m),
                Params = m.Parameters.ToList(),
                Ghost = SpecSymbols.IsGhostFunction(m) || contract.IsLemma,
                HasThis = !StaticContext(m) && !(IsCollection(m.ContainingType) && m.MethodKind == MethodKind.Constructor) && !(IsStruct(m.ContainingType) && m.MethodKind == MethodKind.Constructor),
                IsCtor = m.MethodKind == MethodKind.Constructor && !IsCollection(m.ContainingType) && !IsStruct(m.ContainingType),
                StructThis = m.MethodKind == MethodKind.Constructor && !m.IsStatic && IsStruct(m.ContainingType) || WritesStructThis(m),
                StructRefThis = WritesStructThis(m),
                ListCtor = m.MethodKind == MethodKind.Constructor && IsCollection(m.ContainingType),
                ThisIsView = !m.IsStatic && SpecSymbols.IsOwned(m.ContainingType) && (m.MethodKind == MethodKind.Constructor || !contract.IsPure),
            };
            // (a constructor knows its object's fields are their defaults: their maps are declared)
            if (_p.IsCtor)
            {
                foreach (var f in InstanceFields(m.ContainingType))
                {
                    _p.Fields.Add(f);
                }
            }
            // (of its contract; Run decides again with its body)
            DecideModes(null);
        }

        public static KProcedure Lower(IMethodSymbol m, Contract contract, SyntaxNode decl, SemanticModel model, MethodResult result,
                                       Func<IMethodSymbol, bool> isProcedure, Func<IMethodSymbol, bool> isFunction, Func<string, string> literal = null, Func<IMethodSymbol, Contract> contractOf = null,
                                       bool contractOnly = false, ControlFlowGraph graph = null) =>
            new Lowering(m, contract, decl, model, result, isProcedure, isFunction, literal, contractOf)
            {
                _contractOnly = contractOnly,
                _graph = graph,
            }.Run();

        /// <summary>A lambda's or a local function's flow graph (its enclosing method's gives it).</summary>
        private ControlFlowGraph _graph;

        /// <summary>
        /// The enclosing methods' parameters a lambda or a local function captures: locals of it, of any value (it may
        /// run at any time).
        /// </summary>
        private readonly HashSet<IParameterSymbol> _capturedParams = new HashSet<IParameterSymbol>(SymbolEqualityComparer.Default);

        /// <summary>
        /// A library member (not a collection's) whose stub contract the library gives, which writes nothing and runs
        /// none of the program's code (no Spec.Modifies, nothing CsVerify's effects analysis says it may write): a
        /// procedure of its contract, which its calls call. Of the subset's types, not generic.
        /// </summary>
        /// <summary>
        /// The values of what a local function captures, as they are where it's called: this method's variables, or
        /// what this lambda or local function captures in turn.
        /// </summary>
        private List<KExpr> LocalFunctionCaptures(IMethodSymbol lf)
        {
            var sig = Signature(lf, _contractOf(lf), _isFunction, _literal, _contractOf);
            var values = new List<KExpr>();
            foreach (var sym in sig.CapturedSymbols)
            {
                bool own = SymbolEqualityComparer.Default.Equals(sym.ContainingSymbol, _m);
                if (!own && !_capturedIn.ContainsKey(sym))
                {
                    throw new NotTranslated("a call of a local function that captures what this doesn't");
                }
                if (sym is IParameterSymbol p)
                {
                    values.Add(new KVar(_assigned.TryGetValue(p, out var pv) ? pv : Local(p)));
                }
                else
                {
                    values.Add(new KVar(Declare(Local(sym), ((ILocalSymbol)sym).Type)));
                }
            }
            return values;
        }

        /// <summary>
        /// A lambda's or a local function's captured variables, of the methods it is in: inputs of its procedure (its
        /// contract may name them), each some value of its type (it may run at any time).
        /// </summary>
        private void Captures(ControlFlowGraph cfg)
        {
            var decl = _decl ?? _m.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax();
            var model = _model ?? (decl == null ? null : KernelTypes.Compilation?.GetSemanticModel(decl.SyntaxTree));
            var ops = cfg.Blocks.SelectMany(b => b.Operations.Concat(b.BranchValue == null ? new IOperation[0] : new[] { b.BranchValue })).SelectMany(o => o.DescendantsAndSelf()).ToList();
            bool Encloses(ISymbol owner)
            {
                for (var up = _m.ContainingSymbol; up != null; up = up.ContainingSymbol)
                {
                    if (SymbolEqualityComparer.Default.Equals(up, owner))
                    {
                        return true;
                    }
                }
                return false;
            }
            // (and what its contract names)
            var named = _contract.Requires.Concat(_contract.Ensures.Select(e => e.Expr)).Concat(new[] { _contract.Reads, _contract.Modifies }).Where(x => x != null).SelectMany(x => x.DescendantsAndSelf());
            var syms = ops.Concat(named).Select(o => o is IParameterReferenceOperation pr ? (ISymbol)pr.Parameter : o is ILocalReferenceOperation lr ? lr.Local : null)
                .Where(x => x != null && Encloses(x.ContainingSymbol)).Distinct(SymbolEqualityComparer.Default).ToList();
            foreach (var sym in syms)
            {
                var type = sym is IParameterSymbol ps ? ps.Type : ((ILocalSymbol)sym).Type;
                if (!InSubset(type) || sym is ILocalSymbol { RefKind: not RefKind.None } || sym is IParameterSymbol { RefKind: not RefKind.None })
                {
                    continue;
                }
                var input = Local(sym) + "$c";
                _capturedIn[sym] = input;
                if (sym is IParameterSymbol cp)
                {
                    _capturedParams.Add(cp);
                }
                if (!NeverWrittenIn(decl, sym))
                {
                    _capturedWritten.Add(sym);
                }
                // (one with one value all along, a foreach's or one assigned only where it's declared, that the
                // compiler's flow analysis has as not null: not null)
                bool notNull = sym is ILocalSymbol && IsNullable(type) && model != null && NeverWritten(sym) &&
                               ops.OfType<ILocalReferenceOperation>().Any(r => SymbolEqualityComparer.Default.Equals(r.Local, sym) && r.Syntax.SyntaxTree == model.SyntaxTree &&
                                                                              model.GetTypeInfo(r.Syntax).Nullability.FlowState == NullableFlowState.NotNull);
                _p.Captured.Add((input, type, notNull));
                _p.CapturedSymbols.Add(sym);
            }
        }

        /// <summary>The captured variables: each one's input.</summary>
        private readonly Dictionary<ISymbol, string> _capturedIn = new Dictionary<ISymbol, string>(SymbolEqualityComparer.Default);

        /// <summary>
        /// Those the lambda writes: a precondition reads one's value at entry (its input), a postcondition its value at
        /// each return, as for a parameter the body assigns (callers don't assume it).
        /// </summary>
        private readonly HashSet<ISymbol> _capturedWritten = new HashSet<ISymbol>(SymbolEqualityComparer.Default);

        private KExpr CapturedInSpec(ISymbol s) => new KVar(_capturedIn[s]);

        private KProcedure Run()
        {
            if (IsNested(_m) && _graph != null)
            {
                Captures(_graph);
            }
            // (a data type's member: this is one of its cases, which the program declares)
            if (_p.HasThis && IsData(_m.ContainingType))
            {
                Data(_m.ContainingType);
            }
            if (SpecSymbols.IsPredicate(_m))
            {
                return Predicate();
            }
            // (a data type's constructor that does nothing: a procedure of no statements, and no object)
            if (BoogieTranslator.EmptyDataConstructor(_m))
            {
                _p.Blocks.Add(new KBlock
                {
                    Label = "b0",
                    Ordinal = 0,
                    Jump = new KReturn { At = _decl },
                });
                return _p;
            }
            // (Dafny's dynamic frames: what it may write. An [Owned] class's objects are framed by their views instead)
            if (_contract.Modifies != null)
            {
                // (an [Owned] class's objects change through their views, not by Spec.Modifies: CSV1017)
                if (SpecSymbols.IsOwned(_m.ContainingType))
                {
                    _ownedModifies = true;
                }
                _p.Frame = Spec(_contract.Modifies, null);
                LentRoots(_contract.Modifies);
            }
            ContractOf(this, _contract);
            LibraryCalls();
            if (KernelTypes.Trees && !_m.IsStatic && SpecSymbols.IsOwned(_m.ContainingType) && _contract.Reads == null && (_contract.IsPure || _isFunction(_m)))
            {
                _p.TreeReads = true;
            }
            // (an abstract member: its contract alone)
            if (_m.IsAbstract || _m.MethodKind == MethodKind.DelegateInvoke)
            {
                _p.Abstract = true;
                return _p;
            }
            // (a body that doesn't translate: its contract alone, which its callers call)
            if (_contractOnly)
            {
                _p.Abstract = true;
                _p.Opaque = true;
                return _p;
            }
            // (a collection's member: its stub's contract alone; what it may change is its own collection's models, a new one's for a constructor)
            if (IsCollection(_m.ContainingType))
            {
                if (!_contract.IsStub)
                {
                    throw new NotTranslated("a collection's member without a stub contract: " + _m.Name);
                }
                _p.Abstract = true;
                foreach (var model in ModelsOf((INamedTypeSymbol)_m.ContainingType))
                {
                    _p.Models[model.Name] = model;
                    if (_contract.Modifies != null)
                    {
                        _p.Modifies.Add(model.Name);
                        _p.AnyWrites.Add(model.Name);
                    }
                }
                if (_p.ListCtor)
                {
                    _p.Modifies.Add("$Alloc");
                    _p.AnyWrites.Add("$Alloc");
                }
                return _p;
            }
            // (a library member's stub, that writes nothing: its contract alone)
            // (what it may change is what CsVerify's effects analysis says: the arrays it's handed, anything where it runs the
            // program's code, its delegates; as a body not translated is framed, Opaque)
            if (_decl == null && LibraryStub(_m))
            {
                _p.Abstract = true;
                _p.Opaque = true;
                return _p;
            }
            EfNotYet();
            // (an iterator's postconditions would be of the enumerable, made before its body runs)
            if (_m.IsIterator && _contract.Ensures.Count > 0)
            {
                throw new NotTranslated("an iterator's postcondition");
            }
            var cfg = _graph ?? _model.GetOperation(_decl) switch
            {
                IMethodBodyOperation body => ControlFlowGraph.Create(body),
                IConstructorBodyOperation body => ControlFlowGraph.Create(body),
                // (an accessor, an expression-bodied property's getter)
                IBlockOperation block => ControlFlowGraph.Create(block),
                _ => throw new NotTranslated("no body"),
            };
            DecideModes(cfg);
            // (foreach over an array or a string: a loop over an index, its enumerator's try/finally gone)
            ForEachLoops(cfg);
            // (try and catch: each catch of an exception type the kernel has, with its filter or not; finally)
            foreach (var r in cfg.Root.NestedRegions.SelectMany(AllRegions).Concat(cfg.Root.NestedRegions))
            {
                if (_erased.Contains(r) || _erased.Contains(r.EnclosingRegion))
                {
                    continue;
                }
                else if (!(r.Kind is ControlFlowRegionKind.LocalLifetime or ControlFlowRegionKind.TryAndCatch or ControlFlowRegionKind.Try or ControlFlowRegionKind.TryAndFinally or ControlFlowRegionKind.Finally or ControlFlowRegionKind.Filter ||
                      r.Kind is ControlFlowRegionKind.Catch or ControlFlowRegionKind.FilterAndHandler && (r.ExceptionType == null || IsException(r.ExceptionType))))
                {
                    throw new NotTranslated(r.Kind == ControlFlowRegionKind.Catch ? "a catch of " + r.ExceptionType : r.Kind.ToString());
                }
            }
            _cfg = cfg;
            // (a function's definition is its body: not one an override may answer, which is of its contract alone)
            if (_isFunction(_m) && _contract.PureBody != null && !Engine.IsOverridable(_m))
            {
                _p.FunctionBody = Spec(_contract.PureBody, null);
            }
            else if (_isFunction(_m) && _contract.PureStatements != null && !Engine.IsOverridable(_m))
            {
                _p.FunctionBody = PureStatements(_contract.PureStatements, 0);
            }
            var heads = LoopHeads(cfg);
            foreach (var h in heads)
            {
                var hb = cfg.Blocks[h];
                var loop = (hb.BranchValue?.Syntax ?? hb.Operations.FirstOrDefault()?.Syntax)?.AncestorsAndSelf()
                    .FirstOrDefault(n => n is ForStatementSyntax || n is WhileStatementSyntax || n is DoStatementSyntax || n is CommonForEachStatementSyntax);
                if (loop != null)
                {
                    _p.LoopSyntax[h] = loop;
                }
            }
            foreach (var h in heads)
            {
                _p.LoopBodies[h] = cfg.Blocks.Where(x => new[] { x.FallThroughSuccessor, x.ConditionalSuccessor }.Any(s => s?.Destination?.Ordinal == h) && x.Ordinal >= h).Max(x => x.Ordinal);
            }
            // (a cycle with no single entry, a goto into a loop: not supported, CSV1901)
            foreach (var (h, last) in _p.LoopBodies)
            {
                foreach (var x in cfg.Blocks.Where(x => x.Ordinal < h))
                {
                    foreach (var d in new[] { x.FallThroughSuccessor, x.ConditionalSuccessor }.Select(s => s?.Destination).Where(d => d != null && d.Ordinal > h && d.Ordinal <= last))
                    {
                        _secondEntries.Add(d.Ordinal);
                    }
                }
            }
            // (a parameter the body assigns is a local of it, which starts as the parameter: Boogie's parameters are
            // constants; the contract was read of the parameter already, and a postcondition is checked of the local)
            // (a parameter of the enclosing method's this lambda writes: a local of its own, from its input)
            foreach (var ap in AssignedParameters(cfg))
            {
                var v = Declare(_assigned[ap] = Local(ap) + "$v", ap.Type);
                if (!_capturedParams.Contains(ap))
                {
                    _p.AssignedParams[Local(ap)] = v;
                }
            }
            // (a captured variable this lambda writes: at a return, its value then)
            foreach (var cw in _capturedWritten.Where(_capturedIn.ContainsKey))
            {
                _p.AssignedParams[_capturedIn[cw]] = cw is IParameterSymbol cwp && _assigned.TryGetValue(cwp, out var cwv) ? cwv : Declare(Local(cw), ((ILocalSymbol)cw).Type);
            }
            // (what it captures: a variable of it, which starts as what came in)
            foreach (var (sym, input) in _capturedIn)
            {
                if (sym is IParameterSymbol cp)
                {
                    _assigned[cp] = Declare(input + "$v", cp.Type);
                }
                else
                {
                    Declare(Local(sym), ((ILocalSymbol)sym).Type);
                }
            }
            ReadLoopSpecs(cfg, heads);
            LoopFacts(heads);
            ForEachInvariants();
            if (_p.IsCtor)
            {
                Initializers();
            }
            // (a view that comes in says what its cells hold)
            else if (_m.Parameters.Any(x => IsMemView(x.Type) && x.RefKind != RefKind.Out))
            {
                _block = new KBlock
                {
                    Label = "mem",
                    Ordinal = -1,
                    Jump = new KGoto("b0"),
                };
                _p.Blocks.Add(_block);
                foreach (var x in _m.Parameters.Where(x => IsMemView(x.Type) && x.RefKind != RefKind.Out))
                {
                    Emit(new KAssume { Cond = MemTie(new KVar(Local(x)), x.Type) });
                }
            }
            foreach (var b in cfg.Blocks)
            {
                _block = new KBlock
                {
                    Label = $"b{b.Ordinal}",
                    Ordinal = b.Ordinal,
                };
                _p.Blocks.Add(_block);
                _cfgBlock = b;
                // (its data values are valid: their invariants hold)
                if (b.Ordinal == 0)
                {
                    foreach (var (param, local) in _assigned)
                    {
                        Emit(new KAssign
                        {
                            Var = local,
                            Value = new KVar(_capturedIn.TryGetValue(param, out var cin) ? cin : Local(param)),
                        });
                    }
                    foreach (var (sym, input) in _capturedIn.Where(x => x.Key is ILocalSymbol))
                    {
                        Emit(new KAssign
                        {
                            Var = Local(sym),
                            Value = new KVar(input),
                        });
                    }
                    if (_unshared != null)
                    {
                        Emit(new KAssign
                        {
                            Var = _unshared,
                            Value = new KOp("lambda", new KLit("r$: Ref"), KLit.False),
                        });
                    }
                    TrackerEntry();
                    MemLiveEntry();
                    // (a struct's constructor: its value begins as the default)
                    if (_p.StructThis && !_p.StructRefThis)
                    {
                        Emit(new KAssign
                        {
                            Var = "this",
                            Value = StructDefault(_m.ContainingType),
                        });
                    }
                    // (an iterator's body runs at the first MoveNext, after the call: the state may have changed since; what
                    // the call gave, the enumerable C# makes, isn't null)
                    if (_m.IsIterator)
                    {
                        CallersRun();
                        Emit(new KHavoc { Var = "result" });
                        Emit(new KAssume { Cond = NotNull(new KVar("result")) });
                    }
                    // (an [Atomic] field's step: a step after a step is a step, so what other threads do between two reads is one; CSV1030)
                    if (KernelTypes.SteppedBy?.Invoke(_m)?.FirstOrDefault() is IFieldSymbol stepped && _m.IsStatic && _m.Parameters.Length == 2 && _isFunction(_m))
                    {
                        var ft = stepped.Type;
                        KExpr S(string x, string y) => new KFnCall
                        {
                            Callee = _m.OriginalDefinition,
                            Args = new KExpr[] { new KVar(x), new KVar(y) },
                            At = _decl,
                        };
                        KExpr R(string x) => IsIntegral(ft) ? InRange(new KVar(x), ft) : KLit.True;
                        KExpr body = new KOp("==>", AndAlso(S("q$a", "q$b"), S("q$b", "q$c")), S("q$a", "q$c"));
                        foreach (var v in new[] { "q$c", "q$b", "q$a" })
                        {
                            body = KQuant.ForAll(v, TypeOf(ft), new KOp("==>", R(v), body));
                        }
                        Emit(new KCheck
                        {
                            Cond = body,
                            Id = "CSV1030",
                            At = _decl,
                            NotAssumedAfter = true,
                            Message = $"step '{_m.Name}' of [Atomic] '{stepped.Name}' might not be transitive: two steps of other threads in a row must make one",
                        });
                    }
                    if (_ownedModifies)
                    {
                        Emit(new KCheck
                        {
                            Cond = KLit.False,
                            Id = "CSV1017",
                            At = _decl,
                            NotAssumedAfter = true,
                            Message = $"{_m.ContainingType.Name} is [Owned]: its objects are changed through their views, not by Spec.Modifies",
                        });
                    }
                    foreach (var cl in Confined())
                    {
                        Emit(new KAssign
                        {
                            Var = Declare(Local(cl), cl.Type),
                            Value = KLit.Null,
                        });
                    }
                    if (_p.HasThis && HasInvariants(_m.ContainingType))
                    {
                        AssumeValid(new KVar("this"), _m.ContainingType);
                    }
                    foreach (var dp in _m.Parameters.Where(x => x.RefKind != RefKind.Out && HasInvariants(x.Type)))
                    {
                        AssumeValid(new KVar(Local(dp)), dp.Type);
                    }
                }
                // (the delegates it takes to be steady are: its callers prove it)
                if (b.Ordinal == 0)
                {
                    foreach (var sp in SteadyParams(_m).Where(x => IsFunc(x.Type)))
                    {
                        _p.DelegateKeys.Add(FuncKey(sp.Type));
                        Emit(new KAssume { Cond = new KOp("$steady", new KVar(Local(_m.Parameters[sp.Ordinal]))) });
                    }
                }
                if (b.Ordinal == 0)
                {
                    EnclosingFacts();
                }
                if (b.Kind == BasicBlockKind.Exit)
                {
                    _block.Jump = new KStop();
                    continue;
                }
                // (an erased finally: nothing goes there)
                if (b.EnclosingRegion.Kind == ControlFlowRegionKind.Finally && _erased.Contains(b.EnclosingRegion.EnclosingRegion))
                {
                    _block.Jump = new KStop();
                    continue;
                }
                // (at a loop's head, every atomic field went by steps since entry)
                if (heads.Contains(b.Ordinal) && _p.Fields.Any(Atomics.IsAtomic))
                {
                    Emit(new KAtomicSteps());
                }
                // (a proof's loop must be shown to end: CSV1011 without Spec.Decreases)
                if (heads.Contains(b.Ordinal) && (_p.Ghost || _contract.IsPure || _contract.IsLemma) && !_p.Measures.ContainsKey(b.Ordinal) && !_forEachAt.ContainsKey(b.Ordinal))
                {
                    Emit(new KCheck
                    {
                        Cond = KLit.False,
                        Id = "CSV1011",
                        At = _p.LoopSyntax.TryGetValue(b.Ordinal, out var ls0) ? ls0 : b.Operations.FirstOrDefault()?.Syntax ?? b.BranchValue?.Syntax ?? _decl,
                        NotAssumedAfter = true,
                        Message = "a loop in a lemma or [Pure] function needs Spec.Decreases",
                    });
                }
                if (_secondEntries.Contains(b.Ordinal))
                {
                    Emit(new KCheck
                    {
                        Cond = KLit.False,
                        Id = "CSV1901",
                        At = b.Operations.FirstOrDefault()?.Syntax ?? b.BranchValue?.Syntax ?? _decl,
                        Message = "a cycle with no single entry (a goto into a loop) is not supported",
                    });
                }
                foreach (var op in b.Operations)
                {
                    // (a tracked database query's facts, guarded where it is read: Lowering.Ef's _known, for its statement)
                    _known = null;
                    Statement(op);
                    // (while a task it started runs alongside, what the method doesn't hold is forgotten from each statement to the next)
                    if (AllTasks().Any() && !InSpec(op.Syntax))
                    {
                        Alongside();
                    }
                }
                Branch(b);
            }
            // (the confined locals, for the loops' frames: none once code of its own was started, which may reach anything)
            if (!_opaque)
            {
                _p.Confined = Confined().Select(l => Declare(Local(l), l.Type)).ToList();
            }
            // (a loop fact's value on the loop's entry, taken on each way in)
            foreach (var (h, var, value) in _entryValues)
            {
                foreach (var into in _p.Blocks.Where(x => x.Ordinal < h && x.Jump is KGoto g && g.Targets.Contains($"b{h}")))
                {
                    into.Stmts.Add(new KSpecStmt
                    {
                        Spec = Eq(new KVar(var), value),
                        Assume = true,
                        Free = true,
                        At = _decl,
                        ArgumentAt = _decl,
                    });
                }
            }
            // (no task started in a loop is running at the method's entry)
            // (each loop it's started in: the one of the last round was awaited on every way back, so at the head none is running)
            foreach (var (aw, block, awAt, awName) in _awaitedAtEntry)
            {
                _p.Blocks[0].Stmts.Insert(0, new KAssign
                {
                    Var = aw,
                    Value = KLit.True,
                });
                foreach (var (h, last) in _p.LoopBodies.Where(lb => lb.Key <= block && block <= lb.Value))
                {
                    _p.Blocks.FirstOrDefault(x => x.Label == $"b{h}")?.Stmts.Insert(0, new KAssume { Cond = new KVar(aw) });
                    foreach (var back in _p.Blocks.Where(x => x.Ordinal >= h && x.Ordinal <= last && x.Jump is KGoto g && g.Targets.Contains($"b{h}")))
                    {
                        back.Stmts.Add(new KCheck
                        {
                            Cond = new KVar(aw),
                            Id = "CSV1026",
                            At = awAt,
                            NotAssumedAfter = true,
                            Message = $"the task of '{awName}' might not be awaited on every path: a failure in it would be lost",
                        });
                    }
                }
            }
            if (_exitUsed)
            {
                _p.Blocks.Add(new KBlock
                {
                    Label = "x$exit",
                    Ordinal = cfg.Blocks.Length,
                    Stmts = { new KThrowExit() },
                    Jump = new KStop(),
                });
            }
            FinallyEnds();
            LoopCauses();
            return _p;
        }

        /// <summary>
        /// A Spec statement's argument as written: the control-flow graph lowers &amp;&amp; and ?: in it into blocks, but a
        /// specification is one formula.
        /// </summary>
        private IOperation SpecArgument(IInvocationOperation inv) =>
            (_model.GetOperation(inv.Syntax) as IInvocationOperation)?.Arguments[0].Value ?? throw new NotTranslated("a specification without its operation");

        private static IInvocationOperation SpecCall(IOperation op, string name) =>
            (op is IExpressionStatementOperation es ? es.Operation : op) is IInvocationOperation inv &&
            SpecSymbols.IsSpecClass(inv.TargetMethod.ContainingType) && inv.TargetMethod.Name == name ? inv : null;

        /// <summary>
        /// Is this syntax inside a Spec statement's argument? What the graph lowers it to is left out (a specification
        /// argument never runs), and each branch of it is a choice of either way, which meet again at the Spec call.
        /// </summary>
        private bool InSpec(SyntaxNode at) =>
            at != null && at.AncestorsAndSelf().OfType<ArgumentSyntax>().Any(arg => arg.Parent?.Parent is InvocationExpressionSyntax call &&
                _model.GetSymbolInfo(call).Symbol is IMethodSymbol m && SpecSymbols.IsSpecClass(m.ContainingType));

        // ------------------------------------------------------------------ statements

        private void Emit(KStmt s)
        {
            _block.Stmts.Add(s);
            Track(s);
        }

        private string Declare(string name, ITypeSymbol type)
        {
            if (!_p.Locals.Any(l => l.Name == name))
            {
                _p.Locals.Add(new KLocal
                {
                    Name = name,
                    Type = type,
                });
            }
            return name;
        }

        private static IOperation Unconverted(IOperation op)
        {
            while (op is IConversionOperation c && c.IsImplicit)
            {
                op = c.Operand;
            }
            return op;
        }
    }
}
