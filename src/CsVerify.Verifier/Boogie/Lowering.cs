using System;
using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.FlowAnalysis;
using Microsoft.CodeAnalysis.Operations;
using static CsVerify.Verifier.Boogie.KernelTypes;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>
    /// Pass 1: a method's control-flow graph (Roslyn's lowering of C#) to a kernel procedure. Each block is a block, its
    /// operations kernel statements; what C# means is kept in typed nodes (arithmetic in its context, conversions,
    /// array reads and lengths, functions' calls in specifications) for Checks to make obligations of. Specifications
    /// are read whole from the operations the source has, and what the graph lowers their arguments to is left out:
    /// they never run. Throws <see cref="NotTranslated"/> at anything outside the subset.
    /// </summary>
    internal sealed class Lowering
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

        private Lowering(IMethodSymbol m, Contract contract, SyntaxNode decl, SemanticModel model, MethodResult result,
                         Func<IMethodSymbol, bool> isProcedure, Func<IMethodSymbol, bool> isFunction, Func<string, string> literal, Func<IMethodSymbol, Contract> contractOf)
        {
            _m = m; _contract = contract; _decl = decl; _model = model; _isProcedure = isProcedure; _isFunction = isFunction;
            _literal = literal; _contractOf = contractOf;
            _p = new KProcedure
            {
                Method = IsCollection(m.ContainingType) ? m : m.OriginalDefinition, Contract = contract, Result = result, Name = Name(m), Params = m.Parameters.ToList(),
                Ghost = SpecSymbols.IsGhostFunction(m) || contract.IsLemma,
                HasThis = !m.IsStatic && !(IsCollection(m.ContainingType) && m.MethodKind == MethodKind.Constructor),
                IsCtor = m.MethodKind == MethodKind.Constructor && !IsCollection(m.ContainingType),
                ListCtor = m.MethodKind == MethodKind.Constructor && IsCollection(m.ContainingType),
                ThisIsView = !m.IsStatic && SpecSymbols.IsOwned(m.ContainingType) && (m.MethodKind == MethodKind.Constructor || !contract.IsPure),
            };
            _p.UsesPerm = _p.ThisIsView || m.Parameters.Any(x => IsView(x.Type));
        }

        public static KProcedure Lower(IMethodSymbol m, Contract contract, SyntaxNode decl, SemanticModel model, MethodResult result,
                                       Func<IMethodSymbol, bool> isProcedure, Func<IMethodSymbol, bool> isFunction, Func<string, string> literal = null, Func<IMethodSymbol, Contract> contractOf = null) =>
            new Lowering(m, contract, decl, model, result, isProcedure, isFunction, literal, contractOf).Run();

        /// <summary>
        /// A [Pure] member of string whose stub contract the library gives (its parameters and result in the subset): a
        /// function of its arguments, which its contract describes.
        /// </summary>
        private bool IsStub(IMethodSymbol m) =>
            IsString(m.ContainingType) && _contractOf?.Invoke(m) is Contract c && c.IsStub && c.IsPure && !m.ReturnsVoid && InSubset(m.ReturnType) &&
            m.Parameters.All(x => x.RefKind == RefKind.None && InSubset(x.Type)) && c.Stub.Parameters.All(x => x.RefKind == RefKind.None && InSubset(x.Type));

        /// <summary>
        /// A data type's invariant's body, of the value "this" (its own fields only: an invariant that calls anything, or
        /// reads anything but its fields, isn't translated, as CsVerify's engine reports one that reads mutable state).
        /// </summary>
        public static KExpr InvariantBody(IMethodSymbol inv, Func<IMethodSymbol, bool> isFunction, Func<string, string> literal, Func<IMethodSymbol, Contract> contractOf)
        {
            var c = contractOf(inv);
            if (c.PureBody == null) throw new NotTranslated("an invariant without an expression body: " + inv.Name);
            if (c.PureBody.DescendantsAndSelf().Any(o => o is IInvocationOperation || o is IFieldReferenceOperation ||
                                                       o is IPropertyReferenceOperation pr && !(pr.Instance != null && IsData(pr.Instance.Type) && DataTypes.IsPositional(pr.Property.OriginalDefinition))))
                throw new NotTranslated("an invariant that reads more than its record's fields: " + inv.Name);
            var l = new Lowering(inv, c, null, c.Model, null, _ => false, isFunction, literal, contractOf);
            return l.Spec(c.PureBody, null);
        }

        /// <summary>
        /// A data case's field that its base record has: the argument its record header gives the base's primary
        /// constructor, over the case's own constructor parameters (Ind(Fact Prev) : Fact(Prev.N + 1, ...)).
        /// </summary>
        public static KExpr BaseArgument(INamedTypeSymbol c, IPropertySymbol prop, Func<IMethodSymbol, bool> isFunction, Func<string, string> literal, Func<IMethodSymbol, Contract> contractOf)
        {
            var def = DataTypes.Def(c);
            var decl = def.DeclaringSyntaxReferences.Select(r => r.GetSyntax()).OfType<RecordDeclarationSyntax>().FirstOrDefault();
            var baseType = decl?.BaseList?.Types.OfType<PrimaryConstructorBaseTypeSyntax>().FirstOrDefault() ?? throw new NotTranslated("a base field without its argument: " + prop.Name);
            var ctor = DataTypes.PrimaryConstructor(def);
            var model = KernelTypes.Compilation.GetSemanticModel(decl.SyntaxTree);
            var call = model.GetOperation(baseType)?.DescendantsAndSelf().OfType<IInvocationOperation>().FirstOrDefault(i => i.TargetMethod.MethodKind == MethodKind.Constructor)
                       ?? throw new NotTranslated("a base constructor call not found: " + c.Name);
            var arg = call.Arguments.FirstOrDefault(a => a.Parameter?.Name == prop.Name) ?? throw new NotTranslated("a base field not given by name: " + prop.Name);
            var l = new Lowering(ctor, contractOf(ctor), decl, model, null, _ => false, isFunction, literal, contractOf);
            return l.Spec(arg.Value, null);
        }

        /// <summary>A callee's contract alone (its requires and its measure, over its parameters): what a call of it is checked against.</summary>
        public static KProcedure Signature(IMethodSymbol m, Contract contract, Func<IMethodSymbol, bool> isFunction, Func<string, string> literal = null, Func<IMethodSymbol, Contract> contractOf = null)
        {
            var l = new Lowering(m, contract, null, null, null, _ => false, isFunction, literal, contractOf);
            // (the permissions its postconditions give back, and a predicate's body, for folding and unfolding it)
            ContractOf(l, contract);
            if (contract.Modifies != null) l._p.Frame = l.Spec(contract.Modifies, null);
            if ((SpecSymbols.IsPredicate(m) || isFunction(m) && !Engine.IsOverridable(m)) && contract.PureBody != null) l._p.FunctionBody = l.Spec(contract.PureBody, null);
            return l._p;
        }

        /// <summary>
        /// The contract: its requires, its ensures (an inherited one where its precondition was weakened: promised where the
        /// base's held on entry), its measure; an override's own precondition and each base's, and the bases' frames.
        /// </summary>
        private static void ContractOf(Lowering l, Contract contract)
        {
            KExpr And(IEnumerable<KExpr> xs) => xs.DefaultIfEmpty(new KLit("true")).Aggregate((a, b) => new KOp("&&", a, b));
            foreach (var r in contract.Requires) l._p.Requires.Add(new KSpec { Expr = l.Spec(r, null), At = r.Syntax });
            foreach (var (type, cond, at) in contract.ThrowEnsures)
            {
                if (!IsException(type)) throw new NotTranslated("Spec.EnsuresOnThrow of " + type);
                l._p.ThrowEnsures.Add((type, l.Spec(cond, null), at));
                l._p.ExceptionTypes.Add(type);
            }
            foreach (var e in contract.Ensures)
            {
                var post = l.Spec(e.Expr, e.ResultParameter);
                if (e.Guard != null) post = new KOp("==>", new KOp("old", And(e.Guard.Select(g => l.Spec(g, null)))), post);
                l._p.Ensures.Add(new KSpec { Expr = post, At = e.Syntax });
            }
            if (contract.Decreases != null) l._p.Decreases = contract.Decreases.Select(d => l.Measure(d)).ToList();
            if (contract.Reads != null) l._p.ReadsFrame = l.Spec(contract.Reads, null);
            if (contract.OwnRequires.Count > 0)
            {
                l._p.OwnRequires = contract.OwnRequires.Select(r => l.Spec(r, null)).ToList();
                foreach (var b in contract.Bases) l._p.BaseRequires.Add((b.Method, b.Requires.Select(r => l.Spec(r, null)).ToList()));
            }
            foreach (var (b, frame) in contract.BaseModifies.Where(x => !ReferenceEquals(x.Frame, contract.Modifies)))
                l._p.BaseFrames.Add((b.Method, l.Spec(frame, null)));
        }

        /// <summary>
        /// A virtual member called on this: where this class (or a base of it) overrides it and nothing below may again
        /// (the override sealed, or the class), the call is of that override, as CsVerify's engine reads it.
        /// </summary>
        private IMethodSymbol OnThis(IMethodSymbol m, IOperation instance)
        {
            m = m.OriginalDefinition;
            if (!(instance is IInstanceReferenceOperation) || !Engine.IsOverridable(m) || _m.ContainingType == null) return m;
            for (var t = _m.ContainingType; t != null; t = t.BaseType)
                foreach (var o in t.GetMembers(m.Name).OfType<IMethodSymbol>())
                    for (var b = o.OverriddenMethod; b != null; b = b.OverriddenMethod)
                        if (SymbolEqualityComparer.Default.Equals(b.OriginalDefinition, m))
                            return o.IsSealed || _m.ContainingType.IsSealed ? o.OriginalDefinition : m;
            return m;
        }

        /// <summary>A contract class's member means the member it specifies (the one it overrides or implements).</summary>
        private static IPropertySymbol Specified(IPropertySymbol p)
        {
            if (p == null || !SpecSymbols.IsContractsClass(p.ContainingType)) return p;
            if (p.OverriddenProperty != null) return p.OverriddenProperty;
            var target = SpecSymbols.ContractClassTarget(p.ContainingType);
            return target?.GetMembers(p.Name).OfType<IPropertySymbol>().FirstOrDefault() ?? p;
        }

        /// <summary>Does a specification name permissions (Spec.Acc, or a predicate)?</summary>
        public static bool HasAtoms(IOperation op) =>
            op != null && op.DescendantsAndSelf().OfType<IInvocationOperation>().Any(i =>
                SpecSymbols.IsPredicate(i.TargetMethod.OriginalDefinition) || SpecSymbols.IsSpecClass(i.TargetMethod.ContainingType) && i.TargetMethod.Name is "Acc" or "AccRead");

        /// <summary>A predicate's own check: its body, its arithmetic as code's (checked), read left to right.</summary>
        private KProcedure Predicate()
        {
            if (!_m.IsStatic || _m.ReturnType.SpecialType != SpecialType.System_Boolean || _contract.PureBody == null)
                throw new NotTranslated("a [Predicate] that isn't a static bool method of one expression");
            // (ghost code: its arithmetic is mathematical, its reads and divisions checked)
            _p.IsPredicate = _p.UsesPerm = _p.Ghost = true;
            _codeArith = true;
            try { _p.FunctionBody = Spec(_contract.PureBody, null); }
            finally { _codeArith = false; }
            _p.Blocks.Add(new KBlock { Label = "b0", Ordinal = 0, Jump = new KStop() });
            return _p;
        }

        /// <summary>In a predicate's own check: arithmetic is code's.</summary>
        private bool _codeArith;

        private KProcedure Run()
        {
            if (SpecSymbols.IsPredicate(_m)) return Predicate();
            // (Dafny's dynamic frames: what it may write. An [Owned] class's objects are framed by their views instead)
            if (_contract.Modifies != null)
            {
                if (SpecSymbols.IsOwned(_m.ContainingType)) throw new NotTranslated("Spec.Modifies of an [Owned] class's method");
                _p.Frame = Spec(_contract.Modifies, null);
            }
            // (Viper's functions over predicates read their footprint: not yet)
            _p.UsesPerm |= _contract.Requires.Any(HasAtoms) || _contract.Ensures.Any(e => HasAtoms(e.Expr));
            ContractOf(this, _contract);
            // (an abstract member: its contract alone)
            if (_m.IsAbstract || _m.MethodKind == MethodKind.DelegateInvoke) { _p.Abstract = true; return _p; }
            // (a collection's member: its stub's contract alone; what it may change is its own collection's models, a new one's for a constructor)
            if (IsCollection(_m.ContainingType))
            {
                if (!_contract.IsStub) throw new NotTranslated("a collection's member without a stub contract: " + _m.Name);
                _p.Abstract = true;
                foreach (var model in ModelsOf((INamedTypeSymbol)_m.ContainingType))
                {
                    _p.Models[model.Name] = model;
                    if (_contract.Modifies != null) { _p.Modifies.Add(model.Name); _p.AnyWrites.Add(model.Name); }
                }
                if (_p.ListCtor) { _p.Modifies.Add("$Alloc"); _p.AnyWrites.Add("$Alloc"); }
                return _p;
            }
            var cfg = _model.GetOperation(_decl) switch
            {
                IMethodBodyOperation body => ControlFlowGraph.Create(body),
                IConstructorBodyOperation body => ControlFlowGraph.Create(body),
                // (an accessor, an expression-bodied property's getter)
                IBlockOperation block => ControlFlowGraph.Create(block),
                _ => throw new NotTranslated("no body"),
            };
            // (foreach over an array or a string: a loop over an index, its enumerator's try/finally gone)
            ForEachLoops(cfg);
            // (try and catch: each catch of an exception type the kernel has; not finally, nor filters, yet)
            foreach (var r in cfg.Root.NestedRegions.SelectMany(AllRegions).Concat(cfg.Root.NestedRegions))
                if (_erased.Contains(r) || _erased.Contains(r.EnclosingRegion)) continue;
                else if (!(r.Kind is ControlFlowRegionKind.LocalLifetime or ControlFlowRegionKind.TryAndCatch or ControlFlowRegionKind.Try or ControlFlowRegionKind.TryAndFinally or ControlFlowRegionKind.Finally ||
                      r.Kind == ControlFlowRegionKind.Catch && (r.ExceptionType == null || IsException(r.ExceptionType))))
                    throw new NotTranslated(r.Kind == ControlFlowRegionKind.Catch ? "a catch of " + r.ExceptionType : r.Kind.ToString());
            _cfg = cfg;
            // (a function's definition is its body: not one an override may answer, which is of its contract alone)
            if (_isFunction(_m) && _contract.PureBody != null && !Engine.IsOverridable(_m)) _p.FunctionBody = Spec(_contract.PureBody, null);
            var heads = LoopHeads(cfg);
            foreach (var h in heads)
            {
                var hb = cfg.Blocks[h];
                var loop = (hb.BranchValue?.Syntax ?? hb.Operations.FirstOrDefault()?.Syntax)?.AncestorsAndSelf()
                    .FirstOrDefault(n => n is ForStatementSyntax || n is WhileStatementSyntax || n is DoStatementSyntax || n is CommonForEachStatementSyntax);
                if (loop != null) _p.LoopSyntax[h] = loop;
            }
            foreach (var h in heads)
                _p.LoopBodies[h] = cfg.Blocks.Where(x => new[] { x.FallThroughSuccessor, x.ConditionalSuccessor }.Any(s => s?.Destination?.Ordinal == h) && x.Ordinal >= h).Max(x => x.Ordinal);
            ReadLoopSpecs(cfg, heads);
            ForEachInvariants();
            if (_p.IsCtor) Initializers();
            foreach (var b in cfg.Blocks)
            {
                _block = new KBlock { Label = $"b{b.Ordinal}", Ordinal = b.Ordinal };
                _p.Blocks.Add(_block);
                _cfgBlock = b;
                // (its data values are valid: their invariants hold)
                if (b.Ordinal == 0)
                {
                    foreach (var cl in Confined()) Emit(new KAssign { Var = Declare(Local(cl), cl.Type), Value = new KLit("null") });
                    if (_p.HasThis && HasInvariants(_m.ContainingType)) AssumeValid(new KVar("this"), _m.ContainingType);
                    foreach (var dp in _m.Parameters.Where(x => x.RefKind != RefKind.Out && HasInvariants(x.Type))) AssumeValid(new KVar(Local(dp)), dp.Type);
                }
                // (the delegates it takes to be steady are: its callers prove it)
                if (b.Ordinal == 0)
                    foreach (var sp in SteadyParams(_m).Where(x => IsFunc(x.Type)))
                    {
                        _p.DelegateKeys.Add(FuncKey(sp.Type));
                        Emit(new KAssume { Cond = new KOp("$steady", new KVar(Local(_m.Parameters[sp.Ordinal]))) });
                    }
                if (b.Kind == BasicBlockKind.Exit) { _block.Jump = new KStop(); continue; }
                // (an erased finally: nothing goes there)
                if (b.EnclosingRegion.Kind == ControlFlowRegionKind.Finally && _erased.Contains(b.EnclosingRegion.EnclosingRegion)) { _block.Jump = new KStop(); continue; }
                // (at a loop's head, every atomic field went by steps since entry)
                if (heads.Contains(b.Ordinal) && _p.Fields.Any(Atomics.IsAtomic)) Emit(new KAtomicSteps());
                foreach (var op in b.Operations)
                {
                    Statement(op);
                    // (while a task it started runs alongside, what the method doesn't hold is forgotten from each statement to the next)
                    if (_tasks.Count > 0 && !InSpec(op.Syntax)) Alongside();
                }
                Branch(b);
            }
            if (_exitUsed) _p.Blocks.Add(new KBlock { Label = "x$exit", Ordinal = cfg.Blocks.Length, Stmts = { new KThrowExit() }, Jump = new KStop() });
            FinallyEnds();
            return _p;
        }

        // ------------------------------------------------------------------ foreach

        /// <summary>A foreach over an array or a string, as C# compiles it: an index from 0 to its length.</summary>
        private sealed class ForEach
        {
            public int Head;
            public string Array, Index;
            public ITypeSymbol Type, Element;
            public bool String;
            /// <summary>Over a collection (null: an array or a string).</summary>
            public INamedTypeSymbol Collection;
            /// <summary>A list its loop may change: through its enumerator, whose MoveNext checks the list's version (Version, as it was).</summary>
            public string Version;
            public SyntaxNode At;
        }

        private readonly Dictionary<CaptureId, ForEach> _forEach = new Dictionary<CaptureId, ForEach>();
        private readonly Dictionary<int, ForEach> _forEachAt = new Dictionary<int, ForEach>();
        private readonly Dictionary<ILocalSymbol, ForEach> _forEachOf = new Dictionary<ILocalSymbol, ForEach>(SymbolEqualityComparer.Default);
        /// <summary>The try/finally regions of those loops' enumerators: C# emits neither.</summary>
        private readonly HashSet<ControlFlowRegion> _erased = new HashSet<ControlFlowRegion>();

        private void ForEachLoops(ControlFlowGraph cfg)
        {
            foreach (var fs in _decl.DescendantNodes().OfType<CommonForEachStatementSyntax>())
            {
                if (!(_model.GetOperation(fs) is IForEachLoopOperation fo) || fo.IsAsynchronous) continue;
                var collection = Unconverted(fo.Collection);
                bool isString = IsString(collection.Type);
                bool isCollection = IsCollection(collection.Type);
                if (!IsArray(collection.Type) && !isString && !isCollection) continue;
                // (a list: over its model, where the loop changes no list; any other collection, or a list it may change,
                // through its enumerator, whose MoveNext checks the collection's version)
                bool enumerated = isCollection && !(IsList(collection.Type) && ChangesNoList(fs.Statement));
                bool pairs = CollectionKind(collection.Type) == "Dictionary";
                var element = isString ? _model.Compilation.GetSpecialType(SpecialType.System_Char)
                            : pairs ? fo.Locals.FirstOrDefault()?.Type ?? throw new NotTranslated("a foreach over a dictionary without its variable")
                            : isCollection ? ((INamedTypeSymbol)collection.Type).TypeArguments[0] : ((IArrayTypeSymbol)collection.Type).ElementType;
                if (pairs && !IsPair(element)) throw new NotTranslated("a foreach over a dictionary not by its pairs");
                var conv = Microsoft.CodeAnalysis.CSharp.CSharpExtensions.GetForEachStatementInfo(_model, fs).ElementConversion;
                var target = fo.Locals.FirstOrDefault()?.Type;
                if (!(conv.IsIdentity || conv.IsImplicit && conv.IsNumeric && IsIntegral(element) && target != null && IsIntegral(target)))
                    throw new NotTranslated("a foreach's conversion of its elements");
                var capture = cfg.Blocks.SelectMany(b => b.Operations).OfType<IFlowCaptureOperation>()
                    .FirstOrDefault(c => c.Syntax == fs.Expression && c.Value is IInvocationOperation gi && gi.TargetMethod.Name == "GetEnumerator");
                var head = capture == null ? null : cfg.Blocks.FirstOrDefault(b => b.BranchValue is IInvocationOperation mn && mn.TargetMethod.Name == "MoveNext" &&
                                                                                   mn.Instance is IFlowCaptureReferenceOperation r && r.Id.Equals(capture.Id));
                if (head == null) throw new NotTranslated("a foreach without its enumerator");
                var n = _forEachAt.Count;
                var fe = new ForEach
                {
                    Head = head.Ordinal, Array = Declare($"fe${n}$a", collection.Type), Index = Declare($"fe${n}$i", _model.Compilation.GetSpecialType(SpecialType.System_Int32)),
                    Type = collection.Type, Element = element, String = isString, At = fs.Expression, Collection = isCollection ? (INamedTypeSymbol)collection.Type : null,
                };
                if (isCollection) foreach (var model in ModelsOf(fe.Collection)) _p.Models[model.Name] = model;
                if (enumerated) fe.Version = Declare($"fe${n}$v", _model.Compilation.GetSpecialType(SpecialType.System_Int32));
                _forEach[capture.Id] = fe;
                _forEachAt[head.Ordinal] = fe;
                foreach (var l in fo.Locals) _forEachOf[l] = fe;
                for (var region = head.EnclosingRegion; region != null; region = region.EnclosingRegion)
                    if (region.Kind == ControlFlowRegionKind.Try && region.EnclosingRegion?.Kind == ControlFlowRegionKind.TryAndFinally)
                    {
                        _erased.Add(region.EnclosingRegion);
                        break;
                    }
            }
        }

        private KExpr Current(ForEach fe)
        {
            if (fe.Version == null) return CurrentOf(fe);
            // (through the enumerator: what it gives isn't known; a dictionary's, a pair it has)
            var v = Declare("t$" + _temps++, fe.Element);
            Emit(new KHavoc { Var = v });
            if (CollectionKind(fe.Collection) == "Dictionary")
            {
                var key = Pair(new KVar(v), fe.Element, "Key");
                var value = Pair(new KVar(v), fe.Element, "Value");
                Emit(new KAssume { Cond = new KOp("&&", new KOp("sel", new KVar(ModelOf("Domain", fe.Collection).Name), new KVar(fe.Array), key),
                                                       new KOp("==", new KOp("sel", new KVar(ModelOf("Entries", fe.Collection).Name), new KVar(fe.Array), key), value)) });
            }
            return new KVar(v);
        }

        /// <summary>A dictionary's pair's Key or Value.</summary>
        private KExpr Pair(KExpr pair, ITypeSymbol type, string member)
        {
            var args = ((INamedTypeSymbol)type).TypeArguments;
            var (k, v) = (Kind(args[0]), Kind(args[1]));
            _p.Pairs.Add((k, v));
            return new KOp(member == "Key" ? "$kvp.Key." + k : "$kvp.Value." + v, pair);
        }

        private static KExpr CurrentOf(ForEach fe) => fe.Collection != null ? new KOp("sel", new KVar(ModelOf("Items", fe.Collection).Name), new KVar(fe.Array), new KVar(fe.Index)) :
            new KElem { String = fe.String, Array = new KVar(fe.Array), Index = new KVar(fe.Index), ArrayType = fe.String ? null : fe.Type, At = fe.At, ArrayAt = fe.At };

        /// <summary>A loop body that calls nothing that may change a list: only specifications, [Pure] members and lists' [Pure] stubs.</summary>
        private bool ChangesNoList(SyntaxNode body) => body.DescendantNodesAndSelf().Select(n => _model.GetOperation(n)).Where(o => o != null).All(o => o switch
        {
            IInvocationOperation inv => SpecSymbols.IsSpecClass(inv.TargetMethod.ContainingType) || _contractOf?.Invoke(inv.TargetMethod) is Contract c && (c.IsPure || c.IsLemma),
            IObjectCreationOperation oc => !IsCollection(oc.Type) && (oc.Constructor == null || oc.Constructor.DeclaringSyntaxReferences.Length > 0 && _contractOf?.Invoke(oc.Constructor) is Contract cc && cc.IsPure),
            IPropertyReferenceOperation pr => !IsCollection(pr.Instance?.Type) || !(pr.Parent is IAssignmentOperation a && a.Target == pr),
            IAnonymousFunctionOperation _ => false,
            _ => true,
        });

        /// <summary>The collection's length: an array's or a string's, or a list's Size.</summary>
        private KExpr LengthOf(ForEach fe, bool inSpec = false) => fe.Collection != null
            ? Model("Size", fe.Collection, new KVar(fe.Array))
            : new KLen { String = fe.String, Array = new KVar(fe.Array), InSpec = inSpec, At = fe.At, ArrayAt = fe.At };

        /// <summary>A foreach's index stays within its collection: the loop's first invariant (it holds by itself).</summary>
        private void ForEachInvariants()
        {
            foreach (var fe in _forEachAt.Values.Where(x => x.Version == null))
            {
                if (!_p.Invariants.TryGetValue(fe.Head, out var list)) _p.Invariants[fe.Head] = list = new List<KSpec>();
                var i = new KVar(fe.Index);
                list.Insert(0, new KSpec
                {
                    Expr = new KOp("&&", new KOp("<=", new KLit("0"), i), new KOp("<=", i, LengthOf(fe, true))),
                    At = fe.At,
                });
            }
        }

        // ------------------------------------------------------------------ exceptions

        private ControlFlowGraph _cfg;
        private BasicBlock _cfgBlock;
        private bool _exitUsed;
        private readonly Dictionary<ControlFlowRegion, string> _dispatch = new Dictionary<ControlFlowRegion, string>();

        /// <summary>The innermost try a region is in (not a handler of it: an exception there goes past it); null if none.</summary>
        private static ControlFlowRegion TryOf(ControlFlowRegion r)
        {
            for (; r != null; r = r.EnclosingRegion)
            {
                if (r.Kind == ControlFlowRegionKind.Try && r.EnclosingRegion?.Kind == ControlFlowRegionKind.TryAndCatch) return r;
                if (r.Kind == ControlFlowRegionKind.Catch) r = r.EnclosingRegion; // (its TryAndCatch: go on outside it)
                else if (r.Kind == ControlFlowRegionKind.Finally) r = r.EnclosingRegion;
            }
            return null;
        }

        /// <summary>
        /// Where an exception thrown in this region goes: its try's handlers, or the method's exit where it has
        /// EnsuresOnThrow; null where exceptions aren't seen (the path just ends, as in CsVerify's engine).
        /// </summary>
        private string ThrowTarget(ControlFlowRegion r)
        {
            if (_p.Ghost || _contract.IsPure || _contract.IsLemma || _cfg == null) return null; // (proofs may not throw)
            var t = TryOf(r);
            // (a try with a finally, inside the handlers' try, or with none: the finally runs, then the exception goes on)
            var f = FinallyTryOf(r);
            if (f != null && (t == null || IsInside(f, t)))
            {
                if (_throughFinally.TryGetValue(f, out var known)) return known;
                var outer = ThrowTarget(f.EnclosingRegion.EnclosingRegion ?? f.EnclosingRegion);
                var via = (KGoto)ThroughFinally(f.EnclosingRegion.NestedRegions.First(x => x.Kind == ControlFlowRegionKind.Finally), outer == null ? new KStop() : new KGoto(outer), f.FirstBlockOrdinal);
                Declare("ex$", _model.Compilation.GetTypeByMetadataName("System.Exception"));
                return _throughFinally[f] = via.Targets[0];
            }
            if (t == null)
            {
                if (_contract.ThrowEnsures.Count == 0) return null;
                if (!_exitUsed) Declare("ex$", _model.Compilation.GetTypeByMetadataName("System.Exception"));
                _exitUsed = true;
                return "x$exit";
            }
            return Dispatch(t);
        }

        private readonly Dictionary<ControlFlowRegion, string> _throughFinally = new Dictionary<ControlFlowRegion, string>();

        /// <summary>The innermost try with a finally a region is in (not its finally: an exception there goes past it); null if none.</summary>
        private ControlFlowRegion FinallyTryOf(ControlFlowRegion r)
        {
            for (; r != null; r = r.EnclosingRegion)
            {
                if (r.Kind == ControlFlowRegionKind.Try && r.EnclosingRegion?.Kind == ControlFlowRegionKind.TryAndFinally && !_erased.Contains(r.EnclosingRegion)) return r;
                if (r.Kind == ControlFlowRegionKind.Finally) r = r.EnclosingRegion;
            }
            return null;
        }

        /// <summary>Is region a inside region b?</summary>
        private static bool IsInside(ControlFlowRegion a, ControlFlowRegion b)
        {
            for (var r = a; r != null; r = r.EnclosingRegion) if (r == b) return true;
            return false;
        }

        /// <summary>A try's handlers, in order: each catch tests the exception's type; none taken, it goes on outward.</summary>
        private string Dispatch(ControlFlowRegion tryRegion)
        {
            if (_dispatch.TryGetValue(tryRegion, out var label)) return label;
            label = $"x${tryRegion.FirstBlockOrdinal}";
            _dispatch[tryRegion] = label;
            var outer = ThrowTarget(tryRegion.EnclosingRegion.EnclosingRegion ?? tryRegion.EnclosingRegion);
            var handlers = tryRegion.EnclosingRegion.NestedRegions.Where(x => x.Kind == ControlFlowRegionKind.Catch).ToList();
            var ex = new KVar("ex$");
            Declare("ex$", _model.Compilation.GetTypeByMetadataName("System.Exception"));
            // (handler k: taken where the type matches, else on to the next; past the last, outward)
            for (int k = 0; k < handlers.Count; k++)
            {
                var h = handlers[k];
                var all = h.ExceptionType == null || h.ExceptionType.ToDisplayString() == "System.Exception";
                if (!all) _p.ExceptionTypes.Add(h.ExceptionType);
                var test = all ? (KExpr)new KLit("true") : new KOp("sub", new KOp("dtype", ex), new KLit(TypeConst(h.ExceptionType)));
                string here = k == 0 ? label : $"{label}$n{k - 1}", take = $"{label}$h{k}", pass = $"{label}$t{k}";
                if (k > 0) _p.Blocks.Last(x => x.Label == here).Jump = new KGoto(take, pass);
                else _p.Blocks.Add(new KBlock { Label = here, Ordinal = tryRegion.FirstBlockOrdinal, Jump = new KGoto(take, pass) });
                _p.Blocks.Add(new KBlock { Label = take, Ordinal = tryRegion.FirstBlockOrdinal, Stmts = { new KAssume { Cond = test } }, Jump = new KGoto($"b{h.FirstBlockOrdinal}") });
                var next = new KBlock { Label = pass, Ordinal = tryRegion.FirstBlockOrdinal, Stmts = { new KAssume { Cond = new KOp("!", test) } } };
                _p.Blocks.Add(next);
                if (k == handlers.Count - 1) next.Jump = outer == null ? new KStop() : new KGoto(outer);
                else { next.Jump = new KGoto($"{label}$n{k}"); _p.Blocks.Add(new KBlock { Label = $"{label}$n{k}", Ordinal = tryRegion.FirstBlockOrdinal }); }
            }
            if (handlers.Count == 0) _p.Blocks.Add(new KBlock { Label = label, Ordinal = tryRegion.FirstBlockOrdinal, Jump = outer == null ? new KStop() : new KGoto(outer) });
            return label;
        }

        /// <summary>
        /// A constructor's start: the field initializers of its class, in order (its fields are their defaults before,
        /// as the caller makes them). One that chains to another (this(...), or base(...) of a class not object) isn't
        /// translated yet.
        /// </summary>
        private void Initializers()
        {
            if (_decl is ConstructorDeclarationSyntax { Initializer: { } chained } && chained.ThisOrBaseKeyword.IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.ThisKeyword))
                throw new NotTranslated("a constructor that calls this(...)");
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

        private static IEnumerable<ControlFlowRegion> AllRegions(ControlFlowRegion r) => r.NestedRegions.Concat(r.NestedRegions.SelectMany(AllRegions));

        // ------------------------------------------------------------------ loops

        /// <summary>The blocks a later block goes back to: loop heads.</summary>
        private static HashSet<int> LoopHeads(ControlFlowGraph cfg)
        {
            var heads = new HashSet<int>();
            foreach (var b in cfg.Blocks)
                foreach (var s in new[] { b.FallThroughSuccessor, b.ConditionalSuccessor })
                    if (s?.Destination != null && s.Destination.Ordinal <= b.Ordinal) heads.Add(s.Destination.Ordinal);
            return heads;
        }

        /// <summary>The innermost loop a block is in: the latest head before it whose back edge comes from it or after it; -1 if none.</summary>
        private static int HeadOf(ControlFlowGraph cfg, HashSet<int> heads, BasicBlock b) =>
            heads.Where(h => h <= b.Ordinal && cfg.Blocks.Any(x => x.Ordinal >= b.Ordinal &&
                new[] { x.FallThroughSuccessor, x.ConditionalSuccessor }.Any(s => s?.Destination?.Ordinal == h))).DefaultIfEmpty(-1).Max();

        /// <summary>Each Spec.Invariant and loop Spec.Decreases, at the head of the innermost loop it is in.</summary>
        private void ReadLoopSpecs(ControlFlowGraph cfg, HashSet<int> heads)
        {
            foreach (var b in cfg.Blocks)
                foreach (var op in b.Operations)
                {
                    if (SpecCall(op, "Decreases") is IInvocationOperation dec && HeadOf(cfg, heads, b) is int h && h >= 0)
                    {
                        var whole = _model.GetOperation(dec.Syntax) as IInvocationOperation ?? throw new NotTranslated("a measure without its operation");
                        var measure = new List<KSpec>();
                        for (int k = 0; k < whole.Arguments.Length; k++)
                        {
                            measure.Add(new KSpec { Expr = Measure(whole.Arguments[k].Value), At = whole.Arguments[k].Value.Syntax });
                            Declare($"m${h}${k}", IsData(whole.Arguments[k].Value.Type) ? _model.Compilation.GetSpecialType(SpecialType.System_Int32) : whole.Arguments[k].Value.Type);
                        }
                        _p.Measures[h] = measure;
                    }
                    if (SpecCall(op, "Invariant") is IInvocationOperation inv)
                    {
                        var head = HeadOf(cfg, heads, b);
                        if (head < 0) throw new NotTranslated("an invariant outside a loop");
                        if (!_p.Invariants.TryGetValue(head, out var list)) _p.Invariants[head] = list = new List<KSpec>();
                        var arg = SpecArgument(inv);
                        list.Add(new KSpec { Expr = Spec(arg, null), At = arg.Syntax });
                    }
                }
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

        private void Emit(KStmt s) => _block.Stmts.Add(s);

        private void Statement(IOperation op)
        {
            if (op is IExpressionStatementOperation es) op = es.Operation;
            if (op is IFlowCaptureOperation spec && InSpec(spec.Value.Syntax)) return;
            switch (op)
            {
                case IInvocationOperation baseCall when baseCall.TargetMethod.MethodKind == MethodKind.Constructor &&
                                                        baseCall.TargetMethod.ContainingType.SpecialType == SpecialType.System_Object:
                    return; // (object's constructor does nothing)
                case IInvocationOperation chain when chain.TargetMethod.MethodKind == MethodKind.Constructor && chain.Instance is IInstanceReferenceOperation && _p.IsCtor:
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
                case IInvocationOperation own when SpecSymbols.IsCsVerifyType(own.TargetMethod.ContainingType, "Own"):
                    Own(own);
                    return;
                case IInvocationOperation inv when SpecSymbols.IsSpecClass(inv.TargetMethod.ContainingType):
                    switch (inv.TargetMethod.Name)
                    {
                        case "Requires": case "Ensures": case "Invariant": case "Decreases": case "Modifies": case "EnsuresOnThrow": return; // (the contract; the loop heads)
                        case "Fold": case "Unfold":
                        {
                            var whole = SpecArgument(inv);
                            if (!(Spec(whole, null) is KInst instance)) throw new NotTranslated("Spec." + inv.TargetMethod.Name + " of what isn't a predicate instance");
                            _p.UsesPerm = true;
                            Emit(new KFold { Inst = instance, Unfold = inv.TargetMethod.Name == "Unfold", At = inv.Syntax, InstAt = whole.Syntax });
                            return;
                        }
                        case "Assert": case "Assume":
                            Emit(new KSpecStmt { Spec = Spec(SpecArgument(inv), null), Assume = inv.TargetMethod.Name == "Assume", At = inv.Syntax, ArgumentAt = inv.Arguments[0].Syntax });
                            return;
                        default: throw new NotTranslated("Spec." + inv.TargetMethod.Name);
                    }
                case IInvocationOperation { TargetMethod.Name: "Start", Instance: ILocalReferenceOperation sl, Arguments.Length: 0 } when _threads.TryGetValue(sl.Local, out var startedLambda):
                    Start(sl.Local, StartedCall(startedLambda), thread: true);
                    return;
                case IInvocationOperation { TargetMethod.Name: "Join", Instance: ILocalReferenceOperation jl, Arguments.Length: 0 } when _tasks.TryGetValue(jl.Local, out var joined):
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
                // (Task.Run(() => F(...)): a task of the call, proved where it starts; of any other lambda, a task of code verified on its own)
                case ISimpleAssignmentOperation run when run.Target is ILocalReferenceOperation { Local: var rl } && IsTaskLike(rl.Type) &&
                                                         Unconverted(run.Value) is IInvocationOperation tr && tr.TargetMethod.ContainingType?.ToDisplayString() == "System.Threading.Tasks.Task" &&
                                                         tr.TargetMethod.Name == "Run" && tr.Arguments.Length == 1 && LambdaSyntax(tr.Arguments[0]) is AnonymousFunctionExpressionSyntax runLambda:
                    Start(rl, StartedCall(runLambda));
                    return;
                // (new Thread(() => F(...)): started by Start, finished by Join)
                case ISimpleAssignmentOperation th when th.Target is ILocalReferenceOperation { Local: var thl } && thl.Type.OriginalDefinition.ToDisplayString(SymbolDisplayFormat.FullyQualifiedFormat) == "global::System.Threading.Thread" &&
                                                        Unconverted(th.Value) is IObjectCreationOperation tc && tc.Arguments.Length == 1 && LambdaSyntax(tc.Arguments[0]) is AnonymousFunctionExpressionSyntax thLambda:
                    if (_threads.ContainsKey(thl)) throw new NotTranslated("a thread local assigned again");
                    _threads[thl] = thLambda;
                    return;
                case ISimpleAssignmentOperation a:
                    Assign(a.Target, Expr(a.Value));
                    return;
                case ICompoundAssignmentOperation ca:
                {
                    var v = Operands(ca.Target, ca.Value);
                    Assign(ca.Target, Arith(Op(ca.OperatorKind), v[0], v[1], ca.Type, ca.Syntax, ca.IsChecked));
                    return;
                }
                case IIncrementOrDecrementOperation id:
                    Assign(id.Target, Arith(id.Kind == OperationKind.Increment ? "+" : "-", Expr(id.Target), new KLit("1"), id.Type, id.Syntax, id.IsChecked));
                    return;
                case IFlowCaptureOperation en when _forEach.TryGetValue(en.Id, out var fe):
                {
                    // the collection, evaluated once (a null one throws), and the index at its start
                    var coll = Expr(Unconverted(((IInvocationOperation)en.Value).Instance ?? ((IInvocationOperation)en.Value).Arguments[0].Value));
                    Emit(new KAssign { Var = fe.Array, Value = coll });
                    Emit(new KAssign { Var = fe.Index, Value = new KLit("0") });
                    // (its length, read once: where a null one throws)
                    if (fe.Collection != null)
                        Emit(new KCheck { Cond = new KOp("!=", new KVar(fe.Array), new KLit("null")), Id = "CSV1013", At = fe.At, Message = $"'{fe.At}' might be null in '{fe.At}'" });
                    if (fe.Version != null) Emit(new KAssign { Var = fe.Version, Value = new KOp("sel", new KVar(VersionMap), new KVar(fe.Array)) });
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
                case IFlowCaptureOperation fc:
                    _captured[fc.Id] = fc.Value;
                    // (a field captured as what an assignment writes, x.f = c ? a : b: its object, kept)
                    if (fc.Value is IFieldReferenceOperation { Field.IsStatic: false } cf &&
                        cf.Instance is ILocalReferenceOperation or IParameterReferenceOperation or IInstanceReferenceOperation)
                        _lvalues[fc.Id] = cf;
                    var value = Expr(fc.Value);
                    Emit(new KAssign { Var = Capture(fc.Id, fc.Value.Type), Value = value });
                    return;
                default:
                    throw new NotTranslated(op.Kind.ToString());
            }
        }

        private void Assign(IOperation target, KExpr value)
        {
            switch (target)
            {
                case ILocalReferenceOperation l when IsView(l.Local.Type):
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
                // (a computed property: its setter, called with the value)
                case IPropertyReferenceOperation sp when IsComputed(sp.Property) && sp.Property.SetMethod != null:
                    Invoke(sp.Property.SetMethod, sp.Instance, sp.Arguments, sp.Syntax, value);
                    return;
                case IFieldReferenceOperation _: case IPropertyReferenceOperation _:
                {
                    var (field, instance, onThis, instanceAt) = FieldOf(target);
                    if (IsOwnedField(field)) _p.UsesPerm = true;
                    if (Atomics.IsAtomic(field) && !(_p.IsCtor && onThis) && !(target.Syntax.Parent is InitializerExpressionSyntax)) value = AtomicWrite(field, instance, onThis, value, target.Syntax);
                    Emit(new KFieldStore { Field = field, Instance = instance, OnThis = onThis, Value = value, At = target.Syntax, InstanceAt = instanceAt });
                    return;
                }
                case IArrayElementReferenceOperation e when IsArray(e.ArrayReference.Type) && e.Indices.Length == 1:
                {
                    var v = Operands(e.ArrayReference, e.Indices[0]);
                    HeldCell(v[0], e.Syntax, write: true);
                    Emit(new KStore { Array = v[0], Index = v[1], Value = value, ArrayType = e.ArrayReference.Type, At = e.Syntax, ArrayAt = e.ArrayReference.Syntax });
                    return;
                }
                case IParameterReferenceOperation p when p.Parameter.RefKind is RefKind.Ref or RefKind.Out && InSubset(p.Parameter.Type) && !IsView(p.Parameter.Type):
                {
                    Emit(new KAssign { Var = Local(p.Parameter), Value = value });
                    return;
                }
                case IParameterReferenceOperation: throw new NotTranslated("an assignment to a parameter");
                case IFlowCaptureReferenceOperation cr when _lvalues.TryGetValue(cr.Id, out var lv):
                    Assign(lv, value);
                    return;
                default: throw new NotTranslated("an assignment to " + target.Kind);
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
            // (a return: every task it started was awaited, else a failure in it would be lost)
            if (fall?.Destination?.Kind == BasicBlockKind.Exit) TasksAwaited(_block);
            // (a constructor's end: the invariants of its object's locks hold, before anyone can take them)
            if (fall?.Destination?.Kind == BasicBlockKind.Exit && _p.IsCtor && KernelTypes.Locks != null)
                foreach (var (lockField, invariant) in KernelTypes.Locks.InvariantsIn(_m.ContainingType).Where(x => !x.lockField.IsStatic))
                    Emit(new KCheck { Cond = InvariantCall(invariant, new KVar("this")), Id = "CSV1024", At = _decl,
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

        // ------------------------------------------------------------------ locks

        private readonly Dictionary<CaptureId, IOperation> _captured = new Dictionary<CaptureId, IOperation>();

        private KExpr InvariantCall(IMethodSymbol invariant, KExpr owner)
        {
            if (!_isFunction(invariant.OriginalDefinition)) throw new NotTranslated("a lock invariant that isn't a function: " + invariant.Name);
            return new KFnCall { Callee = invariant.OriginalDefinition, Receiver = invariant.IsStatic ? null : owner, ReceiverIsThis = owner is KVar { Name: "this" }, Args = new KExpr[0], At = _decl };
        }

        /// <summary>
        /// lock (o) { ... }: Monitor.Enter forgets what the lock guards (others have had it) and gives its invariants;
        /// Monitor.Exit, in its finally, proves them (CSV1024). Only a lock field of this object or a static one, not
        /// inside another lock (whose order, lock levels, isn't translated yet).
        /// </summary>
        private void Monitor(IInvocationOperation call)
        {
            var arg = call.Arguments.OrderBy(a => a.Parameter.Ordinal).First().Value;
            var lockOp = Unconverted(arg is IFlowCaptureReferenceOperation r && _captured.TryGetValue(r.Id, out var v) ? v : arg);
            if (KernelTypes.Locks == null) throw new NotTranslated("locks without their guards");
            var stmt = call.Syntax.AncestorsAndSelf().OfType<LockStatementSyntax>().FirstOrDefault() ?? (SyntaxNode)call.Syntax;
            // (whose lock: a lock field of this object, of an object a variable holds, a static one; or an object of a class with a level)
            IFieldSymbol lockField = null;
            KExpr owner;
            if (lockOp is IFieldReferenceOperation { Field: IFieldSymbol lf } fr && IsLockObject(lf))
            {
                lockField = lf;
                owner = lf.IsStatic ? null : fr.Instance is IInstanceReferenceOperation ? new KVar("this") : Fixed(fr.Instance) ? Expr(fr.Instance) : throw new NotTranslated("a lock of an object that may change");
            }
            else if (Fixed(lockOp) && LockLevels.LeveledClass(lockOp.Type) != null) owner = Expr(lockOp);
            else throw new NotTranslated("a lock of something other than a lock field or an object with a level");
            if (call.TargetMethod.Name == "Enter")
            {
                if (call.Arguments.Length == 2) Emit(new KAssign { Var = RefVariable(call.Arguments.OrderBy(a => a.Parameter.Ordinal).Last()), Value = new KLit("true") });
                ProveOrderAt(stmt);
                if (lockField == null) return;
                foreach (var g in KernelTypes.Locks.GuardedBy(lockField).Where(g => g.IsStatic == lockField.IsStatic))
                {
                    if (!IsField(g)) throw new NotTranslated("a guarded member the kernel doesn't have: " + g.Name);
                    var t = Declare("t$" + _temps++, FieldType(g));
                    Emit(new KHavoc { Var = t });
                    _p.Fields.Add(g.OriginalDefinition);
                    Emit(new KFieldStore { Field = g.OriginalDefinition, Instance = owner, OnThis = owner != null, Value = new KVar(t), At = stmt, InstanceAt = stmt });
                }
                foreach (var inv in KernelTypes.Locks.InvariantsOf(lockField))
                    Emit(new KSpecStmt { Spec = InvariantCall(inv, owner), Assume = true, At = stmt, ArgumentAt = stmt });
            }
            else if (lockField != null)
                foreach (var inv in KernelTypes.Locks.InvariantsOf(lockField))
                    Emit(new KCheck { Cond = InvariantCall(inv, owner), Id = "CSV1024", At = stmt, Message = $"the invariant of lock '{lockField.Name}' might not hold when it is released" });
        }

        /// <summary>This object, a local or a parameter assigned nowhere in the method, or a field of one: the same object while a lock of it is held.</summary>
        private bool Fixed(IOperation op)
        {
            while (op is IConversionOperation { IsImplicit: true } c) op = c.Operand;
            return op switch
            {
                IInstanceReferenceOperation _ => true,
                ILocalReferenceOperation l => NeverWritten(l.Local) || l.Local.DeclaringSyntaxReferences.Length == 1 && OnlyDeclared(l.Local),
                IParameterReferenceOperation p => NeverWritten(p.Parameter),
                IFieldReferenceOperation f => (f.Field.IsReadOnly || f.Field.IsConst) && (f.Instance == null || Fixed(f.Instance)),
                _ => false,
            };
        }

        private bool OnlyDeclared(ILocalSymbol l) =>
            !_decl.DescendantNodes().OfType<AssignmentExpressionSyntax>().Any(a => a.Left is IdentifierNameSyntax n && n.Identifier.Text == l.Name && SymbolEqualityComparer.Default.Equals(_model.GetSymbolInfo(n).Symbol, l));

        /// <summary>An owner as written (null: this), as a value in a specification.</summary>
        private KExpr OwnerValue(ExpressionSyntax owner)
        {
            if (owner == null) return new KVar("this");
            var op = _model.GetOperation(owner);
            while (op is IConversionOperation { IsImplicit: true } c) op = c.Operand;
            while (op is IParenthesizedOperation p) op = p.Operand;
            return op != null && Fixed(op) ? Spec(op, null) : throw new NotTranslated("a lock's owner that may change: " + owner);
        }

        private KExpr KeyOf(IFieldSymbol key, KExpr owner)
        {
            _p.Fields.Add(key.OriginalDefinition);
            return new KField { Field = key.OriginalDefinition, Instance = owner, At = _decl, InstanceAt = _decl };
        }

        /// <summary>
        /// A lock taken while another of its field or class is held (Account's Lock of from, then of to): in increasing
        /// order of its OrderedBy id (CSV1025), as CsVerify's engine proves it. Which locks are held is its static analysis's.
        /// </summary>
        private void ProveOrderAt(SyntaxNode stmt)
        {
            var levels = KernelTypes.Levels;
            if (levels == null) return;
            var a = levels.AcquiredAt(stmt, _model);
            if (a?.Lock == null || a.Element || a.Static || !(LockLevels.OrderedBy(a.Lock) is IFieldSymbol key)) return;
            if (!(key.IsReadOnly || key.IsConst)) throw new NotTranslated("a lock ordered by what may change");
            foreach (var h in levels.HeldAt(a.At, _decl, _model))
            {
                if (h == null || !SymbolEqualityComparer.Default.Equals(h.Lock, a.Lock) || h.Element || h.Receiver == a.Receiver) continue;
                Emit(new KCheck { Cond = new KOp("<", KeyOf(key, OwnerValue(h.Owner)), KeyOf(key, OwnerValue(a.Owner))), Id = "CSV1025", At = a.At, NotAssumedAfter = true,
                                  Message = $"'{a.Receiver}''s '{a.Lock.Name}' might not come after '{h.Receiver}''s by '{key.Name}': two of them taken in different orders can deadlock" });
            }
        }

        // ------------------------------------------------------------------ atomic fields

        private KExpr Step(ISymbol field, KExpr old, KExpr now)
        {
            var step = Atomics.StepOf(field)?.OriginalDefinition;
            if (step == null) return null;
            if (!_isFunction(step)) throw new NotTranslated("an atomic field's step that isn't a function: " + step.Name);
            return new KOp("||", new KOp("==", old, now), new KFnCall { Callee = step, Args = new[] { old, now }, At = _decl });
        }

        /// <summary>
        /// The others take their steps: the field at the object is now the same as this thread last knew, or a step on;
        /// this thread now knows that value.
        /// </summary>
        private KExpr OthersStep(ISymbol field, KExpr o, bool onThis, SyntaxNode at)
        {
            var now = Declare("t$" + _temps++, FieldType(field));
            Emit(new KHavoc { Var = now });
            var last = new KField { Field = field, Instance = o, OnThis = onThis, At = at, InstanceAt = at };
            if (Step(field, last, new KVar(now)) is KExpr step) Emit(new KSpecStmt { Spec = step, Assume = true, At = at, ArgumentAt = at });
            Emit(new KFieldStore { Field = field, Instance = o, OnThis = onThis, Value = new KVar(now), At = at, InstanceAt = at });
            return new KVar(now);
        }

        private KExpr AtomicRead(ISymbol field, KExpr o, bool onThis, SyntaxNode at)
        {
            if (field is IFieldSymbol { IsVolatile: false })
                Emit(new KCheck { Cond = new KLit("false"), Id = "CSV1030", At = at, NotAssumedAfter = true,
                                  Message = $"'{at}' reads [Atomic] '{field.Name}' plainly, which the compiler may reorder or keep from an earlier read: declare it volatile, or read it with Volatile.Read or Interlocked" });
            return OthersStep(field, o, onThis, at);
        }

        /// <summary>A plain write: one step from whatever the others have made it, which this thread doesn't read first (CSV1030).</summary>
        private KExpr AtomicWrite(ISymbol field, KExpr o, bool onThis, KExpr v, SyntaxNode at)
        {
            if (field is IFieldSymbol { IsVolatile: false })
                Emit(new KCheck { Cond = new KLit("false"), Id = "CSV1030", At = at, NotAssumedAfter = true,
                                  Message = $"'{at}' writes [Atomic] '{field.Name}' plainly, which the compiler may reorder: declare it volatile, or write it with Volatile.Write or Interlocked" });
            var written = Declare("t$" + _temps++, FieldType(field));
            Emit(new KAssign { Var = written, Value = v });
            var cur = OthersStep(field, o, onThis, at);
            if (Step(field, cur, new KVar(written)) is KExpr step)
                Emit(new KCheck { Cond = step, Id = "CSV1030", At = at,
                                  Message = $"this write of [Atomic] '{field.Name}' might not be a step from what it overwrites, which another thread may have changed since this one read it: write it with Interlocked.CompareExchange, or a value any it could replace allows" });
            return new KVar(written);
        }

        /// <summary>Volatile.Read/Write and Interlocked's operations on an atomic field: each one step after the others'; what it writes, a step (CSV1030).</summary>
        private KExpr AtomicCall(IInvocationOperation inv)
        {
            var ordered = inv.Arguments.OrderBy(a => a.Parameter.Ordinal).ToList();
            var target = ordered[0].Value is IFlowCaptureReferenceOperation c && _captured.TryGetValue(c.Id, out var cv) ? cv : ordered[0].Value;
            if (!(Unconverted(target) is IFieldReferenceOperation fr) || !Atomics.IsAtomic(fr.Field)) throw new NotTranslated("Interlocked of a field that isn't atomic");
            var (field, o, onThis, _) = FieldOf(fr);
            // (each argument evaluated, in a variable of its own: the checks below are of values)
            var args = ordered.Skip(1).Select(a =>
            {
                var t = Declare("t$" + _temps++, a.Value.Type);
                Emit(new KAssign { Var = t, Value = Expr(a.Value) });
                return (KExpr)new KVar(t);
            }).ToArray();
            var type = FieldType(field);
            var cur = OthersStep(field, o, onThis, inv.Syntax);
            string what = $"'{inv.Syntax}' might not be a step of [Atomic] '{field.Name}'";
            void Write(KExpr v, KExpr when = null)
            {
                if (Step(field, cur, v) is KExpr step)
                    Emit(new KCheck { Cond = when == null ? step : new KOp("==>", when, step), Id = "CSV1030", At = inv.Syntax, Message = what });
                Emit(new KFieldStore { Field = field, Instance = o, OnThis = onThis, Value = when == null ? v : new KOp("ite", when, v, cur), At = inv.Syntax, InstanceAt = inv.Syntax });
            }
            var name = (inv.TargetMethod.ContainingType.Name == "Volatile" ? "Volatile." : "") + inv.TargetMethod.Name;
            switch (name)
            {
                case "Volatile.Read": case "Read": return cur;
                case "Volatile.Write": Write(args[0]); return null;
                case "Increment": case "Decrement": case "Add":
                {
                    // (wrapping at the type's ends, as at run time)
                    var delta = name == "Increment" ? new KLit("1") : name == "Decrement" ? new KLit("(-1)") : args[0];
                    var t = Declare("t$" + _temps++, type);
                    Emit(new KAssign { Var = t, Value = new KArith { Op = "+", Left = cur, Right = delta, Type = type, Mode = KMode.Unchecked, At = inv.Syntax } });
                    Write(new KVar(t));
                    return new KVar(t);
                }
                case "Exchange": Write(args[0]); return cur;
                case "CompareExchange": Write(args[0], new KOp("==", cur, args[1])); return cur;
                default: throw new NotTranslated(name + " of an atomic field");
            }
        }

        // ------------------------------------------------------------------ gates and concurrent code

        /// <summary>A SemaphoreSlim of count 1 that is this object's field (or a static one) and guards state: a lock that can be held across awaits.</summary>
        private IFieldSymbol GateOf(IInvocationOperation call)
        {
            if (!(Unconverted(call.Instance) is IFieldReferenceOperation { Field: IFieldSymbol gate } fr) || !(gate.IsStatic || fr.Instance is IInstanceReferenceOperation) ||
                KernelTypes.Locks == null || !KernelTypes.Locks.IsMutexGate(gate))
                throw new NotTranslated("a semaphore other than this object's gate");
            var at = call.Syntax;
            // (taking one while it's held waits for itself: CsVerify's engine's static checks report it, CSV1025)
            // (taken inside another lock: in order of levels, CsVerify's engine's static checks say)
            return gate;
        }

        /// <summary>Taking a gate: what it guards is forgotten (others have had it), and its invariants hold.</summary>
        private void Take(IFieldSymbol gate, SyntaxNode at)
        {
            var owner = gate.IsStatic ? null : (KExpr)new KVar("this");
            foreach (var g in KernelTypes.Locks.GuardedBy(gate).Where(g => g.IsStatic == gate.IsStatic))
            {
                if (!IsField(g)) throw new NotTranslated("a guarded member the kernel doesn't have: " + g.Name);
                var t = Declare("t$" + _temps++, FieldType(g));
                Emit(new KHavoc { Var = t });
                _p.Fields.Add(g.OriginalDefinition);
                Emit(new KFieldStore { Field = g.OriginalDefinition, Instance = owner, OnThis = owner != null, Value = new KVar(t), At = at, InstanceAt = at });
            }
            foreach (var inv in KernelTypes.Locks.InvariantsOf(gate))
                Emit(new KSpecStmt { Spec = InvariantCall(inv, owner), Assume = true, At = at, ArgumentAt = at });
        }

        /// <summary>Giving a gate back: its invariants must hold (CSV1024).</summary>
        private void Give(IFieldSymbol gate, SyntaxNode at)
        {
            var owner = gate.IsStatic ? null : (KExpr)new KVar("this");
            foreach (var inv in KernelTypes.Locks.InvariantsOf(gate))
                Emit(new KCheck { Cond = InvariantCall(inv, owner), Id = "CSV1024", At = at, Message = $"the invariant of lock '{gate.Name}' might not hold when it is released" });
        }

        /// <summary>The gates held at a point: the try of 'await g.WaitAsync(); try { here } finally { g.Release(); }'.</summary>
        private IEnumerable<IFieldSymbol> GatesHeld(SyntaxNode at)
        {
            if (KernelTypes.Locks == null) yield break;
            foreach (var t in at.Ancestors().OfType<TryStatementSyntax>().Where(t => _decl.Span.Contains(t.Span) && t.Block.Span.Contains(at.Span)))
                if (KernelTypes.Locks.GateOfTry(t, _model) is IFieldSymbol g) yield return g;
        }

        private bool Concurrent => KernelTypes.Started != null && KernelTypes.Started.RunsAlongside(_m) && !_p.Ghost;

        /// <summary>
        /// A field used by code that runs alongside other code: it never changes, a lock guards it (CsVerify's engine's
        /// static checks have their say), or its object is in hand (a confined local's, or the one a constructor is
        /// building); otherwise another could be writing it (CSV1027).
        /// </summary>
        private void Held(ISymbol field, KExpr o, SyntaxNode at)
        {
            if (!Concurrent || InSpec(at) || KernelTypes.Locks?.GuardOf(field) != null || Atomics.IsAtomic(field)) return;
            if (field is IFieldSymbol x ? x.IsReadOnly || x.IsConst : field is IPropertySymbol p && (p.SetMethod == null || p.SetMethod.IsInitOnly)) return;
            string fix = "guard it with a lock, hold a Spec.Acc for it (the class must be [Owned]), or make it [Atomic]";
            if (o == null)
            {
                Emit(new KCheck { Cond = new KLit("false"), Id = "CSV1027", At = at, NotAssumedAfter = true, Message = $"'{at}' is static, with no lock, and this runs alongside other code: {fix}" });
                return;
            }
            if (_p.IsCtor && o is KVar { Name: "this" }) return;
            // (an [Owned] object's field, under permissions: checked as permissions are)
            if (IsOwnedField(field) && _p.UsesPerm) return;
            Emit(new KCheck { Cond = InHand(o), Id = "CSV1027", At = at, NotAssumedAfter = true,
                              Message = $"'{at}' has no lock and no permission here, and this runs alongside other code that could be using it: {fix}" });
        }

        private void HeldCell(KExpr array, SyntaxNode at, bool write)
        {
            // (under cell permissions, they say: checked as any cell is, CSV1016)
            if (!Concurrent || InSpec(at) || _p.UsesPerm || _p.UsesCells || _p.ArrayMode) return;
            Emit(new KCheck { Cond = InHand(array), Id = "CSV1027", At = at, NotAssumedAfter = true,
                              Message = write ? $"'{at}' writes an array this code has no Spec.Acc for, and it runs alongside other code that could be using it"
                                              : $"'{at}' reads an array this code has no Spec.Acc or Spec.AccRead for, and it runs alongside other code that could be writing it" });
        }

        /// <summary>An object only this code has: a confined local's.</summary>
        private KExpr InHand(KExpr o) =>
            Confined().Select(l => (KExpr)new KOp("==", o, new KVar(Declare(Local(l), l.Type)))).DefaultIfEmpty(new KLit("false")).Aggregate((a, b) => new KOp("||", a, b));

        /// <summary>A call while a lock is held, of what may take it again (or other locks, in an order not translated yet): not yet.</summary>
        private void UnderLock(IMethodSymbol callee, SyntaxNode at, IOperation instance, IReadOnlyList<IArgumentOperation> arguments)
        {
            if (at == null || KernelTypes.Levels == null || _contractOf?.Invoke(callee) is Contract c && (c.IsPure || c.IsLemma)) return;
            var held = KernelTypes.Levels.HeldAt(at, _decl, _model).Where(h => h?.Lock != null).ToList();
            if (held.Count == 0) return;
            foreach (var t in KernelTypes.Levels.OfCall(at, _model, _m).Taken)
                foreach (var h in held.Where(h => SymbolEqualityComparer.Default.Equals(h.Lock, t.Lock) && !t.Element))
                {
                    // (another object's: in increasing order of id, proved at the call; the same one's, taken again: not yet)
                    if (!(t.Origin is LockLevels.Origin { AtCall: true } o) || !(LockLevels.OrderedBy(t.Lock) is IFieldSymbol key) || h.Static)
                        throw new NotTranslated("a call under a lock that may take it again");
                    var given = o.Index < 0 ? instance : arguments.FirstOrDefault(x => x.Parameter?.Ordinal == o.Index)?.Value;
                    while (given is IConversionOperation { IsImplicit: true } cv) given = cv.Operand;
                    if (given == null || given.Syntax.ToString() == h.Receiver || !Fixed(given)) throw new NotTranslated("a call under a lock that may take it again");
                    if (!(key.IsReadOnly || key.IsConst)) throw new NotTranslated("a lock ordered by what may change");
                    Emit(new KCheck { Cond = new KOp("<", KeyOf(key, OwnerValue(h.Owner)), KeyOf(key, Spec(given, null))), Id = "CSV1025", At = at, NotAssumedAfter = true,
                                      Message = $"'{at}' takes '{t.Lock.Name}' (in '{t.In?.Name}') of '{given.Syntax}', which might not come after '{h.Receiver}''s by '{key.Name}': two of them taken in different orders can deadlock" });
                }
        }

        // ------------------------------------------------------------------ async

        private bool _awaiting;

        /// <summary>
        /// await t: other code may run, so what the method doesn't hold is forgotten (all but its confined locals'
        /// objects). An awaited async method of the program is a call, its contract of the task's result; a library's
        /// Task.Yield, Task.Delay, Task.CompletedTask gives nothing. ConfigureAwait is seen through.
        /// </summary>
        private KExpr Await(IAwaitOperation aw)
        {
            if (_p.Ghost || _contract.IsPure || _contract.IsLemma) throw new NotTranslated("an await in a proof");
            if (_p.UsesPerm) throw new NotTranslated("an await with permissions");
            var op = aw.Operation;
            IFieldSymbol gate = null;
            while (op is IInvocationOperation ca && ca.TargetMethod.Name == "ConfigureAwait" && ca.Instance != null) op = ca.Instance;
            KExpr value = null;
            switch (op)
            {
                case ILocalReferenceOperation tl when _tasks.TryGetValue(tl.Local, out var task):
                    Emit(new KAssign { Var = task.Awaited, Value = new KLit("true") });
                    value = task.Result == null ? null : new KVar(task.Result);
                    break;
                case IInvocationOperation all when all.TargetMethod.ContainingType?.ToDisplayString() == "System.Threading.Tasks.Task" && all.TargetMethod.Name == "WhenAll" &&
                                                   (aw.Parent is IExpressionStatementOperation || aw.Parent == null):
                    foreach (var a in all.Arguments.SelectMany(x => x.Value is IArrayCreationOperation ac ? ac.Initializer?.ElementValues.AsEnumerable() ?? new IOperation[0]
                                                                  : x.Value is ICollectionExpressionOperation ce ? ce.Elements.AsEnumerable() : new[] { x.Value }))
                        if (Unconverted(a is IFlowCaptureReferenceOperation wc && _captured.TryGetValue(wc.Id, out var wv) ? wv : a) is ILocalReferenceOperation wl &&
                            _tasks.TryGetValue(wl.Local, out var wt)) Emit(new KAssign { Var = wt.Awaited, Value = new KLit("true") });
                        else throw new NotTranslated("Task.WhenAll of a task not started here");
                    break;
                case IInvocationOperation call when call.TargetMethod.IsAsync && call.TargetMethod.DeclaringSyntaxReferences.Length > 0:
                    _awaiting = true;
                    try { value = Call(call); }
                    finally { _awaiting = false; }
                    break;
                case IInvocationOperation wait when IsSemaphore(wait.TargetMethod.ContainingType) && wait.TargetMethod.Name == "WaitAsync" && wait.Arguments.All(a => IsToken(a.Value.Type)):
                    gate = GateOf(wait);
                    break;
                case IInvocationOperation lib when lib.TargetMethod.ContainingType?.ToDisplayString() == "System.Threading.Tasks.Task" && lib.TargetMethod.Name is "Yield" or "Delay":
                    foreach (var a in lib.Arguments.Select(x => x.Value))
                        if (InSubset(a.Type)) Expr(a);
                        else if (!(Unconverted(a) is IParameterReferenceOperation or ILocalReferenceOperation)) throw new NotTranslated("an argument of " + lib.TargetMethod.Name);
                    break;
                case IPropertyReferenceOperation { Property.Name: "CompletedTask" } done when done.Property.ContainingType?.ToDisplayString() == "System.Threading.Tasks.Task":
                    break;
                default: throw new NotTranslated("an await of " + op.Syntax);
            }
            _p.Awaits = true;
            _p.CallsDelegates = true;
            // (what a gate held here guards stays, as nobody else can have it)
            var kept = new List<(ISymbol field, string var)>();
            foreach (var g in GatesHeld(aw.Syntax))
                foreach (var f in KernelTypes.Locks.GuardedBy(g).Where(f => !f.IsStatic && IsField(f)))
                {
                    var t = Declare("t$" + _temps++, FieldType(f));
                    _p.Fields.Add(f.OriginalDefinition);
                    Emit(new KAssign { Var = t, Value = new KField { Field = f.OriginalDefinition, Instance = new KVar("this"), OnThis = true, At = aw.Syntax, InstanceAt = aw.Syntax } });
                    kept.Add((f.OriginalDefinition, t));
                }
            var keep = new KAwait();
            if (!_opaque) foreach (var l in Confined()) keep.Keep.Add(Declare(Local(l), l.Type));
            Emit(keep);
            foreach (var (f, t) in kept)
                Emit(new KAssume { Cond = new KOp("==", new KField { Field = f, Instance = new KVar("this"), OnThis = true, At = aw.Syntax, InstanceAt = aw.Syntax }, new KVar(t)) });
            ForgetCaptured();
            // (where exceptions are seen: a library's await may throw, a cancellation say)
            if (!(op is IInvocationOperation awaited && awaited.TargetMethod.IsAsync && awaited.TargetMethod.DeclaringSyntaxReferences.Length > 0) &&
                _cfgBlock != null && ThrowTarget(_cfgBlock.EnclosingRegion) is string target)
                Emit(new KFork { Overflow = new KLit("false"), Target = target, Exception = null });
            if (gate != null) Take(gate, aw.Syntax);
            return value;
        }

        /// <summary>A task started and kept in a local, awaited later: whether it has been, and its result.</summary>
        private sealed class Task
        {
            public IMethodSymbol Method;
            public string Awaited, Result;
            public SyntaxNode At;
            /// <summary>A thread, or a task of code of its own: not reported if never finished.</summary>
            public bool Thread;
        }

        private readonly Dictionary<ILocalSymbol, Task> _tasks = new Dictionary<ILocalSymbol, Task>(SymbolEqualityComparer.Default);

        /// <summary>
        /// var t = F(...): F's precondition is checked here, and what it gives is the task's result, known once it's
        /// awaited; t is used only by await t, Task.WhenAll and t.Result, and never assigned again.
        /// </summary>
        private void Start(ILocalSymbol local, IInvocationOperation call, bool thread = false)
        {
            if (_tasks.ContainsKey(local)) throw new NotTranslated("a task local assigned again");
            foreach (var id in _decl.DescendantNodes().OfType<IdentifierNameSyntax>().Where(i => i.Identifier.Text == local.Name && SymbolEqualityComparer.Default.Equals(_model.GetSymbolInfo(i).Symbol, local)))
            {
                SyntaxNode e = id;
                while (e.Parent is ParenthesizedExpressionSyntax) e = e.Parent;
                bool ok = thread ? e.Parent is MemberAccessExpressionSyntax tm && tm.Name.Identifier.Text is "Start" or "Join" || e.Parent is VariableDeclaratorSyntax || e is VariableDeclaratorSyntax
                        : e.Parent is AwaitExpressionSyntax || e.Parent is MemberAccessExpressionSyntax ma && ma.Name.Identifier.Text == "Result" ||
                          e.Parent is ArgumentSyntax arg && arg.Parent?.Parent is InvocationExpressionSyntax wa && wa.Expression.ToString().EndsWith("WhenAll");
                if (!ok || id.Ancestors().Any(a => a is AnonymousFunctionExpressionSyntax || a is LocalFunctionStatementSyntax)) throw new NotTranslated("a task used otherwise than awaited: " + local.Name);
            }
            KExpr result = null;
            if (call != null)
            {
                _awaiting = true;
                try { result = Call(call); }
                finally { _awaiting = false; }
                if (_p.UsesPerm) throw new NotTranslated("a task with permissions");
            }
            // (of code of its own: what it gives isn't known, and it may reach anything, a confined local's object too)
            if (call == null && local.Type is INamedTypeSymbol { Arity: 1 } tt && InSubset(tt.TypeArguments[0]))
            {
                var unknown = Declare("t$" + _temps++, tt.TypeArguments[0]);
                Emit(new KHavoc { Var = unknown });
                result = new KVar(unknown);
            }
            if (call == null) _opaque = true;
            var task = new Task { Method = call?.TargetMethod, At = call?.Syntax, Result = (result as KVar)?.Name, Thread = thread || call == null,
                                  Awaited = Declare($"aw${_tasks.Count}", _model.Compilation.GetSpecialType(SpecialType.System_Boolean)) };
            if (result != null && task.Result == null) { task.Result = Declare("t$" + _temps++, Returns(call.TargetMethod)); Emit(new KAssign { Var = task.Result, Value = result }); }
            Emit(new KAssign { Var = task.Awaited, Value = new KLit("false") });
            _tasks[local] = task;
        }

        /// <summary>A task of code of its own was started: no object is in hand from then on.</summary>
        private bool _opaque;

        private static AnonymousFunctionExpressionSyntax LambdaSyntax(IArgumentOperation a) =>
            (a.Syntax as ArgumentSyntax)?.Expression as AnonymousFunctionExpressionSyntax ?? a.Value.Syntax as AnonymousFunctionExpressionSyntax;

        private readonly Dictionary<ILocalSymbol, AnonymousFunctionExpressionSyntax> _threads = new Dictionary<ILocalSymbol, AnonymousFunctionExpressionSyntax>(SymbolEqualityComparer.Default);

        /// <summary>The one call a started lambda is, with values that don't change (proved where it starts); null for any other lambda.</summary>
        private IInvocationOperation StartedCall(AnonymousFunctionExpressionSyntax lambda)
        {
            var call = KernelTypes.Started?.CallOf(lambda);
            if (call == null)
            {
                // (code of its own, verified on its own: what it may change, anything)
                if (lambda.AsyncKeyword.IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.AsyncKeyword)) throw new NotTranslated("an async lambda started");
                return null;
            }
            return _model.GetOperation(call) as IInvocationOperation ?? throw new NotTranslated("a started call without its operation");
        }

        private void TasksAwaited(KBlock at)
        {
            foreach (var t in _tasks.Values.Where(t => !t.Thread))
                at.Stmts.Add(new KCheck { Cond = new KVar(t.Awaited), Id = "CSV1026", At = t.At, NotAssumedAfter = true,
                                          Message = $"the task of '{t.Method.Name}' might not be awaited on every path: a failure in it would be lost" });
        }

        private int _keeps;

        /// <summary>Between two statements, while a task started here may still be running: other code may change what the method doesn't hold.</summary>
        private void Alongside()
        {
            _p.Awaits = true;
            _p.CallsDelegates = true;
            var running = _tasks.Values.Select(t => (KExpr)new KOp("!", new KVar(t.Awaited))).Aggregate((a, b) => new KOp("||", a, b));
            var k = new KAwait { When = running };
            if (!_opaque) foreach (var l in Confined()) k.Keep.Add(Declare(Local(l), l.Type));
            Emit(k);
        }

        /// <summary>t.Result: of a task that has finished (else it blocks, CSV1026).</summary>
        private KExpr ResultOf(Task task, SyntaxNode at)
        {
            Emit(new KCheck { Cond = new KVar(task.Awaited), Id = "CSV1026", At = at, NotAssumedAfter = true,
                              Message = $"the task of '{task.Method.Name}' might not have finished: reading Result blocks until it does, and that can deadlock (await it first)" });
            return task.Result == null ? throw new NotTranslated("the Result of a task of nothing") : new KVar(task.Result);
        }

        private List<ILocalSymbol> _confined;

        /// <summary>
        /// The locals that only ever hold objects the method made itself, used only in ways that can't hand them to other
        /// code: no code that runs at an await can reach their objects.
        /// </summary>
        private List<ILocalSymbol> Confined()
        {
            if (_confined != null) return _confined;
            _confined = new List<ILocalSymbol>();
            if (_decl == null) return _confined;
            var locals = _decl.DescendantNodes().OfType<VariableDeclaratorSyntax>().Select(d => _model.GetDeclaredSymbol(d) as ILocalSymbol).Where(l => l != null).ToList();
            foreach (var l in locals.Where(l => IsClass(l.Type) || IsArray(l.Type)))
            {
                bool ok = true;
                foreach (var d in l.DeclaringSyntaxReferences.Select(r => r.GetSyntax()).OfType<VariableDeclaratorSyntax>())
                    if (d.Initializer != null && !Fresh(d.Initializer.Value)) ok = false;
                foreach (var id in _decl.DescendantNodes().OfType<IdentifierNameSyntax>().Where(i => i.Identifier.Text == l.Name && SymbolEqualityComparer.Default.Equals(_model.GetSymbolInfo(i).Symbol, l)))
                {
                    if (id.Ancestors().Any(a => a is AnonymousFunctionExpressionSyntax || a is LocalFunctionStatementSyntax)) { ok = false; break; }
                    switch (id.Parent)
                    {
                        case MemberAccessExpressionSyntax ma when ma.Expression == id && _model.GetSymbolInfo(ma.Name).Symbol is IFieldSymbol or IPropertySymbol: continue;
                        case ElementAccessExpressionSyntax ea when ea.Expression == id: continue;
                        case BinaryExpressionSyntax be when (be.IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.EqualsExpression) || be.IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.NotEqualsExpression)) &&
                                                          (be.Left.IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.NullLiteralExpression) || be.Right.IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.NullLiteralExpression)): continue;
                        case AssignmentExpressionSyntax asg when asg.Left == id && Fresh(asg.Right): continue;
                        case ArgumentSyntax arg when InSpec(arg): continue;
                        case ReturnStatementSyntax _: continue;
                        default: ok = false; break;
                    }
                    if (!ok) break;
                }
                if (ok) _confined.Add(l);
            }
            return _confined;
        }

        /// <summary>A new array, or a new object of a program class whose construction doesn't let it out (it calls nothing, and uses this only for its fields).</summary>
        private bool Fresh(ExpressionSyntax e)
        {
            if (e is ArrayCreationExpressionSyntax || e is ImplicitArrayCreationExpressionSyntax) return true;
            if (!(e is BaseObjectCreationExpressionSyntax oc) || !(_model.GetSymbolInfo(oc).Symbol is IMethodSymbol ctor) || !IsClass(ctor.ContainingType)) return false;
            if (ctor.ContainingType.BaseType?.SpecialType != SpecialType.System_Object) return false;
            var code = ctor.DeclaringSyntaxReferences.Select(r => r.GetSyntax())
                .Concat(ctor.ContainingType.GetMembers().Where(m => !m.IsStatic).SelectMany(m => m.DeclaringSyntaxReferences).Select(r => r.GetSyntax()).OfType<VariableDeclaratorSyntax>());
            foreach (var n in code.SelectMany(c => c.DescendantNodesAndSelf()))
            {
                if (n is InvocationExpressionSyntax inv && !(inv.Expression.ToString() is "nameof") && !inv.Expression.ToString().StartsWith("Spec.")) return false;
                if (n is ThisExpressionSyntax t && !(t.Parent is MemberAccessExpressionSyntax)) return false;
            }
            return true;
        }

        // ------------------------------------------------------------------ data types

        /// <summary>Pattern variables in a specification: what they are bound to.</summary>
        private readonly Dictionary<ILocalSymbol, KExpr> _bound = new Dictionary<ILocalSymbol, KExpr>(SymbolEqualityComparer.Default);

        /// <summary>(a call's declared result type, where it's a local's: for unboxing)</summary>
        private ITypeSymbol _resultType;

        private void BindInCode(ILocalSymbol l, KExpr v) => Emit(new KAssign { Var = Declare(Local(l), l.Type), Value = v });

        /// <summary>A measure: a number, or a data value's rank (how deep it is).</summary>
        private KExpr Measure(IOperation d)
        {
            var v = Spec(d, null);
            return IsData(d.Type) ? new KOp("$rank", v) : v;
        }

        /// <summary>A value of a type with invariants: valid (where it isn't null).</summary>
        private void AssumeValid(KExpr v, ITypeSymbol t)
        {
            if (!HasInvariants(t)) return;
            foreach (var inv in DataTypes.Invariants(DataTypes.Def(t))) InvariantBody(inv.OriginalDefinition, _isFunction, _literal, _contractOf);
            Data(t);
            _p.Valid.Add(DataTypes.Def(t));
            Emit(new KAssume { Cond = new KOp("||", new KOp("==", v, new KLit("null")), new KOp(ValidName(t), v)) });
        }

        private void Data(ITypeSymbol t)
        {
            var def = DataTypes.Def(t);
            _p.DataTypes.Add(def);
            foreach (var c in KernelTypes.Data.Cases(def)) _p.DataTypes.Add(c);
        }

        /// <summary>A positional property as the type it's read at has it (its own or a base's).</summary>
        private static IPropertySymbol Actual(ITypeSymbol t, string name)
        {
            for (var s = t as INamedTypeSymbol; s != null; s = s.BaseType)
                if (s.GetMembers(name).OfType<IPropertySymbol>().FirstOrDefault() is IPropertySymbol p) return p;
            return null;
        }

        /// <summary>A data value's field, as the type it's read at has it (unboxed where generic).</summary>
        private KExpr FieldOfData(KExpr v, IPropertySymbol prop, ITypeSymbol at) =>
            Unbox(new KOp(FieldFunction(prop), v), prop.OriginalDefinition.Type, Actual(at, prop.Name)?.Type ?? prop.Type);

        /// <summary>
        /// The data types' operations, in code or in a specification (each lowers its operands its own way): a case's
        /// construction, a field's read, type tests and patterns, casts, a record's ==; null where it is none.
        /// </summary>
        private KExpr DataExpr(IOperation e, Func<IOperation, KExpr> lower, Action<ILocalSymbol, KExpr> bind, bool inSpec = false)
        {
            switch (e)
            {
                case IObjectCreationOperation oc when IsData(oc.Type) && oc.Initializer == null && oc.Constructor != null:
                {
                    Data(oc.Type);
                    var ordered = oc.Arguments.OrderBy(a => a.Parameter.Ordinal).ToList();
                    var values = inSpec ? ordered.Select(a => lower(a.Value)).ToArray() : Operands(ordered.Select(a => a.Value).ToArray());
                    var def = oc.Constructor.OriginalDefinition;
                    // (a non-nullable field isn't null: each construction says so)
                    if (!inSpec)
                        for (int k = 0; k < ordered.Count; k++)
                            if (IsNullable(def.Parameters[ordered[k].Parameter.Ordinal].Type) && NotNullable(def.Parameters[ordered[k].Parameter.Ordinal].Type))
                                Emit(new KCheck { Cond = new KOp("!=", values[k], new KLit("null")), Id = "CSV1014", At = ordered[k].Value.Syntax,
                                                  Message = $"'{ordered[k].Value.Syntax}' might be null, but parameter '{ordered[k].Parameter.Name}' of '{oc.Type.Name}' is not nullable" });
                    var args = ordered.Select((a, k) => Box(values[k], def.Parameters[a.Parameter.Ordinal].Type, a.Parameter.Type)).ToArray();
                    var made = new KOp(CaseName((INamedTypeSymbol)oc.Type), args);
                    if (inSpec || !HasInvariants(oc.Type)) return made;
                    // (an immutable value's invariants: proved where it's built, assumed everywhere else)
                    var t = Declare("t$" + _temps++, oc.Type);
                    Emit(new KAssign { Var = t, Value = made });
                    foreach (var inv in DataTypes.Invariants(DataTypes.Def(oc.Type)))
                    {
                        if (!_isFunction(inv.OriginalDefinition)) throw new NotTranslated("an invariant that isn't a function: " + inv.Name);
                        Emit(new KCheck { Cond = new KFnCall { Callee = inv.OriginalDefinition, Receiver = new KVar(t), Args = new KExpr[0], At = oc.Syntax }, Id = "CSV1015", At = oc.Syntax,
                                          Message = $"invariant '{inv.Name}' of {oc.Type.Name} might not hold for '{oc.Syntax}'" });
                    }
                    AssumeValid(new KVar(t), oc.Type);
                    return new KVar(t);
                }
                case IPropertyReferenceOperation dp when dp.Instance != null && IsData(dp.Instance.Type) && DataTypes.IsPositional(dp.Property.OriginalDefinition):
                {
                    Data(dp.Instance.Type);
                    var v = lower(dp.Instance);
                    var prop = dp.Property.OriginalDefinition;
                    var read = Unbox(new KDataField { Function = FieldFunction(prop), Value = v, At = dp.Syntax, ValueAt = dp.Instance.Syntax }, prop.Type, dp.Type);
                    if (inSpec || !HasInvariants(dp.Type)) return read;
                    var t = Declare("t$" + _temps++, dp.Type);
                    Emit(new KAssign { Var = t, Value = read });
                    AssumeValid(new KVar(t), dp.Type);
                    return new KVar(t);
                }
                // (a ghost value: the value itself)
                case IInvocationOperation go when SpecSymbols.IsCsVerifyType(go.TargetMethod.ContainingType, "Ghost") && go.TargetMethod.Name == "Of" && go.Arguments.Length == 1:
                    return lower(go.Arguments[0].Value);
                case IPropertyReferenceOperation gv when gv.Property.Name == "Value" && IsGhost(gv.Instance?.Type) &&
                                                         !(gv.Instance is IPropertyReferenceOperation { Property.Name: "Obj" } obj && IsView(obj.Instance?.Type)):
                    return lower(gv.Instance);
                case IIsTypeOperation it when IsData(it.TypeOperand) && !it.IsNegated:
                    Data(it.TypeOperand);
                    return IsCase(Operand(it.ValueOperand, lower, inSpec), it.TypeOperand);
                case IIsPatternOperation ip when IsData(Unconverted(ip.Value).Type) || Scalar(ip.Value.Type):
                {
                    var v = Operand(Unconverted(ip.Value), lower, inSpec);
                    return Pattern(ip.Pattern, v, Unconverted(ip.Value).Type, lower, bind);
                }
                case ISwitchExpressionOperation sw when inSpec:
                {
                    var v = lower(sw.Value);
                    KExpr acc = null;
                    var arms = sw.Arms.Select(arm =>
                    {
                        var cond = Pattern(arm.Pattern, v, sw.Value.Type, lower, bind);
                        if (arm.Guard != null) cond = new KOp("&&", cond, lower(arm.Guard));
                        return (cond, value: lower(arm.Value));
                    }).ToList();
                    // (where no arm matches, the definition throws: its check says so; the value is the last arm's)
                    for (int k = arms.Count - 1; k >= 0; k--) acc = acc == null ? arms[k].value : new KOp("ite", arms[k].cond, arms[k].value, acc);
                    return acc ?? throw new NotTranslated("a switch with no arms");
                }
                case IConversionOperation up when up.IsImplicit && IsData(up.Type) && IsData(up.Operand.Type):
                    return lower(up.Operand);
                case IConversionOperation down when !down.IsImplicit && down.Conversion.IsReference && IsData(down.Type) && IsData(down.Operand.Type):
                {
                    Data(down.Type);
                    var v = Operand(down.Operand, lower, inSpec);
                    if (!inSpec && _cfgBlock != null && ThrowTarget(_cfgBlock.EnclosingRegion) != null) throw new NotTranslated("a cast where exceptions are seen");
                    return new KCast { Value = v, Test = new KOp("||", new KOp("==", v, new KLit("null")), IsCase(v, down.Type)), At = down.Syntax };
                }
                // (a record's == and !=: its values' equality, which is its references', a value being its constructor's)
                case IBinaryOperation eq when eq.OperatorMethod != null && eq.OperatorKind is BinaryOperatorKind.Equals or BinaryOperatorKind.NotEquals &&
                                              IsData(eq.OperatorMethod.ContainingType):
                {
                    if (!KernelTypes.Data.HasValueEquality((INamedTypeSymbol)eq.OperatorMethod.ContainingType)) throw new NotTranslated("== of a record whose fields don't compare as values");
                    var l = lower(eq.LeftOperand);
                    var r = lower(eq.RightOperand);
                    return new KOp(eq.OperatorKind == BinaryOperatorKind.Equals ? "==" : "!=", l, r);
                }
                default: return null;
            }
        }

        /// <summary>An operand that's tested more than once: in code, in a variable of its own.</summary>
        private KExpr Operand(IOperation op, Func<IOperation, KExpr> lower, bool inSpec)
        {
            var v = lower(op);
            if (inSpec || v is KVar || v is KLit) return v;
            var t = Declare("t$" + _temps++, op.Type);
            Emit(new KAssign { Var = t, Value = v });
            return new KVar(t);
        }

        /// <summary>A pattern, as a condition of the value; the variables it declares bound to their parts.</summary>
        private KExpr Pattern(IPatternOperation p, KExpr v, ITypeSymbol type, Func<IOperation, KExpr> lower, Action<ILocalSymbol, KExpr> bind)
        {
            KExpr TypeTest(ITypeSymbol t)
            {
                if (t == null || SymbolEqualityComparer.Default.Equals(DataTypes.Def(t), DataTypes.Def(type)) && !IsData(t)) return new KLit("true");
                if (IsData(t)) { Data(t); return IsCase(v, t); }
                if (Scalar(t) && SymbolEqualityComparer.Default.Equals(t, type)) return new KLit("true");
                throw new NotTranslated("a type test of " + t);
            }
            switch (p)
            {
                case IDiscardPatternOperation _: return new KLit("true");
                case IDeclarationPatternOperation d:
                {
                    if (d.DeclaredSymbol is ILocalSymbol l) bind(l, v);
                    return d.MatchesNull ? new KLit("true") : IsData(d.MatchedType) ? TypeTest(d.MatchedType) : IsNullable(type) ? new KOp("!=", v, new KLit("null")) : new KLit("true");
                }
                case ITypePatternOperation tp: return TypeTest(tp.MatchedType);
                case IConstantPatternOperation cp: return new KOp("==", v, lower(cp.Value));
                case IRelationalPatternOperation rp:
                {
                    var op = rp.OperatorKind switch
                    {
                        BinaryOperatorKind.LessThan => "<", BinaryOperatorKind.LessThanOrEqual => "<=", BinaryOperatorKind.GreaterThan => ">",
                        BinaryOperatorKind.GreaterThanOrEqual => ">=", BinaryOperatorKind.Equals => "==", BinaryOperatorKind.NotEquals => "!=",
                        _ => throw new NotTranslated("the pattern " + rp.Syntax),
                    };
                    return new KOp(op, v, lower(rp.Value));
                }
                case INegatedPatternOperation np: return new KOp("!", Pattern(np.Pattern, v, type, lower, bind));
                case IBinaryPatternOperation bp:
                    return new KOp(bp.OperatorKind == BinaryOperatorKind.And ? "&&" : "||", Pattern(bp.LeftPattern, v, type, lower, bind), Pattern(bp.RightPattern, v, type, lower, bind));
                case IRecursivePatternOperation rp when rp.MatchedType == null || IsData(rp.MatchedType):
                {
                    var matched = rp.MatchedType ?? type;
                    if (!IsData(matched)) throw new NotTranslated("a recursive pattern of " + matched);
                    KExpr cond = TypeTest(matched);
                    if (rp.DeclaredSymbol is ILocalSymbol l) bind(l, v);
                    for (int k = 0; k < rp.DeconstructionSubpatterns.Length; k++)
                    {
                        var prop = DataTypes.PositionalProperty((INamedTypeSymbol)matched, k) ?? throw new NotTranslated("a deconstruction of " + matched);
                        var actual = Actual(matched, prop.Name);
                        cond = new KOp("&&", cond, Pattern(rp.DeconstructionSubpatterns[k], FieldOfData(v, prop, matched), actual?.Type ?? prop.Type, lower, bind));
                    }
                    foreach (var sp in rp.PropertySubpatterns)
                    {
                        if (!(sp.Member is IPropertyReferenceOperation { Property: IPropertySymbol member }) || !DataTypes.IsPositional(member.OriginalDefinition))
                            throw new NotTranslated("a property pattern of " + sp.Member.Syntax);
                        cond = new KOp("&&", cond, Pattern(sp.Pattern, FieldOfData(v, member.OriginalDefinition, matched), member.Type, lower, bind));
                    }
                    return cond;
                }
                default: throw new NotTranslated("the pattern " + p.Kind);
            }
        }

        // ------------------------------------------------------------------ finally

        /// <summary>Each finally's ways on: by the number its continuation variable holds, where to go after it.</summary>
        private readonly Dictionary<ControlFlowRegion, List<(int id, KJump then)>> _finExits = new Dictionary<ControlFlowRegion, List<(int, KJump)>>();
        private readonly List<(ControlFlowRegion fin, KBlock end)> _finEnds = new List<(ControlFlowRegion, KBlock)>();
        private int _edges;

        /// <summary>The finally a block is in (not one of a foreach's enumerator, which isn't there).</summary>
        private ControlFlowRegion FinallyOf(ControlFlowRegion r)
        {
            for (; r != null; r = r.EnclosingRegion)
                if (r.Kind == ControlFlowRegionKind.Finally) return _erased.Contains(r.EnclosingRegion) ? null : r;
            return null;
        }

        private string Continuation(ControlFlowRegion fin) => Declare($"fin${fin.FirstBlockOrdinal}", _model.Compilation.GetSpecialType(SpecialType.System_Int32));

        /// <summary>Runs this finally, then goes on as given.</summary>
        private KJump ThroughFinally(ControlFlowRegion fin, KJump then, int ordinal)
        {
            if (!_finExits.TryGetValue(fin, out var exits)) _finExits[fin] = exits = new List<(int, KJump)>();
            var id = exits.Count;
            exits.Add((id, then));
            var label = $"e${_edges++}";
            _p.Blocks.Add(new KBlock { Label = label, Ordinal = ordinal, Stmts = { new KAssign { Var = Continuation(fin), Value = new KLit(id.ToString()) } }, Jump = new KGoto($"b{fin.FirstBlockOrdinal}") });
            return new KGoto(label);
        }

        /// <summary>A way out of a block: through the finallies it leaves (innermost first), then to where it goes.</summary>
        private KJump Edge(BasicBlock from, ControlFlowBranch branch)
        {
            var target = To(from, branch?.Destination);
            if (branch == null) return target;
            var fins = branch.FinallyRegions.Where(f => !_erased.Contains(f.EnclosingRegion)).ToList();
            for (int k = fins.Count - 1; k >= 0; k--) target = ThroughFinally(fins[k], target, from.Ordinal);
            return target;
        }

        /// <summary>Each finally's end: to each way on, where its continuation says (nowhere, if nothing runs it).</summary>
        private void FinallyEnds()
        {
            foreach (var (fin, end) in _finEnds)
            {
                var exits = _finExits.TryGetValue(fin, out var x) ? x : new List<(int id, KJump then)>();
                if (exits.Count == 0) { end.Jump = new KStop(); continue; }
                var v = Continuation(fin);
                var labels = new List<string>();
                foreach (var (id, then) in exits)
                {
                    var label = $"{end.Label}$f{id}";
                    labels.Add(label);
                    _p.Blocks.Add(new KBlock { Label = label, Ordinal = end.Ordinal, Stmts = { new KAssume { Cond = new KOp("==", new KVar(v), new KLit(id.ToString())) } }, Jump = then });
                }
                end.Jump = new KGoto(labels.ToArray());
            }
        }

        /// <summary>A jump to a block, or a return where it is to the exit.</summary>
        private KJump To(BasicBlock from, BasicBlock to)
        {
            if (to == null) return new KStop();
            if (to.Kind == BasicBlockKind.Exit)
            {
                // (where CsVerify's engine reports a return: the return statement or its value; a return; at its block's
                // last operation; falling off the end, at the method)
                var at = from.BranchValue?.Syntax.Parent as ReturnStatementSyntax as SyntaxNode ?? from.BranchValue?.Syntax ??
                         (from.FallThroughSuccessor?.Semantics == ControlFlowBranchSemantics.Return ? from.Operations.LastOrDefault()?.Syntax : null) ?? _decl;
                return new KReturn { At = at };
            }
            return new KGoto($"b{to.Ordinal}");
        }

        private string Declare(string name, ITypeSymbol type)
        {
            if (!_p.Locals.Any(l => l.Name == name)) _p.Locals.Add(new KLocal { Name = name, Type = type });
            return name;
        }

        /// <summary>
        /// A collection: of the subset's values, or, in a collection member's stub (written over List&lt;T&gt;), the
        /// collection it is for; null for anything else.
        /// </summary>
        private INamedTypeSymbol CollectionOf(ITypeSymbol t)
        {
            if (IsCollection(t)) return (INamedTypeSymbol)t;
            if (CollectionKind(t) != null && ((INamedTypeSymbol)t).TypeArguments.Any(a => a is ITypeParameterSymbol) && _contract.IsStub && IsCollection(_m.ContainingType) &&
                SymbolEqualityComparer.Default.Equals(t.OriginalDefinition, _m.ContainingType.OriginalDefinition))
                return (INamedTypeSymbol)_m.ContainingType;
            return null;
        }

        /// <summary>A type as it is here: in a collection member's stub, its type parameters are the collection's arguments.</summary>
        private ITypeSymbol Actual(ITypeSymbol t) =>
            t is ITypeParameterSymbol tp && _contract.IsStub && IsCollection(_m.ContainingType) && tp.Ordinal < ((INamedTypeSymbol)_m.ContainingType).TypeArguments.Length
                ? ((INamedTypeSymbol)_m.ContainingType).TypeArguments[tp.Ordinal] : t;

        private KExpr Model(string name, INamedTypeSymbol collection, KExpr of)
        {
            var model = ModelOf(name, collection) ?? throw new NotTranslated("the model " + name);
            _p.Models[model.Name] = model;
            return new KOp("sel", new KVar(model.Name), of);
        }

        private readonly Dictionary<CaptureId, IFieldReferenceOperation> _lvalues = new Dictionary<CaptureId, IFieldReferenceOperation>();

        private string Capture(CaptureId id, ITypeSymbol type)
        {
            if (type == null || !InSubset(type)) throw new NotTranslated("a capture of " + type);
            return Declare("c$" + id.GetHashCode(), type);
        }

        /// <summary>A field access's field, its object (null for a static field), whether that is this, and where it is.</summary>
        private (ISymbol field, KExpr instance, bool onThis, SyntaxNode at) FieldOf(IOperation access, IParameterSymbol specResult = null, bool spec = false)
        {
            var (symbol, instance) = access switch
            {
                IFieldReferenceOperation f => ((ISymbol)f.Field, f.Instance),
                IPropertyReferenceOperation p when p.Arguments.Length == 0 => (p.Property, p.Instance),
                _ => throw new NotTranslated(access.Kind.ToString()),
            };
            if (!IsField(symbol)) throw new NotTranslated("the member " + symbol.Name);
            symbol = symbol.OriginalDefinition;
            if (symbol.IsStatic && IsNullable(FieldType(symbol)) && NotNullable(FieldType(symbol))) throw new NotTranslated("a non-nullable static field");
            _p.Fields.Add(symbol);
            var name = (access.Syntax as MemberAccessExpressionSyntax)?.Name ?? access.Syntax;
            if (symbol.IsStatic) { if (!spec) Held(symbol, null, name); return (symbol, null, false, null); }
            if (instance is IInstanceReferenceOperation { ReferenceKind: InstanceReferenceKind.ContainingTypeInstance })
            {
                if (!spec) Held(symbol, new KVar("this"), name);
                return (symbol, new KVar("this"), true, instance.Syntax);
            }
            var o = spec ? Spec(instance, specResult) : Expr(instance);
            if (!spec) Held(symbol, o, name);
            return (symbol, o, false, instance.Syntax);
        }

        // ------------------------------------------------------------------ expressions (run time)

        private KMode Mode(SyntaxNode at, bool isChecked) =>
            !isChecked && InUnchecked(at) ? KMode.Unchecked : _p.Ghost ? KMode.Math : isChecked ? KMode.Checked : KMode.Default;

        /// <summary>
        /// Operands, in C#'s order: where a later one is a call (or an allocation), lowered to a statement before the
        /// expression, each earlier one is evaluated into a temporary before it, so its checks (and its reads of
        /// memory) come first, as they do in C#.
        /// </summary>
        private KExpr[] Operands(params IOperation[] ops)
        {
            var values = new KExpr[ops.Length];
            var after = new int[ops.Length];
            for (int k = 0; k < ops.Length; k++)
            {
                values[k] = Expr(ops[k]);
                after[k] = _block.Stmts.Count;
            }
            int end = _block.Stmts.Count;
            for (int k = ops.Length - 2; k >= 0; k--)
            {
                if (after[k] == end || values[k] is KLit || values[k] is KVar || !InSubset(ops[k].Type)) continue;
                var t = Declare("t$" + _temps++, ops[k].Type);
                _block.Stmts.Insert(after[k], new KAssign { Var = t, Value = values[k] });
                values[k] = new KVar(t);
            }
            return values;
        }

        private KExpr Arith(string op, KExpr l, KExpr r, ITypeSymbol type, SyntaxNode at, bool isChecked)
        {
            if (!IsIntegral(type)) throw new NotTranslated("arithmetic on " + type);
            var mode = Mode(at, isChecked);
            // (checked overflow, and MinValue / -1, throw an OverflowException: where exceptions are seen, to the handlers)
            var throwsTo = _cfgBlock != null && (mode == KMode.Checked || op is "/" or "%") && !_codeArith ? ThrowTarget(_cfgBlock.EnclosingRegion) : null;
            if (throwsTo != null) _p.ExceptionTypes.Add(_model.Compilation.GetTypeByMetadataName("System.OverflowException"));
            return new KArith { Op = op, Left = l, Right = r, Type = type, Mode = mode, At = at, ThrowsTo = throwsTo };
        }

        private static string Op(BinaryOperatorKind k) => k switch
        {
            BinaryOperatorKind.Add => "+", BinaryOperatorKind.Subtract => "-", BinaryOperatorKind.Multiply => "*",
            BinaryOperatorKind.Divide => "/", BinaryOperatorKind.Remainder => "%",
            _ => throw new NotTranslated("the operator " + k),
        };

        private KExpr Expr(IOperation e)
        {
            if (DataExpr(e, Expr, BindInCode) is KExpr data) return data;
            if (e is IPropertyReferenceOperation { Property.Name: "Result", Instance: ILocalReferenceOperation resultOf } && _tasks.TryGetValue(resultOf.Local, out var resultTask)) return ResultOf(resultTask, e.Syntax);
            switch (e)
            {
                case { ConstantValue: { HasValue: true } cv } when Scalar(e.Type) || IsNullable(e.Type): return Constant(cv.Value, e.Type);
                case ILocalReferenceOperation l when InSubset(l.Local.Type) && l.Local.RefKind == RefKind.None: return new KVar(Declare(Local(l.Local), l.Local.Type));
                case IParameterReferenceOperation p when InSubset(p.Parameter.Type) && p.Parameter.RefKind is RefKind.None or RefKind.Ref or RefKind.Out: return new KVar(Local(p.Parameter));
                case IInvocationOperation own when SpecSymbols.IsCsVerifyType(own.TargetMethod.ContainingType, "Own"):
                    return Own(own);
                // (a quantifier in code, a [Pure] or ghost function's body: mathematics, its reads checked over its range)
                case IInvocationOperation q when SpecSymbols.IsSpecClass(q.TargetMethod.ContainingType) && q.TargetMethod.Name is "Forall" or "Exists" && q.Arguments.Length == 3:
                    // (read as the source has it: the graph lowers its lambda)
                    return Spec(_model.GetOperation(q.Syntax) as IInvocationOperation ?? q, null);
                case IInvocationOperation mv when mv.TargetMethod.Name == "MoveNext" && mv.Instance is IFlowCaptureReferenceOperation ev && _forEach.TryGetValue(ev.Id, out var fv) && fv.Version != null:
                {
                    // (the list may not have changed since: MoveNext throws if it has; whether there's another, unknown)
                    var what = CollectionKind(fv.Collection) switch { "Dictionary" => "dictionary", "HashSet" => "set", "Stack" => "stack", "Queue" => "queue", _ => "list" };
                    Emit(new KCheck { Cond = new KOp("==", new KOp("sel", new KVar(VersionMap), new KVar(fv.Array)), new KVar(fv.Version)), Id = "CSV1001", At = fv.At,
                                      Message = $"the {what} may have changed while it is enumerated: MoveNext would throw InvalidOperationException (collection was modified)" });
                    var more = Declare("t$" + _temps++, _model.Compilation.GetSpecialType(SpecialType.System_Boolean));
                    Emit(new KHavoc { Var = more });
                    return new KVar(more);
                }
                case IInvocationOperation mn when mn.TargetMethod.Name == "MoveNext" && mn.Instance is IFlowCaptureReferenceOperation er && _forEach.TryGetValue(er.Id, out var fm):
                    return new KOp("<", new KVar(fm.Index), LengthOf(fm));
                case IConversionOperation cc when Unconverted(cc) is IPropertyReferenceOperation { Property.Name: "Current", Instance: IFlowCaptureReferenceOperation cr } && _forEach.TryGetValue(cr.Id, out var fcur):
                {
                    var el = Current(fcur);
                    return SymbolEqualityComparer.Default.Equals(cc.Type, fcur.Element) ? el : new KConv { Value = el, From = fcur.Element, To = cc.Type, Mode = KMode.Default, At = cc.Syntax };
                }
                case IPropertyReferenceOperation { Property.Name: "Current", Instance: IFlowCaptureReferenceOperation cr2 } when _forEach.TryGetValue(cr2.Id, out var fcur2):
                    return Current(fcur2);
                case IFlowCaptureReferenceOperation r: return new KVar(Capture(r.Id, r.Type));
                case IInstanceReferenceOperation { ReferenceKind: InstanceReferenceKind.ContainingTypeInstance } when !_p.IsCtor:
                    return new KVar("this");
                // (in a catch: the exception it caught)
                case ICaughtExceptionOperation _:
                    return new KVar("ex$");
                // (a new exception of the library's: its arguments' values aren't kept, only what is in the kernel is checked)
                // (a list: its stub's constructor, which gives a new one)
                case IObjectCreationOperation lo when IsCollection(lo.Type) && lo.Initializer == null && lo.Constructor != null:
                    return Invoke(lo.Constructor, null, lo.Arguments, lo.Syntax, null);
                case IObjectCreationOperation ne when IsException(ne.Type) && ne.Initializer == null:
                {
                    foreach (var a in ne.Arguments.Where(a => InSubset(a.Value.Type) && !(a.Value is IInterpolatedStringOperation))) Expr(a.Value);
                    var t = Declare("t$" + _temps++, ne.Type);
                    _p.ExceptionTypes.Add(ne.Type);
                    Emit(new KNewExc { Var = t, Type = ne.Type });
                    return new KVar(t);
                }
                case IInstanceReferenceOperation _:
                    throw new NotTranslated(_p.IsCtor ? "this, escaping its constructor" : "an instance reference");
                // (a computed property: its getter, called)
                case IPropertyReferenceOperation cp when IsComputed(cp.Property) && cp.Property.GetMethod != null:
                    return Invoke(cp.Property.GetMethod, cp.Instance, cp.Arguments, cp.Syntax, null);
                case IFieldReferenceOperation _:
                case IPropertyReferenceOperation pf when !(pf.Property.Name == "Length" && IsArray(pf.Instance?.Type)) && !IsString(pf.Instance?.Type) && CollectionOf(pf.Instance?.Type) == null && !IsPair(pf.Instance?.Type) && !SpecSymbols.IsCsVerifyType(pf.Instance?.Type, "Seq`1") &&
                                                      !SpecSymbols.IsCsVerifyType(pf.Instance?.Type, "Ghost`1") && !SpecSymbols.IsCsVerifyType(pf.Instance?.Type, "Map`2"):
                {
                    var (field, instance, onThis, instanceAt) = FieldOf(e);
                    if (Atomics.IsAtomic(field) && !(_p.IsCtor && onThis)) return AtomicRead(field, instance, onThis, e.Syntax);
                    return new KField { Field = field, Instance = instance, OnThis = onThis, At = e.Syntax, InstanceAt = instanceAt };
                }
                case IObjectCreationOperation oc when IsClass(oc.Type) && oc.Initializer == null && oc.Constructor != null:
                {
                    var ctor = oc.Constructor.OriginalDefinition;
                    bool isImplicit = ctor.IsImplicitlyDeclared;
                    if (!isImplicit && !_isProcedure(ctor)) throw new NotTranslated("a call of " + oc.Type.Name + "'s constructor");
                    if (!isImplicit) _p.Calls.Add(ctor);
                    var ordered = oc.Arguments.OrderBy(a => a.Parameter.Ordinal).ToList();
                    var args = Operands(ordered.Select(a => a.Value).ToArray());
                    var t = Declare("t$" + _temps++, oc.Type);
                    foreach (var f in InstanceFields(oc.Type)) _p.Fields.Add(f);
                    Emit(new KNewObj { Var = t, Type = oc.Type, Ctor = isImplicit ? null : ctor, Args = args, ArgsAt = ordered.Select(a => a.Value.Syntax).ToArray(), At = oc.Syntax });
                    return new KVar(t);
                }
                case IParenthesizedOperation par: return Expr(par.Operand);
                case IConversionOperation conv when conv.Conversion.IsIdentity || conv.IsImplicit && IsIntegral(conv.Type) && IsIntegral(conv.Operand.Type) && conv.Conversion.IsNumeric:
                    return Expr(conv.Operand);
                case IConversionOperation conv when Upcast(conv):
                    return conv.Operand.ConstantValue.HasValue ? new KLit("null") : Expr(conv.Operand);
                case IConversionOperation conv when IsIntegral(conv.Type) && IsIntegral(conv.Operand.Type) && conv.Conversion.IsNumeric:
                    return new KConv { Value = Expr(conv.Operand), From = conv.Operand.Type, To = conv.Type, Mode = Mode(conv.Syntax, conv.IsChecked), At = conv.Syntax };
                case IUnaryOperation u when u.OperatorKind == UnaryOperatorKind.Not: return new KOp("!", Expr(u.Operand));
                case IUnaryOperation u when u.OperatorKind == UnaryOperatorKind.Plus: return Expr(u.Operand);
                case IUnaryOperation u when u.OperatorKind == UnaryOperatorKind.Minus && IsIntegral(u.Type):
                    return Arith("-", new KLit("0"), Expr(u.Operand), u.Type, u.Syntax, u.IsChecked);
                case IBinaryOperation b when b.OperatorMethod == null && (InSubset(b.LeftOperand.Type) && InSubset(b.RightOperand.Type) ||
                                             b.OperatorKind is BinaryOperatorKind.Equals or BinaryOperatorKind.NotEquals && (RefOperand(b.LeftOperand) || RefOperand(b.RightOperand))):
                    return Binary(b);
                case IArrayElementReferenceOperation el when IsArray(el.ArrayReference.Type) && el.Indices.Length == 1:
                {
                    var v = Operands(el.ArrayReference, el.Indices[0]);
                    HeldCell(v[0], el.Syntax, write: false);
                    return new KElem { Array = v[0], Index = v[1], ArrayType = el.ArrayReference.Type, At = el.Syntax, ArrayAt = el.ArrayReference.Syntax };
                }
                case IPropertyReferenceOperation { Property.Name: "Result", Instance: ILocalReferenceOperation rl } when _tasks.TryGetValue(rl.Local, out var rt):
                    return ResultOf(rt, e.Syntax);
                // (a list's Count and indexer: its stub's getters)
                case IPropertyReferenceOperation kp when IsPair(kp.Instance?.Type) && kp.Property.Name is "Key" or "Value":
                    return Pair(Expr(kp.Instance), kp.Instance.Type, kp.Property.Name);
                case IPropertyReferenceOperation lp when IsCollection(lp.Instance?.Type) && lp.Property.GetMethod != null:
                    return Invoke(lp.Property.GetMethod, lp.Instance, lp.Arguments, lp.Syntax, null);
                case IPropertyReferenceOperation sl when sl.Property.Name == "Length" && IsString(sl.Instance?.Type):
                    return new KLen { String = true, Array = Expr(sl.Instance), At = sl.Syntax, ArrayAt = sl.Instance.Syntax };
                case IPropertyReferenceOperation sc when sc.Property.IsIndexer && IsString(sc.Instance?.Type) && sc.Arguments.Length == 1:
                {
                    var v = Operands(sc.Instance, sc.Arguments[0].Value);
                    return new KElem { String = true, Array = v[0], Index = v[1], At = sc.Syntax, ArrayAt = sc.Instance.Syntax };
                }
                case IBinaryOperation sb when IsString(sb.LeftOperand.Type) && IsString(sb.RightOperand.Type) &&
                                             (sb.OperatorMethod == null || IsString(sb.OperatorMethod.ContainingType)) &&
                                             sb.OperatorKind is BinaryOperatorKind.Equals or BinaryOperatorKind.NotEquals or BinaryOperatorKind.Add:
                {
                    var v = Operands(sb.LeftOperand, sb.RightOperand);
                    return StringBinary(sb.OperatorKind, v[0], v[1]);
                }
                case IPropertyReferenceOperation pr when pr.Property.Name == "Length" && IsArray(pr.Instance?.Type):
                    return new KLen { Array = Expr(pr.Instance), At = pr.Syntax, ArrayAt = pr.Instance.Syntax };
                case IArrayCreationOperation ac when IsArray(ac.Type) && ac.DimensionSizes.Length == 1:
                {
                    var v = Operands(new[] { ac.DimensionSizes[0] }.Concat(ac.Initializer?.ElementValues ?? Enumerable.Empty<IOperation>()).ToArray());
                    var size = v[0];
                    var elements = ac.Initializer == null ? null : v.Skip(1).ToArray();
                    var t = Declare("t$" + _temps++, ac.Type);
                    Emit(new KNew { Var = t, ArrayType = ac.Type, Size = size, Elements = elements });
                    return new KVar(t);
                }
                case IInvocationOperation call:
                    return Call(call);
                case IAwaitOperation aw:
                    return Await(aw) ?? throw new NotTranslated("an await of nothing, as a value");
                case IIsNullOperation isNull:
                    return new KOp("==", Expr(Unconverted(isNull.Operand)), new KLit("null"));
                case IDelegateCreationOperation cd when Contracted(cd.Type) && LambdaOf(cd.Target) != null:
                {
                    // (a lambda made a delegate with a contract: proved against it on its own; here, a new reference)
                    var t = Declare("t$" + _temps++, cd.Type);
                    Emit(new KNewObj { Var = t, Type = cd.Type, At = cd.Syntax, Args = new KExpr[0], ArgsAt = new SyntaxNode[0] });
                    return new KVar(t);
                }
                case IDelegateCreationOperation dc when IsFunc(dc.Type) && LambdaOf(dc.Target) is IAnonymousFunctionOperation af:
                    return Lambda(dc, af);
                case IDelegateCreationOperation mg when IsFunc(mg.Type) && mg.Target is IMethodReferenceOperation mr && mr.Method.IsStatic && !mr.Method.IsGenericMethod &&
                                                       !SymbolEqualityComparer.Default.Equals(mr.Method.OriginalDefinition, _m.OriginalDefinition):
                    return MethodGroup(mg, mr.Method);
                default:
                    if (e.ConstantValue.HasValue && e.ConstantValue.Value == null && IsNullable(e.Type)) return new KLit("null");
                    throw new NotTranslated(e.Kind + " '" + e.Syntax + "'");
            }
        }

        /// <summary>
        /// A reference made an object (to compare it with ==, or null): the same reference. Comparing two objects as
        /// objects is reference equality.
        /// </summary>
        private static bool Upcast(IConversionOperation conv) =>
            conv.IsImplicit && conv.Conversion.IsReference && (IsRef(conv.Operand.Type) || IsException(conv.Operand.Type) && IsException(conv.Type) || conv.Operand.ConstantValue is { HasValue: true, Value: null });

        private static IOperation Unconverted(IOperation op)
        {
            while (op is IConversionOperation c && c.IsImplicit) op = c.Operand;
            return op;
        }

        private static bool RefOperand(IOperation op) => IsRef(op.Type) || op is IConversionOperation c && Upcast(c) && IsRef(c.Operand.Type);

        private KExpr Constant(object v, ITypeSymbol type)
        {
            if (v is bool x) return new KLit(x ? "true" : "false");
            if (v == null && IsNullable(type)) return new KLit("null");
            // (a string literal: one value per contents)
            if (v is string str) return new KVar(_literal?.Invoke(str) ?? throw new NotTranslated("a string literal"));
            System.Numerics.BigInteger n;
            switch (v)
            {
                case char c: n = c; break;
                case sbyte b: n = b; break; case byte b: n = b; break;
                case short h: n = h; break; case ushort h: n = h; break;
                case int i: n = i; break; case uint i: n = i; break;
                case long l: n = l; break; case ulong l: n = l; break;
                default: throw new NotTranslated("a constant " + v);
            }
            return Number(n);
        }

        private KExpr Binary(IBinaryOperation b)
        {
            var v = Operands(b.LeftOperand, b.RightOperand);
            var (l, r) = (v[0], v[1]);
            switch (b.OperatorKind)
            {
                case BinaryOperatorKind.Add: case BinaryOperatorKind.Subtract: case BinaryOperatorKind.Multiply:
                case BinaryOperatorKind.Divide: case BinaryOperatorKind.Remainder:
                    return Arith(Op(b.OperatorKind), l, r, b.Type, b.Syntax, b.IsChecked);
                case BinaryOperatorKind.Equals: return new KOp("==", l, r);
                case BinaryOperatorKind.NotEquals: return new KOp("!=", l, r);
                case BinaryOperatorKind.LessThan: return new KOp("<", l, r);
                case BinaryOperatorKind.LessThanOrEqual: return new KOp("<=", l, r);
                case BinaryOperatorKind.GreaterThan: return new KOp(">", l, r);
                case BinaryOperatorKind.GreaterThanOrEqual: return new KOp(">=", l, r);
                case BinaryOperatorKind.And when b.Type.SpecialType == SpecialType.System_Boolean:
                case BinaryOperatorKind.ConditionalAnd: return new KOp("&&", l, r);
                case BinaryOperatorKind.Or when b.Type.SpecialType == SpecialType.System_Boolean:
                case BinaryOperatorKind.ConditionalOr: return new KOp("||", l, r);
                case BinaryOperatorKind.ExclusiveOr when b.Type.SpecialType == SpecialType.System_Boolean: return new KOp("!=", l, r);
                default: throw new NotTranslated("the operator " + b.OperatorKind);
            }
        }

        /// <summary>== != and + of strings: equality of values (characters), and concatenation (null counts as empty).</summary>
        private static KExpr StringBinary(BinaryOperatorKind k, KExpr l, KExpr r) => k switch
        {
            BinaryOperatorKind.Equals => new KOp("streq", l, r),
            BinaryOperatorKind.NotEquals => new KOp("!", new KOp("streq", l, r)),
            _ => new KOp("scat", l, r),
        };

        /// <summary>string.Equals(a, b), a.Equals(b), ordinally (StringComparison.Ordinal, or none); null for any other call.</summary>
        private (IOperation a, IOperation b)? StringEquals(IInvocationOperation inv)
        {
            var m = inv.TargetMethod;
            if (m.Name != "Equals" || !IsString(m.ContainingType)) return null;
            var strings = m.Parameters.TakeWhile(p => IsString(p.Type)).Count();
            var rest = m.Parameters.Skip(strings).ToList();
            if (rest.Count > 1 || rest.Count == 1 && !(rest[0].Type.Name == "StringComparison" &&
                inv.Arguments.First(a => a.Parameter.Ordinal == rest[0].Ordinal).Value.ConstantValue is { HasValue: true, Value: 4 })) return null;
            if (m.IsStatic && strings == 2) return (inv.Arguments.First(a => a.Parameter.Ordinal == 0).Value, inv.Arguments.First(a => a.Parameter.Ordinal == 1).Value);
            if (!m.IsStatic && strings == 1 && inv.Instance != null) return (inv.Instance, inv.Arguments.First(a => a.Parameter.Ordinal == 0).Value);
            return null;
        }

        /// <summary>A stub's call: its receiver (not null) and arguments; its precondition checked, its value the function's.</summary>
        private KFnCall StubCall(IInvocationOperation call, Func<IOperation, KExpr> eval)
        {
            _p.Stubs.Add(call.TargetMethod.OriginalDefinition);
            var ordered = call.Arguments.OrderBy(a => a.Parameter.Ordinal).Select(a => a.Value).ToList();
            KExpr receiver = null;
            KExpr[] args;
            if (eval == null)
            {
                var v = Operands((call.Instance == null ? new IOperation[0] : new[] { call.Instance }).Concat(ordered).ToArray());
                receiver = call.Instance == null ? null : v[0];
                args = call.Instance == null ? v : v.Skip(1).ToArray();
            }
            else
            {
                receiver = call.Instance == null ? null : eval(call.Instance);
                args = ordered.Select(eval).ToArray();
            }
            return new KFnCall { Callee = call.TargetMethod.OriginalDefinition, Receiver = receiver, ReceiverAt = call.Instance?.Syntax, Args = args, At = call.Syntax, Stub = true };
        }

        private KExpr Call(IInvocationOperation call)
        {
            // (a delegate type's contract: its Invoke is a procedure of it alone, as an interface member is)
            if (call.TargetMethod.MethodKind == MethodKind.DelegateInvoke && Contracted(call.TargetMethod.ContainingType))
            {
                return Invoke(call.TargetMethod, call.Instance, call.Arguments, call.Syntax, null);
            }
            if (call.TargetMethod.MethodKind == MethodKind.DelegateInvoke) return DelegateCall(call);
            // (a lock statement's Monitor.Enter and Monitor.Exit)
            if (call.TargetMethod.ContainingType?.ToDisplayString() == "System.Threading.Monitor" && call.TargetMethod.Name is "Enter" or "Exit") { Monitor(call); return null; }
            // (Interlocked and Volatile of an atomic field: one step each)
            if (call.TargetMethod.ContainingType?.ToDisplayString() is "System.Threading.Interlocked" or "System.Threading.Volatile" && call.Arguments.Length > 0 &&
                call.Arguments.OrderBy(a => a.Parameter.Ordinal).First().Parameter.RefKind != RefKind.None)
                return AtomicCall(call);
            // (a gate: taken by Wait, given back by Release)
            if (IsSemaphore(call.TargetMethod.ContainingType) && call.TargetMethod.Name == "Wait" && call.Arguments.Length == 0) { Take(GateOf(call), call.Syntax); return null; }
            if (IsSemaphore(call.TargetMethod.ContainingType) && call.TargetMethod.Name == "Release" && call.Arguments.Length == 0)
            {
                if (!(Unconverted(call.Instance) is IFieldReferenceOperation { Field: IFieldSymbol released } rf) || !(released.IsStatic || rf.Instance is IInstanceReferenceOperation))
                    throw new NotTranslated("a semaphore other than this object's gate");
                Give(released, call.Syntax);
                return null;
            }
            // (an async method's task is awaited at once, or it runs alongside: not yet)
            if (call.TargetMethod.IsAsync && !_awaiting) throw new NotTranslated("a task that isn't awaited at once: " + call.TargetMethod.Name);
            if (IsCollection(call.TargetMethod.ContainingType)) return Invoke(call.TargetMethod, call.Instance, call.Arguments, call.Syntax, null);
            // (IDisposable.Dispose of a class's object, as using calls it: that class's Dispose runs, its contract a
            // library interface's, so what it does isn't known: anything, as for a delegate)
            if (call.TargetMethod.ContainingType.ToDisplayString() == "System.IDisposable" && call.TargetMethod.Name == "Dispose" && call.Instance != null &&
                IsClass(Unconverted(call.Instance).Type))
            {
                DelegatesHere("a call of Dispose");
                if (_cfgBlock != null && ThrowTarget(_cfgBlock.EnclosingRegion) != null) throw new NotTranslated("a call of Dispose where exceptions are seen");
                Expr(Unconverted(call.Instance));
                _p.HavocsAll = true;
                _p.CallsDelegates = true;
                Emit(new KHavocAll());
                ForgetCaptured();
                return null;
            }
            var callee = call.TargetMethod.OriginalDefinition;
            if (StringEquals(call) is (IOperation ea, IOperation eb))
            {
                var v = Operands(ea, eb);
                if (call.Instance == null) return new KOp("streq", v[0], v[1]);
                // (a.Equals(b) dereferences a: its length, read, is checked not null, and is never negative)
                var deref = new KLen { String = true, Array = v[0], At = call.Syntax, ArrayAt = call.Instance.Syntax };
                return new KOp("&&", new KOp(">=", deref, new KLit("0")), new KOp("streq", v[0], v[1]));
            }
            if (!_isProcedure(callee) && IsStub(callee)) return StubCall(call, null);
            return Invoke(callee, call.Instance, call.Arguments, call.Syntax, null);
        }

        /// <summary>
        /// A call of a procedure: a method, or a property's accessor (its indices the arguments, and a setter's value
        /// after them). A virtual one is of the member as bound here, whose contract every override keeps.
        /// </summary>
        // ------------------------------------------------------------------ delegates

        /// <summary>
        /// The Func and Action parameters whose Spec.Pre, Spec.Post or Spec.Total a method's specifications speak of: it
        /// takes them to be the same in every state, and its callers must give such ones (a lambda reading no state, or
        /// one of their own such parameters).
        /// </summary>
        private HashSet<IParameterSymbol> SteadyParams(IMethodSymbol m)
        {
            var named = new HashSet<IParameterSymbol>(SymbolEqualityComparer.Default);
            var reading = new HashSet<IParameterSymbol>(SymbolEqualityComparer.Default);
            var c = _contractOf?.Invoke(m);
            if (c == null) return named;
            foreach (var op in c.Requires.Concat(c.Ensures.Select(e => e.Expr)).Where(x => x != null).SelectMany(x => x.DescendantsAndSelf()).OfType<IInvocationOperation>())
                if (SpecSymbols.IsSpecClass(op.TargetMethod.ContainingType) && op.Arguments.Length > 0 && Unconverted(op.Arguments[0].Value) is IParameterReferenceOperation pr)
                    switch (op.TargetMethod.Name)
                    {
                        case "Pre": case "Post": case "Total": named.Add(pr.Parameter.OriginalDefinition); break;
                        case "Reads" when op.Arguments.Length == 2: reading.Add(pr.Parameter.OriginalDefinition); break;
                        case "ReadsOf": reading.Add(pr.Parameter.OriginalDefinition); break;
                    }
            named.ExceptWith(reading);
            return named;
        }

        /// <summary>At a call: what the callee takes to be steady must be (CSV1001).</summary>
        private void SteadyArguments(IMethodSymbol callee, KExpr[] args, SyntaxNode at)
        {
            foreach (var p in SteadyParams(callee).Where(p => p.Ordinal < args.Length && args[p.Ordinal] != null))
                Emit(new KCheck
                {
                    Cond = new KOp("$steady", args[p.Ordinal]), Id = "CSV1001", At = at,
                    Message = $"'{callee.Name}' takes what '{p.Name}' accepts and gives to be the same in every state, but this might depend on state: " +
                              $"say what it reads with Spec.Requires(Spec.Reads({p.Name}, ...)) in '{callee.Name}'",
                });
        }

        /// <summary>Locals that lambdas and local functions here write: unknown after every call that may run one.</summary>
        private HashSet<ILocalSymbol> _capturedWrites;

        private HashSet<ILocalSymbol> CapturedWrites()
        {
            if (_capturedWrites != null) return _capturedWrites;
            _capturedWrites = new HashSet<ILocalSymbol>(SymbolEqualityComparer.Default);
            foreach (var fn in _decl.DescendantNodes().Where(n => n is AnonymousFunctionExpressionSyntax || n is LocalFunctionStatementSyntax))
                foreach (var id in fn.DescendantNodes().OfType<IdentifierNameSyntax>())
                {
                    SyntaxNode e = id;
                    while (e.Parent is ParenthesizedExpressionSyntax) e = e.Parent;
                    bool written = e.Parent is AssignmentExpressionSyntax a && a.Left == e || e.Parent is PrefixUnaryExpressionSyntax ||
                                   e.Parent is PostfixUnaryExpressionSyntax pu && !pu.IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.SuppressNullableWarningExpression) ||
                                   e.Parent is ArgumentSyntax arg && !arg.RefKindKeyword.IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.None);
                    if (written && _model.GetSymbolInfo(id).Symbol is ILocalSymbol l && !fn.Span.Contains(l.DeclaringSyntaxReferences.FirstOrDefault()?.Span ?? default))
                        _capturedWrites.Add(l);
                }
            return _capturedWrites;
        }

        /// <summary>After a call that may run a lambda that writes locals: those locals are unknown.</summary>
        private void ForgetCaptured()
        {
            foreach (var l in CapturedWrites())
            {
                if (!InSubset(l.Type)) throw new NotTranslated("a lambda that writes a local of " + l.Type);
                Emit(new KHavoc { Var = Declare(Local(l), l.Type) });
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
            if (_p.UsesPerm || _contract.Modifies != null) throw new NotTranslated(what + " with permissions or Spec.Modifies");
        }

        private KExpr DelegateCall(IInvocationOperation call)
        {
            if (!IsFunc(call.Instance?.Type)) throw new NotTranslated("a call of a delegate of " + call.Instance?.Type);
            DelegatesHere("a call of a delegate");
            var throwsTo = _cfgBlock != null ? ThrowTarget(_cfgBlock.EnclosingRegion) : null;
            var values = Operands(new[] { call.Instance }.Concat(call.Arguments.OrderBy(a => a.Parameter.Ordinal).Select(a => a.Value)).ToArray());
            var key = FuncKey(call.Instance.Type);
            _p.DelegateKeys.Add(key);
            _p.CallsDelegates = true;
            var result = call.TargetMethod.ReturnsVoid ? null : Declare("t$" + _temps++, call.TargetMethod.ReturnType);
            Emit(new KInvoke { Result = result, Delegate = values[0], Args = values.Skip(1).ToArray(), Key = key, At = call.Syntax, DelegateAt = call.Instance.Syntax });
            // (where exceptions are seen: it may throw, anything)
            if (throwsTo != null) Emit(new KFork { Overflow = new KLit("false"), Target = throwsTo, Exception = null });
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
            DelegatesHere("a lambda");
            var fn = af.Symbol;
            var c = _contractOf?.Invoke(fn) ?? throw new NotTranslated("a lambda without its contract");
            var own = new HashSet<ISymbol>(fn.Parameters, SymbolEqualityComparer.Default);
            var key = FuncKey(dc.Type);
            _p.DelegateKeys.Add(key);
            var invoke = ((INamedTypeSymbol)dc.Type).DelegateInvokeMethod;
            var t = Declare("t$" + _temps++, dc.Type);
            var lam = new KLambda { Var = t, Key = key, ResultType = invoke.ReturnsVoid ? null : TypeOf(invoke.ReturnType), NoChange = WritesNothing(af), Steady = true };
            foreach (var p in fn.Parameters) lam.Params.Add(("q$" + p.Name, TypeOf(p.Type)));
            if (!c.OwnRequires.All(r => Steady(r, own)))
            {
                // (one that reads state says what with its own Spec.Reads: its precondition is of the state it's made in,
                // and holds while what it reads stays as it is; what the precondition reads must be in that frame)
                var objects = new List<IOperation>();
                if (c.Reads == null || !Steady(c.Reads, own) || !c.OwnRequires.All(r => StateRead(r, own, objects)))
                {
                    Emit(new KCheck { Cond = new KLit("false"), Id = "CSV1029", NotAssumedAfter = true, At = dc.Syntax,
                                      Message = $"the precondition of what is made a '{dc.Type.Name}' here depends on state that may change: " +
                                                "say what it reads with Spec.Reads(...) in the lambda (fields and array cells of the objects it names), or use a delegate type with a contract" });
                    Emit(new KNewObj { Var = t, Type = dc.Type, At = dc.Syntax, Args = new KExpr[0], ArgsAt = new SyntaxNode[0] });
                    return new KVar(t);
                }
                lam.Steady = false;
                var frame = Spec(c.Reads, null);
                lam.PreS = c.OwnRequires.Select(r => Spec(r, null)).Aggregate((a, b) => new KOp("&&", a, b));
                lam.Reads = frame;
                foreach (var o in objects)
                    Emit(new KCheck { Cond = Forall(lam.Params, new KOp("sel", frame, Spec(o, null))), Id = "CSV1029", NotAssumedAfter = true, At = o.Syntax,
                                      Message = $"the precondition reads '{o.Syntax}', which isn't in its Spec.Reads" });
            }
            else if (c.OwnRequires.Count > 0)
                lam.Pre = c.OwnRequires.Select(r => Spec(r, null)).Aggregate((a, b) => new KOp("&&", a, b));
            if (c.Modifies != null && Steady(c.Modifies, own)) { lam.Changes = Spec(c.Modifies, null); lam.NoChange = false; }
            foreach (var post in c.Ensures.Where(e => e.Guard == null && lam.Steady))
            {
                var mine = new HashSet<ISymbol>(own, SymbolEqualityComparer.Default);
                if (post.ResultParameter != null) mine.Add(post.ResultParameter);
                if (!Steady(post.Expr, mine)) continue;
                lam.Posts.Add(Spec(post.Expr, post.ResultParameter));
            }
            // (an expression's value)
            if (lam.Steady && !invoke.ReturnsVoid && fn.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() is AnonymousFunctionExpressionSyntax { ExpressionBody: ExpressionSyntax body } &&
                _model.GetOperation(body) is IOperation value && Steady(value, own))
            {
                try { lam.Posts.Add(new KOp("==", new KVar("result"), Spec(value, null))); }
                catch (NotTranslated) { }
            }
            Emit(lam);
            return new KVar(t);
        }

        /// <summary>
        /// A static method made a Func or an Action: what it accepts is its precondition, what it gives its
        /// postconditions, as far as they're steady; it changes nothing if it's [Pure].
        /// </summary>
        private KExpr MethodGroup(IDelegateCreationOperation dc, IMethodSymbol fn)
        {
            DelegatesHere("a method group");
            var c = _contractOf?.Invoke(fn) ?? throw new NotTranslated("a method group without its contract");
            var invoke = ((INamedTypeSymbol)dc.Type).DelegateInvokeMethod;
            if (invoke.Parameters.Length != fn.Parameters.Length || fn.Parameters.Any(p => p.RefKind != RefKind.None)) throw new NotTranslated("a method group of another shape");
            if (c.Modifies != null || c.Reads != null) throw new NotTranslated("a method group with Spec.Modifies or Spec.Reads");
            var own = new HashSet<ISymbol>(fn.Parameters, SymbolEqualityComparer.Default);
            if (!c.Requires.All(r => Steady(r, own))) throw new NotTranslated("a method group whose precondition depends on state");
            var key = FuncKey(dc.Type);
            _p.DelegateKeys.Add(key);
            var t = Declare("t$" + _temps++, dc.Type);
            var lam = new KLambda { Var = t, Key = key, ResultType = invoke.ReturnsVoid ? null : TypeOf(invoke.ReturnType), NoChange = c.IsPure, Steady = true };
            foreach (var p in fn.Parameters)
            {
                lam.Params.Add(("q$" + p.Name, TypeOf(p.Type)));
                lam.Rename[Local(p)] = new KVar("q$" + p.Name);
            }
            if (c.Requires.Count > 0) lam.Pre = c.Requires.Select(r => Spec(r, null)).Aggregate((a, b) => new KOp("&&", a, b));
            foreach (var post in c.Ensures.Where(e => e.Guard == null))
            {
                var mine = new HashSet<ISymbol>(own, SymbolEqualityComparer.Default);
                if (post.ResultParameter != null) mine.Add(post.ResultParameter);
                if (Steady(post.Expr, mine)) lam.Posts.Add(Spec(post.Expr, post.ResultParameter));
            }
            Emit(lam);
            return new KVar(t);
        }

        /// <summary>For every value of these variables (none: the body itself).</summary>
        private static KExpr Forall(List<(string name, string type)> vars, KExpr body)
        {
            for (int k = vars.Count - 1; k >= 0; k--) body = new KQuant { Forall = true, Var = vars[k].name, Type = vars[k].type, Body = body };
            return body;
        }

        /// <summary>
        /// Of state that a frame can say: fields and array cells of steady objects (each added to <paramref name="objects"/>),
        /// array lengths, and what's steady.
        /// </summary>
        private bool StateRead(IOperation op, ISet<ISymbol> own, List<IOperation> objects)
        {
            if (op == null) return false;
            if (op.ConstantValue.HasValue) return true;
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

        /// <summary>The same in every state: of its own parameters, constants, this, and variables never written after they're declared.</summary>
        private bool Steady(IOperation op, ISet<ISymbol> own) => op.DescendantsAndSelf().All(o => o.ConstantValue.HasValue || o switch
        {
            IBinaryOperation or IUnaryOperation or IParenthesizedOperation or IConditionalOperation or IInstanceReferenceOperation => true,
            IConversionOperation conv => !IsFunc(conv.Type),
            // (sets of objects made of what's steady: ObjSet.Of(o), .Add, .Union, ObjSet.Empty)
            IInvocationOperation set when IsObjSet(set.TargetMethod.ContainingType) && set.TargetMethod.Name is "Of" or "Add" or "Union" => true,
            IArgumentOperation _ => true,
            IFieldReferenceOperation { Field.Name: "Empty", Instance: null } empty when IsObjSet(empty.Type) => true,
            IPropertyReferenceOperation { Property.Name: "Empty", Instance: null } emptyp when IsObjSet(emptyp.Type) => true,
            IParameterReferenceOperation p => own.Contains(p.Parameter) || NeverWritten(p.Parameter),
            ILocalReferenceOperation l => NeverWritten(l.Local),
            _ => false,
        });

        /// <summary>A local or parameter assigned nowhere after its declaration (nor passed by ref or out).</summary>
        private bool NeverWritten(ISymbol s)
        {
            var owner = s.ContainingSymbol?.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax();
            if (owner == null) return false;
            var model = _model.Compilation.GetSemanticModel(owner.SyntaxTree);
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

        /// <summary>A lambda that writes no field, array cell or captured variable, makes no object and calls only what's [Pure].</summary>
        private bool WritesNothing(IAnonymousFunctionOperation af)
        {
            foreach (var op in af.Body.DescendantsAndSelf())
            {
                if (InSpec(op.Syntax)) continue;
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

        private KExpr Invoke(IMethodSymbol callee, IOperation instance, IReadOnlyList<IArgumentOperation> arguments, SyntaxNode at, KExpr value)
        {
            var constructed = callee;
            // (a list's member: the procedure of its stub, as it is for this list's kind)
            bool list = IsCollection(callee.ContainingType);
            bool listCtor = list && callee.MethodKind == MethodKind.Constructor;
            if (list)
            {
                if (!(_contractOf?.Invoke(callee) is Contract lc && lc.IsStub)) throw new NotTranslated("a call of List's " + callee.Name + ", which has no stub contract");
                if (_p.UsesPerm) throw new NotTranslated("a list with permissions");
                _p.LibCalls.Add(callee);
                foreach (var model in ModelsOf((INamedTypeSymbol)callee.ContainingType)) _p.Models[model.Name] = model;
            }
            else callee = callee.OriginalDefinition;
            if (!list && !_isProcedure(callee)) throw new NotTranslated("a call of " + callee.Name);
            UnderLock(callee, at, instance, arguments);
            _p.Calls.Add(callee);
            var ordered = arguments.OrderBy(a => a.Parameter.Ordinal).ToList();
            if (!callee.IsStatic && instance == null && !listCtor) throw new NotTranslated("a call of " + callee.Name + " without its receiver");
            var call = (Instance: instance, Syntax: at);
            bool onThis = call.Instance is IInstanceReferenceOperation;
            // (a ref or out argument is a variable, which gets what the callee gives back; an out one isn't read)
            var refOuts = ordered.Where(a => a.Parameter.RefKind != RefKind.None).Select(a => (a.Parameter.Ordinal, RefVariable(a))).ToList();
            var ins = ordered.Where(a => a.Parameter.RefKind != RefKind.Out).ToList();
            var operands = (call.Instance == null || onThis ? Enumerable.Empty<IOperation>() : new[] { call.Instance }).Concat(ins.Select(a => a.Value)).ToArray();
            var values = Operands(operands);
            var receiver = call.Instance == null ? null : onThis ? Expr(call.Instance) : values[0];
            var inValues = call.Instance == null || onThis ? values : values.Skip(1).ToArray();
            var args = new KExpr[ordered.Count + (value == null ? 0 : 1)];
            for (int k = 0; k < ins.Count; k++)
            {
                var ordinal = ins[k].Parameter.Ordinal;
                args[ordinal] = list ? inValues[k] : Box(inValues[k], callee.OriginalDefinition.Parameters[ordinal].Type, ins[k].Parameter.Type);
            }
            if (value != null) args[ordered.Count] = value;
            foreach (var (ordinal, v) in refOuts) args[ordinal] ??= new KVar(v);
            if (refOuts.Any()) _p.UsesPerm |= ordered.Any(a => IsView(a.Parameter.Type));
            if (ordered.Any(a => IsView(a.Parameter.Type)) || IsOwnedClass(callee.ContainingType) && !callee.IsStatic) _p.UsesPerm = true;
            var gives = Returns(constructed);
            var result = listCtor ? Declare("t$" + _temps++, callee.ContainingType) : gives == null ? null : Declare("t$" + _temps++, !list && Returns(callee.OriginalDefinition) is ITypeParameterSymbol tp ? tp : gives);
            // (where exceptions are seen, a call of what may throw (not a proof) throws, or returns)
            var throwsTo = _cfgBlock == null || _contractOf?.Invoke(callee) is Contract cc && (cc.IsPure || cc.IsLemma) ? null : ThrowTarget(_cfgBlock.EnclosingRegion);
            SteadyArguments(callee, args, call.Syntax);
            // (an async callee's awaits let other code run, which can't reach this method's confined objects)
            var keepers = constructed.IsAsync && !list ? Confined().Select(l => Declare(Local(l), l.Type)).ToList() : new List<string>();
            int keepId = _keeps++;
            if (keepers.Count > 0) Emit(new KKeep { Id = keepId, Keep = keepers });
            Emit(new KCall { Callee = callee, Receiver = receiver, ReceiverIsThis = onThis, ReceiverAt = call.Instance?.Syntax, ThrowsTo = throwsTo,
                             Args = args, ArgsAt = ordered.Select(a => a.Value.Syntax).Concat(value == null ? new SyntaxNode[0] : new[] { at }).ToArray(),
                             Result = result, At = call.Syntax, RefOuts = refOuts });
            if (keepers.Count > 0) Emit(new KKeep { Id = keepId, After = true, Keep = keepers });
            if (!(_contractOf?.Invoke(callee) is Contract pc && (pc.IsPure || pc.IsLemma))) ForgetCaptured();
            foreach (var (_, rv) in refOuts) { var ro = ordered.First(a => RefVariableName(a) == rv); if (HasInvariants(ro.Parameter.Type)) AssumeValid(new KVar(rv), ro.Parameter.Type); }
            if (result == null) return null;
            if (gives != null && HasInvariants(gives)) AssumeValid(new KVar(result), gives);
            return list || gives == null ? new KVar(result) : Unbox(new KVar(result), Returns(callee.OriginalDefinition), gives);
        }

        /// <summary>The variable a ref or out argument is: a local (declared there, for out var), or a ref or out parameter.</summary>
        private readonly Dictionary<IArgumentOperation, string> _refVariables = new Dictionary<IArgumentOperation, string>();

        private string RefVariableName(IArgumentOperation a) => _refVariables.TryGetValue(a, out var v) ? v : null;

        private string RefVariable(IArgumentOperation a) => _refVariables[a] = RefVariableOf(a);

        private string RefVariableOf(IArgumentOperation a)
        {
            var v = a.Value is IDeclarationExpressionOperation d ? d.Expression : a.Value;
            switch (v)
            {
                // (out _: a variable of its own, never read)
                case IDiscardOperation discard when InSubset(discard.Type): return Declare("t$" + _temps++, discard.Type);
                case ILocalReferenceOperation l when InSubset(l.Local.Type) && l.Local.RefKind == RefKind.None: return Declare(Local(l.Local), l.Local.Type);
                case IParameterReferenceOperation p when InSubset(p.Parameter.Type) && p.Parameter.RefKind is RefKind.Ref or RefKind.Out: return Local(p.Parameter);
                default: throw new NotTranslated("a ref or out argument that isn't a variable");
            }
        }

        /// <summary>Own.New(new C(...), out view): a view of the new object; Own.Drop(view). The rest of Own isn't translated yet.</summary>
        private KExpr Own(IInvocationOperation own)
        {
            _p.UsesPerm = true;
            switch (own.TargetMethod.Name)
            {
                case "New" when own.Arguments[0].Value is IObjectCreationOperation:
                {
                    var obj = Expr(own.Arguments[0].Value);
                    var view = RefVariable(own.Arguments[1]);
                    Emit(new KOwn { Kind = "new", Obj = obj, View = view, Type = own.Arguments[0].Value.Type, At = own.Syntax });
                    return obj;
                }
                case "ToAcc" when IsView(own.Arguments[0].Value.Type):
                    // (the view goes, its permission stays in hand: a view and Spec.Acc are one permission here)
                    Expr(own.Arguments[0].Value);
                    return null;
                case "FromAcc" when IsOwnedClass(own.Arguments[0].Value.Type):
                {
                    var obj = Expr(own.Arguments[0].Value);
                    Emit(new KOwn { Kind = "fromacc", Obj = obj, View = RefVariable(own.Arguments[1]), Type = own.Arguments[0].Value.Type, At = own.Syntax });
                    return null;
                }
                case "Drop" when IsView(own.Arguments[0].Value.Type):
                    Emit(new KOwn { Kind = "drop", Obj = Expr(own.Arguments[0].Value), Type = ViewOf(own.Arguments[0].Value.Type), At = own.Syntax });
                    return null;
                default: throw new NotTranslated("Own." + own.TargetMethod.Name + (own.TargetMethod.Name == "New" ? " of an existing object" : ""));
            }
        }

        // ------------------------------------------------------------------ specifications (mathematical)

        /// <summary>A specification: mathematics, its array reads, lengths, divisions and functions' calls kept for Checks' well-definedness.</summary>
        private KExpr Spec(IOperation e, IParameterSymbol result)
        {
            // (ObjSet.Empty: no objects)
            if ((e is IFieldReferenceOperation { Field.Name: "Empty", Instance: null } || e is IPropertyReferenceOperation { Property.Name: "Empty", Instance: null }) && IsObjSet(e.Type))
                return new KLit("(lambda r$: Ref :: false)");
            if (e is ILocalReferenceOperation bl && _bound.TryGetValue(bl.Local, out var bv)) return bv;
            if (DataExpr(e, x => Spec(x, result), (l, v) => _bound[l] = v, inSpec: true) is KExpr data) return data;
            switch (e)
            {
                case IDelegateCreationOperation d: return Spec(d.Target, result);
                case IAnonymousFunctionOperation fn when fn.Body.Operations.Length == 1 && fn.Body.Operations[0] is IReturnOperation ret:
                    return Spec(ret.ReturnedValue, fn.Symbol.Parameters.FirstOrDefault() ?? result);
                case { ConstantValue: { HasValue: true } cv } when Scalar(e.Type) || IsNullable(e.Type): return Constant(cv.Value, e.Type);
                case IParameterReferenceOperation p when result != null && SymbolEqualityComparer.Default.Equals(p.Parameter, result): return new KVar("result");
                case IParameterReferenceOperation p when p.Parameter.ContainingSymbol is IMethodSymbol { MethodKind: MethodKind.AnonymousFunction }:
                    return new KVar("q$" + p.Parameter.Name); // (a quantifier's variable)
                // (a base's contract, inherited: its parameters are this method's, by position)
                case IParameterReferenceOperation p when InSubset(p.Parameter.Type) && !_contract.IsStub && p.Parameter.ContainingSymbol is IMethodSymbol pm &&
                                                         _contract.Aliases.Any(a => SymbolEqualityComparer.Default.Equals(a.OriginalDefinition, pm.OriginalDefinition)) &&
                                                         p.Parameter.Ordinal < _m.Parameters.Length:
                    return new KVar(Local(_m.Parameters[p.Parameter.Ordinal]));
                // (a list member's stub: its @this is the receiver, the rest the member's own parameters)
                case IParameterReferenceOperation p when _contract.IsStub && IsCollection(_m.ContainingType) && _contract.Stub != null &&
                                                         SymbolEqualityComparer.Default.Equals(p.Parameter.ContainingSymbol.OriginalDefinition, _contract.Stub.OriginalDefinition):
                {
                    int shift = _p.HasThis ? 1 : 0;
                    if (shift == 1 && p.Parameter.Ordinal == 0) return new KVar("this");
                    return new KVar(Local(_m.Parameters[p.Parameter.Ordinal - shift]));
                }
                case IParameterReferenceOperation p when InSubset(p.Parameter.Type): return new KVar(Local(p.Parameter));
                case ILocalReferenceOperation l when InSubset(l.Local.Type): return new KVar(Declare(Local(l.Local), l.Local.Type));
                case IInstanceReferenceOperation { ReferenceKind: InstanceReferenceKind.ContainingTypeInstance }: return new KVar("this");
                // (a view's object: v.Obj.Value)
                case IPropertyReferenceOperation { Property.Name: "Value", Instance: IPropertyReferenceOperation { Property.Name: "Obj" } obj } when IsView(obj.Instance?.Type):
                    return Spec(obj.Instance, result);
                // (a [Pure] computed property: its getter, a function; in a contract class, the member it specifies)
                case IPropertyReferenceOperation cp when Specified(cp.Property) is IPropertySymbol sp && IsComputed(sp) && sp.GetMethod != null && _isFunction(sp.GetMethod):
                    return new KFnCall
                    {
                        Callee = OnThis(Specified(cp.Property).GetMethod, cp.Instance), Receiver = cp.Instance == null ? null : Spec(cp.Instance, result),
                        ReceiverIsThis = cp.Instance is IInstanceReferenceOperation, ReceiverAt = cp.Instance?.Syntax,
                        Args = cp.Arguments.OrderBy(a => a.Parameter.Ordinal).Select(a => Spec(a.Value, result)).ToArray(), At = cp.Syntax,
                    };
                case IFieldReferenceOperation _:
                case IPropertyReferenceOperation pf when !(pf.Property.Name == "Length" && IsArray(pf.Instance?.Type)) && !IsString(pf.Instance?.Type) && CollectionOf(pf.Instance?.Type) == null && !IsPair(pf.Instance?.Type) && !SpecSymbols.IsCsVerifyType(pf.Instance?.Type, "Seq`1") &&
                                                      !SpecSymbols.IsCsVerifyType(pf.Instance?.Type, "Ghost`1") && !SpecSymbols.IsCsVerifyType(pf.Instance?.Type, "Map`2"):
                {
                    var (field, instance, onThis, instanceAt) = FieldOf(e, result, spec: true);
                    return new KField { Field = field, Instance = instance, OnThis = onThis, At = e.Syntax, InstanceAt = instanceAt };
                }
                case IParenthesizedOperation par: return Spec(par.Operand, result);
                case IConversionOperation conv when conv.Conversion.IsIdentity || IsIntegral(conv.Type) && IsIntegral(conv.Operand.Type) && conv.Conversion.IsNumeric &&
                                                    (conv.IsImplicit || Range(conv.Operand.Type).lo >= Range(conv.Type).lo && Range(conv.Operand.Type).hi <= Range(conv.Type).hi):
                    return Spec(conv.Operand, result);
                case IConversionOperation conv when Upcast(conv):
                    return conv.Operand.ConstantValue.HasValue ? new KLit("null") : Spec(conv.Operand, result);
                case IUnaryOperation u when u.OperatorKind == UnaryOperatorKind.Not: return new KOp("!", Spec(u.Operand, result));
                case IUnaryOperation u when u.OperatorKind == UnaryOperatorKind.Minus && _codeArith: return Arith("-", new KLit("0"), Spec(u.Operand, result), u.Type, u.Syntax, u.IsChecked);
                case IUnaryOperation u when u.OperatorKind == UnaryOperatorKind.Minus: return new KOp("-", new KLit("0"), Spec(u.Operand, result));
                case IUnaryOperation u when u.OperatorKind == UnaryOperatorKind.Plus: return Spec(u.Operand, result);
                case IConditionalOperation c when c.WhenFalse != null:
                    return new KOp("ite", Spec(c.Condition, result), Spec(c.WhenTrue, result), Spec(c.WhenFalse, result));
                case IBinaryOperation b when b.OperatorMethod == null:
                {
                    var l = Spec(b.LeftOperand, result);
                    var r = Spec(b.RightOperand, result);
                    return b.OperatorKind switch
                    {
                        BinaryOperatorKind.Add when _codeArith => Arith("+", l, r, b.Type, b.Syntax, b.IsChecked),
                        BinaryOperatorKind.Subtract when _codeArith => Arith("-", l, r, b.Type, b.Syntax, b.IsChecked),
                        BinaryOperatorKind.Multiply when _codeArith => Arith("*", l, r, b.Type, b.Syntax, b.IsChecked),
                        BinaryOperatorKind.Divide when _codeArith => Arith("/", l, r, b.Type, b.Syntax, b.IsChecked),
                        BinaryOperatorKind.Remainder when _codeArith => Arith("%", l, r, b.Type, b.Syntax, b.IsChecked),
                        BinaryOperatorKind.Add => new KOp("+", l, r),
                        BinaryOperatorKind.Subtract => new KOp("-", l, r),
                        BinaryOperatorKind.Multiply => new KOp("*", l, r),
                        BinaryOperatorKind.Divide => new KArith { Op = "/", Left = l, Right = r, Type = b.Type, Mode = KMode.Math, At = b.Syntax },
                        BinaryOperatorKind.Remainder => new KArith { Op = "%", Left = l, Right = r, Type = b.Type, Mode = KMode.Math, At = b.Syntax },
                        BinaryOperatorKind.Equals => new KOp("==", l, r),
                        BinaryOperatorKind.NotEquals => new KOp("!=", l, r),
                        BinaryOperatorKind.LessThan => new KOp("<", l, r),
                        BinaryOperatorKind.LessThanOrEqual => new KOp("<=", l, r),
                        BinaryOperatorKind.GreaterThan => new KOp(">", l, r),
                        BinaryOperatorKind.GreaterThanOrEqual => new KOp(">=", l, r),
                        BinaryOperatorKind.ConditionalAnd => new KOp("&&", l, r),
                        BinaryOperatorKind.ConditionalOr => new KOp("||", l, r),
                        BinaryOperatorKind.And => new KOp("&", l, r),
                        BinaryOperatorKind.Or => new KOp("|", l, r),
                        BinaryOperatorKind.ExclusiveOr => new KOp("!=", l, r),
                        _ => throw new NotTranslated("the operator " + b.OperatorKind),
                    };
                }
                case IArrayElementReferenceOperation el when IsArray(el.ArrayReference.Type) && el.Indices.Length == 1:
                    return new KElem { Array = Spec(el.ArrayReference, result), Index = Spec(el.Indices[0], result), ArrayType = el.ArrayReference.Type, InSpec = true, At = el.Syntax, ArrayAt = el.ArrayReference.Syntax };
                case IPropertyReferenceOperation sl when sl.Property.Name == "Length" && IsString(sl.Instance?.Type):
                    return new KLen { String = true, Array = Spec(sl.Instance, result), InSpec = true, At = sl.Syntax, ArrayAt = sl.Instance.Syntax };
                case IPropertyReferenceOperation sc when sc.Property.IsIndexer && IsString(sc.Instance?.Type) && sc.Arguments.Length == 1:
                    return new KElem { String = true, Array = Spec(sc.Instance, result), Index = Spec(sc.Arguments[0].Value, result), InSpec = true, At = sc.Syntax, ArrayAt = sc.Instance.Syntax };
                case IBinaryOperation sb when IsString(sb.LeftOperand.Type) && IsString(sb.RightOperand.Type) &&
                                             (sb.OperatorMethod == null || IsString(sb.OperatorMethod.ContainingType)) &&
                                             sb.OperatorKind is BinaryOperatorKind.Equals or BinaryOperatorKind.NotEquals or BinaryOperatorKind.Add:
                    return StringBinary(sb.OperatorKind, Spec(sb.LeftOperand, result), Spec(sb.RightOperand, result));
                case IInvocationOperation se when StringEquals(se) is (IOperation ea, IOperation eb):
                    return new KOp("streq", Spec(ea, result), Spec(eb, result));
                case IInvocationOperation st when !_isFunction(st.TargetMethod) && IsStub(st.TargetMethod.OriginalDefinition):
                    return StubCall(st, x => Spec(x, result));
                case IPropertyReferenceOperation pr when pr.Property.Name == "Length" && IsArray(pr.Instance?.Type):
                    return new KLen { Array = Spec(pr.Instance, result), InSpec = true, At = pr.Syntax, ArrayAt = pr.Instance.Syntax };
                // (a list's model: its size, its version, its elements; Count and the indexer as their contracts say)
                case IInvocationOperation mo when SpecSymbols.IsModel(mo.TargetMethod.OriginalDefinition) && mo.Arguments.Length == 1 &&
                                                  CollectionOf(Unconverted(mo.Arguments[0].Value).Type) is INamedTypeSymbol mc:
                    return Model(mo.TargetMethod.Name, mc, Spec(Unconverted(mo.Arguments[0].Value), result));
                case IPropertyReferenceOperation lc when lc.Property.Name == "Count" && CollectionOf(lc.Instance?.Type) is INamedTypeSymbol cc:
                    return Model("Size", cc, Spec(lc.Instance, result));
                case IPropertyReferenceOperation li when li.Property.IsIndexer && CollectionOf(li.Instance?.Type) is INamedTypeSymbol ic && li.Arguments.Length == 1 &&
                                                         CollectionKind(ic) is "List" or "Dictionary":
                {
                    bool dict = CollectionKind(ic) == "Dictionary";
                    var items = ModelOf(dict ? "Entries" : "Items", ic);
                    var bound = ModelOf(dict ? "Domain" : "Size", ic);
                    _p.Models[items.Name] = items;
                    _p.Models[bound.Name] = bound;
                    return new KElem { Model = items.Name, Domain = dict ? bound.Name : null, Array = Spec(li.Instance, result), Index = Spec(li.Arguments[0].Value, result),
                                       InSpec = true, At = li.Syntax, ArrayAt = li.Instance.Syntax };
                }
                // (a dictionary's ContainsKey and a set's Contains: its model, as their stubs say)
                case IInvocationOperation ck when ck.Instance != null && CollectionOf(ck.Instance.Type) is INamedTypeSymbol cd && ck.Arguments.Length == 1 &&
                                                  (CollectionKind(cd) == "Dictionary" && ck.TargetMethod.Name == "ContainsKey" || CollectionKind(cd) == "HashSet" && ck.TargetMethod.Name == "Contains"):
                {
                    var model = ModelOf(CollectionKind(cd) == "Dictionary" ? "Domain" : "Members", cd);
                    _p.Models[model.Name] = model;
                    var of = Spec(ck.Instance, result);
                    return new KOp("&&", new KOp("!=", of, new KLit("null")), new KOp("sel", new KVar(model.Name), of, Spec(ck.Arguments[0].Value, result)));
                }
                case IPropertyReferenceOperation sk when IsPair(sk.Instance?.Type) && sk.Property.Name is "Key" or "Value":
                    return Pair(Spec(sk.Instance, result), sk.Instance.Type, sk.Property.Name);
                // (a ghost map: a Boogie map; a ghost value's Value: the value)
                case IPropertyReferenceOperation mi when mi.Property.IsIndexer && SpecSymbols.IsCsVerifyType(mi.Instance?.Type, "Map`2") && mi.Arguments.Length == 1:
                    return new KOp("sel", Spec(mi.Instance, result), Spec(mi.Arguments[0].Value, result));
                case IPropertyReferenceOperation gv when gv.Property.Name == "Value" && SpecSymbols.IsCsVerifyType(gv.Instance?.Type, "Ghost`1"):
                    return Spec(gv.Instance, result);
                case IInvocationOperation mu when SpecSymbols.IsCsVerifyType(mu.TargetMethod.ContainingType, "Map`2") && mu.TargetMethod.Name == "Update" && mu.Instance != null:
                    return new KOp("store", Spec(mu.Instance, result), Spec(mu.Arguments[0].Value, result), Spec(mu.Arguments[1].Value, result));
                case IInvocationOperation mk when SpecSymbols.IsCsVerifyType(mk.TargetMethod.ContainingType, "Map") && mk.TargetMethod.Name == "Const" && mk.Arguments.Length == 1:
                    return new KOp("map.const." + BoogieOf(Kind(Actual(mk.TargetMethod.TypeArguments[0]))), Spec(mk.Arguments[0].Value, result));
                // (a ghost sequence: an [int] map; a ghost value: the value)
                case IPropertyReferenceOperation si when si.Property.IsIndexer && SpecSymbols.IsCsVerifyType(si.Instance?.Type, "Seq`1") && si.Arguments.Length == 1:
                    return new KOp("sel", Spec(si.Instance, result), Spec(si.Arguments[0].Value, result));
                case IInvocationOperation sq when SpecSymbols.IsCsVerifyType(sq.TargetMethod.ContainingType, "Seq`1") && sq.Instance != null:
                {
                    var a = sq.Arguments.OrderBy(x => x.Parameter.Ordinal).Select(x => Spec(x.Value, result)).ToArray();
                    var self = Spec(sq.Instance, result);
                    return sq.TargetMethod.Name switch
                    {
                        "Update" => new KOp("store", self, a[0], a[1]),
                        "Drop" => new KOp("seq.drop", self, a[0]),
                        "Concat" => new KOp("seq.concat", self, a[0], a[1]),
                        _ => throw new NotTranslated("Seq." + sq.TargetMethod.Name),
                    };
                }
                case IInvocationOperation sc when SpecSymbols.IsCsVerifyType(sc.TargetMethod.ContainingType, "Seq") && sc.TargetMethod.Name == "Const" && sc.Arguments.Length == 1:
                    return new KOp("seq.const", Spec(sc.Arguments[0].Value, result));
                case IInvocationOperation go when SpecSymbols.IsCsVerifyType(go.TargetMethod.ContainingType, "Ghost") && go.TargetMethod.Name == "Of" && go.Arguments.Length == 1:
                    return Spec(go.Arguments[0].Value, result);
                case IBinaryOperation gb when gb.OperatorMethod != null && gb.OperatorKind is BinaryOperatorKind.Equals or BinaryOperatorKind.NotEquals &&
                                              (SpecSymbols.IsCsVerifyType(gb.OperatorMethod.ContainingType, "Seq`1") || SpecSymbols.IsCsVerifyType(gb.OperatorMethod.ContainingType, "Ghost`1") ||
                                               SpecSymbols.IsCsVerifyType(gb.OperatorMethod.ContainingType, "Map`2")):
                    return new KOp(gb.OperatorKind == BinaryOperatorKind.Equals ? "==" : "!=", Spec(gb.LeftOperand, result), Spec(gb.RightOperand, result));
                case IConversionOperation gc when gc.OperatorMethod != null && SpecSymbols.IsCsVerifyType(gc.OperatorMethod.ContainingType, "Ghost`1"):
                    return Spec(gc.Operand, result);
                // (ghost sets of objects)
                case IPropertyReferenceOperation { Property.Name: "Empty" } empty when IsObjSet(empty.Type) && empty.Instance == null:
                    return new KLit("(lambda r$: Ref :: false)");
                case IInvocationOperation of when IsObjSet(of.TargetMethod.ContainingType) && of.TargetMethod.Name == "Of" && of.Arguments.Length == 1 &&
                                                  (IsRef(Unconverted(of.Arguments[0].Value).Type) || CollectionOf(Unconverted(of.Arguments[0].Value).Type) != null || Unconverted(of.Arguments[0].Value) is IInstanceReferenceOperation):
                    return new KOp("set.of", Spec(Unconverted(of.Arguments[0].Value), result));
                case IInvocationOperation add when IsObjSet(add.TargetMethod.ContainingType) && add.TargetMethod.Name == "Add" && add.Instance != null && IsRef(Unconverted(add.Arguments[0].Value).Type):
                    return new KOp("set.add", Spec(add.Instance, result), Spec(Unconverted(add.Arguments[0].Value), result));
                case IInvocationOperation has when IsObjSet(has.TargetMethod.ContainingType) && has.TargetMethod.Name == "Contains" && has.Instance != null && IsRef(Unconverted(has.Arguments[0].Value).Type):
                    return new KOp("sel", Spec(has.Instance, result), Spec(Unconverted(has.Arguments[0].Value), result));
                case IInvocationOperation sub when IsObjSet(sub.TargetMethod.ContainingType) && sub.TargetMethod.Name is "IsSubsetOf" or "IsDisjointFrom" && sub.Instance != null:
                    return new KOp(sub.TargetMethod.Name == "IsSubsetOf" ? "set.subset" : "set.disjoint", Spec(sub.Instance, result), Spec(sub.Arguments[0].Value, result));
                case IInvocationOperation union when IsObjSet(union.TargetMethod.ContainingType) && union.TargetMethod.Name == "Union" && union.Instance != null:
                    return new KOp("set.union", Spec(union.Instance, result), Spec(union.Arguments[0].Value, result));
                case IInvocationOperation acc when SpecSymbols.IsSpecClass(acc.TargetMethod.ContainingType) && acc.TargetMethod.Name == "Acc" &&
                                                   acc.Arguments.Length == 1 && IsOwnedClass(Unconverted(acc.Arguments[0].Value).Type):
                {
                    var target = Unconverted(acc.Arguments[0].Value);
                    _p.UsesPerm = true;
                    return new KAcc { Obj = Spec(target, result), Type = target.Type, At = acc.Syntax };
                }
                case IInvocationOperation fa when SpecSymbols.IsSpecClass(fa.TargetMethod.ContainingType) && fa.TargetMethod.Name == "Acc" &&
                                                  fa.Arguments.Length == 2 && IsOwnedClass(Unconverted(fa.Arguments[0].Value).Type):
                {
                    var target = Unconverted(fa.Arguments[0].Value);
                    // (only of a sealed class without an [Invariant], and not an [Owns] field: CsVerify's engine reports the rest)
                    if (!(fa.Arguments[1].Value.ConstantValue is { HasValue: true, Value: string name }) || !(target.Type is INamedTypeSymbol { IsSealed: true } t) ||
                        DataTypes.Invariants(t).Any() || !(WholeFields(t).FirstOrDefault(x => x.Name == name) is ISymbol field))
                        throw new NotTranslated("a Spec.Acc of a field CsVerify's engine rejects");
                    _p.UsesPerm = true;
                    return new KFieldAcc { Obj = Spec(target, result), Field = field, Type = target.Type, At = fa.Syntax };
                }
                case IInvocationOperation pc when SpecSymbols.IsPredicate(pc.TargetMethod.OriginalDefinition) && pc.TargetMethod.IsStatic:
                    _p.UsesPerm = true;
                    _p.Preds.Add(pc.TargetMethod.OriginalDefinition);
                    return new KInst { Pred = pc.TargetMethod.OriginalDefinition, Args = pc.Arguments.OrderBy(a => a.Parameter.Ordinal).Select(a => Spec(a.Value, result)).ToArray(), At = pc.Syntax };
                case IInvocationOperation inv when SpecSymbols.IsSpecClass(inv.TargetMethod.ContainingType):
                    switch (inv.TargetMethod.Name)
                    {
                        case "Old": return new KOp("old", Spec(inv.Arguments[0].Value, result));
                        case "Equal" when inv.Arguments.Length == 2: return new KOp("==", Spec(inv.Arguments[0].Value, result), Spec(inv.Arguments[1].Value, result));
                        // (what a Func or an Action accepts and gives, the same in every state; whether it changes nothing)
                        case "Pre" or "Post" or "Total" or "ChangesNothing" or "ReadsOf" when IsFunc(Unconverted(inv.Arguments[0].Value).Type):
                        {
                            var f = Unconverted(inv.Arguments[0].Value);
                            var key = FuncKey(f.Type);
                            _p.DelegateKeys.Add(key);
                            var args = inv.Arguments.OrderBy(a => a.Parameter.Ordinal).Select((a, k) => k == 0 ? Spec(f, result) : Spec(a.Value, result)).ToList();
                            // (a parameter this method takes to be steady: in every state; any other, in this one)
                            bool steady = f is IParameterReferenceOperation sp && SteadyParams(_m).Contains(sp.Parameter.OriginalDefinition);
                            var stated = new[] { args[0], new KOp("$state") }.Concat(args.Skip(1)).ToArray();
                            switch (inv.TargetMethod.Name)
                            {
                                case "Pre": return steady ? new KOp("$pre." + key, args.ToArray()) : new KOp("$preS." + key, stated);
                                case "Post": return steady ? new KOp("$post." + key, args.ToArray()) : new KOp("$postS." + key, stated);
                                case "ReadsOf": return new KOp("$readsS." + key, stated);
                                case "Total" when steady: return new KOp("$total." + key, args[0]);
                                case "Total": throw new NotTranslated("Spec.Total of a delegate that may read state");
                                default: return new KOp("$nochange", args[0]);
                            }
                        }
                        // (what a delegate reads, or may change, is within a frame of its arguments)
                        case "Reads" or "Changes" when inv.Arguments.Length == 2 && IsFunc(Unconverted(inv.Arguments[0].Value).Type):
                        {
                            var f = Unconverted(inv.Arguments[0].Value);
                            var key = FuncKey(f.Type);
                            _p.DelegateKeys.Add(key);
                            var given = Unconverted(inv.Arguments[1].Value);
                            var ps = new List<(string name, string type)>();
                            KExpr within;
                            if (given is IDelegateCreationOperation gd && LambdaOf(gd.Target) is IAnonymousFunctionOperation gf &&
                                gf.Body.Operations.Length == 1 && gf.Body.Operations[0] is IReturnOperation gr)
                            {
                                foreach (var p in gf.Symbol.Parameters) ps.Add(("q$" + p.Name, TypeOf(p.Type)));
                                within = Spec(gr.ReturnedValue, null);
                            }
                            else within = Spec(given, result);
                            var xs = ps.Select(p => (KExpr)new KVar(p.name)).ToArray();
                            var d = Spec(f, result);
                            var set = inv.TargetMethod.Name == "Reads"
                                ? new KOp("$readsS." + key, new[] { d, new KOp("$state") }.Concat(xs).ToArray())
                                : new KOp("$frame." + key, new[] { d }.Concat(xs).ToArray());
                            return Forall(ps, new KOp("set.subset", set, within));
                        }
                        // (a foreach's index: of its element in the body, the number gone through at its head)
                        case "Index" when Unconverted(inv.Arguments[0].Value) is ILocalReferenceOperation ix && _forEachOf.TryGetValue(ix.Local, out var fx) && fx.Version != null:
                            throw new NotTranslated("Spec.Index of a foreach through an enumerator");
                        case "Index" when Unconverted(inv.Arguments[0].Value) is ILocalReferenceOperation ix && _forEachOf.TryGetValue(ix.Local, out var fx):
                            return new KVar(fx.Index);
                        // (allocated during the call)
                        case "Fresh" when IsRef(Unconverted(inv.Arguments[0].Value).Type):
                            // (its argument read now: only the allocated set is as it was)
                            return new KOp("&&", new KOp("!=", Spec(Unconverted(inv.Arguments[0].Value), result), new KLit("null")),
                                new KOp("!", new KOp("sel", new KOp("old", new KVar("$Alloc")), Spec(Unconverted(inv.Arguments[0].Value), result))));
                        case "Acc" or "AccRead" when IsArray(Unconverted(inv.Arguments[0].Value).Type) && inv.Arguments.Length is 1 or 3:
                        {
                            var arr = Spec(Unconverted(inv.Arguments[0].Value), result);
                            _p.UsesPerm = true;
                            return new KCells
                            {
                                Arr = arr, Read = inv.TargetMethod.Name == "AccRead", At = inv.Syntax,
                                Lo = inv.Arguments.Length == 1 ? new KLit("0") : Spec(inv.Arguments[1].Value, result),
                                Hi = inv.Arguments.Length == 1 ? new KOp("len", arr) : Spec(inv.Arguments[2].Value, result),
                            };
                        }
                        case "Result": return new KVar("result");
                        case "Forall": case "Exists" when inv.Arguments.Length == 3:
                        {
                            var lo = Spec(inv.Arguments[0].Value, result);
                            var hi = Spec(inv.Arguments[1].Value, result);
                            var fn = (inv.Arguments[2].Value as IDelegateCreationOperation)?.Target as IAnonymousFunctionOperation
                                     ?? throw new NotTranslated("a quantifier without a lambda");
                            if (!(fn.Body.Operations.Length == 1 && fn.Body.Operations[0] is IReturnOperation ret)) throw new NotTranslated("a quantifier's body");
                            var q = "q$" + fn.Symbol.Parameters[0].Name;
                            return new KQuant
                            {
                                Forall = inv.TargetMethod.Name == "Forall", Var = q,
                                Range = new KOp("&&", new KOp("<=", lo, new KVar(q)), new KOp("<", new KVar(q), hi)),
                                Body = Spec(ret.ReturnedValue, result),
                            };
                        }
                        default: throw new NotTranslated("Spec." + inv.TargetMethod.Name + " in a specification");
                    }
                case IInvocationOperation fn when _isFunction(fn.TargetMethod) && (fn.TargetMethod.IsStatic || fn.Instance != null && !fn.TargetMethod.IsVirtual && !fn.TargetMethod.IsAbstract && !fn.TargetMethod.IsOverride):
                {
                    bool onThis = fn.Instance is IInstanceReferenceOperation;
                    var call = new KFnCall
                    {
                        Callee = fn.TargetMethod.OriginalDefinition, Receiver = fn.Instance == null ? null : Spec(fn.Instance, result), ReceiverIsThis = onThis, ReceiverAt = fn.Instance?.Syntax,
                        Args = fn.Arguments.OrderBy(a => a.Parameter.Ordinal)
                                 .Select(a => Box(Spec(a.Value, result), fn.TargetMethod.OriginalDefinition.Parameters[a.Parameter.Ordinal].Type, a.Parameter.Type)).ToArray(),
                        At = fn.Syntax,
                    };
                    return Unbox(call, fn.TargetMethod.OriginalDefinition.ReturnType, fn.TargetMethod.ReturnType);
                }
                default:
                    throw new NotTranslated("in a specification: " + e.Kind + " '" + e.Syntax + "'");
            }
        }
    }
}
