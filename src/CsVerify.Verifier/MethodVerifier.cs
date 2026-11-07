using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.FlowAnalysis;
using Microsoft.CodeAnalysis.Operations;
using Microsoft.CodeAnalysis.Text;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Verifies one method: symbolic execution over its Roslyn control flow graph, a forward computation of the
    /// weakest-precondition verification conditions. Every proof obligation (callee precondition, array bound,
    /// assertion, invariant, termination measure, postcondition) becomes the query "path condition and not goal",
    /// which Z3 must find unsatisfiable. Loops are cut at their head with Spec.Invariant; calls are modular.
    /// </summary>
    internal sealed partial class MethodVerifier
    {
        private sealed class Loop
        {
            public int Id, Head;
            public SyntaxNode Syntax;
            public List<IOperation> Invariants = new List<IOperation>();
            public IReadOnlyList<IOperation> Decreases;
            public HashSet<ISymbol> Havoc = new HashSet<ISymbol>(SymbolEqualityComparer.Default);
            public HashSet<ISymbol> HavocArrays = new HashSet<ISymbol>(SymbolEqualityComparer.Default);
            public bool HavocHeap;
            public HashSet<ISymbol> HavocFields = new HashSet<ISymbol>(SymbolEqualityComparer.Default);
            public bool HavocAllFields;
            /// <summary>The loop awaits: other code may run, changing everything but what the method holds or confines.</summary>
            public bool Awaits;
            public bool HavocThis; // a struct constructor's loop writes this's members
            public bool HavocRoot; // ownership changes hands in the loop (Own.New/Take/Give)
            public bool Permissions; // permissions are exchanged in the loop (folds, unfolds, calls whose contracts speak of them)
            public ITypeSymbol ArrayElement;
            /// <summary>A foreach over a List: its index runs over the list's model (Size(), Items()), not an array.</summary>
            public bool OverList;
            /// <summary>A foreach over a string: its index runs over the characters.</summary>
            public bool OverString;
            /// <summary>A foreach over an IReadOnlyList or IList: its index runs over the interface's Count and indexer.</summary>
            public bool OverInterface;
            /// <summary>A foreach over a LINQ view (Select, Where, Take, Skip of what the verifier reads): over the view, read once.</summary>
            public bool OverView;
            public List<LoopFact> Facts = new List<LoopFact>(); // inferred, for a loop without invariants (MethodVerifier.LoopFacts)
            public HashSet<ISymbol> Rebound = new HashSet<ISymbol>(SymbolEqualityComparer.Default); // ref locals bound anew in the loop // a foreach over an array of these: its enumerator is an index (Frame.ForEach)
        }

        private readonly Engine _engine;
        private readonly SmtSolver _z3;
        private readonly Contract _contract;
        private readonly IMethodSymbol _method;
        private readonly SemanticModel _model;
        private readonly MethodResult _result;
        private readonly Dictionary<int, Loop> _loops = new Dictionary<int, Loop>();
        private readonly HashSet<SyntaxNode> _loopSpecStatements = new HashSet<SyntaxNode>();
        private readonly HashSet<SyntaxNode> _contractStatements = new HashSet<SyntaxNode>();
        private readonly HashSet<(string, TextSpan)> _reported = new HashSet<(string, TextSpan)>();
        private Frame _entry;
        private Term[] _entryMeasure;
        private int _paths, _unfoldDepth, _quantDepth;
        private readonly Stack<List<Term>> _quantFacts = new Stack<List<Term>>();
        private readonly Stack<Term> _conditionalInstances = new Stack<Term>(); // the receiver of the a?.b being evaluated
        private readonly Stack<Term> _patternInputs = new Stack<Term>(); // the value a property pattern { P: ... } reads P of

        /// <summary>A condition a partial operation needs: an index in bounds, a pure function's precondition, a divisor.</summary>
        private sealed class Obligation
        {
            public Term Condition;
            public string Id, Message;
            public SyntaxNode At;
        }

        // Well-definedness: obligations collected while an expression is evaluated, under the guards (&&, ||, ?:,
        // quantifier ranges) that protect them. A quantifier closes the obligations made inside it over its variable.
        private readonly Stack<List<Obligation>> _obligations = new Stack<List<Obligation>>();
        private readonly List<Term> _guards = new List<Term>();
        private int _foreignSpec; // > 0 while evaluating a callee's contract or definition: checked when the callee is

        /// <summary>
        /// The operation at <paramref name="at"/> is defined only if <paramref name="condition"/> holds. In code it is
        /// an obligation of its own (bounds, division, precondition); in one of this method's specifications it is a
        /// well-definedness obligation (CSV1012).
        /// </summary>
        private void Require(Term condition, string codeId, SyntaxNode at, string what)
        {
            if (!_codeMode && _foreignSpec > 0) return;
            var ob = new Obligation
            {
                Condition = T.Implies(T.And(_guards.ToArray()), condition),
                Id = _codeMode ? codeId : "CSV1012",
                At = at,
                Message = _codeMode ? what : $"specification might not be well-defined: {what}",
            };
            Emit(ob);
        }

        private void Emit(Obligation ob)
        {
            if (_obligations.Count > 0) _obligations.Peek().Add(ob);
            else if (_codeMode) Prove(ob.Condition, ob.Id, ob.At, ob.Message);
        }

        private void WithGuard(Term guard, Action action)
        {
            _guards.Add(guard);
            try { action(); }
            finally { _guards.RemoveAt(_guards.Count - 1); }
        }

        /// <summary>One of this method's own specifications: its well-definedness is proved before it is used.</summary>
        private Term EvalOwnSpec(IOperation op, Frame f, SpecEnv spec)
        {
            var obligations = new List<Obligation>();
            _obligations.Push(obligations);
            Term t;
            try { t = EvalSpec(op, f, spec); }
            finally { _obligations.Pop(); }
            foreach (var ob in obligations) Prove(ob.Condition, ob.Id, ob.At, ob.Message, assume: false);
            return t;
        }

        /// <summary>A callee's contract or definition, or a specification already checked elsewhere: no obligations.</summary>
        private Term EvalForeignSpec(IOperation op, Frame f, SpecEnv spec)
        {
            _foreignSpec++;
            try { return EvalSpec(op, f, spec); }
            finally { _foreignSpec--; }
        }

        /// <summary>Assumes a background fact, or inside a quantifier records it as a hypothesis of the quantifier's body.</summary>
        private void AssumeSide(Term fact)
        {
            if (_quantFacts.Count == 0) _z3.Assume(fact);
            else _quantFacts.Peek().Add(fact);
        }
        private bool _codeMode; // obligations are only generated for code, not for specification expressions

        /// <summary>
        /// Lemmas and [Pure]/[GhostFunction] methods are proofs and definitions: they must terminate on every path,
        /// or a lemma that loops forever would "prove" anything and a definition f(x) = f(x) + 1 would be false.
        /// </summary>
        private bool ProofCode => (_contract.IsLemma || _contract.IsPure) && !_contract.IsTrusted;

        public MethodVerifier(Engine engine, Contract contract, MethodResult result, ISet<string> excludedLoopFacts = null)
        {
            _excludedFacts = excludedLoopFacts;
            _engine = engine;
            _z3 = engine.Solver;
            _contract = contract;
            _method = contract.Method;
            _model = contract.Model;
            _result = result;
        }

        // ================================================================================== driver

        /// <summary>A lambda's or local function's flow graph, from its enclosing method's (Engine's nested functions).</summary>
        public ControlFlowGraph NestedGraph;

        /// <summary>When the method's time budget runs out (a Stopwatch timestamp; 0 for none).</summary>
        public long Deadline;
        public bool OverBudget => Deadline > 0 && System.Diagnostics.Stopwatch.GetTimestamp() > Deadline;

        /// <summary>Past the budget: reported once; the rest is not proved.</summary>
        private bool BudgetSpent()
        {
            if (!OverBudget) return false;
            if (!_budgetReported)
            {
                _budgetReported = true;
                NotModeled(MethodLocationNode(), $"time budget ({_engine.Options.MethodBudgetMs} ms) reached; the rest of '{_method.Name}' is not verified");
            }
            return true;
        }
        private bool _budgetReported;

        public void Run()
        {
            var body = _model.GetOperation(_contract.Declaration);
            ControlFlowGraph cfg;
            if (NestedGraph != null) cfg = NestedGraph;
            else switch (body)
            {
                case IMethodBodyOperation mb: cfg = ControlFlowGraph.Create(mb); break;
                case IConstructorBodyOperation cb: cfg = ControlFlowGraph.Create(cb); break;
                case IBlockOperation block: cfg = ControlFlowGraph.Create(block); break; // an expression-bodied property
                default: return;
            }
            FindContractStatements();
            CheckLocking();
            if (SpecSymbols.IsPredicate(_method)) { VerifyPredicate(); return; }
            if (SpecSymbols.IsInvariant(_method) && !Data.IsData(_method.ContainingType) && !SpecSymbols.IsOwned(_method.ContainingType) && !IsImmutableClass(_method.ContainingType))
                Warn(MethodLocationNode(), $"[Invariant] '{_method.Name}' is not used: {_method.ContainingType.Name} is mutable. Make it immutable (readonly fields) or [Owned], or state the invariant as a Valid() precondition (Dafny style)");
            if (SpecSymbols.IsInvariant(_method) && (Data.IsData(_method.ContainingType) || SpecSymbols.IsOwned(_method.ContainingType) || IsImmutableClass(_method.ContainingType)) &&
                _engine.Fields.InvariantDependence(_method, !Data.IsData(_method.ContainingType)) is string why)
                Report("CSV1015", MethodLocationNode(), $"invariant '{_method.Name}' could be broken behind its back: {why}", isError: true);
            if (ProofCode && _method.IsAsync) NotModeled(MethodLocationNode(), "a lemma or [Pure] function cannot be async");
            FindLoops(cfg);
            _cfg = cfg;

            _z3.Push();
            try
            {
                var f = new Frame { Heap = _z3.Fresh("heap", Sort.Heap) };
                if (!_method.IsStatic) { f.This = _z3.Fresh("this", Sort.Int); _z3.Assume(NotNull(f.This)); HasType(f.This, _method.ContainingType); }
                if (_engine.UsesOwnership) f.Root = _z3.Fresh("root", Sort.Row);
                if (_method.MethodKind == MethodKind.Constructor && !_method.IsStatic) EnterConstructor(f);
                foreach (var p in _method.Parameters)
                {
                    f.Vars[p] = FreshOf(p.Type, p.Name);
                    // a non-nullable parameter is a precondition: each caller proves it (an out parameter is not set yet)
                    if (p.RefKind != RefKind.Out && IsNonNullable(p)) _z3.Assume(NotNull(f.Vars[p]));
                    else if (p.RefKind != RefKind.Out && MayBeNullType(p.Type))
                        _z3.Origins[f.Vars[p].S] = $"parameter '{p.Name}' is declared '{NullableNote(p.Type)}'";
                }
                foreach (var alias in _contract.Aliases) AliasParameters(f, alias, _method.Parameters.Select(p => f.Vars.TryGetValue(p, out var v) ? v : null).ToArray());
                EnterAlloc(f);
                EnterOwned(f);
                EnterPredicates(f);
                EnterCells(f);
                EnterGate(f);
                _entry = EntryState(f);
                var spec = new SpecEnv { Old = _entry };
                CheckSubtyping(f, spec);
                // the permissions the preconditions give (then, as conditions, they say they are in hand)
                foreach (var req in _contract.Requires) Inhale(req, f, spec, f);
                // each precondition must be well-defined given the ones before it
                foreach (var req in _contract.Requires) _z3.Assume(AsBool(EvalOwnSpec(req, f, spec)));
                EnterFrames(f, spec);
                if (_contract.Decreases != null) _entryMeasure = _contract.Decreases.Select(m => ToMeasure(m, EvalOwnSpec(m, f, spec))).ToArray();
                _entry = EntryState(f);
                Exec(cfg.Blocks[0], f, new HashSet<int>());
            }
            finally { _z3.Pop(); }
        }

        /// <summary>The state Spec.Old refers to (for a constructor, from before its object was allocated).</summary>
        private Frame EntryState(Frame f)
        {
            var entry = f.Clone();
            if (_allocEntry != null) entry.Alloc = _allocEntry;
            return entry;
        }

        private void FindContractStatements()
        {
            BlockSyntax block = (_contract.Declaration as BaseMethodDeclarationSyntax)?.Body ?? (_contract.Declaration as AccessorDeclarationSyntax)?.Body ??
                                (_contract.Declaration as LocalFunctionStatementSyntax)?.Body ?? (_contract.Declaration as AnonymousFunctionExpressionSyntax)?.Block;
            if (block == null) return;
            foreach (var s in block.Statements.OfType<ExpressionStatementSyntax>())
                if (s.Expression is InvocationExpressionSyntax inv && SpecName(inv) is string n && (n == "Requires" || n == "Ensures" || n == "EnsuresOnThrow" || n == "Decreases" || n == "Modifies" || n == "Reads"))
                    _contractStatements.Add(inv);
        }

        private string SpecName(InvocationExpressionSyntax inv) =>
            _model.GetSymbolInfo(inv).Symbol is IMethodSymbol m && SpecSymbols.IsSpecClass(m.ContainingType) ? m.Name : null;

        private static bool HasExceptionRegion(ControlFlowRegion region) =>
            region.Kind == ControlFlowRegionKind.Try || region.Kind == ControlFlowRegionKind.Catch ||
            region.Kind == ControlFlowRegionKind.Finally || region.Kind == ControlFlowRegionKind.Filter ||
            region.NestedRegions.Any(HasExceptionRegion);

        private void FindLoops(ControlFlowGraph cfg)
        {
            foreach (var stmt in _contract.Declaration.DescendantNodes().OfType<StatementSyntax>())
            {
                StatementSyntax loopBody; ExpressionSyntax cond;
                switch (stmt)
                {
                    case WhileStatementSyntax w: loopBody = w.Statement; cond = w.Condition; break;
                    case ForStatementSyntax fs: loopBody = fs.Statement; cond = fs.Condition; break;
                    case DoStatementSyntax d: loopBody = d.Statement; cond = null; break;
                    case CommonForEachStatementSyntax fe: FindForEach(fe, cfg); continue;
                    default: continue;
                }
                var loop = new Loop { Id = _loops.Count, Syntax = stmt };
                var span = cond != null ? cond.Span : loopBody.Span;
                var heads = cfg.Blocks.Where(b => b.Operations.Any(o => span.Contains(o.Syntax.Span)) ||
                                                  (b.BranchValue != null && span.Contains(b.BranchValue.Syntax.Span)));
                if (!heads.Any()) continue;
                loop.Head = heads.Min(b => b.Ordinal);
                ReadLoopSpecs(loopBody is BlockSyntax bs ? bs.Statements : new SyntaxList<StatementSyntax>(loopBody), loop);
                InferLoopFacts(loop, cond);
                AddLoop(loop, new[] { stmt }, needsMeasure: true);
            }
            FindGotoLoops(cfg);
        }

        /// <summary>The loop's Spec.Invariant and Spec.Decreases: the leading statements of its body.</summary>
        private void ReadLoopSpecs(IEnumerable<StatementSyntax> leading, Loop loop)
        {
            foreach (var s in leading)
            {
                if (!(s is ExpressionStatementSyntax es && es.Expression is InvocationExpressionSyntax inv)) break;
                var name = SpecName(inv);
                if (name != "Invariant" && name != "Decreases") break;
                var args = ((IInvocationOperation)_model.GetOperation(inv)).Arguments;
                if (name == "Invariant") loop.Invariants.Add(args[0].Value); else loop.Decreases = args.Select(a => a.Value).ToList();
                _loopSpecStatements.Add(inv);
            }
        }

        /// <param name="roots">the syntax the loop runs (its statement, or the code of its blocks): what it may change</param>
        /// <param name="needsMeasure">in a proof, the loop must be shown to terminate with Spec.Decreases</param>
        private void AddLoop(Loop loop, IReadOnlyCollection<SyntaxNode> roots, bool needsMeasure)
        {
            if (ProofCode && needsMeasure && loop.Decreases == null)
                NotTotal(loop.Syntax, "a loop in a lemma or [Pure] function needs Spec.Decreases");
            CollectHavoc(roots, loop);
            loop.Permissions = roots.Any(LoopExchangesPermissions);
            if (loop.Permissions) loop.HavocRoot = true;
            _loops[loop.Head] = loop;
        }

        private void CollectHavoc(IEnumerable<SyntaxNode> roots, Loop loop)
        {
            var throughRefs = new HashSet<ISymbol>(SymbolEqualityComparer.Default);
            void Target(ExpressionSyntax e)
            {
                // a stubbed setter (list[i] = x): what its stub may change
                if (_model.GetSymbolInfo(e).Symbol is IPropertySymbol sp && sp.SetMethod != null && _engine.HasStub(sp.SetMethod))
                {
                    AddFieldWrites(loop, sp.SetMethod);
                    return;
                }
                // a struct's member: the struct that holds it changes (this, in a struct's constructor)
                if ((e is MemberAccessExpressionSyntax || e is IdentifierNameSyntax) && IsStructMember(_model.GetSymbolInfo(e).Symbol))
                {
                    if (e is MemberAccessExpressionSyntax sm) Target(sm.Expression); else loop.HavocThis = true;
                    return;
                }
                if (e is ThisExpressionSyntax) { loop.HavocThis = true; return; }
                // a write through a ref local writes whatever it is ever bound to
                if (e is IdentifierNameSyntax rn && _model.GetSymbolInfo(rn).Symbol is ILocalSymbol rl && rl.RefKind != RefKind.None)
                {
                    if (throughRefs.Add(rl)) foreach (var b in RefBindings(rl)) Target(b);
                    return;
                }
                if ((e is IdentifierNameSyntax || e is MemberAccessExpressionSyntax) && _model.GetSymbolInfo(e).Symbol is ISymbol hs && FieldEffects.IsHeapField(hs))
                {
                    loop.HavocFields.Add(FieldEffects.Key(hs));
                    return;
                }
                switch (e)
                {
                    case IdentifierNameSyntax _:
                        var s = _model.GetSymbolInfo(e).Symbol;
                        if (s is ILocalSymbol || s is IParameterSymbol) loop.Havoc.Add(s);
                        break;
                    case ElementAccessExpressionSyntax ea when ea.Expression is IdentifierNameSyntax:
                        var a = _model.GetSymbolInfo(ea.Expression).Symbol;
                        if ((a is ILocalSymbol || a is IParameterSymbol) && !IsSpan(TypeOf(a))) loop.HavocArrays.Add(a); else loop.HavocHeap = true;
                        break;
                    case ParenthesizedExpressionSyntax p: Target(p.Expression); break;
                    case DeclarationExpressionSyntax _: break;
                    default: loop.HavocHeap = true; break;
                }
            }
            foreach (var n in roots.SelectMany(r => r.DescendantNodesAndSelf(n => !(n is AnonymousFunctionExpressionSyntax))))
            {
                switch (n)
                {
                    case AssignmentExpressionSyntax asg when asg.Right is RefExpressionSyntax && _model.GetSymbolInfo(asg.Left).Symbol is ILocalSymbol rebound:
                        loop.Rebound.Add(rebound);
                        break;
                    case AssignmentExpressionSyntax asg: Target(asg.Left); break;
                    case PrefixUnaryExpressionSyntax pre when pre.IsKind(SyntaxKind.PreIncrementExpression) || pre.IsKind(SyntaxKind.PreDecrementExpression): Target(pre.Operand); break;
                    case PostfixUnaryExpressionSyntax post when post.IsKind(SyntaxKind.PostIncrementExpression) || post.IsKind(SyntaxKind.PostDecrementExpression): Target(post.Operand); break;
                    case ArgumentSyntax arg when !arg.RefKindKeyword.IsKind(SyntaxKind.None) && !arg.RefKindKeyword.IsKind(SyntaxKind.InKeyword): Target(arg.Expression); break;
                    case InvocationExpressionSyntax inv when _model.GetSymbolInfo(inv).Symbol is IMethodSymbol m: CalledInLoop(loop, m); break;
                    case AwaitExpressionSyntax _:
                        // other code runs at an await: as after a call to unknown code
                        loop.Awaits = loop.HavocRoot = true;
                        loop.Havoc.UnionWith(ClosureWritten());
                        break;
                    case BaseObjectCreationExpressionSyntax oc when _model.GetSymbolInfo(oc).Symbol is IMethodSymbol ctor:
                        AddFieldWrites(loop, ctor);
                        loop.HavocFields.UnionWith(FieldEffects.FieldsOf(ctor.ContainingType)); // the new object's fields are set
                        break;
                    case CommonForEachStatementSyntax fe:
                        // the iteration variables, and what the enumerator's methods do in each iteration
                        foreach (var l in ForEachLocals(fe)) loop.Havoc.Add(l);
                        if (!IsArrayForEach(fe) && !NestedViewForEach(fe))
                        {
                            var info = _model.GetForEachStatementInfo(fe);
                            foreach (var m in new[] { info.MoveNextMethod, info.CurrentProperty?.GetMethod }.Where(m => m != null)) CalledInLoop(loop, m);
                        }
                        break;
                }
            }
            foreach (var a in loop.HavocArrays) if (loop.Havoc.Contains(a)) loop.HavocHeap = true;
        }

        /// <summary>
        /// A foreach over a LINQ view (or a group) whose enumerator the verifier replaces by an index, if its own body
        /// leaves it one (what that body does is collected with the outer loop's anyway).
        /// </summary>
        private bool NestedViewForEach(CommonForEachStatementSyntax fe)
        {
            if (!(_model.GetOperation(fe.Expression) is IOperation collection) || ViewForEachElement(collection) == null) return false;
            var c = _model.GetForEachStatementInfo(fe).ElementConversion;
            return c.IsIdentity || c.IsImplicit && c.IsReference;
        }

        private void CalledInLoop(Loop loop, IMethodSymbol m)
        {
            if (RunsCode(m)) loop.Havoc.UnionWith(ClosureWritten());
            if (HavocsHeap(m)) loop.HavocHeap = true;
            if (SpecSymbols.IsCsVerifyType(m.ContainingType, "Own")) loop.HavocRoot = true;
            if (!SpecSymbols.IsSpecClass(m.ContainingType)) AddFieldWrites(loop, m);
        }

        private void AddFieldWrites(Loop loop, IMethodSymbol m)
        {
            var (fields, all) = _engine.Fields.WritesOf(m);
            loop.HavocFields.UnionWith(fields);
            loop.HavocAllFields |= all;
        }

        // ================================================================================== CFG walk

        private void Exec(BasicBlock block, Frame f, HashSet<int> onPath)
        {
            if (BudgetSpent()) return;
            // (a try with handlers: its raises collected and merged at the handlers; MethodVerifier.Exceptions)
            if (!ProofCode && _codeMode && _foreignSpec == 0 && TryEntry(block) is ControlFlowRegion tryAndCatch)
            {
                CollectTry(tryAndCatch, block, f, onPath);
                return;
            }
            if (++_paths > _engine.Options.MaxPaths)
            {
                if (_paths == _engine.Options.MaxPaths + 1)
                    NotModeled(MethodLocationNode(), $"path limit ({_engine.Options.MaxPaths}) reached; the rest of '{_method.Name}' is not verified");
                return;
            }
            if (block.Kind == BasicBlockKind.Exit) { CheckPostconditions(f); return; }

            if (_loops.TryGetValue(block.Ordinal, out var loop))
            {
                if (f.ActiveLoops.Contains(loop.Id)) { LoopBackEdge(loop, f); return; }
                LoopEntry(loop, f);
            }
            else if (onPath.Contains(block.Ordinal))
            {
                NotModeled(block.Operations.FirstOrDefault()?.Syntax ?? MethodLocationNode(), "a cycle with no single entry (a goto into a loop) is not supported");
                return;
            }

            onPath.Add(block.Ordinal);
            _codeMode = true;
            foreach (var op in block.Operations)
            {
                (_block, _current, _onPath) = (block, f, onPath);
                // (a task this method started may run at any moment: nothing it could write stays known from one statement to the next)
                if (f.Started.Values.Any(t => !t.Awaited)) Interleave(f);
                ExecOperation(op, f);
            }
            (_block, _current, _onPath) = (block, f, onPath);

            var fall = block.FallThroughSuccessor;
            var cond = block.ConditionalSuccessor;
            if (cond != null)
            {
                if (InSpec(block.BranchValue)) Follow(fall, f, onPath);
                else
                {
                    var c = AsBool(Eval(block.BranchValue, f));
                    var taken = block.ConditionKind == ControlFlowConditionKind.WhenTrue ? c : T.Not(c);
                    Branch(cond, f.Clone(), taken, onPath);
                    Branch(fall, f, T.Not(taken), onPath);
                }
            }
            else
            {
                if (block.BranchValue != null && !InSpec(block.BranchValue))
                {
                    if (fall?.Semantics == ControlFlowBranchSemantics.Throw && !ProofCode && block.BranchValue.Syntax is SwitchExpressionSyntax missed)
                    {
                        // the throw the compiler adds to a switch expression, for a value no arm matches: the switch
                        // must cover every value it gets (a failure the program did not write, as an index out of range)
                        Require(T.False, "CSV1022", missed, $"switch expression '{missed.GoverningExpression} switch' might not cover every value: it would throw SwitchExpressionException");
                        onPath.Remove(block.Ordinal);
                        return;
                    }
                    var v = Eval(block.BranchValue, f);
                    if (fall?.Semantics == ControlFlowBranchSemantics.Throw && !ProofCode)
                    {
                        // throw e: e is the exception (throwing null throws a NullReferenceException instead)
                        Require(NotNull(v), "CSV1013", block.BranchValue.Syntax, $"'{block.BranchValue.Syntax}' might be null: throwing it would throw a NullReferenceException");
                        if (ExceptionsObserved)
                        {
                            HasType(v, Unconverted(block.BranchValue).Type);
                            Raise(v, f, block.EnclosingRegion);
                        }
                        onPath.Remove(block.Ordinal);
                        return;
                    }
                    if (fall?.Semantics == ControlFlowBranchSemantics.Return)
                    {
                        f.Result = v;
                        f.ReturnSyntax = block.BranchValue.Syntax.Parent is ReturnStatementSyntax rs ? rs : block.BranchValue.Syntax;
                    }
                }
                else if (fall?.Semantics == ControlFlowBranchSemantics.Return)
                    f.ReturnSyntax = block.Operations.LastOrDefault()?.Syntax;
                if (fall?.Semantics == ControlFlowBranchSemantics.Rethrow && !ProofCode)
                {
                    // throw; in a catch: the exception it handles goes on outward
                    if (ExceptionsObserved) Raise(f.Exception ?? NewException(null), f, block.EnclosingRegion);
                    onPath.Remove(block.Ordinal);
                    return;
                }
                Follow(fall, f, onPath);
            }
            onPath.Remove(block.Ordinal);
        }

        private void Branch(ControlFlowBranch succ, Frame f, Term cond, HashSet<int> onPath)
        {
            _z3.Push();
            _z3.Assume(cond);
            if (_z3.Check(T.True) != "unsat") Follow(succ, f, onPath);
            _z3.Pop();
        }

        private void Follow(ControlFlowBranch succ, Frame f, HashSet<int> onPath)
        {
            if (succ?.Semantics == ControlFlowBranchSemantics.StructuredExceptionHandling)
            {
                Resume(f); // the end of a finally, or a filter that does not hold
                return;
            }
            if (succ?.Destination == null)
            {
                // throw, rethrow, program termination: no normal exit on this path (partial correctness), except
                // that a proof may not escape its obligations by throwing
                if (ProofCode && succ != null)
                    NotTotal(succ.Source.BranchValue?.Syntax ?? succ.Source.Operations.LastOrDefault()?.Syntax ?? MethodLocationNode(),
                        "a lemma or [Pure] function must not throw");
                return;
            }
            switch (succ.Semantics)
            {
                case ControlFlowBranchSemantics.Regular:
                case ControlFlowBranchSemantics.Return:
                    // leaving try regions: their finally blocks run on the way
                    if (succ.FinallyRegions.Length > 0) ThroughFinally(succ, 0, f, after => Exec(succ.Destination, after, onPath));
                    else Exec(succ.Destination, f, onPath);
                    break;
            }
        }

        private void LoopEntry(Loop loop, Frame f)
        {
            var spec = new SpecEnv { Old = _entry };
            foreach (var inv in loop.Invariants)
                Prove(AsBool(EvalForeignSpec(inv, f, spec)), "CSV1005", inv.Syntax, $"loop invariant '{inv.Syntax}' might not hold on entry");
            if (loop.Permissions) LoopPermissionsEntry(loop.Id, loop.Invariants, f, spec);

            LoopFactsEntry(loop, f);
            var memoryBefore = f.Heap;
            // what a loop without invariants changes is unknown at its head (charged to it in the library report)
            var wasCause = _z3.Cause;
            var wasOrigin = _z3.Origin;
            if (loop.Invariants.Count == 0)
            {
                _z3.Cause = "a loop without invariants";
                _z3.Origin = $"the loop at line {LineOf(loop.Syntax)} may change it (it has no invariants to say how)";
            }
            DeferTies();
            foreach (var s in loop.Havoc)
            {
                // a view of memory the loop reassigns: whatever view it holds at the head holds its cells
                bool liveView = IsMemView(TypeOf(s)) && f.LiveMemViews.Contains(s);
                if (liveView) ReleaseMemView(f, s);
                f.Vars[s] = FreshOf(TypeOf(s), s.Name);
                if (IsNonNullVariable(s)) _z3.Assume(NotNull(f.Vars[s])); // (every write proves it)
                if (liveView) MemViewAlive(f, s, f.Vars[s]);
            }
            // (other code at an await cannot reach the objects in confined locals the loop does not reassign)
            var confined = loop.Awaits ? ConfinedValues(f, loop.Havoc) : null;
            if (loop.HavocAllFields) HavocAllFields(f);
            else if (loop.Awaits) HavocAllFieldsKeeping(f, confined);
            foreach (var field in loop.HavocFields) f.Fields[field] = FreshMap(field);
            if (loop.HavocAllFields || loop.Awaits || loop.HavocFields.Count > 0) { f.Link = null; AllocAfterCall(f); }
            if (f.Root != null && (loop.HavocRoot || loop.HavocAllFields || loop.HavocFields.Any(IsOwnedField))) f.Root = _z3.Fresh("root", Sort.Row);
            if (loop.HavocThis && f.This != null) f.This = _z3.Fresh("this", Sort.Int);
            if (loop.HavocHeap) f.Heap = _z3.Fresh("heap", Sort.Heap);
            else
            {
                if (loop.Awaits) f.Heap = KeepConfinedArrays(_z3.Fresh("heap", Sort.Heap), f.Heap, confined);
                foreach (var a in loop.HavocArrays)
                    f.Heap = T.Store(f.Heap, Read(f, a), _z3.Fresh(a.Name + "$elems", Sort.Row));
            }
            // (a foreach's enumerator is captured once, before the loop: the same object in every iteration)
            foreach (var r in loop.Rebound) f.Refs.Remove(r);
            foreach (var key in f.Captures.Keys.Where(k => !_enumerators.Contains(k)).ToList()) f.Captures.Remove(key);
            LoopMemory(f, loop.Havoc, memoryBefore);
            FlushTies(f);
            ArrayForEachHead(loop, f);
            _z3.Cause = wasCause;
            _z3.Origin = wasOrigin;

            if (loop.Permissions) LoopPermissionsHead(loop.Invariants, f, spec);
            // well-definedness of invariants and measure, in an arbitrary iteration (each given the invariants before it)
            foreach (var inv in loop.Invariants) _z3.Assume(AsBool(EvalOwnSpec(inv, f, spec)));
            LoopFactsHead(loop, f);
            if (loop.Decreases != null) f.LoopMeasures[loop.Id] = loop.Decreases.Select(m => ToMeasure(m, EvalOwnSpec(m, f, spec))).ToArray();
            f.ActiveLoops.Add(loop.Id);
        }

        private void LoopBackEdge(Loop loop, Frame f)
        {
            CheckAwaitedInLoop(loop, f);
            LoopFactsBackEdge(loop, f);
            ArrayForEachNext(loop, f);
            var spec = new SpecEnv { Old = _entry };
            foreach (var inv in loop.Invariants)
                Prove(AsBool(EvalForeignSpec(inv, f, spec)), "CSV1006", inv.Syntax, $"loop invariant '{inv.Syntax}' might not be maintained by the loop");
            if (loop.Permissions) LoopPermissionsBackEdge(loop.Id, loop.Invariants, f, spec, loop.Syntax);
            if (loop.Decreases != null)
            {
                var before = f.LoopMeasures[loop.Id];
                var after = EvalMeasure(loop.Decreases, f, spec);
                Prove(LexDecreases(after, before), "CSV1007", loop.Decreases[0].Parent.Syntax,
                    $"loop measure '{MeasureText(loop.Decreases)}' might not decrease or might be negative");
            }
        }

        private void CheckPostconditions(Frame f)
        {
            ConstructorEstablishesLocks(f);
            CheckAllAwaited(f);
            var at = f.ReturnSyntax ?? MethodLocationNode();
            ExitOwned(f, at);
            ProveImmutableInvariants(f, at);
            ProveConstructorSetFields(f, at);
            // a non-nullable return type or out/ref parameter is a postcondition the callers assume
            if (f.Result != null && IsNonNullableReturn(_method))
                Prove(NotNull(f.Result), "CSV1014", at, $"'{_method.Name}' might return null, but its return type '{_method.ReturnType}' is not nullable");
            foreach (var p in _method.Parameters.Where(p => p.RefKind == RefKind.Out || p.RefKind == RefKind.Ref))
                if (IsNonNullable(p) && f.Vars.TryGetValue(p, out var pv))
                    Prove(NotNull(pv), "CSV1014", at, $"'{p.Name}' might be null on return, but its type '{p.Type}' is not nullable");
            // the permissions the postconditions give back must be in hand (and not lent to this method)
            var giving = f.Clone();
            foreach (var post in _contract.Ensures)
                Exhale(post.Expr, f, new SpecEnv { Old = _entry, Result = f.Result, ResultParameter = post.ResultParameter }, giving, at, null, null);
            foreach (var post in _contract.Ensures)
            {
                var spec = new SpecEnv { Old = _entry, Result = f.Result, ResultParameter = post.ResultParameter };
                var goal = AsBool(EvalOwnSpec(post.Expr, f, spec));
                Prove(GuardedBy(post, _entry, goal), "CSV1002", at,
                    $"postcondition '{post.Syntax}' might not hold on this return path");
            }
        }

        private SyntaxNode MethodLocationNode() => _contract.Declaration;

        // ================================================================================== statements

        private bool InSpec(IOperation op) => op != null && SpecSymbols.EnclosingSpecCall(op.Syntax, _model) != null;

        private void ExecOperation(IOperation op, Frame f)
        {
            if (op is IExpressionStatementOperation es) op = es.Operation;
            var specCall = SpecSymbols.EnclosingSpecCall(op.Syntax, _model);
            if (specCall == null) { CheckThisEscape(op); Eval(op, f); return; }
            if (op.Syntax != specCall) return; // a lowered piece of a specification argument: evaluated as a whole below
            if (_contractStatements.Contains(specCall) || _loopSpecStatements.Contains(specCall)) return;

            var inv = (IInvocationOperation)_model.GetOperation(specCall);
            var arg = inv.Arguments.Length > 0 ? inv.Arguments[0].Value : null;
            var spec = new SpecEnv { Old = _entry };
            switch (inv.TargetMethod.Name)
            {
                case "Assert":
                    Prove(AsBool(EvalOwnSpec(arg, f, spec)), "CSV1004", specCall, $"assertion '{arg.Syntax}' might not hold");
                    break;
                case "Assume":
                    _z3.Assume(AsBool(EvalOwnSpec(arg, f, spec)));
                    break;
                case "Fold":
                case "Unfold":
                    _codeMode = true;
                    if (inv.TargetMethod.Name == "Fold") Fold(inv, f, spec); else Unfold(inv, f, spec);
                    break;
                case "Invariant":
                case "Decreases":
                    Warn(specCall, $"Spec.{inv.TargetMethod.Name} must be a leading statement of a loop body or after a label a goto jumps back to (or of the method body for Decreases); ignored");
                    break;
                default:
                    Warn(specCall, $"Spec.{inv.TargetMethod.Name} must be a top-level statement of the method body; ignored");
                    break;
            }
            _codeMode = true;
        }

        // ================================================================================== obligations

        /// <param name="assume">continue as if the goal held; well-definedness checks need not (their quantified
        /// facts would only crowd the solver's instantiation)</param>
        private void Prove(Term goal, string id, SyntaxNode at, string message, bool assume = true)
        {
            if (!_engine.Options.Checked(id))
            {
                // outside the check profile: assumed (counted), not proved
                _result.AssumedObligations++;
                if (assume) _z3.Assume(goal);
                return;
            }
            bool wasCode = _codeMode;
            _result.Obligations++;
            if (BudgetSpent())
            {
                if (assume) _z3.Assume(goal);
                return; // (not proved: the method is reported not verified)
            }
            var r = _z3.Check(T.Not(goal));
            if (r == "unsat") _result.Proved++;
            else
            {
                if (id == "CSV1013" || id == "CSV1014") message += NullReasons(goal);
                if (r != "sat") message += $" (solver: {r})";
                Report(id, at, message, isError: true, causes: _z3.CausesIn(goal));
            }
            if (assume) _z3.Assume(goal); // continue as if it held, so one failure does not cascade
            _codeMode = wasCode;
        }

        private void Report(string id, SyntaxNode at, string message, bool isError, IReadOnlyCollection<string> causes = null)
        {
            if (isError && !_engine.Options.Checked(id)) return;
            if (!_reported.Add((id, at.Span))) return;
            _result.Diagnostics.Add(new VerificationDiagnostic(id, isError, message, at.GetLocation().GetLineSpan())
            {
                Causes = causes ?? (IReadOnlyCollection<string>)Array.Empty<string>(),
            });
        }

        private static string Where(SyntaxNode at) => at.SyntaxTree.FilePath + ":" + at.SpanStart;

        private static int LineOf(SyntaxNode at) => at.GetLocation().GetLineSpan().StartLinePosition.Line + 1;

        /// <summary>
        /// Why a value might be null, from where the values the failed condition mentions came from: a parameter
        /// declared nullable, a call that may return null, a call after which what was checked may have changed (with
        /// the usual fix). Empty if nothing is known.
        /// </summary>
        private string NullReasons(Term goal)
        {
            var origins = _z3.OriginsIn(goal);
            if (origins.Count == 0) return "";
            var text = ": " + string.Join("; ", origins.Take(3));
            if (origins.Any(o => o.Contains(" may change ")))
                text += " (a check made before a call does not hold after it: copy the value to a local, check that, and use the local)";
            return text;
        }

        private static string NullableNote(ITypeSymbol t) => t.ToDisplayString(SymbolDisplayFormat.MinimallyQualifiedFormat.WithMiscellaneousOptions(
            SymbolDisplayMiscellaneousOptions.UseSpecialTypes | SymbolDisplayMiscellaneousOptions.IncludeNullableReferenceTypeModifier));

        /// <summary>
        /// What a call's unknown values are charged to in the library report: a library member without a contract, or
        /// a method of the program without postconditions (whose callers know only its types). Null for a call with a
        /// contract, and for CsVerify's own library.
        /// </summary>
        private static string CallCause(IMethodSymbol m, Contract callee)
        {
            if (SpecSymbols.IsSpecClass(m.ContainingType) || IsCsVerifyNamespace(m.ContainingNamespace)) return null;
            if (m.MethodKind == MethodKind.Constructor && m.ContainingType.SpecialType == SpecialType.System_Object) return null; // base()
            if (m.IsImplicitlyDeclared && m.ContainingType.Locations.Any(l => l.IsInSource)) return null; // a class's default constructor
            if (!callee.HasSource) return "library " + m.OriginalDefinition.ToDisplayString();
            if (callee.IsStub || callee.IsPure || callee.IsLemma || callee.Ensures.Count > 0 || callee.ThrowEnsures.Count > 0) return null;
            return "source " + m.OriginalDefinition.ToDisplayString();
        }

        /// <summary>
        /// For a member of a program's struct (s.X, a[i].P.X), the variable or array cell that holds the struct; null for
        /// anything else (a class's field, which the callee could also reach).
        /// </summary>
        private IOperation StructMemberRoot(IOperation value)
        {
            bool member = false;
            while (true)
            {
                switch (value)
                {
                    case IFieldReferenceOperation sf when sf.Instance != null && IsStructMember(sf.Field): value = sf.Instance; member = true; continue;
                    case IPropertyReferenceOperation sp when sp.Instance != null && IsStructMember(sp.Property): value = sp.Instance; member = true; continue;
                    case ILocalReferenceOperation l when member && l.Local.RefKind == RefKind.None: return value;
                    case IParameterReferenceOperation _ when member: return value;
                    case IArrayElementReferenceOperation _ when member: return value;
                    default: return null;
                }
            }
        }

        private static bool IsCsVerifyNamespace(INamespaceSymbol ns)
        {
            for (; ns != null && !ns.IsGlobalNamespace; ns = ns.ContainingNamespace)
                if (ns.ContainingNamespace?.IsGlobalNamespace == true && ns.Name == "CsVerify") return true;
            return false;
        }

        private void Warn(SyntaxNode at, string message) => Report("CSV1900", at, message, isError: false);

        /// <summary>
        /// Something the verifier cannot model soundly: a path it does not follow, an effect it does not track. The
        /// method is then not verified (an error), instead of reporting "ok" for what was not checked.
        /// </summary>
        private void NotModeled(SyntaxNode at, string message)
        {
            // within a check profile, a warning: the method is verified around it, with its value unknown
            bool degrade = _engine.Options.CheckKinds != null;
            int before = _result.Diagnostics.Count;
            Report("CSV1901", at, degrade ? message + " (not modeled: treated as unknown)" : message, isError: !degrade);
            if (degrade && _result.Diagnostics.Count > before) _result.Unmodeled++;
        }
        private void NotModeled(SyntaxToken at, string message) => NotModeled(at.Parent, message);

        /// <summary>A proof (lemma, [Pure], [GhostFunction]) that might not terminate.</summary>
        private void NotTotal(SyntaxNode at, string message) => Report("CSV1011", at, message, isError: true);
        private void Warn(SyntaxToken at, string message) => Warn(at.Parent, message);

        private static bool ParamsOfLibraryCall(ICollectionExpressionOperation ce)
        {
            IOperation p = ce.Parent;
            while (p is IConversionOperation) p = p.Parent;
            return p is IArgumentOperation a && a.ArgumentKind == ArgumentKind.ParamCollection && !ce.Elements.Any(e => e is ISpreadOperation) &&
                   a.Parent is IInvocationOperation inv && inv.TargetMethod.DeclaringSyntaxReferences.Length == 0;
        }

        private void Unsupported(IOperation op)
        {
            NotModeled(op.Syntax, $"unsupported construct ({op.Kind})");
        }

        // ================================================================================== values

        private static bool IsIntegral(ITypeSymbol t)
        {
            switch (t?.SpecialType)
            {
                case SpecialType.System_SByte: case SpecialType.System_Byte:
                case SpecialType.System_Int16: case SpecialType.System_UInt16:
                case SpecialType.System_Int32: case SpecialType.System_UInt32:
                case SpecialType.System_Int64: case SpecialType.System_UInt64:
                case SpecialType.System_Char:
                    return true;
                default:
                    return t?.TypeKind == TypeKind.Enum;
            }
        }

        private static (BigInteger lo, BigInteger hi) RangeOf(ITypeSymbol t)
        {
            switch (t.TypeKind == TypeKind.Enum ? ((INamedTypeSymbol)t).EnumUnderlyingType.SpecialType : t.SpecialType)
            {
                case SpecialType.System_SByte: return (sbyte.MinValue, sbyte.MaxValue);
                case SpecialType.System_Byte: return (byte.MinValue, byte.MaxValue);
                case SpecialType.System_Int16: return (short.MinValue, short.MaxValue);
                case SpecialType.System_UInt16: case SpecialType.System_Char: return (ushort.MinValue, ushort.MaxValue);
                case SpecialType.System_UInt32: return (uint.MinValue, uint.MaxValue);
                case SpecialType.System_Int64: return (long.MinValue, long.MaxValue);
                case SpecialType.System_UInt64: return (ulong.MinValue, ulong.MaxValue);
                default: return (int.MinValue, int.MaxValue);
            }
        }

        internal static Sort SortOf(ITypeSymbol t)
        {
            if (SpecSymbols.IsGhostType(t)) return SortOf(((INamedTypeSymbol)t).TypeArguments[0]);
            if (SpecSymbols.IsSeqType(t)) return Sort.Row;
            if (t?.SpecialType == SpecialType.System_Single) return Sort.F32;
            if (t?.SpecialType == SpecialType.System_Double) return Sort.F64;
            return t?.SpecialType == SpecialType.System_Boolean ? Sort.Bool : Sort.Int;
        }

        private static bool IsSpan(ITypeSymbol t) =>
            t is INamedTypeSymbol n && (n.OriginalDefinition.ToDisplayString() == "System.Span<T>" || n.OriginalDefinition.ToDisplayString() == "System.ReadOnlySpan<T>");

        internal static bool IsSequence(ITypeSymbol t) =>
            t is IArrayTypeSymbol || t?.SpecialType == SpecialType.System_String || t?.SpecialType == SpecialType.System_Array ||
            (t is INamedTypeSymbol n && (n.OriginalDefinition.ToDisplayString() == "System.Span<T>" || n.OriginalDefinition.ToDisplayString() == "System.ReadOnlySpan<T>"));

        /// <summary>
        /// A sequence whose elements a holder can change: an array (System.Array too) or a span, not a string or a
        /// read-only span.
        /// </summary>
        internal static bool IsWritableSequence(ITypeSymbol t) =>
            t is IArrayTypeSymbol || t?.SpecialType == SpecialType.System_Array ||
            t is INamedTypeSymbol n && n.OriginalDefinition.ToDisplayString() == "System.Span<T>";

        private static ITypeSymbol TypeOf(ISymbol s) => s is ILocalSymbol l ? l.Type : ((IParameterSymbol)s).Type;

        private Term FreshOf(ITypeSymbol type, string hint)
        {
            var t = _z3.Fresh(hint, SortOf(type));
            if (IsIntegral(type)) { var (lo, hi) = RangeOf(type); _z3.Assume(T.InRange(t, lo, hi)); }
            if (IsSequence(type)) Len(t);
            if (IsSpan(type)) SomeSpan(t);
            HasType(t, type);
            return t;
        }

        private Term Len(Term seq)
        {
            var len = _z3.Apply("length", Sort.Int, new[] { seq });
            AssumeSide(T.InRange(len, 0, int.MaxValue));
            return len;
        }

        private Term Read(Frame f, ISymbol s)
        {
            if (f.Vars.TryGetValue(s, out var t)) return t;
            t = FreshOf(TypeOf(s), s.Name);
            // a variable a lambda or local function captures: some value of its type (it may run at any time), not null
            // if its type says so (each write of the outer variable is checked)
            if (!SymbolEqualityComparer.Default.Equals(s.ContainingSymbol, _method) &&
                (s is IParameterSymbol cp && IsNonNullable(cp) || s is ILocalSymbol && IsNonNullVariable(s)))
                _z3.Assume(NotNull(t));
            if (s is IParameterSymbol p && MayBeNullType(p.Type) && !IsNonNullable(p))
                _z3.Origins[t.S] = $"parameter '{p.Name}' is declared '{NullableNote(p.Type)}'";
            f.Vars[s] = t;
            return t;
        }

        private Term Unknown(ITypeSymbol type, string hint = "unknown") => FreshOf(type, hint);

        private static Term AsBool(Term t) => T.Coerce(t, Sort.Bool);

        private Term EvalSpec(IOperation op, Frame f, SpecEnv spec)
        {
            bool wasCode = _codeMode;
            _codeMode = false;
            try { return Eval(op, f, spec); }
            finally { _codeMode = wasCode; }
        }

        private Term Eval(IOperation op, Frame f, SpecEnv spec = null)
        {
            if (op == null) return _z3.Fresh("missing", Sort.Int);
            if (op.Syntax is StackAllocArrayCreationExpressionSyntax && !(op is IConversionOperation)) return StackAlloc(op, f, spec);
            // null as an int? (a literal typed so, or a conversion of one): no value, not the null reference
            if (op.ConstantValue.HasValue && op.ConstantValue.Value == null && IsNullableValue(op.Type)) return None();
            if (op.ConstantValue.HasValue && !(op is IAssignmentOperation))
            {
                switch (op.ConstantValue.Value)
                {
                    case bool b: return T.Bool(b);
                    case char c: return T.Int(c);
                    case null: return T.Int(0);
                    case string str: return StringLiteral(str, op.Type); // a string is its value (MethodVerifier.Values)
                    case float _:
                    case double _: return FloatLiteral(op.ConstantValue.Value);
                    case ulong ul: return T.Int(new BigInteger(ul));
                    case object o when IsIntegral(op.Type) || o is int || o is long: return T.Int(Convert.ToInt64(o));
                }
            }
            if (_arrayForEach.Count > 0 && EvalArrayForEach(op, f, spec) is Term element) return element;
            switch (op)
            {
                case IConversionOperation c: return EvalConversion(c, f, spec);
                case ILocalReferenceOperation l:
                    if (l.Local.RefKind != RefKind.None) return ReadRef(l.Local, f, l.Syntax);
                    return Read(f, l.Local);
                case IParameterReferenceOperation p:
                    if (spec?.ResultParameter != null && SymbolEqualityComparer.Default.Equals(p.Parameter, spec.ResultParameter))
                        return spec.Result ?? Unknown(p.Type, "result");
                    return Read(f, p.Parameter);
                case IInstanceReferenceOperation ir when ir.ReferenceKind == InstanceReferenceKind.PatternInput && _patternInputs.Count > 0:
                    return _patternInputs.Peek();
                case IInstanceReferenceOperation _: return f.This ?? (f.This = _z3.Fresh("this", Sort.Int));
                case IFlowCaptureReferenceOperation r:
                    if (f.Captures.TryGetValue(r.Id, out var cv)) return cv;
                    // a stubbed property captured unread (the target of d[k] = c ? x : y): read where it is used
                    return _captured.TryGetValue(r.Id, out var later) && IsStubbedProperty(later) ? f.Captures[r.Id] = Eval(later, f, spec) : Unknown(r.Type, "capture");
                case IFlowCaptureOperation fc:
                    _captured[fc.Id] = fc.Value;
                    if (IsStubbedProperty(fc.Value)) { f.Captures.Remove(fc.Id); return T.True; } // (its getter's precondition is for reads only)
                    return f.Captures[fc.Id] = Eval(fc.Value, f, spec);
                case IBinaryOperation b: return EvalBinary(b, f, spec);
                case IUnaryOperation u: return EvalUnary(u, f, spec);
                case ICaughtExceptionOperation _: return f.Exception ?? Unknown(op.Type, "exception");
                case IConditionalOperation cond when cond.WhenFalse != null:
                {
                    var c = AsBool(Eval(cond.Condition, f, spec));
                    Term whenTrue = null, whenFalse = null;
                    WithGuard(c, () => whenTrue = Eval(cond.WhenTrue, f, spec));
                    WithGuard(T.Not(c), () => whenFalse = Eval(cond.WhenFalse, f, spec));
                    return T.Ite(c, whenTrue, whenFalse);
                }
                case ISimpleAssignmentOperation rb when rb.IsRef && rb.Target is ILocalReferenceOperation rl:
                    return BindRef(rl.Local, rb.Value, f, spec, rb.Syntax);
                case ISimpleAssignmentOperation a:
                {
                    var v = T.Coerce(Eval(a.Value, f, spec), SortOf(a.Target.Type));
                    // moving a view (w = v) retires the variable it came from
                    if (SpecSymbols.IsViewType(a.Value.Type) && VariableOf(a.Value) is ISymbol moved) Release(f, moved);
                    if (SpecSymbols.IsLinearPackage(a.Value.Type) && VariableOf(a.Value) is ISymbol movedPackage) f.LivePackages.Remove(movedPackage);
                    if (IsMemView(a.Value.Type) && VariableOf(a.Value) is ISymbol movedView) ReleaseMemView(f, movedView);
                    Write(a.Target, v, f, spec);
                    return v;
                }
                case IDeconstructionAssignmentOperation da:
                {
                    var v = Eval(da.Value, f, spec);
                    if (SpecSymbols.IsLinearPackage(da.Value.Type))
                    {
                        if (VariableOf(da.Value) is ISymbol unpacked) f.LivePackages.Remove(unpacked);
                        Unpack(da.Target, v, (INamedTypeSymbol)da.Value.Type, f, spec);
                    }
                    else Deconstruct(da.Target, v, f, spec);
                    return v;
                }
                case ICompoundAssignmentOperation ca:
                {
                    var old = Eval(ca.Target, f, spec);
                    var v = Arith(ca.OperatorKind, old, Eval(ca.Value, f, spec), ca.Type, ca.Syntax, ca.OperatorMethod != null, ca.IsChecked);
                    Write(ca.Target, v, f, spec);
                    return v;
                }
                case IIncrementOrDecrementOperation inc:
                {
                    var old = Eval(inc.Target, f, spec);
                    var kind = inc.Kind == OperationKind.Increment ? BinaryOperatorKind.Add : BinaryOperatorKind.Subtract;
                    var v = Arith(kind, old, IsFloating(inc.Type) ? FloatLiteral(inc.Type.SpecialType == SpecialType.System_Single ? (object)1f : 1d) : T.Int(1), inc.Type, inc.Syntax, inc.OperatorMethod != null, inc.IsChecked);
                    Write(inc.Target, v, f, spec);
                    return inc.IsPostfix ? old : v;
                }
                case IArrayElementReferenceOperation ae:
                {
                    var arr = Eval(ae.ArrayReference, f, spec);
                    var idx = CellOf(ae, arr, f, spec);
                    CheckCellFraming(arr, idx, f, ae.Syntax);
                    CheckCellRead(arr, idx, f, ae.Syntax);
                    return InRangeOf(T.Coerce(T.Select(T.Select(f.Heap, arr, Sort.Row), idx, Sort.Int), SortOf(op.Type)), op.Type);
                }
                case IPropertyReferenceOperation pr: return EvalProperty(pr, f, spec);
                case ITranslatedQueryOperation tq: return Eval(tq.Operation, f, spec); // (query syntax: the calls it stands for)
                case IAnonymousObjectCreationOperation ao: return AnonymousObject(ao, f, spec);
                case IFieldReferenceOperation hf when FieldEffects.IsHeapField(hf.Field) && (hf.Instance != null || hf.Field.IsStatic):
                    return ReadField(hf.Field, hf.Instance, hf.Type, hf.Syntax, f, spec);
                case IFieldReferenceOperation fr when fr.Field.ContainingType?.IsTupleType == true && fr.Instance != null:
                    return T.Coerce(TupleItem(Eval(fr.Instance, f, spec), fr.Field), SortOf(fr.Type));
                case ITupleOperation tuple: return TupleValue(tuple, f, spec);
                case IFieldReferenceOperation fr:
                {
                    var args = fr.Instance != null ? new[] { Eval(fr.Instance, f, spec) } : Array.Empty<Term>();
                    if (fr.Instance != null) Deref(fr.Instance, args[0], fr.Syntax);
                    if (!fr.Field.IsReadOnly && !fr.Field.IsConst && !IsStructMember(fr.Field))
                        NotModeled(fr.Syntax, $"mutable field '{fr.Field.Name}' is not supported (its writes are not tracked)");
                    var fv = T.Coerce(_z3.Apply(fr.Field.OriginalDefinition.ToDisplayString(), SortOf(fr.Field.OriginalDefinition.Type), args), SortOf(fr.Type));
                    if (IsNonNullReadonlyStatic(fr.Field)) AssumeSide(NotNull(fv));
                    return fv;
                }
                case IInvocationOperation inv: return EvalInvocation(inv, f, spec);
                case IAwaitOperation aw: return EvalAwait(aw, f, spec);
                case IArrayCreationOperation ac: return EvalArrayCreation(ac, f, spec);
                case ICollectionExpressionOperation ce when ParamsOfLibraryCall(ce):
                {
                    // the arguments a library method takes as a params span (string.Format with four): evaluated, in
                    // order, and handed over as a span the verifier does not look into
                    foreach (var e in ce.Elements) Eval(e, f, spec);
                    return Unknown(ce.Type, "params");
                }
                case IDefaultValueOperation _ when IsNullableValue(op.Type): return None();
                case IDefaultValueOperation _: return SortOf(op.Type) == Sort.Bool ? T.False : IsFloating(op.Type) ? Zero(SortOf(op.Type)) : T.Int(0);
                case IDeclarationExpressionOperation d: return Eval(d.Expression, f, spec);
                case IArgumentOperation arg: return Eval(arg.Value, f, spec);
                case IExpressionStatementOperation es: return Eval(es.Operation, f, spec);
                case IObjectCreationOperation oc: return NewObject(oc, f, spec);
                case IIsNullOperation isn:
                {
                    // the lowering of ?. and ?? in code
                    var v = Eval(isn.Operand, f, spec);
                    if (IsNullableValue(isn.Operand.Type)) return T.Not(HasValue(v));
                    return MayBeNullType(isn.Operand.Type) ? T.Eq(v, T.Int(0)) : _z3.Fresh("isnull", Sort.Bool);
                }
                case IIsPatternOperation ip: return Pattern(ip.Pattern, Eval(ip.Value, f, spec), f, spec);
                case IIsTypeOperation it when !it.IsNegated: return TypeTest(Eval(it.ValueOperand, f, spec), it.ValueOperand.Type, it.TypeOperand);
                case ISwitchExpressionOperation sw: return SwitchExpression(sw, f, spec);
                case IConditionalAccessOperation ca when MayBeNullType(ca.Type):
                {
                    // a?.b in a specification (code sees it lowered): b is evaluated, and well-defined, only if a is not null
                    var r = Eval(ca.Operation, f, spec);
                    Term v = null;
                    _conditionalInstances.Push(r);
                    try { WithGuard(NotNull(r), () => v = Eval(ca.WhenNotNull, f, spec)); }
                    finally { _conditionalInstances.Pop(); }
                    return T.Ite(NotNull(r), T.Coerce(v, Sort.Int), T.Int(0));
                }
                case IConditionalAccessInstanceOperation _:
                    return _conditionalInstances.Peek();
                case ICoalesceOperation co when IsNullableValue(co.Value.Type):
                {
                    // x ?? y on a nullable value: x's value (or x, if the result is nullable too), else y
                    var v = Eval(co.Value, f, spec);
                    var has = HasValue(v);
                    Term w = null;
                    WithGuard(T.Not(has), () => w = Eval(co.WhenNull, f, spec));
                    var present = IsNullableValue(co.Type) ? v : ValueOf(v, co.Value.Type);
                    return T.Ite(has, T.Coerce(present, SortOf(co.Type)), T.Coerce(w, SortOf(co.Type)));
                }
                case IInterpolatedStringOperation interpolated:
                {
                    // $"...": its holes are evaluated (and checked); the string is one of unknown contents, never null
                    foreach (var part in interpolated.Parts.OfType<IInterpolationOperation>())
                    {
                        Eval(part.Expression, f, spec);
                        if (part.Alignment != null) Eval(part.Alignment, f, spec);
                    }
                    var str = Unknown(op.Type, "interpolated");
                    AssumeSide(NotNull(str));
                    return str;
                }
                case ICoalesceOperation co when MayBeNullType(co.Value.Type) && MayBeNullType(co.Type):
                {
                    var v = Eval(co.Value, f, spec);
                    Term w = null;
                    WithGuard(T.Eq(v, T.Int(0)), () => w = Eval(co.WhenNull, f, spec));
                    return T.Ite(T.Eq(v, T.Int(0)), T.Coerce(w, Sort.Int), v);
                }
                case IFlowAnonymousFunctionOperation _:
                case IDelegateCreationOperation _:
                case IAnonymousFunctionOperation _:
                {
                    var d = _z3.Fresh("delegate", Sort.Int);
                    AssumeSide(NotNull(d)); // a lambda, or a method group made a delegate, is never null
                    return d;
                }
                case ILiteralOperation _:
                    return Unknown(op.Type, "literal");
                default:
                    foreach (var child in op.ChildOperations) Eval(child, f, spec);
                    Unsupported(op);
                    var unknown = Unknown(op.Type);
                    // (within a check profile, the value is what its type declares: not null if not nullable)
                    if (_engine.Options.CheckKinds != null && IsNonNullableType(op.Type)) AssumeSide(NotNull(unknown));
                    return unknown;
            }
        }

        private Term EvalConversion(IConversionOperation c, Frame f, SpecEnv spec)
        {
            var v = Eval(c.Operand, f, spec);
            var from = c.Operand.Type;
            if (c.OperatorMethod == null && (IsNullableValue(c.Type) || IsNullableValue(from))) return NullableConversion(c, v);
            // T[] -> Span<T> / ReadOnlySpan<T> (a span conversion in C# 14, an operator before): the array's own cells
            if (from is IArrayTypeSymbol && IsSpan(c.Type)) return SpanOfArray(v);
            if (c.IsTryCast && c.Conversion.IsReference && ClassTest(v, c.Type) is Term isInstance)
                return T.Ite(isInstance, T.Coerce(v, Sort.Int), T.Int(0)); // as: the object, or null
            if (!c.IsImplicit && c.Conversion.IsReference && from != null && !DataTypes.Derives(from, c.Type) && !Data.IsData(c.Type) &&
                ClassTest(v, c.Type) is Term instance)
            {
                // a downcast throws unless the object is an instance (or null): code that goes on knows it was
                var ok = T.Or(T.Eq(v, T.Int(0)), instance);
                if (_codeMode && !ProofCode)
                {
                    if (_current != null) MayRaise(T.Not(ok), _current, KnownType("System.InvalidCastException"));
                    _z3.Assume(ok);
                }
                else Require(ok, "CSV1011", c.Syntax, $"cast '{c.Syntax}' might fail");
            }
            if (!c.IsImplicit && c.Conversion.IsReference && Data.IsData(c.Type) && from != null && !DataTypes.Derives(from, c.Type))
            {
                // a downcast to a case: it throws unless the value is one (or null). Code that goes on knows it
                // was; a proof or a specification, which may not throw, must show it
                var ok = T.Or(T.Eq(v, T.Int(0)), TypeTest(v, from, c.Type));
                if (_codeMode && !ProofCode)
                {
                    if (_current != null) MayRaise(T.Not(ok), _current, KnownType("System.InvalidCastException"));
                    _z3.Assume(ok);
                }
                else Require(ok, "CSV1011", c.Syntax, $"cast '{c.Syntax}' might fail");
            }
            if (c.OperatorMethod != null)
            {
                // T[] -> Span<T> / ReadOnlySpan<T> keeps the same storage.
                if (from is IArrayTypeSymbol && IsSequence(c.Type)) return IsSpan(c.Type) ? SpanOfArray(v) : v;
                Unsupported(c);
                return Unknown(c.Type);
            }
            if (IsFloating(c.Type) && (IsFloating(from) || IsIntegral(from)) || IsFloating(from) && IsIntegral(c.Type))
                return FloatConversion(v, from, c.Type, c);
            if (IsIntegral(c.Type) && IsIntegral(from))
                return Bounded(v, c.Type, c.Syntax, c.IsChecked, $"conversion '{c.Syntax}' to {c.Type.Name} might overflow");
            else if (IsIntegral(c.Type) && !IsIntegral(from) && from?.SpecialType != SpecialType.System_Boolean && !SpecSymbols.IsGhostType(from) && from != null && from.TypeKind != TypeKind.TypeParameter)
            {
                return Unknown(c.Type, "conv");
            }
            return T.Coerce(v, SortOf(c.Type));
        }

        /// <summary>x == null of a record: its == calls no Equals when either side is null, whatever its fields are.</summary>
        private Term RecordAgainstNull(IBinaryOperation b, Frame f, SpecEnv spec)
        {
            if (b.OperatorMethod == null || !b.OperatorMethod.IsImplicitlyDeclared || !Data.IsData(b.OperatorMethod.ContainingType) ||
                !(b.OperatorKind == BinaryOperatorKind.Equals || b.OperatorKind == BinaryOperatorKind.NotEquals)) return null;
            bool right = IsNullConstant(Unconverted(b.RightOperand)), left = IsNullConstant(Unconverted(b.LeftOperand));
            if (right == left) return null;
            var notNull = NotNull(T.Coerce(Eval(right ? b.LeftOperand : b.RightOperand, f, spec), Sort.Int));
            return b.OperatorKind == BinaryOperatorKind.Equals ? T.Not(notNull) : notNull;
        }

        private Term EvalBinary(IBinaryOperation b, Frame f, SpecEnv spec)
        {
            // (x == null on an int? is not marked lifted, but compares the same way)
            if (b.IsLifted || b.OperatorMethod == null && (IsNullableValue(b.LeftOperand.Type) || IsNullableValue(b.RightOperand.Type)))
                return LiftedBinary(b, f, spec);
            if (RecordAgainstNull(b, f, spec) is Term againstNull) return againstNull;
            if (IsRecordEquality(b)) return RecordEquality(b, f, spec);
            if (b.OperatorMethod != null && b.OperatorMethod.IsImplicitlyDeclared && Data.IsData(b.OperatorMethod.ContainingType))
            {
                // a record whose fields compare in ways the verifier does not model (strings by contents, say)
                Eval(b.LeftOperand, f, spec); Eval(b.RightOperand, f, spec);
                Warn(b.Syntax, $"'{b.Syntax}': {b.OperatorMethod.ContainingType.Name} has fields whose equality is not modeled; the result is unknown");
                return Unknown(b.Type);
            }
            if (b.OperatorMethod != null && b.OperatorMethod.ContainingType.SpecialType == SpecialType.System_String &&
                (b.OperatorKind == BinaryOperatorKind.Equals || b.OperatorKind == BinaryOperatorKind.NotEquals) &&
                (IsNullConstant(b.LeftOperand) || IsNullConstant(b.RightOperand)))
            {
                // string's == against null is the reference comparison
                var eq = T.Eq(Eval(b.LeftOperand, f, spec), Eval(b.RightOperand, f, spec));
                return b.OperatorKind == BinaryOperatorKind.NotEquals ? T.Not(eq) : eq;
            }
            if (b.OperatorMethod != null)
            {
                if (SpecSymbols.IsGhostType(b.OperatorMethod.ContainingType) || SpecSymbols.IsSeqType(b.OperatorMethod.ContainingType))
                {
                    var eq = T.Eq(Eval(b.LeftOperand, f, spec), Eval(b.RightOperand, f, spec));
                    return b.OperatorKind == BinaryOperatorKind.NotEquals ? T.Not(eq) : eq;
                }
                Eval(b.LeftOperand, f, spec); Eval(b.RightOperand, f, spec);
                Unsupported(b);
                return Unknown(b.Type);
            }
            var l = Eval(b.LeftOperand, f, spec);
            if (b.OperatorKind == BinaryOperatorKind.ConditionalAnd || b.OperatorKind == BinaryOperatorKind.ConditionalOr)
            {
                // the right operand is evaluated only when the left one did not decide: that is its guard
                bool and = b.OperatorKind == BinaryOperatorKind.ConditionalAnd;
                Term right = null;
                WithGuard(and ? AsBool(l) : T.Not(AsBool(l)), () => right = AsBool(Eval(b.RightOperand, f, spec)));
                return and ? T.And(AsBool(l), right) : T.Or(AsBool(l), right);
            }
            var r = Eval(b.RightOperand, f, spec);
            var opType = b.LeftOperand.Type;
            if (IsFloating(opType) || IsFloating(b.RightOperand.Type))
                return FloatBinary(b.OperatorKind, l, r, IsFloating(opType) ? opType : b.RightOperand.Type, b.Syntax, b.Type);
            bool numeric = IsIntegral(opType) || IsIntegral(b.RightOperand.Type) || SpecSymbols.IsGhostType(opType);
            bool boolean = l.Sort == Sort.Bool && r.Sort == Sort.Bool;
            if ((b.OperatorKind == BinaryOperatorKind.Equals || b.OperatorKind == BinaryOperatorKind.NotEquals) && opType?.SpecialType == SpecialType.System_String)
                StringsCompared(l, r);
            switch (b.OperatorKind)
            {
                case BinaryOperatorKind.Equals: return numeric || boolean || IsModeledReferenceEquality(b) || SpecSymbols.IsLinear(opType) ? T.Eq(l, r) : Unknown(b.Type);
                case BinaryOperatorKind.NotEquals: return numeric || boolean || IsModeledReferenceEquality(b) ? T.Not(T.Eq(l, r)) : Unknown(b.Type);
                case BinaryOperatorKind.LessThan: return numeric ? T.Lt(l, r) : Unknown(b.Type);
                case BinaryOperatorKind.LessThanOrEqual: return numeric ? T.Le(l, r) : Unknown(b.Type);
                case BinaryOperatorKind.GreaterThan: return numeric ? T.Gt(l, r) : Unknown(b.Type);
                case BinaryOperatorKind.GreaterThanOrEqual: return numeric ? T.Ge(l, r) : Unknown(b.Type);
                case BinaryOperatorKind.And when boolean: return T.And(l, r);
                case BinaryOperatorKind.Or when boolean: return T.Or(l, r);
                case BinaryOperatorKind.ExclusiveOr when boolean: return T.Xor(l, r);
                case BinaryOperatorKind.Add when b.Type?.SpecialType == SpecialType.System_String &&
                                                 b.LeftOperand.Type?.SpecialType == SpecialType.System_String && b.RightOperand.Type?.SpecialType == SpecialType.System_String:
                {
                    // a + b: a string of unknown characters, never null, as long as both (null counts as empty)
                    var cat = Unknown(b.Type, "concat");
                    Term LengthOf(Term x) => IsNullConstant(b.LeftOperand) && x == l || IsNullConstant(b.RightOperand) && x == r ? T.Int(0) : T.Ite(T.Eq(x, T.Int(0)), T.Int(0), Len(x));
                    AssumeSide(T.And(NotNull(cat), T.Eq(Len(cat), T.Add(LengthOf(l), LengthOf(r)))));
                    ConcatIs(cat, IsNullConstant(b.LeftOperand) ? T.Int(0) : l, IsNullConstant(b.RightOperand) ? T.Int(0) : r);
                    return cat;
                }
                default: return Arith(b.OperatorKind, l, r, b.Type, b.Syntax, false, b.IsChecked);
            }
        }

        /// <summary>
        /// Reference <c>==</c> is the verifier's equality of references, except where one side may be a data value:
        /// data values have no identity of their own (a value is its contents), so only a comparison with null is known.
        /// </summary>
        private bool IsModeledReferenceEquality(IBinaryOperation b)
        {
            var t = b.LeftOperand.Type;
            if (t?.IsReferenceType != true) return false;
            if (IsNullConstant(b.LeftOperand) || IsNullConstant(b.RightOperand)) return true;
            // (an anonymous object is a value here: which reference it is, is not known)
            return !Data.MayHoldData(Unconverted(b.LeftOperand).Type) && !Data.MayHoldData(Unconverted(b.RightOperand).Type) &&
                   Unconverted(b.LeftOperand).Type?.IsAnonymousType != true && Unconverted(b.RightOperand).Type?.IsAnonymousType != true;
        }

        /// <summary>
        /// What a flow capture captured, where it is a variable: a call whose arguments branch (a ?: among them) has
        /// the flow graph capture the earlier ones first, by-ref ones too, and pass the captures.
        /// </summary>
        private IOperation Uncaptured(IOperation op) =>
            op is IFlowCaptureReferenceOperation r && _captured.TryGetValue(r.Id, out var captured) && IsVariableReference(captured) ? captured : op;

        /// <summary>The operand under implicit reference conversions (reference == converts both sides to object).</summary>
        private static IOperation Unconverted(IOperation op)
        {
            while (op is IConversionOperation c && c.IsImplicit && c.Conversion.IsReference) op = c.Operand;
            return op;
        }

        private int _ghostDepth;

        /// <summary>Ghost computation (erased: lemma and [GhostFunction] bodies, Ghost.Of arguments) uses mathematical integers.</summary>
        private bool InGhostCode => _ghostDepth > 0 || _contract.IsLemma || SpecSymbols.IsGhostFunction(_method) || SpecSymbols.IsPredicate(_method);

        /// <summary>
        /// Bounded integers. A run-time result <paramref name="v"/> of <paramref name="type"/>:
        /// in an explicit <c>unchecked</c> expression or statement it wraps around, exactly as C# computes it; in a
        /// <c>checked</c> context it throws on overflow, so code that goes on may assume it did not (a proof, which
        /// may not throw, must show it); otherwise (C#'s default, silently wrapping) overflow is reported (CSV1010).
        /// Specifications and ghost code are mathematical. With --no-overflow all integers are mathematical.
        /// </summary>
        private Term Bounded(Term v, ITypeSymbol type, SyntaxNode at, bool isChecked, string message)
        {
            if (!_codeMode || InGhostCode || !_engine.Options.CheckOverflow || !IsIntegral(type)) return v;
            var (lo, hi) = RangeOf(type);
            if (ExplicitlyUnchecked(at))
                return new Term($"(+ (mod (- {v} {T.Int(lo)}) {T.Int(hi - lo + 1)}) {T.Int(lo)})", Sort.Int);
            if (isChecked && !ProofCode)
            {
                // it throws on overflow: a handler, if any, sees that; code that goes on knows it did not
                if (_current != null) MayRaise(T.Not(T.InRange(v, lo, hi)), _current, KnownType("System.OverflowException"));
                _z3.Assume(T.InRange(v, lo, hi));
                return v;
            }
            // (where the operation is evaluated only under conditions: the right operand of &&, a lifted operator's values)
            Prove(T.Implies(T.And(_guards.ToArray()), T.InRange(v, lo, hi)), "CSV1010", at, message);
            return v;
        }

        /// <summary>A value read from memory (a field, an array element, a [Pure] result) of an integer type is in its range.</summary>
        private Term InRangeOf(Term v, ITypeSymbol type)
        {
            if (_engine.Options.CheckOverflow && IsIntegral(type) && v.Sort == Sort.Int)
            {
                var (lo, hi) = RangeOf(type);
                AssumeSide(T.InRange(v, lo, hi));
            }
            return v;
        }

        /// <summary>Is the nearest checked/unchecked expression or statement around this one <c>unchecked</c>?</summary>
        private static bool ExplicitlyUnchecked(SyntaxNode at)
        {
            for (var n = at; n != null; n = n.Parent)
            {
                if (n is CheckedExpressionSyntax ce) return ce.IsKind(SyntaxKind.UncheckedExpression);
                if (n is CheckedStatementSyntax cs) return cs.IsKind(SyntaxKind.UncheckedStatement);
            }
            return false;
        }

        private Term Arith(BinaryOperatorKind kind, Term l, Term r, ITypeSymbol type, SyntaxNode at, bool userDefined, bool isChecked = false)
        {
            if (!userDefined && IsFloating(type)) return FloatBinary(kind, l, r, type, at, type);
            if (userDefined || !IsIntegral(type) || l.Sort != Sort.Int || r.Sort != Sort.Int)
            {
                if (!userDefined && l.Sort == Sort.Bool && r.Sort == Sort.Bool)
                {
                    if (kind == BinaryOperatorKind.And) return T.And(l, r);
                    if (kind == BinaryOperatorKind.Or) return T.Or(l, r);
                    if (kind == BinaryOperatorKind.ExclusiveOr) return T.Xor(l, r);
                }
                if (_codeMode) Warn(at, $"operator on {type?.Name ?? "?"} is not modeled; result is unknown");
                var unknown = Unknown(type);
                if (!userDefined && type?.SpecialType == SpecialType.System_String && kind == BinaryOperatorKind.Add)
                    AssumeSide(NotNull(unknown)); // a concatenation is never null
                return unknown;
            }
            Term v;
            switch (kind)
            {
                case BinaryOperatorKind.Add: v = T.Add(l, r); break;
                case BinaryOperatorKind.Subtract: v = T.Sub(l, r); break;
                case BinaryOperatorKind.Multiply: v = T.Mul(l, r); break;
                case BinaryOperatorKind.Divide:
                case BinaryOperatorKind.Remainder:
                    Require(T.Not(T.Eq(r, T.Int(0))), "CSV1009", at, $"possible division by zero in '{at}'");
                    v = kind == BinaryOperatorKind.Divide ? T.Div(l, r) : T.Rem(l, r);
                    isChecked = true; // MinValue / -1 (and % -1) throw in .NET even when unchecked
                    break;
                case BinaryOperatorKind.LeftShift:
                case BinaryOperatorKind.RightShift:
                case BinaryOperatorKind.UnsignedRightShift:
                case BinaryOperatorKind.And:
                case BinaryOperatorKind.Or:
                case BinaryOperatorKind.ExclusiveOr:
                    return Bitwise(kind, l, r, type); // (it cannot overflow: shifts drop bits, even in checked code)
                default:
                    if (_codeMode) Warn(at, $"operator {kind} is not modeled; result is unknown");
                    return Unknown(type);
            }
            return Bounded(v, type, at, isChecked, $"arithmetic '{at}' might overflow {type.Name}");
        }

        private Term EvalUnary(IUnaryOperation u, Frame f, SpecEnv spec)
        {
            var v = Eval(u.Operand, f, spec);
            switch (u.OperatorKind)
            {
                case UnaryOperatorKind.Not: return T.Not(AsBool(v));
                case UnaryOperatorKind.Plus: return v;
                case UnaryOperatorKind.Minus when IsFloating(u.Type): return FloatNegate(v, u.Type);
                case UnaryOperatorKind.Minus when v.Sort == Sort.Int && IsIntegral(u.Type):
                    return Arith(BinaryOperatorKind.Subtract, T.Int(0), v, u.Type, u.Syntax, false, u.IsChecked);
                case UnaryOperatorKind.BitwiseNegation when v.Sort == Sort.Int && IsIntegral(u.Type) && u.Type.TypeKind != TypeKind.Enum:
                    return Complement(v, u.Type);
                default:
                    Unsupported(u);
                    return Unknown(u.Type);
            }
        }

        /// <summary><c>(a, b) = t</c> and <c>var (a, b) = t</c>: each target gets the tuple's item at its position.</summary>
        private void Deconstruct(IOperation target, Term tuple, Frame f, SpecEnv spec)
        {
            if (target is IDeclarationExpressionOperation d) target = d.Expression;
            if (!(target is ITupleOperation targets) || !(targets.Type is INamedTypeSymbol type && type.IsTupleType))
            {
                Unsupported(target);
                return;
            }
            var fields = type.TupleElements;
            for (int i = 0; i < targets.Elements.Length; i++)
            {
                var item = TupleItem(tuple, fields[i]);
                var element = targets.Elements[i] is IDeclarationExpressionOperation de ? de.Expression : targets.Elements[i];
                if (element is ITupleOperation) Deconstruct(element, item, f, spec);
                else if (!(element is IDiscardOperation)) Write(element, T.Coerce(item, SortOf(element.Type)), f, spec);
            }
        }

        /// <summary>Item n of a tuple, by position: named elements (<c>r.k</c>) and <c>ItemN</c> are the same function.</summary>
        private Term TupleItem(Term tuple, IFieldSymbol field)
        {
            var item = field.CorrespondingTupleField ?? field;
            return _z3.Apply("tuple." + item.Name, SortOf(item.Type), new[] { tuple });
        }

        private void BoundsCheck(Term seq, Term idx, SyntaxNode at)
        {
            var len = Len(seq);
            Require(T.And(T.Le(T.Int(0), idx), T.Lt(idx, len)), "CSV1003", at, $"index in '{at}' might be out of range");
        }

        /// <summary>What each flow capture captured (the flow graph is the method's, so one map serves every path).</summary>
        private readonly Dictionary<CaptureId, IOperation> _captured = new Dictionary<CaptureId, IOperation>();

        private static bool IsVariableReference(IOperation op) =>
            op is ILocalReferenceOperation || op is IParameterReferenceOperation || op is IFieldReferenceOperation ||
            op is IPropertyReferenceOperation || op is IArrayElementReferenceOperation;

        private void Write(IOperation target, Term v, Frame f, SpecEnv spec)
        {
            switch (target)
            {
                case ILocalReferenceOperation l when l.Local.RefKind != RefKind.None:
                    WriteRef(l.Local, v, f, l.Syntax.Parent ?? l.Syntax);
                    break;
                case ILocalReferenceOperation l:
                    CheckNonNullVariable(l.Local, v, l.Syntax.Parent ?? l.Syntax);
                    f.Vars[l.Local] = v;
                    if (IsViewVariable(l.Local)) ViewAlive(l.Local, v, f);
                    if (SpecSymbols.IsLinearPackage(l.Local.Type)) f.LivePackages.Add(l.Local);
                    if (IsMemView(l.Local.Type)) MemViewAlive(f, l.Local, v);
                    break;
                case IParameterReferenceOperation p:
                    CheckNonNullVariable(p.Parameter, v, p.Syntax.Parent ?? p.Syntax);
                    f.Vars[p.Parameter] = v;
                    if (IsViewVariable(p.Parameter) && p.Parameter.RefKind != RefKind.In) ViewAlive(p.Parameter, v, f);
                    if (SpecSymbols.IsLinearPackage(p.Parameter.Type) && p.Parameter.RefKind != RefKind.In) f.LivePackages.Add(p.Parameter);
                    if (IsMemView(p.Parameter.Type) && p.Parameter.RefKind != RefKind.In) MemViewAlive(f, p.Parameter, v);
                    break;
                case IDeclarationExpressionOperation d: Write(d.Expression, v, f, spec); break;
                case IFieldReferenceOperation hf when FieldEffects.IsHeapField(hf.Field) && (hf.Instance != null || hf.Field.IsStatic):
                    WriteField(hf.Field, hf.Instance, v, hf.Syntax, f, spec);
                    break;
                case IPropertyReferenceOperation hp when FieldEffects.IsHeapField(hp.Property) && hp.Instance != null:
                    WriteField(hp.Property, hp.Instance, v, hp.Syntax, f, spec);
                    break;
                case IArrayElementReferenceOperation ae:
                {
                    var arr = Eval(ae.ArrayReference, f, spec);
                    var idx = CellOf(ae, arr, f, spec);
                    CheckCellWrite(arr, idx, f, ae.Syntax);
                    f.Heap = T.Store(f.Heap, arr, T.Store(T.Select(f.Heap, arr, Sort.Row), idx, T.Coerce(v, Sort.Int)));
                    break;
                }
                case IPropertyReferenceOperation ps when IsComputed(ps.Property.SetMethod):
                    CallAccessor(ps.Property.SetMethod, ps.Instance, ps.Arguments.Select(a => a.Value), v, null, ps.Syntax, f, spec);
                    break;
                case IPropertyReferenceOperation ip when InterfaceListSet(ip, v, f, spec):
                    break;
                case IPropertyReferenceOperation ls when _codeMode && ls.Property.SetMethod != null && ls.Property.DeclaringSyntaxReferences.Length == 0 &&
                                                        ls.Property.ContainingType.ContainingNamespace?.ToDisplayString() != SpecSymbols.Namespace && !IsSequence(ls.Instance?.Type):
                    // a library setter (a dictionary's indexer): a call of a library method
                    CallAccessor(ls.Property.SetMethod, ls.Instance, ls.Arguments.Select(a => a.Value), v, null, ls.Syntax, f, spec);
                    break;
                case IPropertyReferenceOperation pr when pr.Property.IsIndexer && IsSequence(pr.Instance?.Type) && pr.Arguments.Length == 1:
                {
                    var arr = Eval(pr.Instance, f, spec);
                    var idx = Eval(pr.Arguments[0].Value, f, spec);
                    Deref(pr.Instance, arr, pr.Syntax);
                    BoundsCheck(arr, idx, pr.Syntax);
                    if (IsSpan(pr.Instance.Type))
                    {
                        // a cell of the span's base (MethodVerifier.Spans); under array permissions, not supported
                        if (!_arrayMode) { CheckWrite(SpanBase(arr), pr.Syntax); SpanWrite(arr, idx, v, f); break; }
                        if (_codeMode)
                            Report("CSV1016", pr.Syntax, $"'{pr.Syntax}' writes through a span, which could be any array's cells: this method's array permissions cannot cover it", isError: true);
                        f.Heap = _z3.Fresh("heap", Sort.Heap); // could be any array's cell
                        break;
                    }
                    CheckCellWrite(arr, idx, f, pr.Syntax);
                    f.Heap = T.Store(f.Heap, arr, T.Store(T.Select(f.Heap, arr, Sort.Row), idx, T.Coerce(v, Sort.Int)));
                    break;
                }
                case IFlowCaptureReferenceOperation r when _captured.TryGetValue(r.Id, out var captured) && IsVariableReference(captured):
                    // the flow graph captures an assignment's target before its value (x = new C { ... }): write the target
                    Write(captured, v, f, spec);
                    break;
                case IFlowCaptureReferenceOperation _:
                case IDiscardOperation _:
                    break;
                case IFieldReferenceOperation sf when sf.Instance != null && IsStructMember(sf.Field):
                    WriteStructMember(sf.Instance, sf.Field, v, sf.Syntax, f, spec);
                    break;
                case IPropertyReferenceOperation sp when sp.Instance != null && IsStructMember(sp.Property):
                    WriteStructMember(sp.Instance, sp.Property, v, sp.Syntax, f, spec);
                    break;
                default:
                    NotModeled(target.Syntax, $"assignment to {target.Kind} is not supported");
                    break;
            }
        }

        private Term EvalProperty(IPropertyReferenceOperation pr, Frame f, SpecEnv spec)
        {
            if (TaskResult(pr, f, spec) is Term given) return given;
            var prop = pr.Property;
            if (pr.Instance != null && IsNullableValue(prop.ContainingType) && NullableProperty(pr, f, spec) is Term nullableMember) return nullableMember;
            if (InterfaceListRead(pr, f, spec) is Term listRead) return listRead;
            if (GroupKey(pr, f, spec) is Term groupKey) return groupKey;
            if (AnonymousMember(pr, f, spec) is Term anonymousMember) return anonymousMember;
            if (DictionaryView(pr, f, spec) is Term dictionaryView) return dictionaryView;
            if (DictionaryCurrent(pr, f, spec) is Term dictionaryCurrent) return dictionaryCurrent;
            if (SpecSymbols.IsGhostType(prop.ContainingType) && prop.Name == "Value") return Eval(pr.Instance, f, spec);
            if ((SpecSymbols.IsObjSet(prop.ContainingType) || SpecSymbols.IsBag(prop.ContainingType)) && prop.Name == "Empty") return T.ZeroRow();
            if (SpecSymbols.IsSeqType(prop.ContainingType) && prop.IsIndexer)
            {
                var index = Eval(pr.Arguments[0].Value, f, spec);
                index = MapKeyType(prop.ContainingType) is ITypeSymbol keyType ? KeyOf(index, keyType) : T.Coerce(index, Sort.Int);
                return T.Coerce(T.Select(Eval(pr.Instance, f, spec), index, Sort.Int), SortOf(pr.Type));
            }
            if (pr.Instance != null && IsSequence(pr.Instance.Type))
            {
                if (prop.Name == "IsEmpty" && IsSpan(pr.Instance.Type)) return T.Eq(Len(T.Coerce(Eval(pr.Instance, f, spec), Sort.Int)), T.Int(0));
                if (prop.Name == "Length")
                {
                    var seq = Eval(pr.Instance, f, spec);
                    Deref(pr.Instance, seq, pr.Syntax);
                    if (RankOf(pr.Instance.Type) > 1) LengthIsProduct(seq, RankOf(pr.Instance.Type));
                    return Len(seq);
                }
                if (prop.IsIndexer && pr.Arguments.Length == 1)
                {
                    var arr = Eval(pr.Instance, f, spec);
                    var idx = Eval(pr.Arguments[0].Value, f, spec);
                    Deref(pr.Instance, arr, pr.Syntax);
                    BoundsCheck(arr, idx, pr.Syntax);
                    if (pr.Instance.Type.SpecialType == SpecialType.System_String)
                        return InRangeOf(Char(arr, idx), pr.Type);
                    // a span views its base at an offset (MethodVerifier.Spans); under array permissions, its contents are unknown
                    if (IsSpan(pr.Instance.Type)) return _arrayMode ? Unknown(pr.Type, "spanElem") : SpanRead(arr, idx, pr.Type, f);
                    return InRangeOf(T.Coerce(T.Select(T.Select(f.Heap, arr, Sort.Row), idx, Sort.Int), SortOf(pr.Type)), pr.Type);
                }
            }
            if (SpecSymbols.IsViewType(prop.ContainingType) && prop.Name == "Obj") return Eval(pr.Instance, f, spec); // a view is its object
            if (pr.Instance != null && FieldEffects.IsHeapField(prop))
                return ReadField(prop, pr.Instance, pr.Type, pr.Syntax, f, spec);
            if (pr.Instance != null && DataTypes.IsPositional(prop) && Data.IsData(prop.ContainingType))
            {
                var o = Eval(pr.Instance, f, spec);
                Deref(pr.Instance, o, pr.Syntax);
                return T.Coerce(Field(prop, o, pr.Instance.Type), SortOf(pr.Type));
            }
            if (pr.Instance != null && IsStructMember(prop) && !LooksAtSharedState(prop)) return T.Coerce(StructMember(prop, Eval(pr.Instance, f, spec)), SortOf(pr.Type));
            if (IsComputed(prop.GetMethod) || _engine.HasStub(prop.GetMethod)) return CallAccessor(prop.GetMethod, pr.Instance, pr.Arguments.Select(a => a.Value), null, pr.Type, pr.Syntax, f, spec);
            if (!IsStableProperty(prop) && _codeMode && prop.DeclaringSyntaxReferences.Length == 0)
            {
                // a library property that may change (Console.Out, a list's Count): each read in code is a value of its own
                if (pr.Instance != null) Deref(pr.Instance, Eval(pr.Instance, f, spec), pr.Syntax);
                foreach (var a in pr.Arguments) Eval(a.Value, f, spec);
                // (a token's state is just that: it could have been cancelled by now, or not)
                // (nor what an async enumerator has just given: that is all it could be)
                if (!LooksAtSharedState(prop) && !(prop.Name == "Current" && prop.ContainingType.Name == "IAsyncEnumerator"))
                    Warn(pr.Syntax, $"property '{prop.Name}' of {prop.ContainingType.Name} is not modeled; its value is unknown");
                var member = prop.OriginalDefinition.ToDisplayString();
                _result.LibraryCalls.Add((member, Where(pr.Syntax)));
                var wasCause = _z3.Cause;
                _z3.Cause = "library " + member;
                var lv = Unknown(pr.Type, prop.Name);
                _z3.Cause = wasCause;
                // as the library declares it, a type parameter as instantiated (a List<string>'s items are strings)
                if (IsNonNullableType(prop.OriginalDefinition.Type) ||
                    prop.OriginalDefinition.Type is ITypeParameterSymbol && (IsNonNullableType(prop.Type) || ConfiguredElementIsNotNull(pr))) AssumeSide(NotNull(lv));
                return lv;
            }
            if (!IsStableProperty(prop))
                NotModeled(pr.Syntax, $"property '{prop.Name}' is not supported: only auto-properties, properties with code, and properties of immutable types are");
            var args = new List<Term>();
            if (pr.Instance != null)
            {
                args.Add(Eval(pr.Instance, f, spec));
                Deref(pr.Instance, args[0], pr.Syntax);
            }
            foreach (var a in pr.Arguments) args.Add(Eval(a.Value, f, spec));
            var def = prop.OriginalDefinition;
            return T.Coerce(_z3.Apply(def.ToDisplayString(), SortOf(def.Type), args), SortOf(pr.Type));
        }

        /// <summary>
        /// A property the verifier may model as a function of its object: its value never changes. The spec library's
        /// ghost members, members of strings and readonly structs, and get-only (or init-only) auto-properties.
        /// A computed getter (List.Count) or a settable property is not.
        /// </summary>
        /// <summary>A readonly struct that is a handle on something others change: a token, a ValueTask, an awaiter. Only whether a token can be cancelled at all stays.</summary>
        private static bool LooksAtSharedState(IPropertySymbol prop)
        {
            var ns = prop.ContainingType.ContainingNamespace?.ToDisplayString();
            return prop.ContainingType.IsValueType && (ns == "System.Threading" || ns == "System.Threading.Tasks" || ns == "System.Runtime.CompilerServices") && prop.Name != "CanBeCanceled";
        }

        /// <summary>
        /// await foreach (var v in xs.ConfigureAwait(false)): the type that call infers for its enumerator's Current has no
        /// nullability, so it is read from what the loop's expression is called on.
        /// </summary>
        private bool ConfiguredElementIsNotNull(IPropertyReferenceOperation pr)
        {
            if (pr.Property.Name != "Current" || !(pr.Syntax.FirstAncestorOrSelf<CommonForEachStatementSyntax>() is CommonForEachStatementSyntax fe)) return false;
            var e = fe.Expression;
            while (e is InvocationExpressionSyntax i && i.Expression is MemberAccessExpressionSyntax ma && (ma.Name.Identifier.Text == "ConfigureAwait" || ma.Name.Identifier.Text == "WithCancellation"))
                e = ma.Expression;
            return e != fe.Expression && _model.GetTypeInfo(e).Type is INamedTypeSymbol { TypeArguments: { Length: 1 } } n && IsNonNullableType(n.TypeArguments[0]);
        }

        /// <summary>A readonly struct can be a view of an array that others write: an ArraySegment's items are not its own.</summary>
        private static bool LooksAtAnArray(IPropertySymbol prop) =>
            prop.IsIndexer && prop.ContainingType.Name == "ArraySegment" && prop.ContainingType.ContainingNamespace?.ToDisplayString() == "System";

        private static bool IsStableProperty(IPropertySymbol prop)
        {
            var type = prop.ContainingType;
            if (type == null) return false;
            if (type.ContainingNamespace?.ToDisplayString() == SpecSymbols.Namespace) return true;
            if (type.SpecialType == SpecialType.System_String || (type.IsValueType && type.IsReadOnly && !LooksAtSharedState(prop) && !LooksAtAnArray(prop))) return true;
            if (prop.SetMethod != null && !prop.SetMethod.IsInitOnly) return false;
            foreach (var syntax in prop.DeclaringSyntaxReferences.Select(r => r.GetSyntax()))
            {
                if (syntax is ParameterSyntax) continue; // a record's positional property: init-only, auto
                if (!(syntax is PropertyDeclarationSyntax pd) || pd.AccessorList == null ||
                    pd.AccessorList.Accessors.Any(a => a.Body != null || a.ExpressionBody != null))
                    return false;
            }
            return prop.DeclaringSyntaxReferences.Length > 0;
        }

        /// <summary>A new array is distinct from every array the method can already see, and from every array a field holds.</summary>
        private void NewArrayIsDistinct(Term r, Frame f)
        {
            foreach (var t in f.Vars.Where(kv => IsSequence(TypeOf(kv.Key))).Select(kv => kv.Value))
                _z3.Assume(T.Not(T.Eq(r, t)));
            // (no field can hold it yet)
            foreach (var field in _engine.Fields.AllFields().Where(x => ValueSort(x) == Sort.Int && IsSequence(FieldType(x))))
            {
                var map = FieldMap(f, field);
                _z3.Assume(new Term($"(forall ((o Int)) (! (distinct (select {map} o) {r}) :pattern ((select {map} o))))", Sort.Bool));
            }
        }

        private Term EvalArrayCreation(IArrayCreationOperation ac, Frame f, SpecEnv spec)
        {
            var sizes = ac.DimensionSizes.Select(d => Eval(d, f, spec)).ToList();
            foreach (var n in sizes)
                if (_codeMode) Prove(T.Le(T.Int(0), n), "CSV1003", ac.Syntax, $"array size in '{ac.Syntax}' might be negative");
            var r = _z3.Fresh("array", Sort.Int);
            _z3.Assume(NotNull(r));
            ListKind(r, ac.Type);
            if (sizes.Count == 1) _z3.Assume(T.Eq(Len(r), sizes[0]));
            NewArrayIsDistinct(r, f);
            var row = sizes.Count > 1 ? NewMultiArray(ac, r, sizes, f, spec) : T.ZeroRow();
            if (ac.Initializer != null && sizes.Count == 1)
                for (int i = 0; i < ac.Initializer.ElementValues.Length; i++)
                    row = T.Store(row, T.Int(i), T.Coerce(Eval(ac.Initializer.ElementValues[i], f, spec), Sort.Int));
            f.Heap = T.Store(f.Heap, r, row);
            NewCells(f, r);
            return r;
        }

        // ================================================================================== calls

        private bool HavocsHeap(IMethodSymbol m) =>
            !SpecSymbols.IsSpecClass(m.ContainingType) && !SpecSymbols.IsGhostOf(m) && _engine.MayWriteHeap(m);

        /// <summary>A call, with the callee's type parameters as it instantiates them (for its contract's equalities).</summary>
        private Term EvalInvocation(IInvocationOperation inv, Frame f, SpecEnv spec) =>
            // (inside a LINQ definition: Q, the lambdas, other definitions; in the definition's own instantiation)
            QueryOperation(inv, f, spec) ?? WithInstantiation(inv.TargetMethod, () => EvalInvocationCore(inv, f, spec));

        private T2 WithInstantiation<T2>(IMethodSymbol called, System.Func<T2> eval)
        {
            if (called == null || SpecSymbols.IsSpecClass(called.ContainingType)) return eval();
            var callee = _engine.ContractOf(called);
            _instantiations.Push(InstantiationOf(called, callee));
            _equalityEpochs.Push(_z3.Fresh("equals", Sort.Int));
            try { return eval(); }
            finally { _instantiations.Pop(); _equalityEpochs.Pop(); }
        }

        private IInvocationOperation _waitingCall;

        private Term EvalInvocationCore(IInvocationOperation inv, Frame f, SpecEnv spec, bool enumerators = true)
        {
            if (_codeMode && !ProofCode) CheckFormatArguments(inv);
            if (enumerators && EnumeratorCall(inv, f, spec) is Term enumerator) return enumerator;
            var m = inv.TargetMethod;
            if (LockEvent(inv, f, spec) is Term locked) return locked;
            if ((GateOf(inv, "Release", f) ?? GateOfWrapperCall(inv, false, f) ?? GateOfDispose(inv, f)) is { } given) GateReleased(given, inv.Syntax, f);
            if (inv != _waitingCall && inv != _awaitedCall && !IsAwaitedHere(inv.Syntax) && (GateOf(inv, "Wait", f) ?? GateOfWrapperCall(inv, true, f)) is { } wanted)
            {
                _waitingCall = inv;
                var waited = EvalInvocationCore(inv, f, spec, enumerators);
                _waitingCall = null;
                GateTaken(wanted, f);
                return waited;
            }
            if (IsGetLength(inv)) return GetLength(inv, f, spec);
            if (SpecSymbols.IsSpecClass(m.ContainingType))
            {
                switch (m.Name)
                {
                    case "Result":
                        return spec?.Result != null ? T.Coerce(spec.Result, SortOf(inv.Type)) : Unknown(inv.Type, "result");
                    case "Old":
                        return spec?.Old != null ? Eval(inv.Arguments[0].Value, OldFrame(spec.Old, f), spec) : Eval(inv.Arguments[0].Value, f, spec);
                    case "Forall":
                    case "Exists":
                        return Quantifier(inv, f, spec, m.Name == "Forall");
                    case "Fresh":
                        return Fresh(Eval(inv.Arguments[0].Value, f, spec), f, spec);
                    case "Multiset":
                        return MultisetOf(inv, f, spec);
                    case "Index":
                        return ForEachIndex(inv, f);
                    case "Equal":
                        return SpecEqual(inv, f, spec);
                    case "AccRead":
                    case "Acc":
                    {
                        var o = Eval(inv.Arguments[0].Value, f, spec);
                        if (Unconverted(inv.Arguments[0].Value).Type is IArrayTypeSymbol)
                        {
                            // cells: each in hand
                            var lo = inv.Arguments.Length == 3 ? Eval(inv.Arguments[1].Value, f, spec) : T.Int(0);
                            var hi = inv.Arguments.Length == 3 ? Eval(inv.Arguments[2].Value, f, spec) : Len(o);
                            return _atomsTrue > 0 || f.ArrPerm == null ? T.True
                                : new Term($"(forall ((i Int)) (=> (and (<= {lo} i) (< i {hi})) (>= (select (select {f.ArrPerm} {o}) i) {(m.Name == "AccRead" ? ShareAmount : FullAmount)})))", Sort.Bool);
                        }
                        if (inv.Arguments.Length == 2 && inv.Arguments[1].Value.ConstantValue is { HasValue: true, Value: string fieldName } &&
                            WholeFields(Unconverted(inv.Arguments[0].Value).Type).FirstOrDefault(x => x.Name == fieldName) is ISymbol accField)
                            return _atomsTrue > 0 || f.Perm == null ? T.True : CanWriteField(f, o, accField);
                        return _atomsTrue > 0 || f.Perm == null ? T.True : CanWrite(f, o);
                    }
                    default:
                        return T.True;
                }
            }
            if (SpecSymbols.IsGhostOf(m))
            {
                // a ghost value is computed with mathematical integers: it never exists at run time
                _ghostDepth++;
                try { return Eval(inv.Arguments[0].Value, f, spec); }
                finally { _ghostDepth--; }
            }
            if (SpecSymbols.IsSeqType(m.ContainingType)) return EvalSeq(inv, f, spec);
            if (SpecSymbols.IsCsVerifyType(m.ContainingType, "Own")) return OwnCall(inv, f, spec);
            if (SpecSymbols.IsModel(m.ReducedFrom ?? m.OriginalDefinition)) return ModelRead(inv, f, spec);
            if (SpecSymbols.IsPredicate(m.OriginalDefinition))
            {
                // as a condition: the instance is held here
                var instance = Instance(m, inv.Arguments.Select(a => Eval(a.Value, f, spec)).ToList());
                return _atomsTrue > 0 || f.Inst == null ? T.True : Held(f, instance);
            }

            if (IsNullableValue(m.ContainingType) && NullableInvocation(inv, f, spec) is Term nullableResult) return nullableResult;
            if (IsDebugAssert(m) && _codeMode) return DebugAssert(inv, f, spec);
            if (SpanInvocation(inv, f, spec) is Term spanResult) return spanResult;
            if (StringEquals(inv, f, spec) is Term stringsEqual) return stringsEqual;
            if (InterfaceListCall(inv, f, spec) is Term listCall) return listCall;
            if (LinqCall(inv, f, spec) is Term linqResult) return linqResult;
            var builtin = Builtin(inv, f, spec);
            if (builtin != null) return builtin;

            var callee = _engine.ContractOf(m);
            CallUnderLock(inv, callee, f);
            // an async stub's contract is of what the task gives when awaited: a task not awaited at once is the library's
            if (callee.IsStub && callee.Stub.IsAsync && inv != _awaitedCall) callee = _engine.LibraryContractOf(m);
            if (callee.IsStub && _codeMode) Assumed(callee);
            if (StartTask(inv, callee, f, spec) is Term startedTask) return startedTask;
            if (StartRun(inv, f, spec) is Term runningTask) return runningTask;
            LambdaGivesTasks(inv, f);
            ThreadEvent(inv, f, spec);
            CheckNotAwaited(inv, callee);
            Term receiver = inv.Instance != null ? Eval(inv.Instance, f, spec) : null;
            if (receiver != null) Deref(inv.Instance, receiver, inv.Syntax);
            var argTerms = new Term[m.Parameters.Length];
            var cells = new Dictionary<IArgumentOperation, (Term arr, Term idx)>();
            foreach (var a in inv.Arguments)
            {
                int i = a.Parameter.Ordinal;
                if (a.Parameter.RefKind != RefKind.None && a.ArgumentKind == ArgumentKind.Explicit && !SpecSymbols.IsSpecClass(m.ContainingType) &&
                    RefCell(a.Value, f, spec) is (Term, Term) cell)
                {
                    // an array cell lent to the callee (copied in, and out again after the call)
                    cells[a] = cell;
                    argTerms[i] = a.Parameter.RefKind == RefKind.Out ? FreshOf(a.Parameter.Type, a.Parameter.Name + "$unset") : ReadCell(cell, a.Value.Type, f, a.Syntax);
                }
                else
                {
                    // a callee's ref/in parameter is a variable of its own; aliasing a field would let writes through the
                    // heap and through the parameter disagree
                    var argument = Uncaptured(a.Value);
                    if (a.Parameter.RefKind != RefKind.None && !(argument is ILocalReferenceOperation || argument is IParameterReferenceOperation ||
                                                                 argument is IDeclarationExpressionOperation || argument is IDiscardOperation) &&
                        a.ArgumentKind == ArgumentKind.Explicit && !SpecSymbols.IsSpecClass(m.ContainingType))
                    {
                        // a struct's member (s.X, a[i].X): a variable of the callee's, written back into the struct after the call
                        var root = StructMemberRoot(argument);
                        if (root == null)
                            NotModeled(a.Syntax, $"passing '{a.Value.Syntax}' by {a.Parameter.RefKind.ToString().ToLowerInvariant()} is not supported: only locals, parameters, array elements and their structs' members");
                        else if (root is IArrayElementReferenceOperation && _engine.MayTouchArrays(m))
                            NotModeled(a.Syntax, $"passing '{a.Value.Syntax}' by reference to '{m.Name}', which may read or write array contents itself, is not supported: " +
                                                 "the cell and the parameter would disagree (copy the member into a local)");
                    }
                    // (a variable passed by reference is read as it is at the call, not when the flow graph captured it:
                    // a later argument may have changed it)
                    var value = a.Parameter.RefKind != RefKind.None && (argument is ILocalReferenceOperation || argument is IParameterReferenceOperation) ? argument : a.Value;
                    argTerms[i] = a.Parameter.RefKind == RefKind.Out ? FreshOf(a.Parameter.Type, a.Parameter.Name + "$unset") : Eval(value, f, spec);
                }
                if (a.Parameter.RefKind != RefKind.Out) NonNullArgument(a, argTerms[i], m);
            }
            if (cells.Count > 0) LendCells(inv, cells);
            if (_codeMode && !SpecSymbols.IsSpecClass(m.ContainingType)) CheckRefAliasing(inv, cells, f);

            if (_codeMode && callee.IsPure && _quantDepth > 0)
            {
                // inside a quantifier (a ghost function's body): the application itself, whose facts and
                // obligations are closed over the quantifier's variable (a fresh result would not be)
                var qpre = CalleeFrame(callee, receiver, argTerms, f.Heap, f);
                foreach (var req in callee.Requires)
                    Require(AsBool(EvalForeignSpec(req, qpre, new SpecEnv { Old = qpre })), "CSV1001", inv.Syntax,
                        $"precondition '{req.Syntax}' of '{m.Name}' might not hold");
                return PureApply(callee, receiver, argTerms, f.Heap, SortOf(inv.Type), null, f);
            }
            if (!_codeMode)
            {
                if (callee.IsPure) return PureApply(callee, receiver, argTerms, f.Heap, SortOf(inv.Type), inv.Syntax, f);
                Warn(inv.Syntax, $"'{m.Name}' is not [Pure] and cannot be used in a specification; treated as unknown");
                return Unknown(inv.Type);
            }

            // the unknown values the call makes are charged to it in the library report
            var wasCause = _z3.Cause;
            var wasOrigin = _z3.Origin;
            if (_codeMode && !SpecSymbols.IsSpecClass(m.ContainingType)) _z3.Origin = $"the call to '{m.Name}' (line {LineOf(inv.Syntax)}) may change what was checked before it";
            if (CallCause(m, callee) is string cause)
            {
                _z3.Cause = cause;
                if (!callee.HasSource) _result.LibraryCalls.Add((cause.Substring("library ".Length), Where(inv.Syntax)));
            }
            try
            {
                bool chained = m.MethodKind == MethodKind.Constructor; // base(...) or this(...): the object is not built yet
                var touched = chained ? new List<Term>() : HandOver(inv, receiver, argTerms, f, callee);
                var pre = CalleeFrame(callee, receiver, argTerms, f.Heap, f);
                if (!callee.HasSource)
                {
                    var libraryMemory = f.Heap;
                    var libraryHeld = f.ArrPerm;
                    DeferTies();
                    var whenNotNull = new List<(Term value, bool when)>();
                    var cellsOut = new List<(IArgumentOperation, Term)>();
                    foreach (var a in inv.Arguments.Where(a => a.Parameter.RefKind == RefKind.Ref || a.Parameter.RefKind == RefKind.Out))
                    {
                        var nv = FreshOf(a.Parameter.Type, a.Parameter.Name);
                        if (IsNonNullable(a.Parameter.OriginalDefinition)) _z3.Assume(NotNull(nv));
                        else if (NotNullWhen(a.Parameter) is bool when) whenNotNull.Add((nv, when));
                        if (cells.ContainsKey(a)) cellsOut.Add((a, nv)); else Write(a.Value, nv, f, spec);
                    }
                    if (HavocsHeap(m)) f.Heap = _z3.Fresh("heap", Sort.Heap);
                    f.Heap = KeepHeldMemory(f.Heap, libraryMemory, libraryHeld);
                    foreach (var (a, nv) in cellsOut) WriteCell(cells[a], nv, f, a.Syntax);
                    FlushTies(f);
                    CalleeModifies(callee, pre, f, inv.Syntax);
                    // (a library can run the program's code only through overrides and interfaces: none, none written)
                    if (_engine.Fields.WritesFieldsAt(inv)) HavocFields(f, m, touched);
                    CallMayThrow(callee, receiver, argTerms, inv.Arguments, f, pre);
                    var libResult = m.ReturnsVoid ? T.True : Unknown(inv.Type, m.Name);
                    if (!m.ReturnsVoid && LibraryGivesAsInstantiated(m)) _z3.Assume(NotNull(libResult));
                    else if (!m.ReturnsVoid && MayBeNullType(inv.Type)) _z3.Origins[libResult.S] = $"'{m.Name}' may return null (line {LineOf(inv.Syntax)})";
                    foreach (var (value, when) in whenNotNull)
                        if (libResult.Sort == Sort.Bool) _z3.Assume(T.Implies(when ? libResult : T.Not(libResult), NotNull(value)));
                    AllocAfterCall(f, libResult);
                    LibraryNullFacts(inv, argTerms, libResult);
                    GuardFacts(inv, argTerms);
                    if (RunsCode(m)) HavocClosureLocals(f); // (a delegate it was handed may write them)
                    return libResult;
                }

                CheckCallReadsInHand(inv, callee);
                var preEnv = new SpecEnv { Old = pre };
                // (the call happens only where the guards around it hold: `n <= a.Length && IsHeap(a, n)`; inside a
                // quantifier, the obligation is closed over its variable with the others made there)
                foreach (var req in callee.Requires)
                    Require(AsBool(EvalForeignSpec(req, pre, preEnv)), "CSV1001", inv.Syntax,
                        $"precondition '{req.Syntax}' of '{m.Name}' might not hold");
                if (callee.IsPure) CheckPureCallReads(callee, pre, inv.Syntax);
                if (callee.IsPure && _codeMode) CheckPurePermissions(callee, pre, preEnv, f, inv.Syntax);
                var modifiable = callee.IsPure || callee.IsLemma ? null : CalleeModifies(callee, pre, f, inv.Syntax, m);
                // lending trees through Spec.Modifies(Own.Tree(x)): the caller must hold them; the call may change them
                if (!callee.IsPure && f.Perm != null)
                    foreach (var root in LentTrees(callee, pre, preEnv))
                    {
                        if (_codeMode)
                            Require(CanWrite(f, root), "CSV1016", inv.Syntax, $"'{m.Name}' borrows a tree through Spec.Modifies, but its root's view is not in hand here");
                        touched.Add(root);
                    }
                // the permissions its preconditions ask for are given to it: what they cover may change
                var touchedInst = new List<Term>();
                var touchedCells = new List<Atom>();
                var touchedFields = new List<(Term obj, ISymbol field)>();
                if (!callee.IsPure && (f.Inst != null || f.ArrPerm != null) && _codeMode)
                    foreach (var req in callee.Requires) Exhale(req, pre, preEnv, f, inv.Syntax, touched, touchedInst, touchedCells, touchedFields: touchedFields);
                // the memory cells still in hand: the call cannot change them
                var heldMemory = f.ArrPerm;
                var memoryBefore = f.Heap;

                if (_engine.IsRecursiveCall(_method, callee.Method))
                {
                    bool self = SymbolEqualityComparer.Default.Equals(callee.Method, _method);
                    if ((_entryMeasure == null || callee.Decreases == null) && ProofCode)
                        NotTotal(inv.Syntax, self
                            ? $"recursive lemma or [Pure] function '{_method.Name}' needs Spec.Decreases"
                            : $"mutually recursive call from '{_method.Name}' to '{m.Name}' needs Spec.Decreases on both");
                    else if (_entryMeasure == null || callee.Decreases == null)
                        Warn(inv.Syntax, self
                            ? $"recursive call without Spec.Decreases in '{_method.Name}'; termination is not checked"
                            : $"mutually recursive call from '{_method.Name}' to '{m.Name}' without Spec.Decreases on both; termination is not checked");
                    else if (callee.Decreases.Count != _entryMeasure.Length)
                        Prove(T.False, "CSV1008", inv.Syntax,
                            $"cannot prove termination: '{m.Name}' and '{_method.Name}' call each other but their measures have different numbers of components");
                    else
                        Prove(LexDecreases(EvalMeasure(callee.Decreases, pre, preEnv), _entryMeasure), "CSV1008", inv.Syntax,
                            $"cannot prove termination: measure '{MeasureText(callee.Decreases)}' of '{m.Name}' might not decrease or might be negative");
                }

                var post = pre.Clone();
                var cellsBack = new List<(IArgumentOperation, Term)>();
                DeferTies();
                var outNotNull = new List<(Term value, bool when)>();
                foreach (var a in inv.Arguments.Where(a => a.Parameter.RefKind == RefKind.Ref || a.Parameter.RefKind == RefKind.Out))
                {
                    var nv = FreshOf(a.Parameter.Type, a.Parameter.Name);
                    if (IsNonNullable(callee.Method.Parameters[a.Parameter.Ordinal])) _z3.Assume(NotNull(nv));
                    else if (callee.IsStub && NotNullWhen(a.Parameter) is bool when) outNotNull.Add((nv, when));
                    post.Vars[callee.Method.Parameters[a.Parameter.Ordinal]] = nv;
                    if (callee.IsStub) post.Vars[StubParameter(callee, a.Parameter.Ordinal)] = nv;
                    if (cells.ContainsKey(a)) cellsBack.Add((a, nv)); else Write(a.Value, nv, f, spec);
                    if (SpecSymbols.IsOwnType(a.Parameter.Type)) touched.Add(nv); // a view that comes out (or another one in its place)
                    touched.AddRange(ViewsIn(nv, a.Parameter.Type));          // or views in a package
                    ViewsArrive(nv, a.Parameter.Type, f);
                }
                // a package that comes back carries views: the call may have changed their objects (and only those it got)
                Term packageResult = null;
                if (SpecSymbols.IsLinearPackage(m.ReturnType))
                {
                    packageResult = FreshOf(m.ReturnType, m.Name);
                    touched.AddRange(ViewsIn(packageResult, m.ReturnType));
                }
                if (f.ArrPerm != null && MentionsCells(callee) && !callee.IsPure)
                    f.Heap = post.Heap = HavocCells(f, touchedCells, f.Alloc, touchedInst); // it writes only the cells it got
                else if (HavocsHeap(m) && callee.Modifies != null && !_arrayMode)
                {
                    // Spec.Modifies names the arrays it writes (a method with sources is checked to: CheckWrite),
                    // and what it allocates: the others keep their contents
                    var frame = T.Coerce(EvalForeignSpec(callee.Modifies, pre, preEnv), Sort.Row);
                    if (!callee.IsStub && f.Alloc != null) frame = new Term($"(cv_mod {frame.S} {f.Alloc.S})", Sort.Row);
                    f.Heap = post.Heap = _z3.Define("heap", new Term($"(cv_frameh {frame} {memoryBefore} {_z3.Fresh("heap", Sort.Heap)})", Sort.Heap));
                }
                else if (HavocsHeap(m))
                {
                    if (_arrayMode && _codeMode)
                        Report("CSV1016", inv.Syntax, $"'{m.Name}' may write any array: give it a contract with Spec.Acc for the cells it writes", isError: true);
                    f.Heap = post.Heap = _z3.Fresh("heap", Sort.Heap);
                }
                if (!IsMemoryNeutral(callee)) f.Heap = post.Heap = KeepHeldMemory(f.Heap, memoryBefore, heldMemory);
                // (the callee's postconditions speak of the heap as it left it: the cells it was lent are written after)
                foreach (var (a, nv) in cellsBack) WriteCell(cells[a], nv, f, a.Syntax);
                FlushTies(f);
                HavocFields(f, m, SpecSymbols.IsOwnType(m.ReturnType) ? null : touched, modifiable, touchedInst, touchedFields);
                if (!chained) CallMayThrow(callee, receiver, argTerms, inv.Arguments, f, pre);
                if (chained && receiver != null) AfterChainedConstructor(f, m, receiver);
                else TakeBack(inv, receiver, f, callee);
                post.Fields = new Dictionary<ISymbol, Term>(f.Fields, SymbolEqualityComparer.Default);
                post.FieldEpoch = f.FieldEpoch;
                post.Link = f.Link;

                var result = packageResult ?? (m.ReturnsVoid || _awaitedCall == inv && AwaitedType(m) == null && (m.IsAsync || IsAsyncStubbed(m)) ? null : FreshOf(ResultTypeOf(inv), m.Name));
                if (packageResult != null) ViewsArrive(packageResult, m.ReturnType, f);
                bool awaitedStub = callee.IsStub && callee.Stub.IsAsync && _awaitedCall == inv;
                if (result != null && (awaitedStub ? IsNonNullableType(AwaitedType(m)) : IsNonNullableReturn(callee.Method) || callee.IsStub && NonNullAsInstantiated(m) || m.IsAsync && callee.HasSource && inv != _awaitedCall /* (the task, not what it gives) */))
                    _z3.Assume(NotNull(result));
                else if (result != null && MayBeNullType(result.Sort == Sort.Int ? ResultTypeOf(inv) : null))
                    _z3.Origins[result.S] = $"'{m.Name}' may return null (line {LineOf(inv.Syntax)})";
                // an array a stub says is fresh (list.ToArray()) is a new one: no other array is it
                if (result != null && callee.StubFreshResult && IsSequence(m.ReturnType)) NewArrayIsDistinct(result, f);
                if (!callee.IsPure && !callee.IsLemma)
                {
                    AllocAfterCall(f, inv.Arguments.Where(a => (a.Parameter?.RefKind == RefKind.Out || a.Parameter?.RefKind == RefKind.Ref) && !(a.Value is IDiscardOperation))
                        .Select(a => Eval(a.Value, f)).Append(result).ToArray());
                    post.Alloc = f.Alloc;
                }
                if (result != null && callee.IsPure)
                    _z3.Assume(T.Eq(result, PureApply(callee, receiver, argTerms, pre.Heap, result.Sort, null, pre)));
                // (a task's postcondition is of the state when it ends, which could be any later one: not of this)
                if (inv == _startedCall && (callee.Requires.Any(HasPermissions) || callee.Ensures.Any(e => HasPermissions(e.Expr))))
                {
                    _finishStarted = FinishLater(callee, pre, result);
                    if (RunsCode(m)) HavocClosureLocals(f);
                    return result ?? T.True;
                }
                if (inv == _startedCall) Interleave(post);
                if (!callee.IsPure && (f.Inst != null || f.ArrPerm != null))
                    foreach (var ens in callee.Ensures) Inhale(ens.Expr, post, new SpecEnv { Old = pre, Result = result, ResultParameter = ens.ResultParameter }, f);
                foreach (var ens in callee.Ensures)
                    _z3.Assume(GuardedBy(ens, pre, AsBool(EvalForeignSpec(ens.Expr, post, new SpecEnv { Old = pre, Result = result, ResultParameter = ens.ResultParameter }))));
                if (callee.IsStub)
                {
                    LibraryNullFacts(inv, argTerms, result ?? T.True);
                    foreach (var (value, when) in outNotNull)
                        if (result?.Sort == Sort.Bool) _z3.Assume(T.Implies(when ? result : T.Not(result), NotNull(value)));
                }
                if (RunsCode(m)) HavocClosureLocals(f); // (a local function, or a delegate it was handed, may write them)
                return result ?? T.True;
            }
            finally { _z3.Cause = wasCause; _z3.Origin = wasOrigin; }
        }

        /// <summary>
        /// A library out parameter <c>[MaybeNullWhen(b)] out TValue value</c>, with TValue a non-nullable type: not null
        /// when the method returns !b (null if the parameter says nothing of the kind).
        /// </summary>
        private static bool? NotNullWhen(IParameterSymbol p) =>
            IsNonNullableType(p.Type) && p.OriginalDefinition.GetAttributes().FirstOrDefault(x =>
                x.AttributeClass?.ToDisplayString() == "System.Diagnostics.CodeAnalysis.MaybeNullWhenAttribute") is AttributeData mnw &&
            mnw.ConstructorArguments.Length == 1 && mnw.ConstructorArguments[0].Value is bool maybeNullWhen
                ? !maybeNullWhen : (bool?)null;

        /// <summary>Ghost sequences are SMT arrays; Drop and Concat are the array lambdas in <see cref="SeqTheory"/>.</summary>
        private Term EvalSeq(IInvocationOperation inv, Frame f, SpecEnv spec)
        {
            var args = inv.Arguments.Select(a => Eval(a.Value, f, spec)).ToArray();
            var self = inv.Instance != null ? Eval(inv.Instance, f, spec) : null;
            if (SpecSymbols.IsBag(inv.TargetMethod.ContainingType))
                switch (inv.TargetMethod.Name)
                {
                    case "Of": return new Term($"(cv_badd {T.ZeroRow()} {T.Coerce(args[0], Sort.Int)})", Sort.Row);
                    case "Count": return T.Select(self, T.Coerce(args[0], Sort.Int), Sort.Int);
                    case "Contains": return T.Lt(T.Int(0), T.Select(self, T.Coerce(args[0], Sort.Int), Sort.Int));
                    case "Add": return new Term($"(cv_badd {self} {T.Coerce(args[0], Sort.Int)})", Sort.Row);
                    case "Union": return new Term($"(cv_bunion {self} {args[0]})", Sort.Row);
                    default: Unsupported(inv); return _z3.Fresh("bag", Sort.Row);
                }
            switch (inv.TargetMethod.Name)
            {
                case "Const": return T.ConstRow(T.Coerce(args[0], Sort.Int));
                case "Contents": return T.Select(f.Heap, T.Coerce(args[0], Sort.Int), Sort.Row); // an array's elements, whatever their type
                case "Of": return T.Store(T.ZeroRow(), T.Coerce(args[0], Sort.Int), T.Int(1));
                case "Contains": return T.Not(T.Eq(T.Select(self, T.Coerce(args[0], Sort.Int), Sort.Int), T.Int(0)));
                case "Add": return T.Store(self, T.Coerce(args[0], Sort.Int), T.Int(1));
                case "Union": return new Term($"(cv_union {self} {args[0]})", Sort.Row);
                case "IsSubsetOf": return new Term($"(cv_subset {self} {args[0]})", Sort.Bool);
                case "IsDisjointFrom": return new Term($"(cv_disjoint {self} {args[0]})", Sort.Bool);
                case "Update":
                    return T.Store(self, MapKeyType(inv.TargetMethod.ContainingType) is ITypeSymbol keyType ? KeyOf(args[0], keyType) : T.Coerce(args[0], Sort.Int),
                                   T.Coerce(args[1], Sort.Int));
                case "Drop": return new Term($"(cv_drop {self} {args[0]})", Sort.Row);
                case "Concat": return new Term($"(cv_concat {self} {args[0]} {args[1]})", Sort.Row);
                default: Unsupported(inv); return _z3.Fresh("seq", Sort.Row);
            }
        }

        /// <summary>
        /// <c>Spec.Multiset(a, n)</c>: the multiset of <c>a[0..n)</c>, well-defined for 0 &lt;= n &lt;= a.Length, and
        /// unfolded one element (the last) where it is used.
        /// </summary>
        private Term MultisetOf(IInvocationOperation inv, Frame f, SpecEnv spec)
        {
            var a = Eval(inv.Arguments[0].Value, f, spec);
            var n = Eval(inv.Arguments[1].Value, f, spec);
            Deref(inv.Arguments[0].Value, a, inv.Syntax);
            Require(T.And(T.Le(T.Int(0), n), T.Le(n, Len(a))), "CSV1003", inv.Syntax, $"'{inv.Syntax}' might not be within the array");
            var row = T.Select(f.Heap, a, Sort.Row);
            var bag = new Term($"(cv_bag {row} {n})", Sort.Row);
            // one element per use; all of them when the length is a small constant (a concrete array)
            int levels = inv.Arguments[1].Value.ConstantValue.Value is int k && k >= 0 && k <= 32 ? k : 1;
            var top = n;
            for (int level = 0; level < levels; level++)
            {
                var prev = T.Sub(top, T.Int(1));
                AssumeSide(T.Implies(T.Lt(T.Int(0), top), T.Eq(new Term($"(cv_bag {row} {top})", Sort.Row),
                    new Term($"(cv_badd (cv_bag {row} {prev}) {T.Select(row, prev, Sort.Int)})", Sort.Row))));
                top = prev;
            }
            return bag;
        }

        /// <summary>Drop and Concat as array lambdas: definitions, not quantified axioms, so they cost Z3 nothing until used.</summary>
        public const string SeqTheory =
            "(define-fun cv_drop ((a (Array Int Int)) (n Int)) (Array Int Int) (lambda ((i Int)) (select a (+ n i))))\n" +
            "(define-fun cv_concat ((a (Array Int Int)) (n Int) (b (Array Int Int))) (Array Int Int) (lambda ((i Int)) (ite (< i n) (select a i) (select b (- i n)))))\n" +
            // object sets (ObjSet) are arrays to 0/1, like sequences
            "(define-fun cv_union ((a (Array Int Int)) (b (Array Int Int))) (Array Int Int) (lambda ((i Int)) (ite (or (distinct (select a i) 0) (distinct (select b i) 0)) 1 0)))\n" +
            "(define-fun cv_subset ((a (Array Int Int)) (b (Array Int Int))) Bool (forall ((i Int)) (=> (distinct (select a i) 0) (distinct (select b i) 0))))\n" +
            "(define-fun cv_disjoint ((a (Array Int Int)) (b (Array Int Int))) Bool (forall ((i Int)) (not (and (distinct (select a i) 0) (distinct (select b i) 0)))))\n" +
            // what a call with Spec.Modifies(w) may change: objects in w, and objects not allocated before it
            "(define-fun cv_mod ((w (Array Int Int)) (alloc (Array Int Int))) (Array Int Int) (lambda ((i Int)) (ite (or (distinct (select w i) 0) (= (select alloc i) 0)) 1 0)))\n" +
            "(define-fun cv_frame ((m (Array Int Int)) (old (Array Int Int)) (new (Array Int Int))) (Array Int Int) (lambda ((i Int)) (ite (distinct (select m i) 0) (select new i) (select old i))))\n" +
            "(define-fun cv_frameh ((m (Array Int Int)) (old (Array Int (Array Int Int))) (new (Array Int (Array Int Int)))) (Array Int (Array Int Int)) (lambda ((i Int)) (ite (distinct (select m i) 0) (select new i) (select old i))))\n" +
            // multisets (Bag): arrays from value to count. cv_bag(r, n) is the multiset of r[0..n); writing r[i]
            // inside the prefix trades the old element for the new one, outside it changes nothing. Each axiom is
            // triggered only by the multiset of a written array, so they cannot loop.
            "(define-fun cv_badd ((m (Array Int Int)) (x Int)) (Array Int Int) (store m x (+ (select m x) 1)))\n" +
            "(define-fun cv_bremove ((m (Array Int Int)) (x Int)) (Array Int Int) (store m x (- (select m x) 1)))\n" +
            "(define-fun cv_bunion ((a (Array Int Int)) (b (Array Int Int))) (Array Int Int) (lambda ((i Int)) (+ (select a i) (select b i))))\n" +
            "(declare-fun cv_bag ((Array Int Int) Int) (Array Int Int))\n" +
            "(assert (forall ((r (Array Int Int))) (! (= (cv_bag r 0) ((as const (Array Int Int)) 0)) :pattern ((cv_bag r 0)))))\n" +
            "(assert (forall ((r (Array Int Int)) (i Int) (v Int) (n Int)) (! (=> (and (<= 0 i) (< i n)) (= (cv_bag (store r i v) n) (cv_badd (cv_bremove (cv_bag r n) (select r i)) v))) :pattern ((cv_bag (store r i v) n)))))\n" +
            "(assert (forall ((r (Array Int Int)) (i Int) (v Int) (n Int)) (! (=> (or (< i 0) (<= n i)) (= (cv_bag (store r i v) n) (cv_bag r n))) :pattern ((cv_bag (store r i v) n)))))";

        /// <param name="state">the caller's state, whose heap fields the callee's contract reads</param>
        /// <summary>A base's or contract class's specifications name their own parameters: they stand for these arguments.</summary>
        private static void AliasParameters(Frame frame, IMethodSymbol alias, Term[] args)
        {
            for (int i = 0; i < alias.Parameters.Length && i < args.Length; i++)
                if (args[i] != null) frame.Vars[alias.Parameters[i]] = args[i];
        }

        /// <summary>An inherited postcondition is promised only where the base's precondition held on entry.</summary>
        private Term GuardedBy(Postcondition post, Frame entry, Term goal)
        {
            if (post.Guard == null) return goal;
            var env = new SpecEnv { Old = entry };
            return T.Implies(T.And(post.Guard.Select(g => AsBool(EvalForeignSpec(g, entry, env))).ToArray()), goal);
        }

        /// <summary>
        /// Behavioural subtyping (Liskov): an override or implementation may not require more than a member it
        /// overrides promises its callers (CSV1018), nor change more than that member's Spec.Modifies allows. Its
        /// postconditions include every inherited one, checked at each return.
        /// </summary>
        private void CheckSubtyping(Frame f, SpecEnv spec)
        {
            foreach (var b in _contract.Bases.Where(b => _contract.OwnRequires.Count > 0))
            {
                _z3.Push();
                foreach (var req in b.Requires) _z3.Assume(AsBool(EvalForeignSpec(req, f, spec)));
                Prove(T.And(_contract.OwnRequires.Select(r => AsBool(EvalForeignSpec(r, f, spec))).ToArray()), "CSV1018", MethodLocationNode(),
                    $"'{_method.Name}' requires more than {b.Method.ContainingType.Name}.{b.Method.Name}, which it overrides, promises its callers", assume: false);
                _z3.Pop();
            }
            foreach (var (b, frame) in _contract.BaseModifies.Where(x => !ReferenceEquals(x.Frame, _contract.Modifies)))
            {
                var own = T.Coerce(EvalForeignSpec(_contract.Modifies, f, spec), Sort.Row);
                var allowed = T.Coerce(EvalForeignSpec(frame, f, spec), Sort.Row);
                Prove(new Term($"(cv_subset {own} {allowed})", Sort.Bool), "CSV1018", MethodLocationNode(),
                    $"Spec.Modifies of '{_method.Name}' might not be within that of {b.Method.ContainingType.Name}.{b.Method.Name}, which it overrides", assume: false);
            }
        }

        private Frame CalleeFrame(Contract callee, Term receiver, Term[] args, Term heap, Frame state = null)
        {
            var frame = new Frame { This = receiver, Heap = heap };
            // a local function's contract may name what it captures: the caller's variables, as they are at the call
            if (callee.Method?.MethodKind == MethodKind.LocalFunction && state != null)
            {
                foreach (var kv in state.Vars) frame.Vars[kv.Key] = kv.Value;
                frame.This ??= state.This;
            }
            foreach (var alias in callee.Aliases.Where(a => !SymbolEqualityComparer.Default.Equals(a, callee.Stub))) AliasParameters(frame, alias, args);
            if (callee.IsStub)
            {
                // the stub's parameters: @this is the receiver, the others are the member's
                if (callee.StubReceiver != null && receiver != null) frame.Vars[callee.StubReceiver] = receiver;
                for (int i = 0; i < args.Length; i++)
                    if (args[i] != null && StubParameter(callee, i) is IParameterSymbol sp) frame.Vars[sp] = args[i];
            }
            if (state != null)
            {
                frame.Fields = new Dictionary<ISymbol, Term>(state.Fields, SymbolEqualityComparer.Default);
                frame.FieldEpoch = state.FieldEpoch;
                frame.Alloc = state.Alloc;
                frame.Root = state.Root;
                frame.Owner = state.Owner;
                frame.Link = state.Link;
            }
            for (int i = 0; i < args.Length && i < callee.Method.Parameters.Length; i++)
                if (args[i] != null) frame.Vars[callee.Method.Parameters[i]] = args[i];
            return frame;
        }

        /// <summary>
        /// A [Pure] method is a mathematical function: an uninterpreted function whose definition (single return
        /// expression) and postconditions are unfolded once, guarded by its preconditions.
        /// </summary>
        /// <param name="specCall">set for a call inside a specification: its precondition is a well-definedness obligation
        /// there (in code it was already checked as the callee's precondition)</param>
        private Term PureApply(Contract callee, Term receiver, Term[] args, Term heap, Sort sort, SyntaxNode specCall = null, Frame state = null)
        {
            var m = callee.Method;
            if (callee.IsStub) Assumed(callee);
            if (callee.StubDefinition != null && state != null) return StubValue(callee, receiver, args, heap, sort, specCall, state);
            var all = new List<Term>();
            if (receiver != null) all.Add(receiver);
            all.AddRange(args.Select(a => a ?? T.Int(0)));
            // (a virtual query and its overrides are one function: what they depend on is decided at the root)
            var rootDecl = m;
            while (rootDecl.OverriddenMethod != null) rootDecl = rootDecl.OverriddenMethod.OriginalDefinition;
            bool readsHeap = m.Parameters.Any(p => IsSequence(p.Type)) || _engine.Fields.ReadsArrays(rootDecl);
            if (readsHeap && _engine.Fields.ReadsOnlyParameterArrays(rootDecl))
            {
                // only its array parameters' contents matter: writing another array leaves the value as it is
                for (int i = 0; i < m.Parameters.Length; i++)
                    if (IsSequence(m.Parameters[i].Type) && args[i] != null && args[i].Sort == Sort.Int)
                        all.Add(T.Select(heap, args[i], Sort.Row));
            }
            else if (readsHeap) all.Add(heap);
            // and the heap fields it reads (for a virtual query, any of its overrides): its value is a function of them too
            var stateFrame = state ?? new Frame();
            var declared = m;
            while (declared.OverriddenMethod != null) declared = declared.OverriddenMethod.OriginalDefinition;
            foreach (var field in _engine.Fields.ReadsOf(declared)) all.Add(FieldMap(stateFrame, field));
            // one function for a virtual query and all its overrides: named after the declaration they all override
            var root = m;
            while (root.OverriddenMethod != null) root = root.OverriddenMethod.OriginalDefinition;
            var app = _z3.Apply("pure:" + root.ToDisplayString(), SortOf(m.ReturnType), all);
            // an override's definition and extra postconditions hold for instances of its class; a body defines the
            // function only where it is the one that runs (not overridable further)
            var instance = receiver != null && (m.IsOverride || _engine.BaseMembers(m).Any()) && ModeledType(m.ContainingType) != null
                ? T.Implies(NotNull(receiver), Isa(receiver, ModeledType(m.ContainingType))) : T.True;
            bool bodyRuns = !Engine.IsOverridable(m);

            bool wanted = specCall != null && !_codeMode && _foreignSpec == 0;
            if (_unfoldDepth == 0 || wanted)
            {
                Term pre;
                bool wasCode = _codeMode;
                _codeMode = false;
                _foreignSpec++; // the callee's own contract and definition: no obligations of ours
                bool unfold = _unfoldDepth == 0;
                _unfoldDepth++;
                try
                {
                    var frame = CalleeFrame(callee, receiver, args, heap, stateFrame);
                    var env = new SpecEnv { Old = frame, Result = app };
                    pre = T.And(callee.Requires.Select(r => AsBool(Eval(r, frame, env))).ToArray());
                    if (unfold)
                    {
                        var body = callee.PureBody != null ? Eval(callee.PureBody, frame, env)
                                 : callee.PureStatements != null ? PureStatementsTerm(callee.PureStatements, 0, frame, env) : null;
                        if (body != null && bodyRuns)
                            AssumeSide(T.Implies(T.And(instance, pre), T.Eq(app, T.Coerce(body, app.Sort))));
                        if (IsNonNullableReturn(m)) AssumeSide(T.Implies(pre, NotNull(app)));
                        foreach (var ens in callee.Ensures)
                            AssumeSide(T.Implies(T.And(instance, pre), AsBool(Eval(ens.Expr, frame, new SpecEnv { Old = frame, Result = app, ResultParameter = ens.ResultParameter }))));
                        // through a base type, each final override defines the query for instances of its class
                        if (receiver != null && Engine.IsOverridable(m))
                            foreach (var o in _engine.Fields.Overrides(root).Where(o => !Engine.IsOverridable(o)))
                            {
                                var oc = _engine.ContractOf(o);
                                if (oc.PureBody == null || !(ModeledType(o.ContainingType) is INamedTypeSymbol ot)) continue;
                                var oframe = CalleeFrame(oc, receiver, args, heap, stateFrame);
                                var oenv = new SpecEnv { Old = oframe, Result = app };
                                var opre = T.And(oc.Requires.Select(r => AsBool(Eval(r, oframe, oenv))).ToArray());
                                AssumeSide(T.Implies(T.And(NotNull(receiver), Isa(receiver, ot), opre), T.Eq(app, Eval(oc.PureBody, oframe, oenv))));
                            }
                    }
                }
                finally { _unfoldDepth--; _foreignSpec--; _codeMode = wasCode; }
                // outside its precondition a pure function's value is unspecified: using it there is ill-defined
                if (wanted) Require(pre, "CSV1001", specCall, $"precondition of '{m.Name}' might not hold in '{specCall}'");
                if (wanted && state != null)
                {
                    var frame = CalleeFrame(callee, receiver, args, heap, stateFrame);
                    CheckPurePermissions(callee, frame, new SpecEnv { Old = frame }, state, specCall);
                }
            }
            LinkPure(callee, receiver, args, sort, state, app);
            // a run-time function returns a value of its type (a ghost function's integers are mathematical)
            if (!SpecSymbols.IsGhostFunction(m)) InRangeOf(app, m.ReturnType);
            return T.Coerce(app, sort);
        }

        private Term[] EvalMeasure(IReadOnlyList<IOperation> measure, Frame f, SpecEnv spec) =>
            measure.Select(m => ToMeasure(m, EvalForeignSpec(m, f, spec))).ToArray();

        private static string MeasureText(IReadOnlyList<IOperation> measure) => string.Join(", ", measure.Select(m => m.Syntax));

        /// <summary>
        /// <paramref name="after"/> &lt; <paramref name="before"/> lexicographically: some component goes down, from a
        /// non-negative value, and every component before it stays the same. Well-founded, as ATS's metrics on nat tuples.
        /// </summary>
        private static Term LexDecreases(Term[] after, Term[] before)
        {
            var cases = new List<Term>();
            for (int i = 0; i < before.Length; i++)
            {
                var same = Enumerable.Range(0, i).Select(j => T.Eq(after[j], before[j]));
                cases.Add(T.And(same.Concat(new[] { T.Le(T.Int(0), before[i]), T.Lt(after[i], before[i]) }).ToArray()));
            }
            return T.Or(cases.ToArray());
        }

        /// <summary>
        /// The state <c>Spec.Old</c> reads: heap and parameters as on entry; locals and quantifier-bound variables,
        /// which the entry state does not have, keep their current values (like Dafny's <c>old</c>).
        /// </summary>
        private static Frame OldFrame(Frame entry, Frame now)
        {
            var old = entry.Clone();
            foreach (var kv in now.Vars)
                if (!old.Vars.ContainsKey(kv.Key)) old.Vars[kv.Key] = kv.Value;
            return old;
        }

        private Term Quantifier(IInvocationOperation inv, Frame f, SpecEnv spec, bool forall)
        {
            // in a control-flow graph (a [GhostFunction] body) the lambda is lowered; read the original tree instead
            if (!((inv.Arguments[2].Value as IDelegateCreationOperation)?.Target is IAnonymousFunctionOperation) &&
                _model.GetOperation(inv.Syntax) is IInvocationOperation original)
                inv = original;
            var lo = Eval(inv.Arguments[0].Value, f, spec);
            var hi = Eval(inv.Arguments[1].Value, f, spec);
            var fn = (inv.Arguments[2].Value as IDelegateCreationOperation)?.Target as IAnonymousFunctionOperation;
            var bodyOp = fn?.Body.Operations.OfType<IReturnOperation>().FirstOrDefault()?.ReturnedValue;
            if (bodyOp == null) { Unsupported(inv); return _z3.Fresh("quant", Sort.Bool); }
            var name = _z3.FreshName(fn.Symbol.Parameters[0].Name);
            var bound = new Term(name, Sort.Int);
            var inner = f.Clone();
            inner.Vars[fn.Symbol.Parameters[0]] = bound;
            _quantDepth++;
            int factLevels = _quantFacts.Count;
            _quantFacts.Push(new List<Term>());
            var inside = new List<Obligation>();
            _obligations.Push(inside);
            _guards.Add(T.And(T.Le(lo, bound), T.Lt(bound, hi)));
            int guardLevel = _guards.Count;
            try
            {
                var body = AsBool(Eval(bodyOp, inner, spec));
                var range = T.And(T.Le(lo, bound), T.Lt(bound, hi));
                // Side facts about the body's terms (lengths, [Pure] unfoldings) may mention the bound variable. They
                // become an axiom of their own, quantified the same way, and assumed whether this quantifier is a
                // hypothesis or a goal. (As a hypothesis of the body they would be useless where the quantifier is
                // assumed: a model could falsify them and satisfy the implication vacuously.)
                // A fact that does not mention it (a [Pure] call on other arguments) is assumed as it is: quantified,
                // it would have no term for Z3 to instantiate it with.
                var collected = _quantFacts.Pop();
                foreach (var plain in collected.Where(x => !x.S.Contains(name))) AssumeSide(plain);
                var facts = T.And(collected.Where(x => x.S.Contains(name)).ToArray());
                if (facts != T.True) AssumeSide(T.Quant("forall", name, T.Implies(range, facts)));
                // obligations made inside (already guarded by the range) hold for every value of the variable
                _guards.RemoveAt(guardLevel - 1);
                _obligations.Pop();
                foreach (var ob in inside)
                    Emit(new Obligation { Condition = T.Quant("forall", name, ob.Condition), Id = ob.Id, At = ob.At, Message = ob.Message });
                return forall ? T.Quant("forall", name, T.Implies(range, body))
                              : T.Quant("exists", name, T.And(range, body));
            }
            finally
            {
                while (_quantFacts.Count > factLevels) _quantFacts.Pop();
                if (_guards.Count >= guardLevel) _guards.RemoveRange(guardLevel - 1, _guards.Count - guardLevel + 1);
                if (_obligations.Count > 0 && ReferenceEquals(_obligations.Peek(), inside)) _obligations.Pop();
                _quantDepth--;
            }
        }

        // ================================================================================== nullability

        private static Term NotNull(Term r) => T.Not(T.Eq(r, T.Int(0)));

        /// <summary>
        /// A value of this type may be null at run time: a reference (array, string, class, interface, delegate) or a
        /// type parameter that is not a value type. Ghosts, sequences and views are values.
        /// </summary>
        private static bool MayBeNullType(ITypeSymbol t) =>
            t != null && !SpecSymbols.IsGhostType(t) && !SpecSymbols.IsSeqType(t) &&
            (t.IsReferenceType || (t is ITypeParameterSymbol tp && !tp.HasValueTypeConstraint && !tp.HasUnmanagedTypeConstraint));

        /// <summary>
        /// The declared type promises a value that is not null: a non-nullable reference type in an enabled nullable
        /// context. An oblivious type (nullable disabled), <c>T?</c> and a type parameter (it may be instantiated with
        /// a nullable type) promise nothing.
        /// </summary>
        private static bool IsNonNullableType(ITypeSymbol t) =>
            SpecSymbols.IsGhostType(t) ? IsNonNullableType(((INamedTypeSymbol)t).TypeArguments[0]) // Ghost<T>: T's
            : MayBeNullType(t) && !(t is ITypeParameterSymbol) && t.NullableAnnotation == NullableAnnotation.NotAnnotated;

        private static bool IsNonNullable(IParameterSymbol p) =>
            (IsNonNullableType(p.OriginalDefinition.Type) || p.OriginalDefinition.Type is ITypeParameterSymbol { HasNotNullConstraint: true } && p.OriginalDefinition.NullableAnnotation != NullableAnnotation.Annotated && MayBeNullType(p.Type)) && !HasAttribute(p.OriginalDefinition.GetAttributes(), "AllowNullAttribute") ||
            // (query syntax's own: the object its previous clause made, or the group of group ... into g)
            p.ContainingSymbol is IMethodSymbol { MethodKind: MethodKind.AnonymousFunction } fn &&
            !(fn.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() is Microsoft.CodeAnalysis.CSharp.Syntax.AnonymousFunctionExpressionSyntax) &&
            (p.Type.IsAnonymousType || p.Type.OriginalDefinition.ToDisplayString() == "System.Linq.IGrouping<TKey, TElement>");

        private static bool IsNonNullableReturn(IMethodSymbol m) =>
            !m.ReturnsVoid && (m.IsAsync ? AsyncResultType(m.OriginalDefinition) is ITypeSymbol t && IsNonNullableType(t) // (what it returns: its task's result)
                                         : IsNonNullableType(m.OriginalDefinition.ReturnType)) &&
            !HasAttribute(m.OriginalDefinition.GetReturnTypeAttributes(), "MaybeNullAttribute");

        private static bool HasAttribute(IEnumerable<AttributeData> attributes, string name) =>
            attributes.Any(a => a.AttributeClass?.ToDisplayString() == "System.Diagnostics.CodeAnalysis." + name);

        private static bool IsNullConstant(IOperation op) => op.ConstantValue.HasValue && op.ConstantValue.Value == null;

        /// <summary>Member access, indexing or a call on <paramref name="receiver"/>: defined only if it is not null.</summary>
        /// <summary>
        /// In a lambda, a local from around it with one value all along (a foreach's, or one assigned only where it is
        /// declared) that the compiler's flow analysis has as not null. What the lambda knows of it is nothing, otherwise.
        /// </summary>
        private bool IsCapturedNotNull(IOperation receiver)
        {
            if (!(Unconverted(receiver) is ILocalReferenceOperation l) || !(l.Syntax.FirstAncestorOrSelf<AnonymousFunctionExpressionSyntax>() is AnonymousFunctionExpressionSyntax lambda)) return false;
            var declared = l.Local.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax();
            if (declared == null || lambda.Span.Contains(declared.Span) || _model.GetTypeInfo(l.Syntax).Nullability.FlowState != NullableFlowState.NotNull) return false;
            var scope = declared.FirstAncestorOrSelf<MemberDeclarationSyntax>();
            return !scope.DescendantNodes().OfType<IdentifierNameSyntax>().Any(id => LockGuards.IsWriteTarget(id) && SymbolEqualityComparer.Default.Equals(_model.GetSymbolInfo(id).Symbol, l.Local));
        }

        private void Deref(IOperation receiver, Term r, SyntaxNode at)
        {
            if (receiver is IInstanceReferenceOperation || !MayBeNullType(receiver.Type)) return;
            if (IsCapturedNotNull(receiver)) return;
            Require(NotNull(r), "CSV1013", at, $"'{receiver.Syntax}' might be null in '{at}'");
        }

        /// <summary>An argument for a non-nullable parameter: the callee assumes it is not null, so the caller proves it.</summary>
        private void NonNullArgument(IArgumentOperation a, Term v, IMethodSymbol callee)
        {
            if (a.Parameter == null || !IsNonNullable(a.Parameter) || SpecSymbols.IsSpecClass(callee?.ContainingType)) return;
            Require(NotNull(v), "CSV1014", a.Syntax, (IsNullConstant(a.Value) ? "null is passed" : $"'{a.Value.Syntax}' might be null,") +
                $" but parameter '{a.Parameter.Name}' of '{callee?.Name}' is not nullable");
        }

        /// <summary>
        /// A library method's (trusted) nullability attributes: <c>[NotNull]</c> parameters are not null after the call
        /// (<c>ArgumentNullException.ThrowIfNull</c>), <c>[NotNullWhen(b)]</c> ones when it returns b
        /// (<c>string.IsNullOrEmpty</c>), and a non-nullable return type is not null.
        /// </summary>
        private void LibraryNullFacts(IInvocationOperation inv, Term[] args, Term result)
        {
            var m = inv.TargetMethod;
            if (IsNonNullableReturn(m)) _z3.Assume(NotNull(result));
            foreach (var a in inv.Arguments)
            {
                var p = a.Parameter;
                if (p == null || p.RefKind == RefKind.Out || args[p.Ordinal] == null || !MayBeNullType(a.Value.Type)) continue;
                foreach (var attr in p.OriginalDefinition.GetAttributes())
                {
                    var name = attr.AttributeClass?.ToDisplayString();
                    if (name == "System.Diagnostics.CodeAnalysis.NotNullAttribute")
                        _z3.Assume(NotNull(args[p.Ordinal]));
                    else if (name == "System.Diagnostics.CodeAnalysis.NotNullWhenAttribute" && result.Sort == Sort.Bool &&
                             attr.ConstructorArguments.Length == 1 && attr.ConstructorArguments[0].Value is bool when)
                        _z3.Assume(T.Implies(when ? result : T.Not(result), NotNull(args[p.Ordinal])));
                }
            }
        }

        /// <summary>
        /// The value of a [Pure] function's statements from the i-th on, as a term: local declarations bind their
        /// variables, an if is a conditional (each branch followed by the statements after it), a return is its value;
        /// specification statements and lemma calls are skipped. Null for anything else (the function is then known by
        /// its contract only).
        /// </summary>
        private Term PureStatementsTerm(IReadOnlyList<IOperation> ops, int i, Frame f, SpecEnv spec)
        {
            if (i >= ops.Count) return null;
            var op = ops[i];
            IReadOnlyList<IOperation> Then(IOperation first) =>
                (first is IBlockOperation b ? b.Operations : (IEnumerable<IOperation>)new[] { first }).Concat(ops.Skip(i + 1)).ToList();
            switch (op)
            {
                case IReturnOperation ret when ret.ReturnedValue != null:
                    return Eval(ret.ReturnedValue, f, spec);
                case IBlockOperation block:
                    return PureStatementsTerm(Then(block), 0, f, spec);
                case IVariableDeclarationGroupOperation group:
                    foreach (var decl in group.Declarations)
                        foreach (var v in decl.Declarators)
                        {
                            var init = v.Initializer?.Value ?? decl.Initializer?.Value;
                            if (init == null) return null;
                            f.Vars[v.Symbol] = Eval(init, f, spec);
                        }
                    return PureStatementsTerm(ops, i + 1, f, spec);
                case IConditionalOperation cond when cond.Type == null || cond.Type.SpecialType == SpecialType.System_Void:
                {
                    var c = AsBool(Eval(cond.Condition, f, spec));
                    var yes = PureStatementsTerm(Then(cond.WhenTrue), 0, f, spec);
                    var no = cond.WhenFalse != null ? PureStatementsTerm(Then(cond.WhenFalse), 0, f, spec) : PureStatementsTerm(ops, i + 1, f, spec);
                    if (yes == null || no == null) return null;
                    return T.Ite(c, yes, T.Coerce(no, yes.Sort));
                }
                case IExpressionStatementOperation es when es.Operation is IInvocationOperation inv &&
                                                          (SpecSymbols.IsSpecClass(inv.TargetMethod.ContainingType) || _engine.ContractOf(inv.TargetMethod).IsLemma):
                    return PureStatementsTerm(ops, i + 1, f, spec);
                default:
                    return null;
            }
        }

        private Term Builtin(IInvocationOperation inv, Frame f, SpecEnv spec)
        {
            var m = inv.TargetMethod;
            if (FloatBuiltin(inv, f, spec) is Term floating) return floating;
            if (m.ContainingType?.ToDisplayString() != "System.Math" || !IsIntegral(inv.Type)) return null;
            var args = inv.Arguments.Select(a => Eval(a.Value, f, spec)).ToArray();
            switch (m.Name)
            {
                case "Max" when args.Length == 2: return T.Ite(T.Ge(args[0], args[1]), args[0], args[1]);
                case "Min" when args.Length == 2: return T.Ite(T.Le(args[0], args[1]), args[0], args[1]);
                case "Abs" when args.Length == 1:
                    // Math.Abs(MinValue) throws, like a checked operation
                    return Bounded(T.Abs(args[0]), inv.Type, inv.Syntax, true, $"'{inv.Syntax}' overflows for {inv.Type.Name}.MinValue");
                default: return null;
            }
        }
    }
}
