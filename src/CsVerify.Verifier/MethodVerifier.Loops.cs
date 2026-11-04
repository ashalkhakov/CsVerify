using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.FlowAnalysis;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Loops that are not while/for/do statements:
    /// <list type="bullet">
    /// <item><c>foreach</c> over a one-dimensional array is what C# compiles it to, a loop over a hidden index
    /// <c>i</c> from 0 to the array's length, reading <c>a[i]</c> into the iteration variable (the array is evaluated
    /// once; the enumerator and its finally do not exist). <c>Spec.Index(x)</c> is that index: in an invariant, the
    /// number of elements gone through, and in the body, the index of <c>x</c>. The loop terminates by itself.</item>
    /// <item><c>foreach</c> over anything else is the enumerator pattern the flow graph shows: GetEnumerator, then
    /// MoveNext and Current in each iteration, and Dispose in a finally, each an ordinary (modular) call.</item>
    /// <item>a cycle made by <c>goto</c> is cut at the head of each natural loop of the flow graph (a block that
    /// dominates the blocks that jump back to it), like a loop statement. Its invariants and measure are the
    /// Spec.Invariant/Decreases statements right after the label. A cycle with no such head (a goto into the middle
    /// of a loop) is still rejected.</item>
    /// </list>
    /// </summary>
    internal sealed partial class MethodVerifier
    {
        /// <summary>The flow captures of foreach enumerators.</summary>
        private readonly HashSet<CaptureId> _enumerators = new HashSet<CaptureId>();
        /// <summary>The foreach loops over arrays, by the flow capture of their enumerator.</summary>
        private readonly Dictionary<CaptureId, Loop> _arrayForEach = new Dictionary<CaptureId, Loop>();
        /// <summary>Their MoveNext calls and Current reads (with the conversion to the iteration variable's type).</summary>
        private readonly Dictionary<IOperation, Loop> _arrayMoveNext = new Dictionary<IOperation, Loop>();
        private readonly Dictionary<IOperation, Loop> _arrayCurrent = new Dictionary<IOperation, Loop>();
        /// <summary>The foreach loop of each iteration variable (for Spec.Index).</summary>
        private readonly Dictionary<ILocalSymbol, Loop> _forEachOf = new Dictionary<ILocalSymbol, Loop>(SymbolEqualityComparer.Default);
        /// <summary>The try/finally regions of foreach loops over arrays: C# emits neither (there is no enumerator to dispose).</summary>
        private readonly HashSet<ControlFlowRegion> _erasedTry = new HashSet<ControlFlowRegion>();

        // ================================================================================== foreach

        private void FindForEach(CommonForEachStatementSyntax fe, ControlFlowGraph cfg)
        {
            if (!(_model.GetOperation(fe) is IForEachLoopOperation fo) || fo.IsAsynchronous)
            {
                NotModeled(fe.ForEachKeyword, "await foreach is not supported");
                return;
            }
            // the enumerator is captured before the loop; the loop's head asks it MoveNext
            var capture = cfg.Blocks.SelectMany(b => b.Operations).OfType<IFlowCaptureOperation>()
                .FirstOrDefault(c => c.Syntax == fe.Expression && c.Value is IInvocationOperation gi && gi.TargetMethod.Name == "GetEnumerator");
            var head = capture == null ? null : cfg.Blocks.FirstOrDefault(b => IsMoveNext(b.BranchValue, capture.Id));
            if (head == null)
            {
                NotModeled(fe.ForEachKeyword, "this foreach is not supported (its enumerator is not the usual GetEnumerator/MoveNext/Current)");
                return;
            }
            _enumerators.Add(capture.Id);
            var loop = new Loop { Id = _loops.Count, Syntax = fe, Head = head.Ordinal };
            ReadLoopSpecs(fe.Statement is BlockSyntax bs ? bs.Statements : new SyntaxList<StatementSyntax>(fe.Statement), loop);
            bool array = IsArrayForEach(fe);
            // a List whose loop changes no model state (else MoveNext would throw): like an array, over its model
            var listElement = array ? null : ListForEachElement(fe, fo);
            if (listElement != null)
            {
                var trial = new Loop();
                CollectHavoc(new SyntaxNode[] { fe }, trial);
                if (trial.HavocAllFields || trial.HavocFields.Any(x => x is IMethodSymbol model && SpecSymbols.IsModel(model))) listElement = null;
            }
            // an IReadOnlyList or IList whose loop changes no state: over its Count and indexer
            var interfaceElement = array || listElement != null ? null : InterfaceForEachElement(fe, fo);
            if (interfaceElement != null)
            {
                // (what its body changes: the enumerator's own MoveNext and Current are replaced by the index)
                var trial = new Loop();
                CollectHavoc(new SyntaxNode[] { fe.Statement }, trial);
                if (trial.HavocAllFields || trial.HavocFields.Count > 0 || trial.HavocHeap || trial.HavocArrays.Count > 0) interfaceElement = null;
            }
            if (array || listElement != null || interfaceElement != null)
            {
                loop.ArrayElement = listElement ?? interfaceElement ?? ((IArrayTypeSymbol)Unconverted(fo.Collection).Type).ElementType;
                loop.OverList = listElement != null;
                loop.OverInterface = interfaceElement != null;
                if (loop.OverList) Assumed("System.Collections.Generic.List<T>.GetEnumerator()");
                _arrayForEach[capture.Id] = loop;
                _arrayMoveNext[head.BranchValue] = loop;
                foreach (var op in cfg.Blocks.SelectMany(b => b.Operations).SelectMany(o => o.DescendantsAndSelf()))
                    if (op is IPropertyReferenceOperation pr && pr.Property.Name == "Current" && pr.Instance is IFlowCaptureReferenceOperation r && r.Id.Equals(capture.Id))
                    {
                        _arrayCurrent[pr] = loop;
                        if (pr.Parent is IConversionOperation conv) _arrayCurrent[conv] = loop;
                    }
            }
            // the enumerator's Dispose: an array has none, and a List's does nothing; neither does a library
            // collection's (trusted, as its Count and indexer are: the program has no list of its own then)
            if (array || IsList(Unconverted(fo.Collection).Type) || interfaceElement != null)
                for (var region = head.EnclosingRegion; region != null; region = region.EnclosingRegion)
                    if (region.Kind == ControlFlowRegionKind.Try && region.EnclosingRegion?.Kind == ControlFlowRegionKind.TryAndFinally)
                    {
                        _erasedTry.Add(region.EnclosingRegion);
                        break;
                    }
            foreach (var l in ForEachLocals(fe)) if (l is ILocalSymbol local) _forEachOf[local] = loop;
            // through an enumerator of a versioned collection: "the version is still the enumerator's", inferred as the
            // loop facts are (held on entry, kept at every back edge; else MoveNext reports the change)
            if (!array && listElement == null && interfaceElement == null && capture.Value is IInvocationOperation ge &&
                VersionModel(ge.TargetMethod.ContainingType) is IMethodSymbol version)
            {
                var id = capture.Id;
                loop.Facts.Add(new LoopFact
                {
                    Key = loop.Id + ":version",
                    Make = fr => fr.Captures.TryGetValue(id, out var e)
                        ? T.Eq(T.Coerce(ModelAt(version, new[] { EnumeratorOf(e) }, fr), Sort.Int), EnumeratorVersion(e))
                        : T.True,
                });
            }
            // a foreach over an array ends by itself: its index goes up to the array's (fixed) length
            AddLoop(loop, new SyntaxNode[] { fe }, needsMeasure: !array && listElement == null && interfaceElement == null);
        }

        private static bool IsMoveNext(IOperation op, CaptureId enumerator) =>
            op is IInvocationOperation mn && mn.TargetMethod.Name == "MoveNext" && mn.Instance is IFlowCaptureReferenceOperation r && r.Id.Equals(enumerator);

        /// <summary>
        /// A foreach over a one-dimensional array whose elements become the iteration variable unchanged (the same
        /// type, a base type, or a wider integer type).
        /// </summary>
        private bool IsArrayForEach(CommonForEachStatementSyntax fe)
        {
            if (!(_model.GetOperation(fe) is IForEachLoopOperation fo) || fo.IsAsynchronous ||
                !(Unconverted(fo.Collection).Type is IArrayTypeSymbol at) || at.Rank != 1) return false;
            var c = _model.GetForEachStatementInfo(fe).ElementConversion;
            var target = fo.Locals.FirstOrDefault()?.Type;
            return c.IsIdentity || c.IsImplicit && c.IsReference ||
                   c.IsImplicit && c.IsNumeric && IsIntegral(at.ElementType) && target != null && IsIntegral(target);
        }

        /// <summary>
        /// A foreach over a List&lt;T&gt; (with CsVerify.Bcl's model functions in use) whose elements become the iteration
        /// variable unchanged: the element type; else null.
        /// </summary>
        private ITypeSymbol ListForEachElement(CommonForEachStatementSyntax fe, IForEachLoopOperation fo)
        {
            if (!IsList(Unconverted(fo.Collection).Type) || ListModel("Items") == null || ListModel("Size") == null) return null;
            var lt = (INamedTypeSymbol)Unconverted(fo.Collection).Type;
            var c = _model.GetForEachStatementInfo(fe).ElementConversion;
            var target = fo.Locals.FirstOrDefault()?.Type;
            var element = lt.TypeArguments[0];
            return c.IsIdentity || c.IsImplicit && c.IsReference ||
                   c.IsImplicit && c.IsNumeric && IsIntegral(element) && target != null && IsIntegral(target) ? element : null;
        }

        private static bool IsList(ITypeSymbol t) =>
            t is INamedTypeSymbol n && n.OriginalDefinition.ToDisplayString() == "System.Collections.Generic.List<T>";

        /// <summary>CsVerify.Bcl's model function of a list: Items or Size.</summary>
        private IMethodSymbol ListModel(string name) =>
            _engine.Models.FirstOrDefault(m => m.Name == name && m.ContainingType.ToDisplayString() == "CsVerify.Bcl.Models" &&
                (m.Parameters[0].Type as INamedTypeSymbol)?.OriginalDefinition.ToDisplayString() == "System.Collections.Generic.List<T>");

        /// <summary>The variables a foreach assigns in each iteration: its iteration variable, or what it deconstructs into.</summary>
        private IEnumerable<ISymbol> ForEachLocals(CommonForEachStatementSyntax fe)
        {
            if (fe is ForEachStatementSyntax single) return new[] { (ISymbol)_model.GetDeclaredSymbol(single) };
            var targets = ((ForEachVariableStatementSyntax)fe).Variable.DescendantNodesAndSelf().OfType<IdentifierNameSyntax>()
                .Select(id => _model.GetSymbolInfo(id).Symbol).Where(s => s is ILocalSymbol || s is IParameterSymbol);
            var declared = ((ForEachVariableStatementSyntax)fe).Variable.DescendantNodesAndSelf().OfType<SingleVariableDesignationSyntax>()
                .Select(d => _model.GetDeclaredSymbol(d)).Where(s => s is ILocalSymbol);
            return targets.Concat(declared).ToList();
        }

        /// <summary>The enumerator of a foreach over an array, its MoveNext and its Current; null for other operations.</summary>
        private Term EvalArrayForEach(IOperation op, Frame f, SpecEnv spec)
        {
            if (op is IFlowCaptureOperation fc && _arrayForEach.TryGetValue(fc.Id, out var loop))
            {
                // the array is evaluated once (a null array throws), and the index starts at 0
                var collection = Unconverted(((IInvocationOperation)fc.Value).Instance);
                var arr = Eval(collection, f, spec);
                Deref(collection, arr, fc.Syntax);
                _captured[fc.Id] = fc.Value;
                f.ForEach[loop.Id] = (arr, T.Int(0));
                return f.Captures[fc.Id] = arr;
            }
            if (_arrayMoveNext.TryGetValue(op, out loop))
            {
                var (arr, i) = f.ForEach[loop.Id];
                return T.Lt(i, ForEachLength(loop, arr, f));
            }
            if (_arrayCurrent.TryGetValue(op, out loop))
            {
                // MoveNext was true: 0 <= i < a.Length
                var (arr, i) = f.ForEach[loop.Id];
                if (loop.OverInterface)
                    return T.Coerce(InRangeOf(ListItemOf(arr, i, loop.ArrayElement, f), loop.ArrayElement), SortOf(op.Type));
                if (loop.OverList)
                    return T.Coerce(InRangeOf(T.Coerce(T.Select(ModelAt(ListModel("Items"), new[] { arr }, f), i, Sort.Int), SortOf(loop.ArrayElement)), loop.ArrayElement), SortOf(op.Type));
                CheckCellFraming(arr, i, f, op.Syntax);
                var elem = InRangeOf(T.Coerce(T.Select(T.Select(f.Heap, arr, Sort.Row), i, Sort.Int), SortOf(loop.ArrayElement)), loop.ArrayElement);
                return T.Coerce(elem, SortOf(op.Type));
            }
            return null;
        }

        /// <summary>At the head of a foreach over an array: any index from 0 to the length (an invariant the loop keeps by itself).</summary>
        private void ArrayForEachHead(Loop loop, Frame f)
        {
            if (loop.ArrayElement == null || !f.ForEach.TryGetValue(loop.Id, out var st)) return;
            var i = _z3.Fresh("index", Sort.Int);
            _z3.Assume(T.And(T.Le(T.Int(0), i), T.Le(i, ForEachLength(loop, st.arr, f))));
            f.ForEach[loop.Id] = (st.arr, i);
        }

        /// <summary>How far a foreach's index goes: the array's length, or the list's Size().</summary>
        private Term ForEachLength(Loop loop, Term collection, Frame f) =>
            loop.OverInterface ? ListSizeOf(collection, f) :
            loop.OverList ? T.Coerce(ModelAt(ListModel("Size"), new[] { collection }, f), Sort.Int) : Len(collection);

        /// <summary>The end of an iteration (or a continue): the index goes on to the next element.</summary>
        private void ArrayForEachNext(Loop loop, Frame f)
        {
            if (loop.ArrayElement == null || !f.ForEach.TryGetValue(loop.Id, out var st)) return;
            f.ForEach[loop.Id] = (st.arr, T.Add(st.idx, T.Int(1)));
        }

        /// <summary>Spec.Index(x): the index of the iteration variable x of a foreach over an array.</summary>
        private Term ForEachIndex(IInvocationOperation inv, Frame f)
        {
            if (Unconverted(inv.Arguments[0].Value) is ILocalReferenceOperation lr && _forEachOf.TryGetValue(lr.Local, out var loop))
            {
                if (loop.ArrayElement != null && f.ForEach.TryGetValue(loop.Id, out var st)) return st.idx;
                if (loop.ArrayElement == null)
                {
                    Warn(inv.Syntax, $"'{inv.Syntax}': only a foreach over an array or a List has an index; its value is unknown");
                    return Unknown(inv.Type, "index");
                }
            }
            Warn(inv.Syntax, $"'{inv.Syntax}' needs the iteration variable of an enclosing foreach (in its body or invariants); its value is unknown");
            return Unknown(inv.Type, "index");
        }

        /// <summary>Is there a try around this block that C# really emits (not the one of a foreach over an array)?</summary>
        private bool InTry(ControlFlowRegion r)
        {
            for (; r != null; r = r.EnclosingRegion)
                if (r.Kind == ControlFlowRegionKind.Try && !_erasedTry.Contains(r.EnclosingRegion)) return true;
            return false;
        }

        // ================================================================================== goto

        private void FindGotoLoops(ControlFlowGraph cfg)
        {
            int n = cfg.Blocks.Length;
            var succ = Enumerable.Range(0, n).Select(_ => new HashSet<int>()).ToArray();
            var pred = Enumerable.Range(0, n).Select(_ => new HashSet<int>()).ToArray();
            void Edge(int a, int b) { succ[a].Add(b); pred[b].Add(a); }
            foreach (var b in cfg.Blocks)
                foreach (var s in new[] { b.FallThroughSuccessor, b.ConditionalSuccessor })
                    if (s?.Destination != null) Edge(b.Ordinal, s.Destination.Ordinal);
            // a handler (catch, filter, finally) is entered from its try
            void Handlers(ControlFlowRegion r)
            {
                if (r.Kind == ControlFlowRegionKind.TryAndCatch || r.Kind == ControlFlowRegionKind.TryAndFinally)
                    foreach (var h in r.NestedRegions.Skip(1).SelectMany(h => h.NestedRegions.Prepend(h)))
                        Edge(r.NestedRegions[0].FirstBlockOrdinal, h.FirstBlockOrdinal);
                foreach (var nested in r.NestedRegions) Handlers(nested);
            }
            Handlers(cfg.Root);

            // dominators (blocks reached from nowhere dominate only themselves)
            var all = Enumerable.Range(0, n).ToList();
            var dom = all.Select(b => b == 0 || pred[b].Count == 0 ? new HashSet<int> { b } : new HashSet<int>(all)).ToArray();
            for (bool changed = true; changed;)
            {
                changed = false;
                for (int b = 1; b < n; b++)
                {
                    if (pred[b].Count == 0) continue;
                    var d = new HashSet<int>(all);
                    foreach (var p in pred[b]) d.IntersectWith(dom[p]);
                    d.Add(b);
                    if (!d.SetEquals(dom[b])) { dom[b] = d; changed = true; }
                }
            }

            var gotoTargets = new HashSet<ISymbol>(_contract.Declaration.DescendantNodes().OfType<GotoStatementSyntax>()
                .Where(g => g.IsKind(SyntaxKind.GotoStatement)).Select(g => _model.GetSymbolInfo(g.Expression).Symbol).Where(s => s != null), SymbolEqualityComparer.Default);
            var labels = _contract.Declaration.DescendantNodes().OfType<LabeledStatementSyntax>()
                .Where(l => gotoTargets.Contains(_model.GetDeclaredSymbol(l))).ToList();

            foreach (var h in all)
            {
                var latches = pred[h].Where(u => dom[u].Contains(h)).ToList();
                if (latches.Count == 0) continue;
                // the natural loop: the blocks that reach a back edge without passing through the head
                var body = new HashSet<int> { h };
                var work = new Stack<int>(latches);
                while (work.Count > 0)
                {
                    var b = work.Pop();
                    if (!body.Add(b)) continue;
                    foreach (var p in pred[b]) work.Push(p);
                }
                // the finally blocks run on the loop's own branches (a goto out of a try and back to its label)
                var natural = body.ToList();
                bool Inside(ControlFlowRegion r, int b) => r.FirstBlockOrdinal <= b && b <= r.LastBlockOrdinal;
                foreach (var b in natural)
                    foreach (var s in new[] { cfg.Blocks[b].FallThroughSuccessor, cfg.Blocks[b].ConditionalSuccessor })
                        if (s?.Destination != null && body.Contains(s.Destination.Ordinal))
                            foreach (var fr in s.FinallyRegions)
                                for (int x = fr.FirstBlockOrdinal; x <= fr.LastBlockOrdinal; x++) body.Add(x);
                // and a try statement the loop runs through is in the loop, with all its handlers, unless the loop is
                // inside one of its parts (the try block, or one handler: no jump enters a try or a handler)
                foreach (var b in natural)
                    for (var r = cfg.Blocks[b].EnclosingRegion; r != null; r = r.EnclosingRegion)
                        if ((r.Kind == ControlFlowRegionKind.TryAndCatch || r.Kind == ControlFlowRegionKind.TryAndFinally) &&
                            !r.NestedRegions.Any(part => natural.All(x => Inside(part, x))))
                            for (int x = r.FirstBlockOrdinal; x <= r.LastBlockOrdinal; x++) body.Add(x);

                if (_loops.TryGetValue(h, out var statement))
                {
                    // a loop statement that a goto also jumps back to: what the code outside the statement changes is havocked too
                    var outside = body.Where(b => BlockSyntax(cfg.Blocks[b]).Any(s => !statement.Syntax.Span.Contains(s.Span))).ToList();
                    if (outside.Count == 0) continue;
                    CollectBlockHavoc(outside.Select(b => cfg.Blocks[b]), statement);
                    continue;
                }

                var loop = new Loop { Id = _loops.Count, Head = h };
                var first = BlockSyntax(cfg.Blocks[h]).OrderBy(s => s.SpanStart).FirstOrDefault();
                var label = first == null ? null : labels.Where(l => l.SpanStart <= first.SpanStart && l.Parent.Span.Contains(first.Span))
                    .OrderByDescending(l => l.SpanStart).FirstOrDefault();
                loop.Syntax = (SyntaxNode)label ?? first ?? MethodLocationNode();
                if (label != null) ReadLoopSpecs(LabelStatements(label), loop);
                CollectBlockHavoc(body.Select(b => cfg.Blocks[b]), loop);
                AddLoop(loop, body.SelectMany(b => BlockSyntax(cfg.Blocks[b])).ToList(), needsMeasure: true);
            }
        }

        private static IEnumerable<SyntaxNode> BlockSyntax(BasicBlock b) =>
            b.Operations.Select(o => o.Syntax).Concat(b.BranchValue != null ? new[] { b.BranchValue.Syntax } : new SyntaxNode[0]);

        /// <summary>The statement a label labels, and the statements after it in its block.</summary>
        private static IEnumerable<StatementSyntax> LabelStatements(LabeledStatementSyntax label)
        {
            yield return label.Statement;
            var siblings = label.Parent is BlockSyntax block ? block.Statements : label.Parent is SwitchSectionSyntax section ? section.Statements : default;
            foreach (var s in siblings.SkipWhile(s => s != label).Skip(1)) yield return s;
        }

        /// <summary>
        /// What blocks change that their syntax does not show: the calls the flow graph makes (a foreach's MoveNext,
        /// a using's Dispose) and the variables it assigns (a foreach's iteration variable).
        /// </summary>
        private void CollectBlockHavoc(IEnumerable<BasicBlock> blocks, Loop loop)
        {
            var blockList = blocks.ToList();
            CollectHavoc(blockList.SelectMany(BlockSyntax).ToList(), loop);
            foreach (var op in blockList.SelectMany(b => b.Operations.Concat(b.BranchValue != null ? new[] { b.BranchValue } : new IOperation[0])).SelectMany(o => o.DescendantsAndSelf()))
            {
                switch (op)
                {
                    case IInvocationOperation io: CalledInLoop(loop, io.TargetMethod); break;
                    case IAssignmentOperation a when a.Target is ILocalReferenceOperation l: loop.Havoc.Add(l.Local); break;
                    case IAssignmentOperation a when a.Target is IParameterReferenceOperation p: loop.Havoc.Add(p.Parameter); break;
                }
            }
            if (blockList.SelectMany(BlockSyntax).Any(LoopExchangesPermissions)) { loop.Permissions = true; loop.HavocRoot = true; }
            foreach (var a in loop.HavocArrays) if (loop.Havoc.Contains(a)) loop.HavocHeap = true;
        }
    }
}
