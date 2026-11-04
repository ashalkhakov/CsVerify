using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Diagnostics;
using Microsoft.CodeAnalysis.FlowAnalysis;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Analyzers
{
    /// <summary>
    /// Disposables as linear resources. A local holding an object that must be disposed (<see cref="Disposables"/>)
    /// that this method made, or got from a call or an await, owns it. On every path it must be disposed
    /// (<c>Dispose()</c>, <c>DisposeAsync()</c>, a <c>using</c>, a <c>finally</c> that disposes it), returned, or handed
    /// over: stored in a field (the object owns it then), passed to a [TakesOwnership] parameter, or given to
    /// <c>Spec.HandOver</c>. Not doing so is a leak (CSV0020); using it, or disposing it again, after it was disposed is
    /// CSV0021. A parameter is borrowed from the caller, unless it is [TakesOwnership]. A class that owns a field of a
    /// disposable type must be IDisposable and dispose the field in its Dispose (CSV0022), and its objects must be
    /// disposed in turn. A path that ends in an exception is not checked, as for linear values: that is what using is
    /// for.
    /// </summary>
    [DiagnosticAnalyzer(LanguageNames.CSharp)]
    public sealed class DisposalAnalyzer : DiagnosticAnalyzer
    {
        public override ImmutableArray<DiagnosticDescriptor> SupportedDiagnostics => ImmutableArray.Create(
            Descriptors.NotDisposed, Descriptors.UsedAfterDispose, Descriptors.OwnerDoesNotDispose);

        public override void Initialize(AnalysisContext context)
        {
            context.ConfigureGeneratedCodeAnalysis(GeneratedCodeAnalysisFlags.None);
            context.EnableConcurrentExecution();
            context.RegisterOperationAction(AnalyzeBody, OperationKind.MethodBody, OperationKind.ConstructorBody);
            context.RegisterSymbolAction(CheckOwner, SymbolKind.NamedType);
        }

        // ---- owners -------------------------------------------------------------------------------------------

        private static void CheckOwner(SymbolAnalysisContext context)
        {
            var type = (INamedTypeSymbol)context.Symbol;
            if (type.TypeKind != TypeKind.Class || SpecSymbols.IsTrusted(type)) return;
            var d = Disposables.For(context.Compilation);
            var owned = d.OwnedFields(type).ToList();
            if (owned.Count == 0) return;
            bool disposable = type.AllInterfaces.Any(i => i.ToDisplayString() == "System.IDisposable" || i.ToDisplayString() == "System.IAsyncDisposable");
            // what the class's Dispose methods dispose (Dispose(), Dispose(bool), DisposeAsync())
            var disposers = type.GetMembers().OfType<IMethodSymbol>()
                .Where(m => m.Name == "Dispose" || m.Name == "DisposeAsync" || m.Name == "DisposeAsyncCore")
                .SelectMany(m => m.DeclaringSyntaxReferences).Select(r => r.GetSyntax()).ToList();
            foreach (var field in owned)
            {
                var what = (field is IFieldSymbol f ? f.Type : ((IPropertySymbol)field).Type).Name;
                if (!disposable)
                    context.ReportDiagnostic(Diagnostic.Create(Descriptors.OwnerDoesNotDispose, field.Locations.FirstOrDefault(), field.Name, what, type.Name,
                        $"{type.Name} is not IDisposable (make it so and dispose the field, or mark the field [NotOwned])"));
                else if (!disposers.Any(s => Disposes(s, field)))
                    context.ReportDiagnostic(Diagnostic.Create(Descriptors.OwnerDoesNotDispose, field.Locations.FirstOrDefault(), field.Name, what, type.Name,
                        $"{type.Name}'s Dispose never disposes it"));
            }
        }

        /// <summary>Does this Dispose body dispose the field: <c>F.Dispose()</c>, <c>F?.Dispose()</c>, <c>this.F.DisposeAsync()</c>, <c>using (F)</c>?</summary>
        private static bool Disposes(SyntaxNode body, ISymbol field)
        {
            bool Names(ExpressionSyntax e) =>
                e is IdentifierNameSyntax id && id.Identifier.Text == field.Name ||
                e is MemberAccessExpressionSyntax ma && ma.Expression is ThisExpressionSyntax && ma.Name.Identifier.Text == field.Name;
            foreach (var inv in body.DescendantNodes().OfType<InvocationExpressionSyntax>())
            {
                switch (inv.Expression)
                {
                    case MemberAccessExpressionSyntax ma when (ma.Name.Identifier.Text == "Dispose" || ma.Name.Identifier.Text == "DisposeAsync") && Names(ma.Expression):
                        return true;
                    case MemberBindingExpressionSyntax mb when (mb.Name.Identifier.Text == "Dispose" || mb.Name.Identifier.Text == "DisposeAsync") &&
                                                              inv.Parent is ConditionalAccessExpressionSyntax ca && Names(ca.Expression):
                        return true;
                }
            }
            return body.DescendantNodes().OfType<UsingStatementSyntax>().Any(u => u.Expression != null && Names(u.Expression));
        }

        // ---- flow ---------------------------------------------------------------------------------------------

        [System.Flags]
        private enum St : byte { None = 0, Live = 1, Disposed = 2 }

        private sealed class Ctx
        {
            public SemanticModel Model;
            public Disposables D;
            public Dictionary<ISymbol, int> Index;
            public ISymbol[] Vars;
            public Dictionary<CaptureId, int> Captures = new Dictionary<CaptureId, int>();
            public List<Diagnostic> Diags; // null while iterating to a fixpoint
            public void Report(DiagnosticDescriptor d, Location loc, params object[] args) => Diags?.Add(Diagnostic.Create(d, loc, args));
        }

        private static void AnalyzeBody(OperationAnalysisContext context)
        {
            if (SpecSymbols.IsTrusted(context.ContainingSymbol) || !(context.ContainingSymbol is IMethodSymbol method)) return;
            ControlFlowGraph cfg;
            switch (context.Operation)
            {
                case IMethodBodyOperation mb: cfg = ControlFlowGraph.Create(mb); break;
                case IConstructorBodyOperation cb: cfg = ControlFlowGraph.Create(cb); break;
                default: return;
            }
            var d = Disposables.For(context.Compilation);
            var model = context.Operation.SemanticModel;
            // (a using declaration's or statement's own variable is disposed by it)
            var usingLocals = new HashSet<ISymbol>(SymbolEqualityComparer.Default);
            foreach (var node in context.Operation.Syntax.DescendantNodesAndSelf())
            {
                if (node is LocalDeclarationStatementSyntax ld && ld.UsingKeyword.RawKind != 0)
                    foreach (var v in ld.Declaration.Variables) if (model.GetDeclaredSymbol(v) is ISymbol s) usingLocals.Add(s);
                if (node is UsingStatementSyntax us && us.Declaration != null)
                    foreach (var v in us.Declaration.Variables) if (model.GetDeclaredSymbol(v) is ISymbol s) usingLocals.Add(s);
            }
            var vars = new List<ISymbol>();
            foreach (var p in method.Parameters.Where(p => p.RefKind == RefKind.None && d.TakesOwnership(p))) vars.Add(p);
            foreach (var l in CollectLocals(cfg).Where(l => l.Type?.IsReferenceType == true && !usingLocals.Contains(l) && l.RefKind == RefKind.None)) vars.Add(l);
            if (vars.Count == 0) return;
            var ctx = new Ctx { Model = model, D = d, Vars = vars.ToArray(), Index = new Dictionary<ISymbol, int>(SymbolEqualityComparer.Default) };
            for (int i = 0; i < ctx.Vars.Length; i++) ctx.Index[ctx.Vars[i]] = i;

            var entry = ctx.Vars.Select(v => v is IParameterSymbol ? St.Live : St.None).ToArray();
            var inStates = Fixpoint(cfg, ctx, entry);
            ctx.Diags = new List<Diagnostic>();
            ctx.Captures.Clear();
            foreach (var block in cfg.Blocks)
                if (inStates[block.Ordinal] != null && block.Kind == BasicBlockKind.Block)
                    Transfer(block, (St[])inStates[block.Ordinal].Clone(), ctx);
            var exit = inStates[cfg.Blocks.Last().Ordinal];
            if (exit != null)
                for (int i = 0; i < ctx.Vars.Length; i++)
                    if ((exit[i] & St.Live) != 0)
                        ctx.Report(Descriptors.NotDisposed, ctx.Vars[i].Locations.FirstOrDefault(), ctx.Vars[i].Name, TypeName(ctx.Vars[i]),
                            (exit[i] & St.Disposed) != 0 ? " (it is disposed on some paths only)" : "");
            foreach (var diag in ctx.Diags.GroupBy(x => (x.Id, x.Location.SourceSpan)).Select(g => g.First())) context.ReportDiagnostic(diag);
        }

        private static string TypeName(ISymbol v) => (v is ILocalSymbol l ? l.Type : ((IParameterSymbol)v).Type).Name;

        private static IEnumerable<ILocalSymbol> CollectLocals(ControlFlowGraph cfg)
        {
            var seen = new HashSet<ILocalSymbol>(SymbolEqualityComparer.Default);
            void Walk(ControlFlowRegion r) { foreach (var l in r.Locals) seen.Add(l); foreach (var n in r.NestedRegions) Walk(n); }
            Walk(cfg.Root);
            return seen;
        }

        /// <summary>The variables each finally region disposes: leaving a try through it, they are disposed.</summary>
        private static Dictionary<ControlFlowRegion, HashSet<int>> FinallyDisposals(ControlFlowGraph cfg, Ctx ctx)
        {
            var result = new Dictionary<ControlFlowRegion, HashSet<int>>();
            void Walk(ControlFlowRegion r)
            {
                if (r.Kind == ControlFlowRegionKind.Finally)
                {
                    var set = new HashSet<int>();
                    for (int b = r.FirstBlockOrdinal; b <= r.LastBlockOrdinal; b++)
                        foreach (var op in cfg.Blocks[b].Operations.SelectMany(o => o.DescendantsAndSelf()).OfType<IInvocationOperation>())
                            if (IsDispose(op.TargetMethod) && op.Instance != null && Var(op.Instance, ctx) is int i) set.Add(i);
                    result[r] = set;
                }
                foreach (var n in r.NestedRegions) Walk(n);
            }
            Walk(cfg.Root);
            return result;
        }

        private static St[][] Fixpoint(ControlFlowGraph cfg, Ctx ctx, St[] entry)
        {
            var finallies = FinallyDisposals(cfg, ctx);
            var inStates = new St[cfg.Blocks.Length][];
            inStates[0] = entry;
            var work = new Queue<int>();
            work.Enqueue(0);
            // a catch (or filter) is entered from anywhere in its try: whatever the try's blocks start with
            var handlers = new List<(ControlFlowRegion tryRegion, int entry)>();
            void FindHandlers(ControlFlowRegion r)
            {
                if (r.Kind == ControlFlowRegionKind.TryAndCatch)
                    foreach (var h in r.NestedRegions.Skip(1))
                        handlers.Add((r.NestedRegions[0], h.Kind == ControlFlowRegionKind.FilterAndHandler ? h.NestedRegions[0].FirstBlockOrdinal : h.FirstBlockOrdinal));
                foreach (var n in r.NestedRegions) FindHandlers(n);
            }
            FindHandlers(cfg.Root);
            void Join(int d, St[] state)
            {
                if (inStates[d] == null) { inStates[d] = (St[])state.Clone(); work.Enqueue(d); return; }
                bool changed = false;
                for (int i = 0; i < state.Length; i++)
                {
                    var merged = inStates[d][i] | state[i];
                    if (merged != inStates[d][i]) { inStates[d][i] = merged; changed = true; }
                }
                if (changed) work.Enqueue(d);
            }
            while (work.Count > 0)
            {
                var block = cfg.Blocks[work.Dequeue()];
                var outState = Transfer(block, (St[])inStates[block.Ordinal].Clone(), ctx);
                foreach (var (tryRegion, h) in handlers)
                    if (tryRegion.FirstBlockOrdinal <= block.Ordinal && block.Ordinal <= tryRegion.LastBlockOrdinal) Join(h, inStates[block.Ordinal]);
                // a null test: on the branch where the variable is null, it holds nothing to dispose
                var nullTest = block.BranchValue != null ? NullTest(block.BranchValue, ctx) : null;
                foreach (var succ in new[] { block.FallThroughSuccessor, block.ConditionalSuccessor })
                {
                    if (succ?.Destination == null) continue;
                    if (succ.Semantics == ControlFlowBranchSemantics.Throw || succ.Semantics == ControlFlowBranchSemantics.Rethrow) continue;
                    var state = outState;
                    if (nullTest is (int v, bool nullWhenTrue))
                    {
                        // the conditional successor is taken when the condition is block.ConditionKind
                        bool conditionTrue = succ == block.ConditionalSuccessor ? block.ConditionKind == ControlFlowConditionKind.WhenTrue
                                                                                : block.ConditionKind == ControlFlowConditionKind.WhenFalse;
                        if (conditionTrue == nullWhenTrue) { state = (St[])outState.Clone(); state[v] = St.None; }
                    }
                    if (succ.FinallyRegions.Length > 0)
                    {
                        state = (St[])outState.Clone();
                        foreach (var fr in succ.FinallyRegions)
                            if (finallies.TryGetValue(fr, out var disposed))
                                foreach (var i in disposed) state[i] = St.Disposed;
                    }
                    Join(succ.Destination.Ordinal, state);
                }
            }
            return inStates;
        }

        /// <summary>A test of a tracked variable against null: the variable, and whether it is null when the test is true.</summary>
        private static (int, bool)? NullTest(IOperation cond, Ctx ctx)
        {
            bool negated = false;
            while (cond is IUnaryOperation u && u.OperatorKind == UnaryOperatorKind.Not) { negated = !negated; cond = u.Operand; }
            switch (cond)
            {
                case IIsNullOperation isn when Var(isn.Operand, ctx) is int a: return (a, !negated);
                case IBinaryOperation b when (b.OperatorKind == BinaryOperatorKind.Equals || b.OperatorKind == BinaryOperatorKind.NotEquals):
                {
                    bool eq = b.OperatorKind == BinaryOperatorKind.Equals;
                    if (IsNull(b.RightOperand) && Var(b.LeftOperand, ctx) is int l) return (l, eq != negated);
                    if (IsNull(b.LeftOperand) && Var(b.RightOperand, ctx) is int r) return (r, eq != negated);
                    return null;
                }
                case IIsPatternOperation ip when Var(ip.Value, ctx) is int p:
                    if (ip.Pattern is IConstantPatternOperation c && IsNull(c.Value)) return (p, !negated);
                    if (ip.Pattern is INegatedPatternOperation n && n.Pattern is IConstantPatternOperation nc && IsNull(nc.Value)) return (p, negated);
                    return null;
                default: return null;
            }
        }

        private static bool IsNull(IOperation op) => op.ConstantValue.HasValue && op.ConstantValue.Value == null;

        private static St[] Transfer(BasicBlock block, St[] state, Ctx ctx)
        {
            foreach (var op in block.Operations) Visit(op, state, ctx);
            if (block.BranchValue != null)
            {
                bool returns = block.FallThroughSuccessor?.Semantics == ControlFlowBranchSemantics.Return;
                if (returns && Var(block.BranchValue, ctx) is int i) state[i] = St.None; // handed to the caller
                else Visit(block.BranchValue, state, ctx);
            }
            return state;
        }

        private static IOperation Unwrap(IOperation op)
        {
            while (op is IConversionOperation c && (c.Conversion.IsIdentity || c.Conversion.IsReference || c.Conversion.IsImplicit)) op = c.Operand;
            return op;
        }

        /// <summary>The tracked variable an operation reads (through conversions and flow captures), if any.</summary>
        private static int? Var(IOperation op, Ctx ctx)
        {
            op = Unwrap(op);
            ISymbol s = op is ILocalReferenceOperation l ? l.Local : op is IParameterReferenceOperation p ? (ISymbol)p.Parameter : null;
            if (s != null && ctx.Index.TryGetValue(s, out var i)) return i;
            if (op is IFlowCaptureReferenceOperation r && ctx.Captures.TryGetValue(r.Id, out var c)) return c;
            return null;
        }

        private static bool IsDispose(IMethodSymbol m) =>
            (m.Name == "Dispose" || m.Name == "DisposeAsync") && m.Parameters.Length == 0 && !m.IsStatic;

        /// <summary>Does this value give its holder a disposable to own: a new one, or one a call or an await returns?</summary>
        private static bool Owned(IOperation value, Ctx ctx)
        {
            value = Unwrap(value);
            switch (value)
            {
                case IObjectCreationOperation oc: return ctx.D.MustDispose(oc.Type);
                case IInvocationOperation inv: return ctx.D.MustDispose(inv.Type) && !SpecSymbols.IsSpecClass(inv.TargetMethod.ContainingType);
                case IAwaitOperation aw: return ctx.D.MustDispose(aw.Type);
                default: return false;
            }
        }

        private static bool IsGhost(IOperation op, Ctx ctx) => SpecSymbols.IsInGhostContext(op.Syntax, ctx.Model);

        private static void Visit(IOperation op, St[] state, Ctx ctx)
        {
            if (op == null || op is IAnonymousFunctionOperation || op is ILocalFunctionOperation) return;
            // Spec.HandOver(x): handed to whoever disposes it
            if (op is IInvocationOperation ho && SpecSymbols.IsSpecClass(ho.TargetMethod.ContainingType) && ho.TargetMethod.Name == "HandOver" && ho.Arguments.Length == 1)
            {
                if (Var(ho.Arguments[0].Value, ctx) is int h) state[h] = St.None;
                return;
            }
            if (IsGhost(op, ctx)) return;
            switch (op)
            {
                case IFlowCaptureOperation fc:
                {
                    if (Var(fc.Value, ctx) is int c)
                    {
                        ctx.Captures[fc.Id] = c;
                        // using (x): the using disposes it
                        if (fc.Syntax.Parent is UsingStatementSyntax us && us.Expression == fc.Syntax) { Use(c, fc.Value, state, ctx); state[c] = St.None; }
                        return;
                    }
                    Visit(fc.Value, state, ctx);
                    return;
                }
                case ISimpleAssignmentOperation asg:
                {
                    var target = Unwrap(asg.Target);
                    bool toVar = target is ILocalReferenceOperation || target is IParameterReferenceOperation;
                    if (Var(asg.Value, ctx) is int src && !IsGhost(asg.Value, ctx))
                    {
                        Use(src, asg.Value, state, ctx);
                        var moved = state[src];
                        state[src] = St.None; // moved to the target (a variable, or the object whose field it is)
                        if (toVar && Var(target, ctx) is int t1) { Overwrite(t1, asg.Target, state, ctx); state[t1] = moved; }
                        else Visit(asg.Target, state, ctx);
                        return;
                    }
                    Visit(asg.Value, state, ctx);
                    if (toVar && Var(target, ctx) is int t2)
                    {
                        Overwrite(t2, asg.Target, state, ctx);
                        state[t2] = Owned(asg.Value, ctx) ? St.Live : St.None;
                    }
                    else Visit(asg.Target, state, ctx);
                    return;
                }
                case IInvocationOperation inv:
                {
                    if (inv.Instance != null && IsDispose(inv.TargetMethod) && Var(inv.Instance, ctx) is int i)
                    {
                        if ((state[i] & St.Disposed) != 0) ctx.Report(Descriptors.UsedAfterDispose, inv.Syntax.GetLocation(), ctx.Vars[i].Name, ": it is disposed twice");
                        foreach (var a in inv.Arguments) Visit(a, state, ctx);
                        state[i] = St.Disposed;
                        return;
                    }
                    if (inv.Instance != null) Visit(inv.Instance, state, ctx);
                    Arguments(inv.Arguments, state, ctx);
                    return;
                }
                case IObjectCreationOperation oc:
                    Arguments(oc.Arguments, state, ctx);
                    if (oc.Initializer != null) Visit(oc.Initializer, state, ctx);
                    return;
                case IReturnOperation ret when ret.ReturnedValue != null && Var(ret.ReturnedValue, ctx) is int r:
                    state[r] = St.None;
                    return;
            }
            if (Var(op, ctx) is int u) { Use(u, op, state, ctx); return; }
            foreach (var child in op.ChildOperations) Visit(child, state, ctx);
        }

        /// <summary>Arguments: a [TakesOwnership] parameter takes the variable; others borrow it.</summary>
        private static void Arguments(ImmutableArray<IArgumentOperation> args, St[] state, Ctx ctx)
        {
            foreach (var a in args)
            {
                if (Var(a.Value, ctx) is int i)
                {
                    Use(i, a.Value, state, ctx);
                    if (ctx.D.TakesOwnership(a.Parameter)) state[i] = St.None;
                }
                else Visit(a.Value, state, ctx);
            }
        }

        private static void Use(int i, IOperation at, St[] state, Ctx ctx)
        {
            if ((state[i] & St.Disposed) != 0) ctx.Report(Descriptors.UsedAfterDispose, at.Syntax.GetLocation(), ctx.Vars[i].Name, "");
        }

        private static void Overwrite(int i, IOperation at, St[] state, Ctx ctx)
        {
            if ((state[i] & St.Live) != 0)
                ctx.Report(Descriptors.NotDisposed, at.Syntax.GetLocation(), ctx.Vars[i].Name, TypeName(ctx.Vars[i]), ": it is overwritten while it still holds one");
        }
    }
}
