using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.Diagnostics;
using Microsoft.CodeAnalysis.FlowAnalysis;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Analyzers
{
    /// <summary>
    /// Linear types (ATS views): every [Linear] local or by-value parameter is consumed exactly once on every path
    /// through the method's control flow graph. Passing by value, returning or assigning to another variable consumes;
    /// <c>ref</c>/<c>in</c> arguments and member reads borrow; uses inside specifications are ghost and free.
    /// </summary>
    [DiagnosticAnalyzer(LanguageNames.CSharp)]
    public sealed class LinearityAnalyzer : DiagnosticAnalyzer
    {
        public override ImmutableArray<DiagnosticDescriptor> SupportedDiagnostics => ImmutableArray.Create(
            Descriptors.NotConsumed, Descriptors.UsedAfterConsume, Descriptors.Captured,
            Descriptors.Copied, Descriptors.BorrowConsumed, Descriptors.Forged);

        public override void Initialize(AnalysisContext context)
        {
            context.ConfigureGeneratedCodeAnalysis(GeneratedCodeAnalysisFlags.None);
            context.EnableConcurrentExecution();
            context.RegisterOperationAction(AnalyzeBody, OperationKind.MethodBody, OperationKind.ConstructorBody);
            context.RegisterOperationAction(CheckCapture, OperationKind.LocalReference, OperationKind.ParameterReference);
            context.RegisterOperationAction(CheckForge, OperationKind.DefaultValue, OperationKind.ObjectCreation);
            context.RegisterSymbolAction(CheckStorage, SymbolKind.Field, SymbolKind.Property);
        }

        // ---- declaration-level rules -------------------------------------------------------------------------

        private static void CheckStorage(SymbolAnalysisContext context)
        {
            var type = context.Symbol is IFieldSymbol f ? f.Type : ((IPropertySymbol)context.Symbol).Type;
            if (context.Symbol.IsImplicitlyDeclared || !SpecSymbols.IsLinear(type)) return;
            if (context.Symbol is IPropertySymbol p && !IsAutoProperty(p)) return;
            if (!SpecSymbols.IsLinear(context.Symbol.ContainingType))
                context.ReportDiagnostic(Diagnostic.Create(Descriptors.Copied, context.Symbol.Locations.FirstOrDefault(),
                    "stored in a field of non-linear type '" + context.Symbol.ContainingType.Name + "'"));
        }

        private static bool IsAutoProperty(IPropertySymbol p) =>
            p.ContainingType.GetMembers().OfType<IFieldSymbol>().Any(f => SymbolEqualityComparer.Default.Equals(f.AssociatedSymbol, p));

        private static void CheckForge(OperationAnalysisContext context)
        {
            var type = context.Operation.Type;
            if (type == null || !SpecSymbols.IsLinear(type) || SpecSymbols.IsTrusted(context.ContainingSymbol)) return;
            if (SpecSymbols.IsInGhostContext(context.Operation.Syntax, context.Operation.SemanticModel)) return;
            context.ReportDiagnostic(Diagnostic.Create(Descriptors.Forged, context.Operation.Syntax.GetLocation(), type.Name));
        }

        private static void CheckCapture(OperationAnalysisContext context)
        {
            var op = context.Operation;
            var symbol = op is ILocalReferenceOperation l ? (ISymbol)l.Local : ((IParameterReferenceOperation)op).Parameter;
            if (!SpecSymbols.IsLinear(op.Type) || SpecSymbols.IsTrusted(context.ContainingSymbol)) return;
            for (var cur = op.Parent; cur != null; cur = cur.Parent)
            {
                ISymbol fn = cur is IAnonymousFunctionOperation af ? af.Symbol
                    : cur is ILocalFunctionOperation lf ? lf.Symbol : null;
                if (fn == null) continue;
                if (SymbolEqualityComparer.Default.Equals(symbol.ContainingSymbol, fn)) return;
                if (SpecSymbols.IsInGhostContext(op.Syntax, op.SemanticModel)) return;
                context.ReportDiagnostic(Diagnostic.Create(Descriptors.Captured, op.Syntax.GetLocation(), symbol.Name));
                return;
            }
        }

        // ---- flow-sensitive consumption ----------------------------------------------------------------------

        [Flags]
        private enum St : byte { None = 0, Unassigned = 1, Live = 2, Consumed = 4 }

        private sealed class Ctx
        {
            public SemanticModel Model;
            public Dictionary<ISymbol, int> Index;
            public ISymbol[] Vars;
            public bool[] Borrowed;
            public List<Diagnostic> Diags; // null while iterating to a fixpoint
            public void Report(DiagnosticDescriptor d, Location loc, params object[] args) =>
                Diags?.Add(Diagnostic.Create(d, loc, args));
        }

        private static void AnalyzeBody(OperationAnalysisContext context)
        {
            if (SpecSymbols.IsTrusted(context.ContainingSymbol)) return;
            ControlFlowGraph cfg;
            switch (context.Operation)
            {
                case IMethodBodyOperation mb: cfg = ControlFlowGraph.Create(mb); break;
                case IConstructorBodyOperation cb: cfg = ControlFlowGraph.Create(cb); break;
                default: return;
            }
            var method = context.ContainingSymbol as IMethodSymbol;
            if (method == null) return;

            var vars = new List<ISymbol>();
            var borrowed = new List<bool>();
            foreach (var p in method.Parameters.Where(p => SpecSymbols.IsLinear(p.Type)))
            {
                vars.Add(p);
                // `in` is a read-only borrow. A `ref` view may be consumed (split, passed on) as long as it holds a
                // value again on return, like ATS's !pf; the exit check below enforces that.
                borrowed.Add(p.RefKind == RefKind.In);
            }
            foreach (var local in CollectLocals(cfg).Where(l => SpecSymbols.IsLinear(l.Type)))
            {
                vars.Add(local);
                borrowed.Add(false);
            }
            if (vars.Count == 0) return;

            var ctx = new Ctx
            {
                Model = context.Operation.SemanticModel,
                Vars = vars.ToArray(),
                Borrowed = borrowed.ToArray(),
                Index = new Dictionary<ISymbol, int>(SymbolEqualityComparer.Default),
            };
            for (int i = 0; i < ctx.Vars.Length; i++) ctx.Index[ctx.Vars[i]] = i;

            var entry = new St[ctx.Vars.Length];
            for (int i = 0; i < entry.Length; i++)
                entry[i] = ctx.Vars[i] is IParameterSymbol p && p.RefKind != RefKind.Out ? St.Live : St.Unassigned;

            var inStates = Fixpoint(cfg, ctx, entry);

            ctx.Diags = new List<Diagnostic>();
            foreach (var block in cfg.Blocks)
                if (inStates[block.Ordinal] != null && block.Kind == BasicBlockKind.Block)
                    Transfer(block, (St[])inStates[block.Ordinal].Clone(), ctx);

            var exit = inStates[cfg.Blocks.Last().Ordinal];
            if (exit != null)
            {
                for (int i = 0; i < ctx.Vars.Length; i++)
                {
                    var v = ctx.Vars[i];
                    bool mustBeLive = ctx.Borrowed[i] || (v is IParameterSymbol p && (p.RefKind == RefKind.Out || p.RefKind == RefKind.Ref));
                    if (!mustBeLive && (exit[i] & St.Live) != 0)
                        ctx.Report(Descriptors.NotConsumed, v.Locations.FirstOrDefault(), v.Name,
                            (exit[i] & St.Consumed) != 0 ? " (it is consumed on some paths only)" : "");
                    if (mustBeLive && (exit[i] & St.Consumed) != 0)
                        ctx.Report(Descriptors.NotConsumed, v.Locations.FirstOrDefault(), v.Name,
                            ": a ref/out linear parameter must hold a value when the method returns");
                }
            }

            foreach (var d in ctx.Diags.GroupBy(d => (d.Id, d.Location.SourceSpan)).Select(g => g.First()))
                context.ReportDiagnostic(d);
        }

        private static IEnumerable<ILocalSymbol> CollectLocals(ControlFlowGraph cfg)
        {
            var seen = new HashSet<ILocalSymbol>(SymbolEqualityComparer.Default);
            void Walk(ControlFlowRegion r)
            {
                foreach (var l in r.Locals) seen.Add(l);
                foreach (var n in r.NestedRegions) Walk(n);
            }
            Walk(cfg.Root);
            return seen;
        }

        private static St[][] Fixpoint(ControlFlowGraph cfg, Ctx ctx, St[] entry)
        {
            var inStates = new St[cfg.Blocks.Length][];
            inStates[0] = entry;
            var work = new Queue<int>();
            work.Enqueue(0);
            while (work.Count > 0)
            {
                var block = cfg.Blocks[work.Dequeue()];
                var outState = Transfer(block, (St[])inStates[block.Ordinal].Clone(), ctx);
                foreach (var succ in new[] { block.FallThroughSuccessor, block.ConditionalSuccessor })
                {
                    if (succ?.Destination == null) continue;
                    // Leaving a region by an exception is not an exit we account for (as in ATS, exceptions leak views).
                    if (succ.Semantics == ControlFlowBranchSemantics.Throw || succ.Semantics == ControlFlowBranchSemantics.Rethrow) continue;
                    int d = succ.Destination.Ordinal;
                    if (inStates[d] == null) { inStates[d] = (St[])outState.Clone(); work.Enqueue(d); continue; }
                    bool changed = false;
                    for (int i = 0; i < outState.Length; i++)
                    {
                        var merged = inStates[d][i] | outState[i];
                        if (merged != inStates[d][i]) { inStates[d][i] = merged; changed = true; }
                    }
                    if (changed) work.Enqueue(d);
                }
            }
            return inStates;
        }

        private static St[] Transfer(BasicBlock block, St[] state, Ctx ctx)
        {
            foreach (var op in block.Operations) Visit(op, state, ctx);
            if (block.BranchValue != null)
            {
                bool returns = block.FallThroughSuccessor?.Semantics == ControlFlowBranchSemantics.Return;
                if (returns && TryVar(Unwrap(block.BranchValue), ctx, out int i) && !IsGhost(block.BranchValue, ctx))
                {
                    Consume(i, block.BranchValue, state, ctx);
                }
                else Visit(block.BranchValue, state, ctx);
            }
            return state;
        }

        private static IOperation Unwrap(IOperation op)
        {
            while (op is IConversionOperation c && c.Conversion.IsIdentity) op = c.Operand;
            return op;
        }

        private static bool TryVar(IOperation op, Ctx ctx, out int index)
        {
            index = -1;
            ISymbol s = op is ILocalReferenceOperation l ? l.Local : op is IParameterReferenceOperation p ? (ISymbol)p.Parameter : null;
            return s != null && ctx.Index.TryGetValue(s, out index);
        }

        private static bool IsGhost(IOperation op, Ctx ctx) => SpecSymbols.IsInGhostContext(op.Syntax, ctx.Model);

        private static void Visit(IOperation op, St[] state, Ctx ctx)
        {
            if (op == null) return;
            if (op is IAnonymousFunctionOperation || op is ILocalFunctionOperation) return; // captures are checked separately

            if (op is ISimpleAssignmentOperation asg)
            {
                Visit(asg.Value, state, ctx);
                if (TryVar(asg.Target, ctx, out int t)) Define(t, asg.Target, state, ctx);
                else Visit(asg.Target, state, ctx);
                return;
            }

            foreach (var child in op.ChildOperations) Visit(child, state, ctx);

            if (!TryVar(op, ctx, out int i) || IsGhost(op, ctx)) return;
            IOperation self = op, parent = op.Parent;
            while ((parent is IConversionOperation c && c.Conversion.IsIdentity) || parent is IDeclarationExpressionOperation) { self = parent; parent = parent.Parent; }

            switch (parent)
            {
                case IArgumentOperation arg:
                    var refKind = arg.Parameter?.RefKind ?? RefKind.None;
                    if (refKind == RefKind.Out) Define(i, op, state, ctx);
                    else if (refKind == RefKind.None) Consume(i, op, state, ctx);
                    else Borrow(i, op, state, ctx);
                    break;
                case ISimpleAssignmentOperation a when a.Value == self:
                    if (!(Unwrap(a.Target) is ILocalReferenceOperation) && !(Unwrap(a.Target) is IParameterReferenceOperation) &&
                        !SpecSymbols.IsLinear(ContainingTypeOf(a.Target)))
                        ctx.Report(Descriptors.Copied, a.Syntax.GetLocation(), "stored outside a linear variable");
                    Consume(i, op, state, ctx);
                    break;
                case IReturnOperation _:
                case IFlowCaptureOperation _:
                    Consume(i, op, state, ctx);
                    break;
                case IConversionOperation conv:
                    ctx.Report(Descriptors.Copied, conv.Syntax.GetLocation(), "converted to '" + conv.Type?.Name + "' (boxing copies it)");
                    Consume(i, op, state, ctx);
                    break;
                default:
                    Borrow(i, op, state, ctx);
                    break;
            }
        }

        private static ITypeSymbol ContainingTypeOf(IOperation target) =>
            target is IMemberReferenceOperation m ? m.Member.ContainingType : null;

        private static void Consume(int i, IOperation at, St[] state, Ctx ctx)
        {
            var name = ctx.Vars[i].Name;
            if (ctx.Borrowed[i]) { ctx.Report(Descriptors.BorrowConsumed, at.Syntax.GetLocation(), name); return; }
            if ((state[i] & St.Consumed) != 0) ctx.Report(Descriptors.UsedAfterConsume, at.Syntax.GetLocation(), name);
            state[i] = St.Consumed;
        }

        private static void Borrow(int i, IOperation at, St[] state, Ctx ctx)
        {
            if ((state[i] & St.Consumed) != 0) ctx.Report(Descriptors.UsedAfterConsume, at.Syntax.GetLocation(), ctx.Vars[i].Name);
        }

        private static void Define(int i, IOperation at, St[] state, Ctx ctx)
        {
            if ((state[i] & St.Live) != 0)
                ctx.Report(Descriptors.NotConsumed, at.Syntax.GetLocation(), ctx.Vars[i].Name, ": it is overwritten while it still holds a value");
            state[i] = St.Live;
        }
    }
}
