using System.Collections.Generic;
using System.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.Operations;
using CsVerify.Analyzers;
using static CsVerify.Verifier.Boogie.KernelTypes;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>
    /// Memory views in hand cover different cells, as CsVerify's engine has them: the views a method is given are of
    /// cells apart (where they hold any), and Mem's allocations give cells no view in hand covers. Their cells live
    /// here (a set the method keeps, m$live): its parameters', what it allocates and what calls give it back, less what
    /// it frees (which may be given out again).
    /// </summary>
    internal sealed partial class Lowering
    {
        private string _memLive;

        private static KExpr InCells(List<KCells> cells, KExpr a) =>
            cells.Select(c => (KExpr)new KOp("&&", new KOp("<=", c.Lo, a), new KOp("<", a, c.Hi))).Aggregate((x, y) => new KOp("||", x, y));

        /// <summary>At the start: whether the method has views, and its parameters' cells apart and live.</summary>
        private void MemLiveEntry()
        {
            var views = _m.Parameters.Where(x => IsMemView(x.Type) && x.RefKind != RefKind.Out).ToList();
            bool uses = views.Count > 0 || _model.GetOperation(_decl) is IOperation root &&
                        root.DescendantsAndSelf().OfType<IInvocationOperation>().Any(i => SpecSymbols.IsCsVerifyType(i.TargetMethod.ContainingType, "Mem"));
            if (!uses) return;
            _memLive = "m$live";
            _p.Locals.Add(new KLocal { Name = _memLive, Raw = "[int]bool" });
            Emit(new KHavoc { Var = _memLive });
            var a = new KVar("m$a");
            foreach (var x in views)
                ShapeFact(new KQuant { Forall = true, Var = "m$a", Type = "int", Body = new KOp("==>", InCells(MemCells(new KVar(Local(x)), x.Type, _decl), a), new KOp("sel", new KVar(_memLive), a)) }, _decl);
            // (two ranges apart, each pair of theirs: an empty one is apart from any)
            for (int i = 0; i < views.Count; i++)
                for (int j = i + 1; j < views.Count; j++)
                    foreach (var x in MemCells(new KVar(Local(views[i])), views[i].Type, _decl))
                        foreach (var y in MemCells(new KVar(Local(views[j])), views[j].Type, _decl))
                            ShapeFact(new KOp("||", new KOp("||", new KOp("<=", x.Hi, x.Lo), new KOp("<=", y.Hi, y.Lo)),
                                                    new KOp("||", new KOp("<=", x.Hi, y.Lo), new KOp("<=", y.Hi, x.Lo))), _decl);
        }

        /// <summary>An allocation's view: of cells none in hand covers; live from here on.</summary>
        private void MemFresh(KExpr view, ITypeSymbol type, SyntaxNode at)
        {
            if (_memLive == null) return;
            var a = new KVar("m$a");
            var cells = MemCells(view, type, at);
            ShapeFact(new KQuant { Forall = true, Var = "m$a", Type = "int", Body = new KOp("==>", InCells(cells, a), new KOp("!", new KOp("sel", new KVar(_memLive), a))) }, at);
            // (said of each range's first cell too, for the solver to find)
            foreach (var c in cells) ShapeFact(new KOp("==>", new KOp("<", c.Lo, c.Hi), new KOp("!", new KOp("sel", new KVar(_memLive), c.Lo))), at);
            MemLive(view, type, at, true);
        }

        /// <summary>A view's cells live (a call gave it, an allocation made it), or not (freed).</summary>
        private void MemLive(KExpr view, ITypeSymbol type, SyntaxNode at, bool live)
        {
            if (_memLive == null) return;
            var a = new KVar("m$a");
            var cells = InCells(MemCells(view, type, at), a);
            var was = new KOp("sel", new KVar(_memLive), a);
            Emit(new KAssign { Var = _memLive, Value = new KOp("lambda", new KLit("m$a: int"), live ? new KOp("||", was, cells) : new KOp("&&", was, new KOp("!", cells))) });
        }
    }
}
