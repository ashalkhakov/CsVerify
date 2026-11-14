using System.Collections.Generic;
using System.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.Operations;
using CsVerify.Analyzers;
using static CsVerify.Verifier.Boogie.KernelTypes;
using static CsVerify.Verifier.Boogie.KOp;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>
    /// Memory views in hand cover different cells: the views a method is given are of
    /// cells apart (where they hold any), and Mem's allocations give cells no view in hand covers. Their cells live
    /// here (a set the method keeps, m$live): its parameters', what it allocates and what calls give it back, less what
    /// it frees (which may be given out again).
    /// </summary>
    internal sealed partial class Lowering
    {
        private string _memLive;

        private static KExpr InCells(List<KCells> cells, KExpr a) =>
            OrAny(cells.Select(c => (KExpr)AndAlso(Le(c.Lo, a), Lt(a, c.Hi))));

        /// <summary>At the start: whether the method has views, and its parameters' cells apart and live.</summary>
        private void MemLiveEntry()
        {
            var views = _m.Parameters.Where(x => IsMemView(x.Type) && x.RefKind != RefKind.Out).ToList();
            bool uses = views.Count > 0 || _model.GetOperation(_decl) is IOperation root &&
                        root.DescendantsAndSelf().OfType<IInvocationOperation>().Any(i => SpecSymbols.IsCsVerifyType(i.TargetMethod.ContainingType, "Mem"));
            if (!uses)
            {
                return;
            }
            _memLive = "m$live";
            _p.Locals.Add(KLocal.Of(_memLive, "[int]bool"));
            Emit(KHavoc.Of(_memLive));
            var a = new KVar("m$a");
            foreach (var x in views)
            {
                ShapeFact(KQuant.ForAll(
                    "m$a",
                    Implies(InCells(MemCells(new KVar(Local(x)), x.Type, _decl), a), Sel(_memLive, a))), _decl);
            }
            // (two ranges apart, each pair of theirs: an empty one is apart from any)
            for (int i = 0; i < views.Count; i++)
            {
                for (int j = i + 1; j < views.Count; j++)
                {
                    foreach (var x in MemCells(new KVar(Local(views[i])), views[i].Type, _decl))
                    {
                        foreach (var y in MemCells(new KVar(Local(views[j])), views[j].Type, _decl))
                        {
                            ShapeFact(OrElse(OrElse(Le(x.Hi, x.Lo), Le(y.Hi, y.Lo)),
                                                    OrElse(Le(x.Hi, y.Lo), Le(y.Hi, x.Lo))), _decl);
                        }
                    }
                }
            }
        }

        /// <summary>An allocation's view: of cells none in hand covers; live from here on.</summary>
        private void MemFresh(KExpr view, ITypeSymbol type, SyntaxNode at)
        {
            if (_memLive == null)
            {
                return;
            }
            var a = new KVar("m$a");
            var cells = MemCells(view, type, at);
            ShapeFact(KQuant.ForAll("m$a", Implies(InCells(cells, a), Not(Sel(_memLive, a)))), at);
            // (said of each range's first cell too, for the solver to find)
            foreach (var c in cells)
            {
                ShapeFact(Implies(Lt(c.Lo, c.Hi), Not(Sel(_memLive, c.Lo))), at);
            }
            MemLive(view, type, at, true);
        }

        /// <summary>A view's cells live (a call gave it, an allocation made it), or not (freed).</summary>
        private void MemLive(KExpr view, ITypeSymbol type, SyntaxNode at, bool live)
        {
            if (_memLive == null)
            {
                return;
            }
            var a = new KVar("m$a");
            var cells = InCells(MemCells(view, type, at), a);
            var was = Sel(_memLive, a);
            Emit(KAssign.Of(_memLive, MapLambda("m$a: int", live ? OrElse(was, cells) : AndAlso(was, Not(cells)))));
        }

        /// <summary>
        /// ATS's manual memory (Mem and Ptr.Offset): the cells are the element maps' rows at
        /// null; a view holds its cells while in hand, and says what they hold; reads and the proof functions (Split,
        /// Join, TakeOut, PutBack) change no memory.
        /// </summary>
        private bool MemCall(IInvocationOperation call, out KExpr value)
        {
            value = null;
            var m = call.TargetMethod;
            bool offset = m.Name == "Offset" && SpecSymbols.IsCsVerifyType(m.ContainingType, "Ptr`1");
            if (!offset && !(SpecSymbols.IsCsVerifyType(m.ContainingType, "Mem") && m.IsGenericMethod))
            {
                return false;
            }
            var elem = offset ? ((INamedTypeSymbol)m.ContainingType).TypeArguments[0] : m.TypeArguments[0];
            if (!Scalar(elem))
            {
                throw new NotTranslated("memory of " + elem);
            }
            var args = call.Arguments.OrderBy(a => a.Parameter.Ordinal).ToList();
            var named = args.ToDictionary(a => a.Parameter.Name, a => a);
            var at = call.Syntax;
            // (each argument evaluated once, here, before any view it names changes)
            var given = new Dictionary<string, KExpr>();
            KExpr In(string name)
            {
                if (given.TryGetValue(name, out var known))
                {
                    return known;
                }
                var t = Declare("t$" + _temps++, named[name].Parameter.Type);
                Emit(KAssign.Of(t, Expr(named[name].Value)));
                return given[name] = new KVar(t);
            }
            string Out(string name) => RefVariable(named[name]);
            ITypeSymbol TypeOfParam(string name) => named[name].Parameter.Type;
            KExpr P(string prop, KExpr v, string param) => MemProp(prop, v, TypeOfParam(param));
            void Need(KExpr cond, string text) => Emit(KCheck.Of(cond, "CSV1001", at, $"precondition '{text}' of '{m.Name}' might not hold"));
            void Assume(KExpr c) => Emit(KAssume.Of(c));
            string New(ITypeSymbol t)
            {
                var v = Declare("t$" + _temps++, t);
                Emit(KHavoc.Of(v));
                return v;
            }
            void Grant(KExpr v, ITypeSymbol t, bool tie = true)
            {
                Emit(KMemCells.Of(MemCells(v, t, at), true));
                if (tie)
                {
                    Assume(MemTie(v, t));
                }
            }
            void Revoke(KExpr v, ITypeSymbol t) => Emit(KMemCells.Of(MemCells(v, t, at), false));
            var arrayOf = (IArrayTypeSymbol)KernelTypes.Compilation.CreateArrayTypeSymbol(elem);
            void StoreCell(KExpr addr, KExpr x) => Emit(new KStore
            {
                Memory = true,
                Index = addr,
                Value = x,
                ArrayType = arrayOf,
                At = at,
                ArrayAt = at,
            });
            switch (m.Name)
            {
                case "Offset":
                {
                    var p = Expr(call.Instance);
                    var k = In("offset");
                    var q = New(m.ReturnType);
                    Assume(Eq(MemProp("Addr", new KVar(q), m.ReturnType), Plus(MemProp("Addr", p, m.ReturnType), k)));
                    value = new KVar(q);
                    return true;
                }
                case "Alloc":
                {
                    var init = In("init");
                    var p = New(m.ReturnType);
                    var view = Out("view");
                    Emit(KHavoc.Of(view));
                    var v = new KVar(view);
                    Assume(AndAll(Eq(P("Addr", v, "view"), MemProp("Addr", new KVar(p), m.ReturnType)), Eq(P("Value", v, "view"), init)));
                    Emit(KMemCells.Of(MemCells(v, TypeOfParam("view"), at), true));
                    MemFresh(v, TypeOfParam("view"), at);
                    StoreCell(P("Addr", v, "view"), init);
                    value = new KVar(p);
                    return true;
                }
                case "Read":
                {
                    var v = In("view"); var p = In("p");
                    Need(Eq(P("Addr", v, "view"), MemProp("Addr", p, TypeOfParam("p"))), "view.Addr == p.Addr");
                    value = P("Value", v, "view");
                    return true;
                }
                case "Write":
                {
                    var v = In("view"); var p = In("p"); var x = In("value");
                    Need(Eq(P("Addr", v, "view"), MemProp("Addr", p, TypeOfParam("p"))), "view.Addr == p.Addr");
                    var old = Declare("t$" + _temps++, TypeOfParam("view"));
                    Emit(KAssign.Of(old, v));
                    var view = Out("view");
                    Emit(KHavoc.Of(view));
                    var nv = new KVar(view);
                    Assume(AndAll(Eq(P("Addr", nv, "view"), P("Addr", new KVar(old), "view")), Eq(P("Value", nv, "view"), x)));
                    StoreCell(P("Addr", nv, "view"), x);
                    return true;
                }
                case "Free":
                {
                    var v = In("view"); var p = In("p");
                    Need(Eq(P("Addr", v, "view"), MemProp("Addr", p, TypeOfParam("p"))), "view.Addr == p.Addr");
                    Revoke(v, TypeOfParam("view"));
                    MemLive(v, TypeOfParam("view"), at, false);
                    return true;
                }
                case "AllocArray":
                {
                    var n = In("length"); var fill = In("fill");
                    Need(Ge(n, KLit.Zero), "length >= 0");
                    var p = New(m.ReturnType);
                    var view = Out("view"); var gc = Out("gc");
                    Emit(KHavoc.Of(view)); Emit(KHavoc.Of(gc));
                    var v = new KVar(view); var g = new KVar(gc);
                    Assume(AndAll(Eq(P("Addr", v, "view"), MemProp("Addr", new KVar(p), m.ReturnType)), Eq(P("Length", v, "view"), n),
                               Eq(P("Elems", v, "view"), new KOp("seq.const", fill))));
                    Assume(AndAll(Eq(P("Addr", g, "gc"), P("Addr", v, "view")), Eq(P("Length", g, "gc"), P("Length", v, "view"))));
                    Emit(KMemCells.Of(MemCells(v, TypeOfParam("view"), at), true));
                    MemFresh(v, TypeOfParam("view"), at);
                    Emit(new KFill
                    {
                        Map = MemMap(TypeOfParam("view")),
                        Lo = P("Addr", v, "view"),
                        Hi = Plus(P("Addr", v, "view"), n),
                        Value = fill,
                    });
                    value = new KVar(p);
                    return true;
                }
                case "LengthIsNatural":
                    Assume(Ge(P("Length", In("view"), "view"), KLit.Zero));
                    return true;
                case "Get":
                {
                    var v = In("view"); var p = In("p"); var i = In("i");
                    Need(AndAll(Eq(P("Addr", v, "view"), MemProp("Addr", p, TypeOfParam("p"))), Le(KLit.Zero, i), Lt(i, P("Length", v, "view"))),
                         "view.Addr == p.Addr && 0 <= i && i < view.Length.Value");
                    value = Sel(P("Elems", v, "view"), i);
                    return true;
                }
                case "Set":
                {
                    var v = In("view"); var p = In("p"); var i = In("i"); var x = In("value");
                    Need(AndAll(Eq(P("Addr", v, "view"), MemProp("Addr", p, TypeOfParam("p"))), Le(KLit.Zero, i), Lt(i, P("Length", v, "view"))),
                         "view.Addr == p.Addr && 0 <= i && i < view.Length.Value");
                    var old = Declare("t$" + _temps++, TypeOfParam("view"));
                    Emit(KAssign.Of(old, v));
                    var view = Out("view");
                    Emit(KHavoc.Of(view));
                    var nv = new KVar(view); var ov = new KVar(old);
                    Assume(AndAll(Eq(P("Addr", nv, "view"), P("Addr", ov, "view")), Eq(P("Length", nv, "view"), P("Length", ov, "view")),
                               Eq(P("Elems", nv, "view"), Store(P("Elems", ov, "view"), i, x))));
                    StoreCell(Plus(P("Addr", nv, "view"), i), x);
                    return true;
                }
                case "FreeArray":
                {
                    var g = In("gc"); var v = In("view"); var p = In("p");
                    Need(AndAll(Eq(P("Addr", g, "gc"), P("Addr", v, "view")), Eq(P("Addr", g, "gc"), MemProp("Addr", p, TypeOfParam("p"))), Eq(P("Length", g, "gc"), P("Length", v, "view"))),
                         "gc.Addr == view.Addr && gc.Addr == p.Addr && gc.Length == view.Length");
                    Revoke(v, TypeOfParam("view"));
                    return true;
                }
                case "Split":
                {
                    var w = In("whole"); var cut = In("at");
                    Need(AndAll(Le(KLit.Zero, cut), Le(cut, P("Length", w, "whole"))), "0 <= at.Value && at.Value <= whole.Length.Value");
                    var left = Out("left"); var right = Out("right");
                    Emit(KHavoc.Of(left)); Emit(KHavoc.Of(right));
                    var l = new KVar(left); var r = new KVar(right);
                    Assume(AndAll(Eq(P("Addr", l, "left"), P("Addr", w, "whole")), Eq(P("Length", l, "left"), cut), Eq(P("Elems", l, "left"), P("Elems", w, "whole")),
                               Ge(P("Length", r, "right"), KLit.Zero)));
                    Assume(AndAll(Eq(P("Addr", r, "right"), Plus(P("Addr", w, "whole"), cut)), Eq(P("Length", r, "right"), Minus(P("Length", w, "whole"), cut)),
                               Eq(P("Elems", r, "right"), new KOp("seq.drop", P("Elems", w, "whole"), cut))));
                    Revoke(w, TypeOfParam("whole"));
                    Grant(l, TypeOfParam("left")); Grant(r, TypeOfParam("right"));
                    return true;
                }
                case "Join":
                {
                    var l = In("left"); var r = In("right");
                    Need(Eq(P("Addr", r, "right"), Plus(P("Addr", l, "left"), P("Length", l, "left"))), "right.Addr.Value == left.Addr.Value + left.Length.Value");
                    var whole = Out("whole");
                    Emit(KHavoc.Of(whole));
                    var w = new KVar(whole);
                    Assume(AndAll(Eq(P("Addr", w, "whole"), P("Addr", l, "left")), Eq(P("Length", w, "whole"), Plus(P("Length", l, "left"), P("Length", r, "right"))),
                               Eq(P("Elems", w, "whole"), new KOp("seq.concat", P("Elems", l, "left"), P("Length", l, "left"), P("Elems", r, "right")))));
                    Revoke(l, TypeOfParam("left")); Revoke(r, TypeOfParam("right"));
                    Grant(w, TypeOfParam("whole"));
                    return true;
                }
                case "TakeOut":
                {
                    var w = In("whole"); var i = In("i");
                    Need(AndAll(Le(KLit.Zero, i), Lt(i, P("Length", w, "whole"))), "0 <= i.Value && i.Value < whole.Length.Value");
                    var cell = Out("cell"); var rest = Out("rest");
                    Emit(KHavoc.Of(cell)); Emit(KHavoc.Of(rest));
                    var c = new KVar(cell); var h = new KVar(rest);
                    Assume(AndAll(Eq(P("Addr", c, "cell"), Plus(P("Addr", w, "whole"), i)), Eq(P("Value", c, "cell"), Sel(P("Elems", w, "whole"), i))));
                    Assume(AndAll(Eq(P("Addr", h, "rest"), P("Addr", w, "whole")), Eq(P("Length", h, "rest"), P("Length", w, "whole")), Eq(P("Index", h, "rest"), i),
                               Eq(P("Elems", h, "rest"), P("Elems", w, "whole"))));
                    Revoke(w, TypeOfParam("whole"));
                    Grant(c, TypeOfParam("cell")); Grant(h, TypeOfParam("rest"));
                    return true;
                }
                case "PutBack":
                {
                    var c = In("cell"); var h = In("rest");
                    Need(Eq(P("Addr", c, "cell"), Plus(P("Addr", h, "rest"), P("Index", h, "rest"))), "cell.Addr.Value == rest.Addr.Value + rest.Index.Value");
                    var whole = Out("whole");
                    Emit(KHavoc.Of(whole));
                    var w = new KVar(whole);
                    Assume(AndAll(Eq(P("Addr", w, "whole"), P("Addr", h, "rest")), Eq(P("Length", w, "whole"), P("Length", h, "rest")),
                               Eq(P("Elems", w, "whole"), Store(P("Elems", h, "rest"), P("Index", h, "rest"), P("Value", c, "cell")))));
                    Revoke(c, TypeOfParam("cell")); Revoke(h, TypeOfParam("rest"));
                    Grant(w, TypeOfParam("whole"));
                    return true;
                }
                default: throw new NotTranslated("Mem." + m.Name);
            }
        }
    }
}
