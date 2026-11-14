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
            _p.AddLocal(KLocal.Of(_memLive, "[int]bool"));
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
            var arrayOf = (IArrayTypeSymbol)KernelTypes.Compilation.CreateArrayTypeSymbol(elem);
            switch (m.Name)
            {
                case "Offset":
                {
                    var p = Expr(call.Instance);
                    var k = ArgumentIn("offset", given, named);
                    var q = FreshLocal(m.ReturnType);
                    Assume(Eq(MemProp("Addr", new KVar(q), m.ReturnType), Plus(MemProp("Addr", p, m.ReturnType), k)));
                    value = new KVar(q);
                    return true;
                }
                case "Alloc":
                {
                    var init = ArgumentIn("init", given, named);
                    var p = FreshLocal(m.ReturnType);
                    var view = RefVariable(named["view"]);
                    Emit(KHavoc.Of(view));
                    var v = new KVar(view);
                    Assume(AndAll(Eq(MemProp("Addr", v, named["view"].Parameter.Type), MemProp("Addr", new KVar(p), m.ReturnType)), Eq(MemProp("Value", v, named["view"].Parameter.Type), init)));
                    Emit(KMemCells.Of(MemCells(v, named["view"].Parameter.Type, at), true));
                    MemFresh(v, named["view"].Parameter.Type, at);
                    StoreCell(MemProp("Addr", v, named["view"].Parameter.Type), init, arrayOf, at);
                    value = new KVar(p);
                    return true;
                }
                case "Read":
                {
                    var v = ArgumentIn("view", given, named);
                    var p = ArgumentIn("p", given, named);
                    CheckPrecondition(Eq(MemProp("Addr", v, named["view"].Parameter.Type), MemProp("Addr", p, named["p"].Parameter.Type)), "view.Addr == p.Addr", at, m.Name);
                    value = MemProp("Value", v, named["view"].Parameter.Type);
                    return true;
                }
                case "Write":
                {
                    var v = ArgumentIn("view", given, named);
                    var p = ArgumentIn("p", given, named);
                    var x = ArgumentIn("value", given, named);
                    CheckPrecondition(Eq(MemProp("Addr", v, named["view"].Parameter.Type), MemProp("Addr", p, named["p"].Parameter.Type)), "view.Addr == p.Addr", at, m.Name);
                    var old = Declare("t$" + _temps++, named["view"].Parameter.Type);
                    Emit(KAssign.Of(old, v));
                    var view = RefVariable(named["view"]);
                    Emit(KHavoc.Of(view));
                    var nv = new KVar(view);
                    Assume(AndAll(Eq(MemProp("Addr", nv, named["view"].Parameter.Type), MemProp("Addr", new KVar(old), named["view"].Parameter.Type)), Eq(MemProp("Value", nv, named["view"].Parameter.Type), x)));
                    StoreCell(MemProp("Addr", nv, named["view"].Parameter.Type), x, arrayOf, at);
                    return true;
                }
                case "Free":
                {
                    var v = ArgumentIn("view", given, named);
                    var p = ArgumentIn("p", given, named);
                    CheckPrecondition(Eq(MemProp("Addr", v, named["view"].Parameter.Type), MemProp("Addr", p, named["p"].Parameter.Type)), "view.Addr == p.Addr", at, m.Name);
                    Revoke(v, named["view"].Parameter.Type, at);
                    MemLive(v, named["view"].Parameter.Type, at, false);
                    return true;
                }
                case "AllocArray":
                {
                    var n = ArgumentIn("length", given, named);
                    var fill = ArgumentIn("fill", given, named);
                    CheckPrecondition(Ge(n, KLit.Zero), "length >= 0", at, m.Name);
                    var p = FreshLocal(m.ReturnType);
                    var view = RefVariable(named["view"]);
                    var gc = RefVariable(named["gc"]);
                    Emit(KHavoc.Of(view));
                    Emit(KHavoc.Of(gc));
                    var v = new KVar(view);
                    var g = new KVar(gc);
                    Assume(AndAll(Eq(MemProp("Addr", v, named["view"].Parameter.Type), MemProp("Addr", new KVar(p), m.ReturnType)), Eq(MemProp("Length", v, named["view"].Parameter.Type), n),
                               Eq(MemProp("Elems", v, named["view"].Parameter.Type), new KOp("seq.const", fill))));
                    Assume(AndAll(Eq(MemProp("Addr", g, named["gc"].Parameter.Type), MemProp("Addr", v, named["view"].Parameter.Type)), Eq(MemProp("Length", g, named["gc"].Parameter.Type), MemProp("Length", v, named["view"].Parameter.Type))));
                    Emit(KMemCells.Of(MemCells(v, named["view"].Parameter.Type, at), true));
                    MemFresh(v, named["view"].Parameter.Type, at);
                    Emit(new KFill
                    {
                        Map = MemMap(named["view"].Parameter.Type),
                        Lo = MemProp("Addr", v, named["view"].Parameter.Type),
                        Hi = Plus(MemProp("Addr", v, named["view"].Parameter.Type), n),
                        Value = fill,
                    });
                    value = new KVar(p);
                    return true;
                }
                case "LengthIsNatural":
                    Assume(Ge(MemProp("Length", ArgumentIn("view", given, named), named["view"].Parameter.Type), KLit.Zero));
                    return true;
                case "Get":
                {
                    var v = ArgumentIn("view", given, named);
                    var p = ArgumentIn("p", given, named);
                    var i = ArgumentIn("i", given, named);
                    CheckPrecondition(AndAll(Eq(MemProp("Addr", v, named["view"].Parameter.Type), MemProp("Addr", p, named["p"].Parameter.Type)), Le(KLit.Zero, i), Lt(i, MemProp("Length", v, named["view"].Parameter.Type))), "view.Addr == p.Addr && 0 <= i && i < view.Length.Value", at, m.Name);
                    value = Sel(MemProp("Elems", v, named["view"].Parameter.Type), i);
                    return true;
                }
                case "Set":
                {
                    var v = ArgumentIn("view", given, named);
                    var p = ArgumentIn("p", given, named);
                    var i = ArgumentIn("i", given, named);
                    var x = ArgumentIn("value", given, named);
                    CheckPrecondition(AndAll(Eq(MemProp("Addr", v, named["view"].Parameter.Type), MemProp("Addr", p, named["p"].Parameter.Type)), Le(KLit.Zero, i), Lt(i, MemProp("Length", v, named["view"].Parameter.Type))), "view.Addr == p.Addr && 0 <= i && i < view.Length.Value", at, m.Name);
                    var old = Declare("t$" + _temps++, named["view"].Parameter.Type);
                    Emit(KAssign.Of(old, v));
                    var view = RefVariable(named["view"]);
                    Emit(KHavoc.Of(view));
                    var nv = new KVar(view);
                    var ov = new KVar(old);
                    Assume(AndAll(Eq(MemProp("Addr", nv, named["view"].Parameter.Type), MemProp("Addr", ov, named["view"].Parameter.Type)), Eq(MemProp("Length", nv, named["view"].Parameter.Type), MemProp("Length", ov, named["view"].Parameter.Type)),
                               Eq(MemProp("Elems", nv, named["view"].Parameter.Type), Store(MemProp("Elems", ov, named["view"].Parameter.Type), i, x))));
                    StoreCell(Plus(MemProp("Addr", nv, named["view"].Parameter.Type), i), x, arrayOf, at);
                    return true;
                }
                case "FreeArray":
                {
                    var g = ArgumentIn("gc", given, named);
                    var v = ArgumentIn("view", given, named);
                    var p = ArgumentIn("p", given, named);
                    CheckPrecondition(AndAll(Eq(MemProp("Addr", g, named["gc"].Parameter.Type), MemProp("Addr", v, named["view"].Parameter.Type)), Eq(MemProp("Addr", g, named["gc"].Parameter.Type), MemProp("Addr", p, named["p"].Parameter.Type)), Eq(MemProp("Length", g, named["gc"].Parameter.Type), MemProp("Length", v, named["view"].Parameter.Type))), "gc.Addr == view.Addr && gc.Addr == p.Addr && gc.Length == view.Length", at, m.Name);
                    Revoke(v, named["view"].Parameter.Type, at);
                    return true;
                }
                case "Split":
                {
                    var w = ArgumentIn("whole", given, named);
                    var cut = ArgumentIn("at", given, named);
                    CheckPrecondition(AndAll(Le(KLit.Zero, cut), Le(cut, MemProp("Length", w, named["whole"].Parameter.Type))), "0 <= at.Value && at.Value <= whole.Length.Value", at, m.Name);
                    var left = RefVariable(named["left"]);
                    var right = RefVariable(named["right"]);
                    Emit(KHavoc.Of(left));
                    Emit(KHavoc.Of(right));
                    var l = new KVar(left);
                    var r = new KVar(right);
                    Assume(AndAll(Eq(MemProp("Addr", l, named["left"].Parameter.Type), MemProp("Addr", w, named["whole"].Parameter.Type)), Eq(MemProp("Length", l, named["left"].Parameter.Type), cut), Eq(MemProp("Elems", l, named["left"].Parameter.Type), MemProp("Elems", w, named["whole"].Parameter.Type)),
                               Ge(MemProp("Length", r, named["right"].Parameter.Type), KLit.Zero)));
                    Assume(AndAll(Eq(MemProp("Addr", r, named["right"].Parameter.Type), Plus(MemProp("Addr", w, named["whole"].Parameter.Type), cut)), Eq(MemProp("Length", r, named["right"].Parameter.Type), Minus(MemProp("Length", w, named["whole"].Parameter.Type), cut)),
                               Eq(MemProp("Elems", r, named["right"].Parameter.Type), new KOp("seq.drop", MemProp("Elems", w, named["whole"].Parameter.Type), cut))));
                    Revoke(w, named["whole"].Parameter.Type, at);
                    Grant(l, named["left"].Parameter.Type, at);
                    Grant(r, named["right"].Parameter.Type, at);
                    return true;
                }
                case "Join":
                {
                    var l = ArgumentIn("left", given, named);
                    var r = ArgumentIn("right", given, named);
                    CheckPrecondition(Eq(MemProp("Addr", r, named["right"].Parameter.Type), Plus(MemProp("Addr", l, named["left"].Parameter.Type), MemProp("Length", l, named["left"].Parameter.Type))), "right.Addr.Value == left.Addr.Value + left.Length.Value", at, m.Name);
                    var whole = RefVariable(named["whole"]);
                    Emit(KHavoc.Of(whole));
                    var w = new KVar(whole);
                    Assume(AndAll(Eq(MemProp("Addr", w, named["whole"].Parameter.Type), MemProp("Addr", l, named["left"].Parameter.Type)), Eq(MemProp("Length", w, named["whole"].Parameter.Type), Plus(MemProp("Length", l, named["left"].Parameter.Type), MemProp("Length", r, named["right"].Parameter.Type))),
                               Eq(MemProp("Elems", w, named["whole"].Parameter.Type), new KOp("seq.concat", MemProp("Elems", l, named["left"].Parameter.Type), MemProp("Length", l, named["left"].Parameter.Type), MemProp("Elems", r, named["right"].Parameter.Type)))));
                    Revoke(l, named["left"].Parameter.Type, at);
                    Revoke(r, named["right"].Parameter.Type, at);
                    Grant(w, named["whole"].Parameter.Type, at);
                    return true;
                }
                case "TakeOut":
                {
                    var w = ArgumentIn("whole", given, named);
                    var i = ArgumentIn("i", given, named);
                    CheckPrecondition(AndAll(Le(KLit.Zero, i), Lt(i, MemProp("Length", w, named["whole"].Parameter.Type))), "0 <= i.Value && i.Value < whole.Length.Value", at, m.Name);
                    var cell = RefVariable(named["cell"]);
                    var rest = RefVariable(named["rest"]);
                    Emit(KHavoc.Of(cell));
                    Emit(KHavoc.Of(rest));
                    var c = new KVar(cell);
                    var h = new KVar(rest);
                    Assume(AndAll(Eq(MemProp("Addr", c, named["cell"].Parameter.Type), Plus(MemProp("Addr", w, named["whole"].Parameter.Type), i)), Eq(MemProp("Value", c, named["cell"].Parameter.Type), Sel(MemProp("Elems", w, named["whole"].Parameter.Type), i))));
                    Assume(AndAll(Eq(MemProp("Addr", h, named["rest"].Parameter.Type), MemProp("Addr", w, named["whole"].Parameter.Type)), Eq(MemProp("Length", h, named["rest"].Parameter.Type), MemProp("Length", w, named["whole"].Parameter.Type)), Eq(MemProp("Index", h, named["rest"].Parameter.Type), i),
                               Eq(MemProp("Elems", h, named["rest"].Parameter.Type), MemProp("Elems", w, named["whole"].Parameter.Type))));
                    Revoke(w, named["whole"].Parameter.Type, at);
                    Grant(c, named["cell"].Parameter.Type, at);
                    Grant(h, named["rest"].Parameter.Type, at);
                    return true;
                }
                case "PutBack":
                {
                    var c = ArgumentIn("cell", given, named);
                    var h = ArgumentIn("rest", given, named);
                    CheckPrecondition(Eq(MemProp("Addr", c, named["cell"].Parameter.Type), Plus(MemProp("Addr", h, named["rest"].Parameter.Type), MemProp("Index", h, named["rest"].Parameter.Type))), "cell.Addr.Value == rest.Addr.Value + rest.Index.Value", at, m.Name);
                    var whole = RefVariable(named["whole"]);
                    Emit(KHavoc.Of(whole));
                    var w = new KVar(whole);
                    Assume(AndAll(Eq(MemProp("Addr", w, named["whole"].Parameter.Type), MemProp("Addr", h, named["rest"].Parameter.Type)), Eq(MemProp("Length", w, named["whole"].Parameter.Type), MemProp("Length", h, named["rest"].Parameter.Type)),
                               Eq(MemProp("Elems", w, named["whole"].Parameter.Type), Store(MemProp("Elems", h, named["rest"].Parameter.Type), MemProp("Index", h, named["rest"].Parameter.Type), MemProp("Value", c, named["cell"].Parameter.Type)))));
                    Revoke(c, named["cell"].Parameter.Type, at);
                    Revoke(h, named["rest"].Parameter.Type, at);
                    Grant(w, named["whole"].Parameter.Type, at);
                    return true;
                }
                default: throw new NotTranslated("Mem." + m.Name);
            }
        }

        private void StoreCell(KExpr addr, KExpr x, IArrayTypeSymbol arrayOf, SyntaxNode at) => Emit(new KStore
        {
            Memory = true,
            Index = addr,
            Value = x,
            ArrayType = arrayOf,
            At = at,
            ArrayAt = at,
        });

        private void Revoke(KExpr v, ITypeSymbol t, SyntaxNode at) => Emit(KMemCells.Of(MemCells(v, t, at), false));

        private void Grant(KExpr v, ITypeSymbol t, SyntaxNode at, bool tie = true)
        {
            Emit(KMemCells.Of(MemCells(v, t, at), true));
            if (tie)
            {
                Assume(MemTie(v, t));
            }
        }

        private string FreshLocal(ITypeSymbol t)
        {
            var v = Declare("t$" + _temps++, t);
            Emit(KHavoc.Of(v));
            return v;
        }

        private void Assume(KExpr c) => Emit(KAssume.Of(c));

        private KExpr ArgumentIn(string name, Dictionary<string, KExpr> given, Dictionary<string, IArgumentOperation> named)
        {
            if (given.TryGetValue(name, out var known))
            {
                return known;
            }
            var t = Declare("t$" + _temps++, named[name].Parameter.Type);
            Emit(KAssign.Of(t, Expr(named[name].Value)));
            return given[name] = new KVar(t);
        }
    }
}
