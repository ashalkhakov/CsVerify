using System;
using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using static CsVerify.Verifier.Boogie.KernelTypes;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>Ownership: views of [Owned] objects and packages in hand, read shares, views at entry.</summary>
    internal sealed partial class Checks
    {
        // ------------------------------------------------------------------ ownership

        /// <summary>Is the object's view in hand (full permission)?</summary>
        private static KExpr Held(KExpr o) => new KOp("sel", new KVar("perm"), o);

        /// <summary>Is the object's view in a package held here?</summary>
        private static KExpr Packed(KExpr o) => new KOp("sel", new KVar("pkg"), o);

        /// <summary>A package arrives (a parameter, a call's result, a ref or out argument): its views, packed, are in hand, each different from the others and from the views in hand.</summary>
        private void Arrive(KExpr p, ITypeSymbol type)
        {
            foreach (var f in PackageViews(type))
            {
                var v = new KOp(FieldFunction(f), p);
                Assume(new KOp("!=", v, new KLit("null")));
                AssumeInvariant(ViewOf(f.Type), v);
                Assume(new KOp("&&", new KOp("!", Held(v)), new KOp("!", Packed(v))));
                // (a view's object is its tree's root, packed or not)
                if (KernelTypes.Trees) Assume(new KOp("==", new KOp("sel", new KVar("$root"), v), v));
                Emit(new KMapUpdate { Map = "pkg", Ref = v, Value = new KLit("true") });
            }
        }

        /// <summary>
        /// Is the object's view in hand whole (write permission)? pk counts read shares as
        /// fractions, each one ε: those in hand, less those given away for good; the view is whole with none missing.
        /// </summary>
        /// <summary>An object in a tree this method borrows (Spec.Modifies(Own.Tree(x))): writable without its view.</summary>
        private KExpr Lent(KExpr o)
        {
            KExpr any = new KLit("false");
            foreach (var root in _p.LentRoots)
            {
                var x = Code(root);
                any = new KOp("||", any, KernelTypes.Trees ? new KOp("&&", new KOp("!=", x, new KLit("null")), new KOp("==", new KOp("sel", new KVar("$root"), o), new KOp("sel", new KVar("$root"), x)))
                                                           : new KOp("==", o, x));
            }
            return any;
        }

        private static KExpr Whole(KExpr o) => new KOp("&&", Held(o), new KOp(">=", new KOp("sel", new KVar("pk"), o), new KLit("0")));

        private void Shares(KExpr o, int by) =>
            Emit(new KMapUpdate { Map = "pk", Ref = o, Value = new KOp(by > 0 ? "+" : "-", new KOp("sel", new KVar("pk"), o), new KLit(System.Math.Abs(by).ToString())) });

        /// <summary>A view received: nobody else has it (views are linear), so it isn't one in hand already; now it is.</summary>
        private void Receive(KExpr o)
        {
            Assume(new KOp("!", Held(o)));
            Assume(new KOp("!", Packed(o)));
            Emit(new KMapUpdate { Map = "perm", Ref = o, Value = new KLit("true") });
            // (an object whose view is in hand is its tree's root: no [Owns] field holds it)
            if (KernelTypes.Trees) Assume(new KOp("==", new KOp("sel", new KVar("$root"), o), o));
        }

        /// <summary>
        /// At entry: the views received are in hand (this, in a method of an [Owned] class that isn't [Pure], or its
        /// constructor; each view parameter), each not null, holding its invariant, and different from the others.
        /// </summary>
        private void EnterOwned()
        {
            Emit(new KAssign { Var = "perm", Value = new KLit("(lambda o: Ref :: false)") });
            Emit(new KAssign { Var = "pk", Value = new KLit("(lambda o: Ref :: 0)") });
            Emit(new KAssign { Var = "pkg", Value = new KLit("(lambda o: Ref :: false)") });
            // (no instances held yet: the preconditions bring them; who owns what is unknown)
            Emit(new KAssign { Var = "pinst", Value = new KLit("(lambda q: Inst :: 0)") });
            Emit(new KHavoc { Var = "owner" });
            Emit(new KHavoc { Var = "psnap" });
            if (_p.UsesFields)
            {
                Emit(new KAssign { Var = "fperm", Value = new KLit("(lambda y$: Ref :: (lambda k$: int :: false))") });
                Emit(new KHavoc { Var = "fowner" });
            }
            if (_p.UsesCells)
            {
                Emit(new KAssign { Var = "cells", Value = new KLit($"(lambda x$: Ref :: (lambda i$: int :: {(_p.ArrayMode ? "0.0" : "1.0")}))") });
                Emit(new KHavoc { Var = "cowner" });
            }
            if (_p.ThisIsView) Emit(new KMapUpdate { Map = "perm", Ref = new KVar("this"), Value = new KLit("true") });
            ViewsAtEntry(grant: true);
        }

        private void ViewsAtEntry(bool grant)
        {
            var m = _p.Method;
            foreach (var param in m.Parameters.Where(HoldsView))
            {
                var v = new KVar(Local(param));
                Assume(new KOp("!=", v, new KLit("null")));
                AssumeInvariant(ViewOf(param.Type), v);
                if (grant) Receive(v);
            }
            // (a share, or a view lent read-only: a share's worth, which may alias other shares, but no view in hand)
            foreach (var param in m.Parameters.Where(HoldsShare))
            {
                var v = new KVar(Local(param));
                Assume(new KOp("!=", v, new KLit("null")));
                AssumeInvariant(ViewOf(param.Type), v);
                if (!grant) continue;
                if (IsView(param.Type)) Assume(new KOp("!", Held(v)));
                Shares(v, 1);
            }
            // (the views in the packages it gets: in hand, packed, each different from the others)
            if (grant)
                foreach (var param in m.Parameters.Where(x => IsPackage(x.Type) && x.RefKind is RefKind.None or RefKind.Ref))
                    Arrive(new KVar(Local(param)), param.Type);
            if (_p.ThisIsView && !_p.IsCtor) AssumeInvariant(m.ContainingType, new KVar("this"));
        }
    }
}
