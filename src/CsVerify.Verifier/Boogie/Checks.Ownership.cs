using System;
using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using static CsVerify.Verifier.Boogie.KernelTypes;
using static CsVerify.Verifier.Boogie.MOp;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>Ownership: views of [Owned] objects and packages in hand, read shares, views at entry.</summary>
    internal sealed partial class Checks
    {
        // ------------------------------------------------------------------ ownership

        /// <summary>Is the object's view in hand (full permission)?</summary>
        private static MExpr Held(MExpr o) => Sel("perm", o);

        /// <summary>Is the object's view in a package held here?</summary>
        private static MExpr Packed(MExpr o) => Sel("pkg", o);

        /// <summary>A package arrives (a parameter, a call's result, a ref or out argument): its views, packed, are in hand, each different from the others and from the views in hand.</summary>
        private void Arrive(MExpr p, ITypeSymbol type)
        {
            foreach (var f in PackageViews(type))
            {
                var v = new MOp(FieldFunction(f), p);
                Assume(NotNull(v));
                AssumeInvariant(ViewOf(f.Type), v);
                Assume(AndAlso(Not(Held(v)), Not(Packed(v))));
                // (a view's object is its tree's root, packed or not)
                if (KernelTypes.Trees)
                {
                    Assume(Eq(Sel("$root", v), v));
                }
                Emit(new MMapUpdate
                {
                    Map = "pkg",
                    Ref = v,
                    Value = new MLit("true"),
                });
            }
        }

        /// <summary>
        /// Is the object's view in hand whole (write permission)? pk counts read shares as
        /// fractions, each one ε: those in hand, less those given away for good; the view is whole with none missing.
        /// </summary>
        /// <summary>An object in a tree this method borrows (Spec.Modifies(Own.Tree(x))): writable without its view.</summary>
        private MExpr Lent(MExpr o)
        {
            MExpr any = new MLit("false");
            foreach (var root in _p.LentRoots)
            {
                var x = Code(root);
                any = OrElse(any, KernelTypes.Trees ? AndAlso(NotNull(x), Eq(Sel("$root", o), Sel("$root", x)))
                                                           : Eq(o, x));
            }
            return any;
        }

        private static MExpr Whole(MExpr o) => AndAlso(Held(o), new MOp(">=", Sel("pk", o), new MLit("0")));

        private void Shares(MExpr o, int by) =>
            Emit(new MMapUpdate
            {
                Map = "pk",
                Ref = o,
                Value = new MOp(by > 0 ? "+" : "-", Sel("pk", o), new MLit(System.Math.Abs(by).ToString())),
            });

        /// <summary>A view received: nobody else has it (views are linear), so it isn't one in hand already; now it is.</summary>
        private void Receive(MExpr o)
        {
            Assume(Not(Held(o)));
            Assume(Not(Packed(o)));
            Emit(new MMapUpdate
            {
                Map = "perm",
                Ref = o,
                Value = new MLit("true"),
            });
            // (an object whose view is in hand is its tree's root: no [Owns] field holds it)
            if (KernelTypes.Trees)
            {
                Assume(Eq(Sel("$root", o), o));
            }
        }

        /// <summary>
        /// At entry: the views received are in hand (this, in a method of an [Owned] class that isn't [Pure], or its
        /// constructor; each view parameter), each not null, holding its invariant, and different from the others.
        /// </summary>
        private void EnterOwned()
        {
            Emit(new MAssign
            {
                Var = "perm",
                Value = new MLit("(lambda o: Ref :: false)"),
            });
            Emit(new MAssign
            {
                Var = "pk",
                Value = new MLit("(lambda o: Ref :: 0)"),
            });
            Emit(new MAssign
            {
                Var = "pkg",
                Value = new MLit("(lambda o: Ref :: false)"),
            });
            // (no instances held yet: the preconditions bring them; who owns what is unknown)
            Emit(new MAssign
            {
                Var = "pinst",
                Value = new MLit("(lambda q: Inst :: 0)"),
            });
            Emit(new MHavoc { Var = "owner" });
            Emit(new MHavoc { Var = "psnap" });
            if (_p.UsesFields)
            {
                Emit(new MAssign
                {
                    Var = "fperm",
                    Value = new MLit("(lambda y$: Ref :: (lambda k$: int :: false))"),
                });
                Emit(new MHavoc { Var = "fowner" });
            }
            if (_p.UsesCells)
            {
                Emit(new MAssign
                {
                    Var = "cells",
                    Value = new MLit($"(lambda x$: Ref :: (lambda i$: int :: {(_p.ArrayMode ? "0.0" : "1.0")}))"),
                });
                Emit(new MHavoc { Var = "cowner" });
            }
            if (_p.ThisIsView)
            {
                Emit(new MMapUpdate
                {
                    Map = "perm",
                    Ref = new MVar("this"),
                    Value = new MLit("true"),
                });
            }
            ViewsAtEntry(grant: true);
        }

        private void ViewsAtEntry(bool grant)
        {
            var m = _p.Method;
            foreach (var param in m.Parameters.Where(HoldsView))
            {
                var v = new MVar(Local(param));
                Assume(NotNull(v));
                AssumeInvariant(ViewOf(param.Type), v);
                if (grant)
                {
                    Receive(v);
                }
            }
            // (a share, or a view lent read-only: a share's worth, which may alias other shares, but no view in hand)
            foreach (var param in m.Parameters.Where(HoldsShare))
            {
                var v = new MVar(Local(param));
                Assume(NotNull(v));
                AssumeInvariant(ViewOf(param.Type), v);
                if (!grant)
                {
                    continue;
                }
                if (IsView(param.Type))
                {
                    Assume(Not(Held(v)));
                }
                Shares(v, 1);
            }
            // (the views in the packages it gets: in hand, packed, each different from the others)
            if (grant)
            {
                foreach (var param in m.Parameters.Where(x => IsPackage(x.Type) && x.RefKind is RefKind.None or RefKind.Ref))
                {
                    Arrive(new MVar(Local(param)), param.Type);
                }
            }
            if (_p.ThisIsView && !_p.IsCtor)
            {
                AssumeInvariant(m.ContainingType, new MVar("this"));
            }
        }
    }
}
