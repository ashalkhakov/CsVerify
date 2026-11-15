using System.Linq;
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
                Emit(MMapUpdate.Of("pkg", v, MLit.True));
            }
        }

        /// <summary>
        /// Is the object's view in hand whole (write permission)? pk counts read shares as
        /// fractions, each one ε: those in hand, less those given away for good; the view is whole with none missing.
        /// </summary>
        /// <summary>An object in a tree this method borrows (Spec.Modifies(Own.Tree(x))): writable without its view.</summary>
        private MExpr Lent(MExpr o)
        {
            MExpr any = MLit.False;
            foreach (var root in _p.LentRoots)
            {
                var x = Code(root);
                any = OrElse(any, KernelTypes.Trees ? AndAlso(NotNull(x), Eq(Sel("$root", o), Sel("$root", x)))
                                                           : Eq(o, x));
            }
            return any;
        }

        private static MExpr Whole(MExpr o) => AndAlso(Held(o), Ge(Sel("pk", o), MLit.Zero));

        private void Shares(MExpr o, int by) =>
            Emit(MMapUpdate.Of("pk", o, new MOp(by > 0 ? "+" : "-", Sel("pk", o), new MLit(System.Math.Abs(by).ToString()))));

        /// <summary>A view received: nobody else has it (views are linear), so it isn't one in hand already; now it is.</summary>
        private void Receive(MExpr o)
        {
            Assume(Not(Held(o)));
            Assume(Not(Packed(o)));
            Emit(MMapUpdate.Of("perm", o, MLit.True));
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
            Emit(MAssign.Of("perm", new MLit("(lambda o: Ref :: false)")));
            Emit(MAssign.Of("pk", new MLit("(lambda o: Ref :: 0)")));
            Emit(MAssign.Of("pkg", new MLit("(lambda o: Ref :: false)")));
            // (no instances held yet: the preconditions bring them; who owns what is unknown)
            Emit(MAssign.Of("pinst", new MLit("(lambda q: Inst :: 0)")));
            Emit(MHavoc.Of("owner"));
            Emit(MHavoc.Of("psnap"));
            if (_p.UsesFields)
            {
                Emit(MAssign.Of("fperm", new MLit("(lambda y$: Ref :: (lambda k$: int :: false))")));
                Emit(MHavoc.Of("fowner"));
            }
            if (_p.UsesCells)
            {
                Emit(MAssign.Of("cells", new MLit($"(lambda x$: Ref :: (lambda i$: int :: {(_p.ArrayMode ? "0.0" : "1.0")}))")));
                Emit(MHavoc.Of("cowner"));
            }
            if (_p.ThisIsView)
            {
                Emit(MMapUpdate.Of("perm", new MVar("this"), MLit.True));
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
