using System;
using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.FlowAnalysis;
using Microsoft.CodeAnalysis.Operations;
using static CsVerify.Verifier.Boogie.KernelTypes;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>Ownership: Own's operations on views of [Owned] objects, and linear packages.</summary>
    internal sealed partial class Lowering
    {
        /// <summary>A package of the subset: its parts are views and ordinary values, not shares or other packages.</summary>
        private static void CheckPackage(ITypeSymbol t)
        {
            if (KernelTypes.Data.Fields((INamedTypeSymbol)t).Any(f => IsShare(f.Type) || IsPackage(f.Type) || SpecSymbols.IsLinear(f.Type) && !IsView(f.Type)))
            {
                throw new NotTranslated("a package of shares or packages");
            }
        }

        /// <summary>A view's or share's object, v.Obj (a package's invariant ties it to the package's other parts).</summary>
        private static bool IsViewsObject(IPropertyReferenceOperation pr) => pr.Property.Name == "Obj" && (IsView(pr.Instance?.Type) || IsShare(pr.Instance?.Type));

        /// <summary>Own.New(new C(...), out view): a view of the new object; Own.Drop(view). The rest of Own isn't translated yet.</summary>
        private KExpr Own(IInvocationOperation own)
        {
            switch (own.TargetMethod.Name)
            {
                // (of an object not made here: its fields may be anyone's, so no view of it, CSV1016)
                case "New" when !(own.Arguments[0].Value is IObjectCreationOperation) && own.Arguments.Length == 2 && IsOwnedClass(own.Arguments[0].Value.Type):
                {
                    Emit(new KCheck
                    {
                        Cond = new KLit("false"),
                        Id = "CSV1016",
                        At = own.Syntax,
                        NotAssumedAfter = true,
                        Message = $"Own.New makes a view only of an object made where it is called, new {own.Arguments[0].Value.Type.Name}(...): '{own.Arguments[0].Value.Syntax}' may be anyone's",
                    });
                    var obj = Expr(own.Arguments[0].Value);
                    var view = RefVariable(own.Arguments[1]);
                    // (the error stands for it: the view, as a new object's would be, nothing else said of it)
                    Emit(new KOwn
                    {
                        Kind = "new",
                        Obj = obj,
                        View = view,
                        Type = own.Arguments[0].Value.Type,
                        At = own.Syntax,
                        Unchecked = true,
                    });
                    return obj;
                }
                case "New" when own.Arguments[0].Value is IObjectCreationOperation:
                {
                    var obj = Expr(own.Arguments[0].Value);
                    var view = RefVariable(own.Arguments[1]);
                    Emit(new KOwn
                    {
                        Kind = "new",
                        Obj = obj,
                        View = view,
                        Type = own.Arguments[0].Value.Type,
                        At = own.Syntax,
                    });
                    return obj;
                }
                case "ToAcc" when IsView(own.Arguments[0].Value.Type):
                    // (the view goes, its permission stays in hand: a view and Spec.Acc are one permission here)
                    Expr(own.Arguments[0].Value);
                    return null;
                case "FromAcc" when IsOwnedClass(own.Arguments[0].Value.Type):
                {
                    var obj = Expr(own.Arguments[0].Value);
                    Emit(new KOwn
                    {
                        Kind = "fromacc",
                        Obj = obj,
                        View = RefVariable(own.Arguments[1]),
                        Type = own.Arguments[0].Value.Type,
                        At = own.Syntax,
                    });
                    return null;
                }
                // (Own.Take(ref c.F, out v) and Own.Give(ref c.F, x, v): a tree's unfolding and folding)
                case "Take" or "Give" when KernelTypes.Trees && Unconverted(own.Arguments.OrderBy(a => a.Parameter.Ordinal).First().Value) is IFieldReferenceOperation { Field: var owns } slot &&
                                           SpecSymbols.IsOwnsField(owns) && slot.Instance != null && IsOwnedClass(owns.ContainingType):
                {
                    var args = own.Arguments.OrderBy(a => a.Parameter.Ordinal).ToList();
                    var container = slot.Instance is IInstanceReferenceOperation ? new KVar("this") : Expr(slot.Instance);
                    _p.Fields.Add(owns.OriginalDefinition);
                    if (own.TargetMethod.Name == "Take")
                    {
                        var view = RefVariable(args[1]);
                        Emit(new KOwn
                        {
                            Kind = "take",
                            Obj = container,
                            Field = owns.OriginalDefinition,
                            View = view,
                            Type = owns.Type,
                            At = own.Syntax,
                            SlotAt = slot.Syntax,
                        });
                        return new KVar(view);
                    }
                    Emit(new KOwn
                    {
                        Kind = "give",
                        Obj = container,
                        Field = owns.OriginalDefinition,
                        Value = Expr(args[1].Value),
                        ViewValue = Expr(args[2].Value),
                        Type = owns.Type,
                        At = own.Syntax,
                        SlotAt = slot.Syntax,
                        ValueAt = args[1].Value.Syntax,
                        ViewAt = args[2].Value.Syntax,
                    });
                    return null;
                }
                case "Tree":
                    return KernelTypes.Trees ? new KOp("$tree", Expr(own.Arguments[0].Value)) : new KOp("set.of", Expr(own.Arguments[0].Value));
                // (Own.Share(ref v, out s): a read share of v's object; Own.Unshare(ref v, s) joins it back)
                case "Share" when IsView(own.Arguments[0].Value.Type):
                    Emit(new KOwn
                    {
                        Kind = "share",
                        Obj = Expr(own.Arguments[0].Value),
                        View = RefVariable(own.Arguments[1]),
                        Type = ViewOf(own.Arguments[0].Value.Type),
                        At = own.Syntax,
                    });
                    return null;
                case "Unshare" when IsView(own.Arguments[0].Value.Type):
                    Emit(new KOwn
                    {
                        Kind = "unshare",
                        Obj = Expr(own.Arguments[0].Value),
                        Value = Expr(own.Arguments[1].Value),
                        Type = ViewOf(own.Arguments[0].Value.Type),
                        At = own.Syntax,
                        SlotAt = own.Arguments[0].Value.Syntax,
                        ValueAt = own.Arguments[1].Value.Syntax,
                    });
                    return null;
                case "Drop" when IsShare(own.Arguments[0].Value.Type):
                    Emit(new KOwn
                    {
                        Kind = "dropshare",
                        Obj = Expr(own.Arguments[0].Value),
                        Type = ViewOf(own.Arguments[0].Value.Type),
                        At = own.Syntax,
                    });
                    return null;
                case "Drop" when IsView(own.Arguments[0].Value.Type):
                    Emit(new KOwn
                    {
                        Kind = "drop",
                        Obj = Expr(own.Arguments[0].Value),
                        Type = ViewOf(own.Arguments[0].Value.Type),
                        At = own.Syntax,
                    });
                    return null;
                default: throw new NotTranslated("Own." + own.TargetMethod.Name + (own.TargetMethod.Name == "New" ? " of an existing object" : ""));
            }
        }
    }
}
