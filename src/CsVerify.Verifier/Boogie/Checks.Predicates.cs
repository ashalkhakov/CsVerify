using System;
using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using static CsVerify.Verifier.Boogie.KernelTypes;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>Predicates: a predicate body's own check (self-framing, well-definedness).</summary>
    internal sealed partial class Checks
    {
        /// <summary>
        /// A predicate's own check: its body read left to right, as code (its arithmetic and reads checked, each under
        /// the conditions before it), each read of a field needing a Spec.Acc to its left (CSV1016).
        /// </summary>
        private void RunPredicate()
        {
            _out = _p.Blocks[0].Stmts;
            Emit(new KAssign { Var = "perm", Value = new KLit("(lambda o: Ref :: false)") });
            _p.UsesCells = _program.UsesPermissions;
            _p.UsesFields = _program.UsesFieldPermissions;
            if (_p.UsesFields) Emit(new KAssign { Var = "fperm", Value = new KLit("(lambda y$: Ref :: (lambda k$: int :: false))") });
            if (_p.UsesCells) Emit(new KAssign { Var = "cells", Value = new KLit("(lambda x$: Ref :: (lambda i$: int :: 0.0))") });
            CWalk(_p.FunctionBody, new KLit("true"));
            _p.FunctionBody = null;
            _p.Obligations = _p.Blocks[0].Stmts.Count(s => s is KAssert a && a.Check != null);
        }

        private KExpr CWalk(KExpr e, KExpr guard)
        {
            switch (e)
            {
                case KOp { Op: "&&" } and:
                {
                    var l = CWalk(and.Args[0], guard);
                    var r = CWalk(and.Args[1], Conj(guard, l));
                    return Conj(l, r);
                }
                case KOp { Op: "||" } or:
                {
                    var l = CWalk(or.Args[0], guard);
                    var r = CWalk(or.Args[1], Conj(guard, new KOp("!", l)));
                    return new KOp("||", l, r);
                }
                case KOp { Op: "ite" } ite:
                {
                    var c = CWalk(ite.Args[0], guard);
                    var t = CWalk(ite.Args[1], Conj(guard, c));
                    var f = CWalk(ite.Args[2], Conj(guard, new KOp("!", c)));
                    return Ite(c, t, f);
                }
                case KAcc acc:
                {
                    var o = CWalk(acc.Obj, guard);
                    // (no permission to null is ever held)
                    Assume(Implies(guard, new KOp("!=", o, new KLit("null"))));
                    SetPerm(o, new KOp("||", Held(o), guard));
                    return new KLit("true");
                }
                case KInst inst:
                    foreach (var a in inst.Args) CWalk(a, guard);
                    return new KLit("true");
                case KFieldAcc fa:
                {
                    var o = CWalk(fa.Obj, guard);
                    Assume(Implies(guard, new KOp("!=", o, new KLit("null"))));
                    if (_p.UsesFields) SetField(o, fa.Field, new KOp("||", FieldHeld(o, fa.Field), guard));
                    return new KLit("true");
                }
                case KCells cl:
                {
                    var c = new KCells { Arr = CWalk(cl.Arr, guard), Lo = CWalk(cl.Lo, guard), Hi = CWalk(cl.Hi, guard), Read = cl.Read, At = cl.At };
                    if (cl.Read) Assert(new KLit("false"), At("CSV1016", cl.At, "a predicate holds whole permissions: Spec.AccRead is for contracts"));
                    if (_p.UsesCells) ChangeCells(guard, c, "+");
                    return new KLit("true");
                }
                case KElem el:
                {
                    var a = CWalk(el.Array, guard);
                    var i = CWalk(el.Index, guard);
                    var v = Guarded(guard, () => Code(new KElem { String = el.String, Array = a, Index = i, ArrayType = el.ArrayType, At = el.At, ArrayAt = el.ArrayAt, Unchecked = el.Unchecked, NoNull = el.NoNull }));
                    if (_p.UsesCells && !el.String)
                        Assert(Implies(guard, new KOp(">", Cell(a, i), new KLit("0.0"))), At("CSV1016", el.At, $"'{el.At}' reads a cell this predicate has no Spec.Acc for (to its left): its value could change while the predicate is folded"));
                    return v;
                }
                case KOp op:
                    return new KOp(op.Op, op.Args.Select(a => CWalk(a, guard)).ToArray());
                case KLit _: case KVar _: return e;
                case KField fd: return Guarded(guard, () => Code(new KField { Field = fd.Field, Instance = fd.Instance == null ? null : CWalk(fd.Instance, guard), OnThis = fd.OnThis, NoNull = fd.NoNull, At = fd.At, InstanceAt = fd.InstanceAt }));
                case KQuant q: return Guarded(guard, () => Code(q));
                case KFnCall fn: return Guarded(guard, () => Code(fn));
                case KLen len: return Guarded(guard, () => Code(new KLen { String = len.String, Array = CWalk(len.Array, guard), At = len.At, ArrayAt = len.ArrayAt }));
                case KArith ar: return Guarded(guard, () => Code(new KArith { Op = ar.Op, Left = CWalk(ar.Left, guard), Right = CWalk(ar.Right, guard), Type = ar.Type, Mode = ar.Mode, At = ar.At }));
                default: throw new NotTranslated("in a predicate's body: " + e.GetType().Name);
            }
        }
    }
}
