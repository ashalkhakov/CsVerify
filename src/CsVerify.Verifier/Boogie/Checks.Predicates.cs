using System;
using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using static CsVerify.Verifier.Boogie.KernelTypes;
using static CsVerify.Verifier.Boogie.MOp;

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
            // (its one block, b0, empty: what the check makes is all of it)
            _m.Blocks = _p.Blocks.Select(b => new MBlock
            {
                Label = b.Label,
                Ordinal = b.Ordinal,
                Jump = b.Jump,
            }).ToList();
            _out = _m.Blocks[0].Stmts;
            Emit(new MAssign
            {
                Var = "perm",
                Value = new MLit("(lambda o: Ref :: false)"),
            });
            _p.UsesCells = _program.UsesPermissions;
            _p.UsesFields = _program.UsesFieldPermissions;
            if (_p.UsesFields)
            {
                Emit(new MAssign
                {
                    Var = "fperm",
                    Value = new MLit("(lambda y$: Ref :: (lambda k$: int :: false))"),
                });
            }
            if (_p.UsesCells)
            {
                Emit(new MAssign
                {
                    Var = "cells",
                    Value = new MLit("(lambda x$: Ref :: (lambda i$: int :: 0.0))"),
                });
            }
            CWalk(_p.FunctionBody, new MLit("true"));
            _m.Obligations = _m.Blocks[0].Stmts.Count(s => s is MAssert a && a.Check != null);
        }

        private MExpr CWalk(KExpr e, MExpr guard)
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
                    var r = CWalk(or.Args[1], Conj(guard, Not(l)));
                    return OrElse(l, r);
                }
                case KOp { Op: "ite" } ite:
                {
                    var c = CWalk(ite.Args[0], guard);
                    var t = CWalk(ite.Args[1], Conj(guard, c));
                    var f = CWalk(ite.Args[2], Conj(guard, Not(c)));
                    return Ite(c, t, f);
                }
                case KAcc acc:
                {
                    var o = CWalk(acc.Obj, guard);
                    // (no permission to null is ever held)
                    Assume(Implies(guard, NotNull(o)));
                    SetPerm(o, OrElse(Held(o), guard));
                    return new MLit("true");
                }
                case KInst inst:
                    foreach (var a in inst.Args)
                    {
                        CWalk(a, guard);
                    }
                    return new MLit("true");
                case KFieldAcc fa:
                {
                    var o = CWalk(fa.Obj, guard);
                    Assume(Implies(guard, NotNull(o)));
                    if (_p.UsesFields)
                    {
                        SetField(o, fa.Field, OrElse(FieldHeld(o, fa.Field), guard));
                    }
                    return new MLit("true");
                }
                case KCells cl:
                {
                    var c = new MCells
                    {
                        Arr = CWalk(cl.Arr, guard),
                        Lo = CWalk(cl.Lo, guard),
                        Hi = CWalk(cl.Hi, guard),
                        Read = cl.Read,
                        At = cl.At,
                    };
                    if (cl.Read)
                    {
                        Assert(new MLit("false"), At("CSV1016", cl.At, "a predicate holds whole permissions: Spec.AccRead is for contracts"));
                    }
                    if (_p.UsesCells)
                    {
                        ChangeCells(guard, c, "+");
                    }
                    return new MLit("true");
                }
                case KElem el:
                {
                    var a = CWalk(el.Array, guard);
                    var i = CWalk(el.Index, guard);
                    var v = Guarded(guard, () => el.String ? StringChar(el, a, i) : Elem(el, a, i, alongside: null));
                    if (_p.UsesCells && !el.String)
                    {
                        Assert(Implies(guard, new MOp(">", Cell(a, i), new MLit("0.0"))), At("CSV1016", el.At, $"'{el.At}' reads a cell this predicate has no Spec.Acc for (to its left): its value could change while the predicate is folded"));
                    }
                    return v;
                }
                case KOp op:
                    return new MOp(op.Op, op.Args.Select(a => CWalk(a, guard)).ToArray());
                case KLit _: case KVar _: return MathTerms.Math(e);
                case KField fd: return Guarded(guard, () => Field(fd, fd.Instance == null ? null : CWalk(fd.Instance, guard)));
                case KQuant q: return Guarded(guard, () => Code(q));
                case KFnCall fn: return Guarded(guard, () => Code(fn));
                case KLen len: return Guarded(guard, () => Len(len, CWalk(len.Array, guard)));
                // (a predicate's body sees no exceptions: its arithmetic throws nowhere)
                case KArith ar: return Guarded(guard, () => Arith(ar, CWalk(ar.Left, guard), CWalk(ar.Right, guard)));
                default: throw new NotTranslated("in a predicate's body: " + e.GetType().Name);
            }
        }
    }
}
