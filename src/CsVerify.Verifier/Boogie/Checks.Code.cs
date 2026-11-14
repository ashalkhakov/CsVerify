using System;
using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using static CsVerify.Verifier.Boogie.KernelTypes;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>Code: run-time expressions as mathematics, their checks first (null, bounds, division, overflow, conversions).</summary>
    internal sealed partial class Checks
    {
        /// <summary>Code's checks, each under the guard (where the code is evaluated at all).</summary>
        private MExpr Guarded(MExpr guard, Func<MExpr> code)
        {
            var outer = _out;
            _out = new List<MStmt>();
            MExpr v;
            try
            {
                v = code();
            }
            finally
            {
                var inner = _out;
                _out = outer;
                foreach (var s in inner)
                {
                    Emit(s switch
                    {
                        MAssert a => new MAssert
                        {
                            Cond = Implies(guard, a.Cond),
                            Check = a.Check,
                            NotAssumedAfter = a.NotAssumedAfter,
                        },
                        MAssume { Always: true } a => a,
                        MAssume a => new MAssume { Cond = Implies(guard, a.Cond) },
                        _ => s,
                    });
                }
            }
            return v;
        }

        // ------------------------------------------------------------------ code

        /// <summary>An expression at run time as mathematics, its checks emitted first, in the order C# evaluates.</summary>
        private MExpr Code(KExpr e)
        {
            switch (e)
            {
                case null: return null;
                case KLit _: case KVar _: case KFnApp _: return MathTerms.Math(e);
                case KOp { Op: "scat" } cat:
                {
                    var (l, r) = (Code(cat.Args[0]), Code(cat.Args[1]));
                    // (a concatenation too long for a string throws: the path ends)
                    Assume(new MOp("<=", new MOp("+", new MOp("sl", l), new MOp("sl", r)), new MLit("2147483647")));
                    return new MOp("scat", l, r);
                }
                case KOp { Op: "streq" } eq:
                {
                    var (l, r) = (Code(eq.Args[0]), Code(eq.Args[1]));
                    Assume(Extensional(l, r));
                    return new MOp("==", l, r);
                }
                case KOp op: return new MOp(op.Op, op.Args.Select(Code).ToArray());
                case KIfc ic:
                {
                    var x = Code(ic.Of);
                    var i = ic.Index == null ? null : Code(ic.Index);
                    Assert(new MOp("!=", x, new MLit("null")), NullAt(ic.At, ic.OfAt, $"'{ic.OfAt}' might be null in '{ic.At}'"));
                    MExpr count = MathTypes.IfcRead(x, null, ic.Element);
                    if (ic.Fresh)
                    {
                        var c = Fresh("int");
                        Assume(new MOp("<=", new MLit("0"), c));
                        count = c;
                    }
                    if (i == null)
                    {
                        return count;
                    }
                    Assert(new MOp("&&", new MOp("<=", new MLit("0"), i), new MOp("<", i, count)), At("CSV1003", ic.At, $"index in '{ic.At}' might be out of range"));
                    return ic.Fresh ? Fresh(TypeOf(ic.Element)) : MathTypes.IfcRead(x, i, ic.Element);
                }
                case KMultiset ms:
                {
                    var a = Code(ms.Array);
                    var n = Code(ms.Count);
                    Assert(new MOp("!=", a, new MLit("null")), At("CSV1013", ms.At, $"'{ms.At}' might dereference null"));
                    Assert(new MOp("&&", new MOp("<=", new MLit("0"), n), new MOp("<=", n, new MOp("len", a))), At("CSV1003", ms.At, $"'{ms.At}' might not be within the array"));
                    MExpr fuel = new MLit("$LZ");
                    for (int k = 0; k < ms.Levels; k++)
                    {
                        fuel = new MOp("$LS", fuel);
                    }
                    return new MOp("$bag", fuel, new MOp("sel", new MVar(Elements(ms.ArrayType)), a), n);
                }
                case KElem { String: true } sc: return StringChar(sc, Code(sc.Array), Code(sc.Index));
                case KElem el:
                {
                    var a = Code(el.Array);
                    var i = Code(el.Index);
                    return Elem(el, a, i, el.Alongside);
                }
                case KDataField df:
                {
                    var v = Code(df.Value);
                    if (!df.Struct)
                    {
                        Assert(new MOp("!=", v, new MLit("null")), NullAt(df.At, df.ValueAt, $"'{df.ValueAt}' might be null in '{df.At}'"));
                    }
                    return new MOp(df.Function, v);
                }
                case KCast cast:
                {
                    // (in code, a failing cast throws, which ends the path; a proof must show it doesn't)
                    var v = Code(cast.Value);
                    var test = Code(cast.Test);
                    if (_p.Ghost || _p.Contract.IsPure || _p.Contract.IsLemma)
                    {
                        Assert(test, At("CSV1011", cast.At, $"cast '{cast.At}' might fail"));
                    }
                    else
                    {
                        Assume(test);
                    }
                    return v;
                }
                case KLen len: return Len(len, Code(len.Array));
                case KQuant q when q.Range is KOp { Op: "&&" } range:
                {
                    // its bounds evaluated, then its body's checks, each for every value in its range (and under the guards in it)
                    var lo = Code(((KOp)range.Args[0]).Args[0]);
                    var hi = Code(((KOp)range.Args[1]).Args[1]);
                    var v = new MVar(q.Var);
                    var mathRange = new MOp("&&", new MOp("<=", lo, v), new MOp("<", v, hi));
                    var outer = _out;
                    _out = new List<MStmt>();
                    MExpr body;
                    _inQuantifier++;
                    try
                    {
                        body = CWalk(q.Body, mathRange);
                    }
                    finally
                    {
                        _inQuantifier--;
                        var inner = _out;
                        _out = outer;
                        foreach (var s in inner)
                        {
                            Emit(s switch
                            {
                                MAssert a => new MAssert
                                {
                                    Cond = new MQuant
                                    {
                                        Forall = true,
                                        Var = q.Var,
                                        Range = null,
                                        Body = a.Cond,
                                    },
                                    Check = a.Check,
                                    NotAssumedAfter = a.NotAssumedAfter,
                                },
                                MAssume { Always: true } a when !Mentions(a.Cond, new HashSet<string> { q.Var }) => a,
                                MAssume a => new MAssume { Cond = new MQuant
                                {
                                    Forall = true,
                                    Var = q.Var,
                                    Range = null,
                                    Body = a.Cond,
                                }
                                },
                                _ => throw new NotTranslated("a quantifier whose body changes state"),
                            });
                        }
                    }
                    return new MQuant
                    {
                        Forall = q.Forall,
                        Var = q.Var,
                        Type = q.Type,
                        Range = mathRange,
                        Body = body,
                    };
                }
                case KFnCall fc when !fc.Stub:
                {
                    // a function's application in code (in a quantifier, a function's body): its precondition checked there
                    // (CSV1001), its value the function's
                    var receiver = fc.Receiver == null ? null : Code(fc.Receiver);
                    var args = fc.Args.Select(Code).ToArray();
                    var wf = new List<MExpr>();
                    if (receiver != null && !fc.ReceiverIsThis && !IsStruct(fc.Callee.ContainingType))
                    {
                        wf.Add(new MOp("!=", receiver, new MLit("null")));
                    }
                    var app = FunctionApp(fc, receiver, args, wf.Add);
                    _facts.Clear();
                    foreach (var w in wf)
                    {
                        Assert(w, At("CSV1001", fc.At, $"precondition of '{fc.Callee.Name}' might not hold in '{fc.At}'"));
                    }
                    return app;
                }
                case KFnCall { Stub: true } st:
                {
                    // a library member's call: its receiver not null, its precondition holding (CSV1001); its value the function's
                    MExpr receiver = null;
                    if (st.Receiver != null)
                    {
                        receiver = Code(st.Receiver);
                        Assert(new MOp("!=", receiver, new MLit("null")), NullAt(st.At, st.ReceiverAt, $"'{st.ReceiverAt}' might be null in '{st.At}'"));
                    }
                    var args = st.Args.Select(Code).ToArray();
                    var given = StubGiven(st.Callee, receiver, args);
                    foreach (var r in _program.Signature(st.Callee).Requires)
                    {
                        var pre = Subst(Spec(r.Expr, out _), given);
                        _facts.Clear();
                        Assert(pre, At("CSV1001", st.At, $"'{st.At}' might throw: its precondition '{r.At}' might not hold"));
                    }
                    _p.Stubs.Add(st.Callee);
                    return StubApp(st.Callee, receiver, args);
                }
                case KArith ar: return Arith(ar, Code(ar.Left), Code(ar.Right));
                case KConv cv: return Convert(cv, Code(cv.Value));
                case KField fd: return Field(fd, fd.Instance == null ? null : Code(fd.Instance));
                default: throw new NotTranslated("in code: " + e.GetType().Name);
            }
        }

        /// <summary>A string's character s[i]: s not null, i within it.</summary>
        private MExpr StringChar(KElem sc, MExpr s, MExpr i)
        {
            Assert(new MOp("!=", s, new MLit("null")), NullAt(sc.At, sc.ArrayAt, $"'{sc.ArrayAt}' might be null in '{sc.At}'"));
            Assert(new MOp("&&", new MOp("<=", new MLit("0"), i), new MOp("<", i, new MOp("slen", s))), At("CSV1003", sc.At, $"index in '{sc.At}' might be out of range"));
            return new MOp("sat", s, i);
        }

        /// <summary>An array's element a[i]: a not null, i within it (where it's checked); alongside other code, a cell held.</summary>
        private MExpr Elem(KElem el, MExpr a, MExpr i, KExpr alongside)
        {
            if (el.Unchecked)
            {
                if (!el.NoNull)
                {
                    Assert(new MOp("!=", a, new MLit("null")), NullAt(el.At, el.ArrayAt, $"'{el.ArrayAt}' might be null in '{el.At}'"));
                }
            }
            else
            {
                InBounds(a, i, el.At, el.ArrayAt);
            }
            // (alongside other code, under cell permissions: read only what it holds)
            if (alongside != null && _p.UsesCells)
            {
                Assert(Implies(Code(alongside), new MOp(">", Cell(a, i), new MLit("0.0"))),
                    At("CSV1016", el.At, $"'{el.At}' reads a cell this code has no Spec.Acc or Spec.AccRead for, and it runs alongside other code that could be writing it"));
            }
            var ev = new MOp("sel", new MVar(Elements(el.ArrayType)), a, i);
            // (an allocated array's element is an allocated object, as a field's value is; of its class's invariant)
            if (IsRefArray(el.ArrayType))
            {
                Assume(Allocated(a, ev));
                ObjectInvariant(ev, ((IArrayTypeSymbol)el.ArrayType).ElementType);
            }
            return ev;
        }

        /// <summary>An array's or a string's length: not null.</summary>
        private MExpr Len(KLen len, MExpr a)
        {
            Assert(new MOp("!=", a, new MLit("null")), NullAt(len.At, len.ArrayAt, $"'{len.ArrayAt}' might be null in '{len.At}'"));
            return new MOp(len.String ? "slen" : "len", a);
        }

        /// <summary>A field's value: of o (null for a static field), not null where it's read; what its type says of it.</summary>
        private MExpr Field(KField fd, MExpr o)
        {
            if (fd.Instance == null)
            {
                var sv = new MOp("sel", new MVar(FieldMap(fd.Field)), new MLit("null"));
                if (NonNullField(fd.Field))
                {
                    Assume(new MOp("!=", sv, new MLit("null")));
                }
                return sv;
            }
            if (!fd.OnThis && !fd.NoNull)
            {
                Assert(new MOp("!=", o, new MLit("null")), NullAt(fd.At, fd.InstanceAt, $"'{fd.InstanceAt}' might be null in '{fd.At}'"));
            }
            // (a function with Spec.Reads reads only objects in it, as of entry: CSV1017)
            if (_p.ReadsFrame != null && !fd.Field.IsStatic)
            {
                Assert(new MOp("sel", new MVar("r$entry"), o), At("CSV1017", fd.At, $"'{fd.At}' reads an object that is not in Spec.Reads"));
            }
            // (a query of an [Owned] class reads only its own tree)
            else if (_p.TreeReads && !fd.Field.IsStatic)
            {
                Assert(new MOp("==", new MOp("sel", new MVar("$root"), o), new MOp("sel", new MVar("$root"), new MVar("this"))), At("CSV1017", fd.At, $"'{fd.At}' reads an object that is not in Spec.Reads"));
            }
            // (in a predicate's body: read only what a Spec.Acc to its left holds, so it can't change while folded)
            if (_p.IsPredicate)
            {
                Assert(CanWrite(o, fd.Field), At("CSV1016", fd.At, $"'{fd.At}' reads an object this predicate has no Spec.Acc for (to its left): its value could change while the predicate is folded"));
            }
            var v = new MOp("sel", new MVar(FieldMap(fd.Field)), o);
            // (a non-nullable field of a built object: not this one's, while its constructor builds it. True in every
            // state, as the type says: not under a quantifier's range, whose variable it doesn't mention, where the
            // solver would have no term to instantiate it with)
            if (NonNullField(fd.Field) && !(_p.IsCtor && fd.OnThis))
            {
                Emit(new MAssume
                {
                    Cond = new MOp("==>", new MOp("!=", o, new MLit("null")), new MOp("!=", v, new MLit("null"))),
                    Always = true,
                });
            }
            // (a field of an allocated object refers to an allocated object)
            if (IsRef(FieldType(fd.Field)))
            {
                Emit(new MAssume
                {
                    Cond = Allocated(o, v),
                    Always = true,
                });
            }
            ObjectInvariant(v, FieldType(fd.Field));
            return v;
        }

        private void InBounds(MExpr a, MExpr i, SyntaxNode at, SyntaxNode arrayAt)
        {
            Assert(new MOp("!=", a, new MLit("null")), NullAt(at, arrayAt, $"'{arrayAt}' might be null in '{at}'"));
            Assert(new MOp("&&", new MOp("<=", new MLit("0"), i), new MOp("<", i, new MOp("len", a))), At("CSV1003", at, $"index in '{at}' might be out of range"));
        }

        /// <summary>
        /// Integer arithmetic at run time: division by zero is an obligation; overflow is one in the default context,
        /// ends the path in a checked one (it throws), as MinValue / -1 does anywhere, and wraps around in an
        /// unchecked one (two's complement); ghost code's is mathematics.
        /// </summary>
        private MExpr Arith(KArith ar, MExpr l, MExpr r)
        {
            if (ar.Op == "/" || ar.Op == "%")
            {
                Assert(new MOp("!=", r, new MLit("0")), At("CSV1009", ar.At, $"division by zero in '{ar.At}'"));
                if (ar.ThrowsTo != null)
                {
                    Emit(new MFork
                    {
                        Overflow = new MOp("!", new MOp("&&", new MOp("==", l, MathTypes.Number(Range(ar.Type).lo)), new MOp("==", r, new MLit("(-1)")))),
                        Target = ar.ThrowsTo,
                    });
                }
                // (MinValue / -1 throws in .NET, checked or not: a [Pure] member or lemma may not throw, so it's reported there)
                var minOverMinus1 = new MOp("!", new MOp("&&", new MOp("==", l, MathTypes.Number(Range(ar.Type).lo)), new MOp("==", r, new MLit("(-1)"))));
                if (_program.CheckOverflow && (_p.Contract.IsPure || _p.Contract.IsLemma) && ar.Mode != KMode.Math)
                {
                    Assert(minOverMinus1, At("CSV1010", ar.At, $"arithmetic '{ar.At}' might overflow {ar.Type.Name}"));
                }
                else
                {
                    Assume(minOverMinus1);
                }
                return new MOp(ar.Op == "/" ? "div" : "rem", l, r);
            }
            var value = new MOp(ar.Op, l, r);
            // (checked: out of range, it throws an OverflowException, which the handlers may catch)
            if (ar.ThrowsTo != null && ar.Mode == KMode.Checked)
            {
                Emit(new MFork
                {
                    Overflow = MathTypes.InRange(value, ar.Type),
                    Target = ar.ThrowsTo,
                });
            }
            return Fit(value, ar.Type, ar.Mode, ar.At, $"arithmetic '{ar.At}' might overflow {ar.Type.Name}");
        }

        /// <summary>An explicit conversion between integer types: as arithmetic where it narrows; a widening one is the value.</summary>
        private MExpr Convert(KConv cv, MExpr value)
        {
            var (lo, hi) = Range(cv.To);
            var (flo, fhi) = Range(cv.From);
            if (flo >= lo && fhi <= hi)
            {
                return value;
            }
            return Fit(value, cv.To, cv.Mode, cv.At, $"conversion '{cv.At}' might overflow {cv.To.Name}");
        }

        private MExpr Fit(MExpr value, ITypeSymbol type, KMode mode, SyntaxNode at, string message)
        {
            switch (mode)
            {
                case KMode.Unchecked: return MathTypes.Wrap(value, type);
                case KMode.Math: return value;
                case KMode.Default when _program.CheckOverflow:
                // (checked, in a [Pure] member or a lemma: it may not throw, so the overflow is reported)
                case KMode.Checked when _program.CheckOverflow && (_p.Contract.IsPure || _p.Contract.IsLemma):
                    Assert(MathTypes.InRange(value, type), At("CSV1010", at, message));
                    return value;
                default:
                    Assume(MathTypes.InRange(value, type));
                    return value;
            }
        }
    }
}
