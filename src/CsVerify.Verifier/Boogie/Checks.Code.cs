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
        private KExpr Guarded(KExpr guard, Func<KExpr> code)
        {
            var outer = _out;
            _out = new List<KStmt>();
            KExpr v;
            try { v = code(); }
            finally
            {
                var inner = _out;
                _out = outer;
                foreach (var s in inner)
                    Emit(s switch
                    {
                        KAssert a => new KAssert { Cond = Implies(guard, a.Cond), Check = a.Check, NotAssumedAfter = a.NotAssumedAfter },
                        KAssume { Always: true } a => a,
                        KAssume a => new KAssume { Cond = Implies(guard, a.Cond) },
                        _ => s,
                    });
            }
            return v;
        }

        // ------------------------------------------------------------------ code

        /// <summary>An expression at run time as mathematics, its checks emitted first, in the order C# evaluates.</summary>
        private KExpr Code(KExpr e)
        {
            switch (e)
            {
                case null: return null;
                case KLit _: case KVar _: case KFnApp _: return e;
                case KOp { Op: "scat" } cat:
                {
                    var (l, r) = (Code(cat.Args[0]), Code(cat.Args[1]));
                    // (a concatenation too long for a string throws: the path ends)
                    Assume(new KOp("<=", new KOp("+", new KOp("sl", l), new KOp("sl", r)), new KLit("2147483647")));
                    return new KOp("scat", l, r);
                }
                case KOp { Op: "streq" } eq:
                {
                    var (l, r) = (Code(eq.Args[0]), Code(eq.Args[1]));
                    Assume(Extensional(l, r));
                    return new KOp("==", l, r);
                }
                case KOp op: return new KOp(op.Op, op.Args.Select(Code).ToArray());
                case KIfc ic:
                {
                    var x = Code(ic.Of);
                    var i = ic.Index == null ? null : Code(ic.Index);
                    Assert(new KOp("!=", x, new KLit("null")), NullAt(ic.At, ic.OfAt, $"'{ic.OfAt}' might be null in '{ic.At}'"));
                    KExpr count = IfcRead(x, null, ic.Element);
                    if (ic.Fresh)
                    {
                        var c = Fresh("int");
                        Assume(new KOp("<=", new KLit("0"), c));
                        count = c;
                    }
                    if (i == null) return count;
                    Assert(new KOp("&&", new KOp("<=", new KLit("0"), i), new KOp("<", i, count)), At("CSV1003", ic.At, $"index in '{ic.At}' might be out of range"));
                    return ic.Fresh ? Fresh(TypeOf(ic.Element)) : IfcRead(x, i, ic.Element);
                }
                case KMultiset ms:
                {
                    var a = Code(ms.Array);
                    var n = Code(ms.Count);
                    Assert(new KOp("!=", a, new KLit("null")), At("CSV1013", ms.At, $"'{ms.At}' might dereference null"));
                    Assert(new KOp("&&", new KOp("<=", new KLit("0"), n), new KOp("<=", n, new KOp("len", a))), At("CSV1003", ms.At, $"'{ms.At}' might not be within the array"));
                    KExpr fuel = new KLit("$LZ");
                    for (int k = 0; k < ms.Levels; k++) fuel = new KOp("$LS", fuel);
                    return new KOp("$bag", fuel, new KOp("sel", new KVar(Elements(ms.ArrayType)), a), n);
                }
                case KElem { String: true } sc:
                {
                    var s = Code(sc.Array);
                    var i = Code(sc.Index);
                    Assert(new KOp("!=", s, new KLit("null")), NullAt(sc.At, sc.ArrayAt, $"'{sc.ArrayAt}' might be null in '{sc.At}'"));
                    Assert(new KOp("&&", new KOp("<=", new KLit("0"), i), new KOp("<", i, new KOp("slen", s))), At("CSV1003", sc.At, $"index in '{sc.At}' might be out of range"));
                    return new KOp("sat", s, i);
                }
                case KElem el:
                {
                    var a = Code(el.Array);
                    var i = Code(el.Index);
                    if (el.Unchecked) { if (!el.NoNull) Assert(new KOp("!=", a, new KLit("null")), NullAt(el.At, el.ArrayAt, $"'{el.ArrayAt}' might be null in '{el.At}'")); }
                    else InBounds(a, i, el.At, el.ArrayAt);
                    // (alongside other code, under cell permissions: read only what it holds)
                    if (el.Alongside != null && _p.UsesCells)
                        Assert(Implies(Code(el.Alongside), new KOp(">", Cell(a, i), new KLit("0.0"))),
                            At("CSV1016", el.At, $"'{el.At}' reads a cell this code has no Spec.Acc or Spec.AccRead for, and it runs alongside other code that could be writing it"));
                    var ev = new KOp("sel", new KVar(Elements(el.ArrayType)), a, i);
                    // (an allocated array's element is an allocated object, as a field's value is; of its class's invariant)
                    if (IsRefArray(el.ArrayType))
                    {
                        Assume(Allocated(a, ev));
                        ObjectInvariant(ev, ((IArrayTypeSymbol)el.ArrayType).ElementType);
                    }
                    return ev;
                }
                case KDataField df:
                {
                    var v = Code(df.Value);
                    if (!df.Struct) Assert(new KOp("!=", v, new KLit("null")), NullAt(df.At, df.ValueAt, $"'{df.ValueAt}' might be null in '{df.At}'"));
                    return new KOp(df.Function, v);
                }
                case KCast cast:
                {
                    // (in code, a failing cast throws, which ends the path; a proof must show it doesn't)
                    var v = Code(cast.Value);
                    var test = Code(cast.Test);
                    if (_p.Ghost || _p.Contract.IsPure || _p.Contract.IsLemma) Assert(test, At("CSV1011", cast.At, $"cast '{cast.At}' might fail"));
                    else Assume(test);
                    return v;
                }
                case KLen len:
                {
                    var a = Code(len.Array);
                    Assert(new KOp("!=", a, new KLit("null")), NullAt(len.At, len.ArrayAt, $"'{len.ArrayAt}' might be null in '{len.At}'"));
                    return new KOp(len.String ? "slen" : "len", a);
                }
                case KQuant q when q.Range is KOp { Op: "&&" } range:
                {
                    // its bounds evaluated, then its body's checks, each for every value in its range (and under the guards in it)
                    var lo = Code(((KOp)range.Args[0]).Args[0]);
                    var hi = Code(((KOp)range.Args[1]).Args[1]);
                    var v = new KVar(q.Var);
                    var mathRange = new KOp("&&", new KOp("<=", lo, v), new KOp("<", v, hi));
                    var outer = _out;
                    _out = new List<KStmt>();
                    KExpr body;
                    _inQuantifier++;
                    try { body = CWalk(q.Body, mathRange); }
                    finally
                    {
                        _inQuantifier--;
                        var inner = _out;
                        _out = outer;
                        foreach (var s in inner)
                            Emit(s switch
                            {
                                KAssert a => new KAssert { Cond = new KQuant { Forall = true, Var = q.Var, Range = null, Body = a.Cond }, Check = a.Check, NotAssumedAfter = a.NotAssumedAfter },
                                KAssume { Always: true } a when !Mentions(a.Cond, new HashSet<string> { q.Var }) => a,
                                KAssume a => new KAssume { Cond = new KQuant { Forall = true, Var = q.Var, Range = null, Body = a.Cond } },
                                _ => throw new NotTranslated("a quantifier whose body changes state"),
                            });
                    }
                    return new KQuant { Forall = q.Forall, Var = q.Var, Type = q.Type, Range = mathRange, Body = body };
                }
                case KFnCall fc when !fc.Stub:
                {
                    // a function's application in code (in a quantifier, a function's body): its precondition checked there
                    // (CSV1001), its value the function's
                    var mark = _out.Count;
                    var receiver = fc.Receiver == null ? null : Code(fc.Receiver);
                    var args = fc.Args.Select(Code).ToArray();
                    var app = Spec(new KFnCall { Callee = fc.Callee, Receiver = receiver, ReceiverIsThis = fc.ReceiverIsThis, ReceiverAt = fc.ReceiverAt, Args = args, At = fc.At }, out var wf);
                    _facts.Clear();
                    foreach (var w in wf) Assert(w, At("CSV1001", fc.At, $"precondition of '{fc.Callee.Name}' might not hold in '{fc.At}'"));
                    return app;
                }
                case KFnCall { Stub: true } st:
                {
                    // a library member's call: its receiver not null, its precondition holding (CSV1001); its value the function's
                    KExpr receiver = null;
                    if (st.Receiver != null)
                    {
                        receiver = Code(st.Receiver);
                        Assert(new KOp("!=", receiver, new KLit("null")), NullAt(st.At, st.ReceiverAt, $"'{st.ReceiverAt}' might be null in '{st.At}'"));
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
                case KField fd:
                {
                    if (fd.Instance == null)
                    {
                        var sv = new KOp("sel", new KVar(FieldMap(fd.Field)), new KLit("null"));
                        if (NonNullField(fd.Field)) Assume(new KOp("!=", sv, new KLit("null")));
                        return sv;
                    }
                    var o = Code(fd.Instance);
                    if (!fd.OnThis && !fd.NoNull) Assert(new KOp("!=", o, new KLit("null")), NullAt(fd.At, fd.InstanceAt, $"'{fd.InstanceAt}' might be null in '{fd.At}'"));
                    // (a function with Spec.Reads reads only objects in it, as of entry: CSV1017)
                    if (_p.ReadsFrame != null && !fd.Field.IsStatic)
                        Assert(new KOp("sel", new KVar("r$entry"), o), At("CSV1017", fd.At, $"'{fd.At}' reads an object that is not in Spec.Reads"));
                    // (a query of an [Owned] class reads only its own tree)
                    else if (_p.TreeReads && !fd.Field.IsStatic)
                        Assert(new KOp("==", new KOp("sel", new KVar("$root"), o), new KOp("sel", new KVar("$root"), new KVar("this"))), At("CSV1017", fd.At, $"'{fd.At}' reads an object that is not in Spec.Reads"));
                    // (in a predicate's body: read only what a Spec.Acc to its left holds, so it can't change while folded)
                    if (_p.IsPredicate)
                        Assert(CanWrite(o, fd.Field), At("CSV1016", fd.At, $"'{fd.At}' reads an object this predicate has no Spec.Acc for (to its left): its value could change while the predicate is folded"));
                    var v = new KOp("sel", new KVar(FieldMap(fd.Field)), o);
                    // (a non-nullable field of a built object: not this one's, while its constructor builds it. True in every
                    // state, as the type says: not under a quantifier's range, whose variable it doesn't mention, where the
                    // solver would have no term to instantiate it with)
                    if (NonNullField(fd.Field) && !(_p.IsCtor && fd.OnThis))
                        Emit(new KAssume { Cond = new KOp("==>", new KOp("!=", o, new KLit("null")), new KOp("!=", v, new KLit("null"))), Always = true });
                    // (a field of an allocated object refers to an allocated object)
                    if (IsRef(FieldType(fd.Field))) Emit(new KAssume { Cond = Allocated(o, v), Always = true });
                    ObjectInvariant(v, FieldType(fd.Field));
                    return v;
                }
                default: throw new NotTranslated("in code: " + e.GetType().Name);
            }
        }

        private void InBounds(KExpr a, KExpr i, SyntaxNode at, SyntaxNode arrayAt)
        {
            Assert(new KOp("!=", a, new KLit("null")), NullAt(at, arrayAt, $"'{arrayAt}' might be null in '{at}'"));
            Assert(new KOp("&&", new KOp("<=", new KLit("0"), i), new KOp("<", i, new KOp("len", a))), At("CSV1003", at, $"index in '{at}' might be out of range"));
        }

        /// <summary>
        /// Integer arithmetic at run time: division by zero is an obligation; overflow is one in the default context,
        /// ends the path in a checked one (it throws), as MinValue / -1 does anywhere, and wraps around in an
        /// unchecked one (two's complement); ghost code's is mathematics.
        /// </summary>
        private KExpr Arith(KArith ar, KExpr l, KExpr r)
        {
            if (ar.Op == "/" || ar.Op == "%")
            {
                Assert(new KOp("!=", r, new KLit("0")), At("CSV1009", ar.At, $"division by zero in '{ar.At}'"));
                if (ar.ThrowsTo != null)
                    Emit(new KFork { Overflow = new KOp("!", new KOp("&&", new KOp("==", l, Number(Range(ar.Type).lo)), new KOp("==", r, new KLit("(-1)")))), Target = ar.ThrowsTo });
                // (MinValue / -1 throws in .NET, checked or not: a [Pure] member or lemma may not throw, so it's reported there)
                var minOverMinus1 = new KOp("!", new KOp("&&", new KOp("==", l, Number(Range(ar.Type).lo)), new KOp("==", r, new KLit("(-1)"))));
                if (_program.CheckOverflow && (_p.Contract.IsPure || _p.Contract.IsLemma) && ar.Mode != KMode.Math) Assert(minOverMinus1, At("CSV1010", ar.At, $"arithmetic '{ar.At}' might overflow {ar.Type.Name}"));
                else Assume(minOverMinus1);
                return new KOp(ar.Op == "/" ? "div" : "rem", l, r);
            }
            var value = new KOp(ar.Op, l, r);
            // (checked: out of range, it throws an OverflowException, which the handlers may catch)
            if (ar.ThrowsTo != null && ar.Mode == KMode.Checked) Emit(new KFork { Overflow = InRange(value, ar.Type), Target = ar.ThrowsTo });
            return Fit(value, ar.Type, ar.Mode, ar.At, $"arithmetic '{ar.At}' might overflow {ar.Type.Name}");
        }

        /// <summary>An explicit conversion between integer types: as arithmetic where it narrows; a widening one is the value.</summary>
        private KExpr Convert(KConv cv, KExpr value)
        {
            var (lo, hi) = Range(cv.To);
            var (flo, fhi) = Range(cv.From);
            if (flo >= lo && fhi <= hi) return value;
            return Fit(value, cv.To, cv.Mode, cv.At, $"conversion '{cv.At}' might overflow {cv.To.Name}");
        }

        private KExpr Fit(KExpr value, ITypeSymbol type, KMode mode, SyntaxNode at, string message)
        {
            switch (mode)
            {
                case KMode.Unchecked: return Wrap(value, type);
                case KMode.Math: return value;
                case KMode.Default when _program.CheckOverflow:
                // (checked, in a [Pure] member or a lemma: it may not throw, so the overflow is reported)
                case KMode.Checked when _program.CheckOverflow && (_p.Contract.IsPure || _p.Contract.IsLemma):
                    Assert(InRange(value, type), At("CSV1010", at, message));
                    return value;
                default:
                    Assume(InRange(value, type));
                    return value;
            }
        }
    }
}
