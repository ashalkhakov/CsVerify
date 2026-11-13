using System;
using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using static CsVerify.Verifier.Boogie.KernelTypes;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>Statements: each kernel statement's obligations; a return's postconditions.</summary>
    internal sealed partial class Checks
    {
        /// <summary>A return: the result checked not null, the postconditions well-defined and holding, here.</summary>
        private void Return(KReturn ret, List<(KSpec spec, KExpr math, List<KExpr> wf, List<KExpr> facts)> ensures)
        {
            var m = _p.Method;
            // the views given back hold their invariants again
            foreach (var param in m.Parameters.Where(x => IsView(x.Type) && x.RefKind is RefKind.Ref or RefKind.Out))
                ProveInvariant(ViewOf(param.Type), new KVar(Local(param)), ret.At, $"when the view '{param.Name}' is given back");
            if (_p.ThisIsView && !_p.IsCtor) ProveInvariant(m.ContainingType, new KVar("this"), ret.At, $"when '{m.Name}' returns");
            // (an immutable object's invariant: established by its constructor)
            if (_p.IsCtor && HasObjectInvariant(m.ContainingType))
                ProveInvariant(m.ContainingType, new KVar("this"), ret.At, $"when the constructor of {m.ContainingType.Name} returns");
            // a non-nullable ref or out parameter is given back not null
            foreach (var param in m.Parameters.Where(x => x.RefKind is RefKind.Ref or RefKind.Out && IsNullable(x.Type) && NotNullable(x.Type)))
                Assert(new KOp("!=", new KVar(Local(param)), new KLit("null")), At("CSV1014", ret.At, $"'{param.Name}' might be null on return, but its type '{param.Type}' is not nullable"));
            // a constructor has set the fields that may not be null (but the required ones, which its callers set)
            if (_p.IsCtor)
                foreach (var field in InstanceFields(m.ContainingType).Where(NonNullField))
                    if (!IsRequired(field) || m.GetAttributes().Any(a => a.AttributeClass?.Name == "SetsRequiredMembersAttribute"))
                        Assert(new KOp("!=", new KOp("sel", new KVar(FieldMap(field)), new KVar("this")), new KLit("null")),
                            At("CSV1014", ret.At, $"field '{field.Name}' is not nullable, but might be null when the constructor of {m.ContainingType.Name} returns"));
            if (Returns(m) != null && IsNullable(Returns(m)) && NotNullable(Returns(m)))
                Assert(new KOp("!=", new KVar("result"), new KLit("null")), At("CSV1014", ret.At, $"'{m.Name}' might return null, but its return type '{m.ReturnType}' is not nullable" +
                    NullReasons(ret.At is Microsoft.CodeAnalysis.CSharp.Syntax.ReturnStatementSyntax rs ? rs.Expression : ret.At is Microsoft.CodeAnalysis.CSharp.Syntax.ArrowExpressionClauseSyntax ar ? ar.Expression : ret.At)));
            // the permissions the postconditions give back are in hand
            if (_p.UsesPerm)
            {
                _old = OldAtEntry;
                try { foreach (var e in _rawEnsures) Exhale(e, null, ret.At, null); }
                finally { _old = null; }
            }
            var before = new List<KExpr>();
            foreach (var e in ensures)
            {
                foreach (var f in e.facts) Assume(AtReturn(f));
                WellDefined(e.wf.Select(AtReturn).ToList(), e.spec.At, before);
                Assert(AtReturn(e.math), At("CSV1002", ret.At, $"postcondition '{e.spec.At}' might not hold on this return path"));
                before.Add(AtReturn(e.math));
            }
        }

        // ------------------------------------------------------------------ statements

        private void Statement(KStmt s, List<KExpr> decreases)
        {
            switch (s)
            {
                case KAssign a:
                {
                    var value = Code(a.Value);
                    if (a.NotNullAt != null)
                        Assert(new KOp("!=", value, new KLit("null")), At("CSV1014", a.NotNullAt, $"'{a.NotNullAt}' might store null, but '{a.NotNullName}' is not nullable"));
                    Emit(new KAssign { Var = a.Var, Value = value });
                    return;
                }
                case KFieldStore fs:
                {
                    var value = Code(fs.Value);
                    var o = fs.Instance == null ? new KLit("null") : Code(fs.Instance);
                    if (fs.Instance != null && !fs.OnThis)
                        Assert(new KOp("!=", o, new KLit("null")), NullAt(fs.At, fs.InstanceAt, $"'{fs.InstanceAt}' might be null in '{fs.At}'"));
                    if (fs.Instance != null && !IsOwnedField(fs.Field)) WithinFrame(o, fs.At);
                    if (IsOwnedField(fs.Field))
                        Assert(new KOp("||", _p.UsesFields ? new KOp("||", Whole(o), FieldHeld(o, fs.Field)) : Whole(o), Lent(o)), At("CSV1016", fs.At, $"'{fs.At}' changes an [Owned] {fs.Field.ContainingType.Name} without holding its view (Own<{fs.Field.ContainingType.Name}>, with no read shares out) or a frame lent to it"));
                    if (NonNullField(fs.Field))
                        Assert(new KOp("!=", value, new KLit("null")), At("CSV1014", fs.At, $"'{fs.At}' might store null, but field '{fs.Field.Name}' is not nullable"));
                    Emit(new KFieldStore { Field = fs.Field, Instance = o, Value = value, OnThis = fs.OnThis, At = fs.At, InstanceAt = fs.InstanceAt });
                    return;
                }
                case KOwn { Kind: "new" } own:
                {
                    // a view is made of a new object: its invariant holds, and nobody else has its view
                    var o = Code(own.Obj);
                    if (!own.Unchecked) ProveInvariant(own.Type, o, own.At, "when its view is made");
                    Emit(new KAssign { Var = own.View, Value = o });
                    // (a new tree of its own)
                    if (KernelTypes.Trees) { _p.Modifies.Add("$root"); _p.AnyWrites.Add("$root"); Emit(new KMapUpdate { Map = "$root", Ref = o, Value = o }); }
                    Receive(o);
                    return;
                }
                case KOwn { Kind: "take" } take:
                {
                    // Own.Take(ref c.F, out v): the object c.F owns comes out with its view, its invariant held at rest; c.F is null;
                    // c's tree splits: what was below the object is now in its own tree, or still in c's
                    var c = Code(take.Obj);
                    Assert(Whole(c), At("CSV1016", take.At, $"'{take.SlotAt}' changes an [Owned] {take.Field.ContainingType.Name} without holding its view"));
                    var x = new KOp("sel", new KVar(FieldMap(take.Field)), c);
                    Assert(new KOp("!=", x, new KLit("null")), At("CSV1016", take.At, $"'{take.SlotAt}' might be null: there is nothing to take"));
                    Emit(new KAssign { Var = take.View, Value = x });
                    var child = new KVar(take.View);
                    // (what an [Owns] field holds is in its container's tree, and isn't its root)
                    var root = new KVar("$root");
                    Assume(new KOp("&&", new KOp("==", new KOp("sel", root, child), new KOp("sel", root, c)), new KOp("!=", new KOp("sel", root, child), child)));
                    var siblings = InstanceFields(take.Field.ContainingType).Where(g => SpecSymbols.IsOwnsField(g) && !SymbolEqualityComparer.Default.Equals(g, take.Field.OriginalDefinition)).Select(FieldMap).ToList();
                    // (and so is what the container's other [Owns] fields hold, each a different object: they stay in its tree)
                    foreach (var g in siblings)
                    {
                        var held = new KOp("sel", new KVar(g), c);
                        Assume(new KOp("||", new KOp("==", held, new KLit("null")),
                            new KOp("&&", new KOp("&&", new KOp("==", new KOp("sel", root, held), new KOp("sel", root, c)), new KOp("!=", new KOp("sel", root, held), held)),
                                new KOp("!=", held, child))));
                    }
                    Emit(new KFieldStore { Field = take.Field, Instance = c, OnThis = true, Value = new KLit("null"), At = take.At, InstanceAt = take.At });
                    _p.Modifies.Add("$root"); _p.AnyWrites.Add("$root");
                    if (!_p.Locals.Any(l => l.Name == "split$")) _p.Locals.Add(new KLocal { Name = "split$", Raw = "[Ref]bool" });
                    Emit(new KRoots { Container = c, Child = child, Siblings = siblings });
                    AssumeInvariant(take.Type, child);
                    Receive(child);
                    return;
                }
                case KOwn { Kind: "give" } give:
                {
                    // Own.Give(ref c.F, x, v): x and its tree join c's under c.F, which must be empty; v, x's view, is handed over
                    var c = Code(give.Obj);
                    var x = Code(give.Value);
                    var v = Code(give.ViewValue);
                    Assert(Whole(c), At("CSV1016", give.At, $"'{give.SlotAt}' changes an [Owned] {give.Field.ContainingType.Name} without holding its view"));
                    Assert(new KOp("==", new KOp("sel", new KVar(FieldMap(give.Field)), c), new KLit("null")), At("CSV1016", give.At, $"'{give.SlotAt}' might still own an object: take it first"));
                    Assert(new KOp("==", v, x), At("CSV1016", give.At, $"'{give.ViewAt}' might not be the view of '{give.ValueAt}'"));
                    Assert(Whole(x), At("CSV1016", give.At, $"'{give.ValueAt}' might have read shares out: join them back (Own.Unshare) first"));
                    Assert(new KOp("!=", new KOp("sel", new KVar("$root"), c), x), At("CSV1016", give.At, $"'{give.ValueAt}' might own the container: ownership would be a cycle"));
                    ProveInvariant(give.Type, x, give.At, "when it is given to its owner");
                    Emit(new KMapUpdate { Map = "perm", Ref = x, Value = new KLit("false") });
                    Emit(new KFieldStore { Field = give.Field, Instance = c, OnThis = true, Value = x, At = give.At, InstanceAt = give.At });
                    _p.Modifies.Add("$root"); _p.AnyWrites.Add("$root");
                    Emit(new KRoots { Join = true, Container = c, Child = x });
                    return;
                }
                case KOwn { Kind: "fromacc" } from:
                {
                    var o = Code(from.Obj);
                    Assert(Held(o), At("CSV1016", from.At, $"'{from.At}' has no permission in hand to make a view of"));
                    Emit(new KAssign { Var = from.View, Value = o });
                    return;
                }
                case KFold fold:
                    Fold(fold);
                    return;
                case KThrow th:
                {
                    // (throwing null throws a NullReferenceException instead: checked, but in a proof)
                    var v = Code(th.Value);
                    if (!(_p.Ghost || _p.Contract.IsPure || _p.Contract.IsLemma))
                        Assert(new KOp("!=", v, new KLit("null")), At("CSV1013", th.At, $"'{th.At}' might be null: throwing it would throw a NullReferenceException"));
                    if (th.Seen) Emit(new KAssign { Var = "ex$", Value = v });
                    return;
                }
                case KInvoke iv:
                {
                    // (a call of a delegate: not null, and it accepts the arguments; what it gives is its $post)
                    var d = Code(iv.Delegate);
                    var args = iv.Args.Select(Code).ToArray();
                    Assert(new KOp("!=", d, new KLit("null")), NullAt(iv.At, iv.DelegateAt, $"'{iv.DelegateAt}' might be null in '{iv.At}'"));
                    Assert(new KOp("$preS." + iv.Key, new[] { d, new KOp("$state") }.Concat(args).ToArray()),
                        At("CSV1001", iv.At, $"'{iv.DelegateAt}' might not accept these arguments: say what it accepts with Spec.Requires(Spec.Pre({iv.DelegateAt}, ...))"));
                    Emit(new KInvoke { Result = iv.Result, Delegate = d, Args = args, Key = iv.Key, At = iv.At, DelegateAt = iv.DelegateAt });
                    return;
                }
                case KHavocAll ha when ha.Unless != null:
                    Emit(new KHavocAll { Unless = Code(ha.Unless), ProgramState = ha.ProgramState });
                    return;
                case KCheck ck:
                {
                    var cond = Spec(ck.Cond, out _);
                    // (what its reads give, free: a field not nullable isn't null)
                    Facts();
                    Assert(cond, At(ck.Id, ck.At, ck.Message), ck.NotAssumedAfter);
                    return;
                }
                case KLambda lam:
                {
                    // (its facts are mathematics of its parameters and of what never changes)
                    var r = new Dictionary<string, KExpr> { ["result"] = new KVar("q$r") };
                    foreach (var kv in lam.Rename) r[kv.Key] = kv.Value;
                    KExpr M(KExpr x) { var v = Spec(x, out _); _facts.Clear(); return Subst(v, r); }
                    Emit(new KLambda { Var = lam.Var, Key = lam.Key, Params = lam.Params, ResultType = lam.ResultType, NoChange = lam.NoChange, Steady = lam.Steady,
                                       Pre = lam.Pre == null ? null : M(lam.Pre), Posts = lam.Posts.Select(M).ToList(),
                                       PreS = lam.PreS == null ? null : M(lam.PreS), Reads = lam.Reads == null ? null : M(lam.Reads), Changes = lam.Changes == null ? null : M(lam.Changes),
                                       PostsS = lam.PostsS.Select(M).ToList() });
                    return;
                }
                case KAwait aw:
                    Emit(new KAwait { Keep = aw.Keep, When = aw.When == null ? null : Code(aw.When), Cells = _p.UsesCells, Perm = _p.UsesPerm });
                    return;
                case KThrowExit _:
                    // leaving by an exception: its own clauses for the exception's type hold
                    foreach (var (type, cond, at) in _p.ThrowEnsures)
                    {
                        var holds = OldAtEntry(Spec(cond, out _));
                        _facts.Clear();
                        Assert(new KOp("==>", Is(new KVar("ex$"), type), holds), At("CSV1002", at, $"postcondition on throw '{at}' might not hold when '{_p.Method.Name}' throws"));
                    }
                    return;
                case KOwn { Kind: "pack" } pack:
                {
                    // a view packed: its invariant holds, and it is the package's now (not in hand to write with)
                    var x = Code(pack.Obj);
                    ProveInvariant(pack.Type, x, pack.At, $"when it is packed into {pack.Into.Name}");
                    Emit(new KMapUpdate { Map = "perm", Ref = x, Value = new KLit("false") });
                    Emit(new KMapUpdate { Map = "pkg", Ref = x, Value = new KLit("true") });
                    return;
                }
                case KOwn { Kind: "unpack" } unpack:
                {
                    // a view taken out of its package: in hand again, its invariant holding
                    var x = Code(unpack.Obj);
                    Assume(new KOp("!=", x, new KLit("null")));
                    Emit(new KMapUpdate { Map = "pkg", Ref = x, Value = new KLit("false") });
                    Emit(new KMapUpdate { Map = "perm", Ref = x, Value = new KLit("true") });
                    AssumeInvariant(unpack.Type, x);
                    if (KernelTypes.Trees) Assume(new KOp("==", new KOp("sel", new KVar("$root"), x), x));
                    return;
                }
                case KOwn { Kind: "share" } share:
                    // Own.Share(ref v, out s): s is a share of v's object; v keeps the rest, so in sum nothing changes here
                    Emit(new KAssign { Var = share.View, Value = Code(share.Obj) });
                    return;
                case KOwn { Kind: "unshare" } unshare:
                {
                    var v = Code(unshare.Obj);
                    Assert(new KOp("==", Code(unshare.Value), v), At("CSV1016", unshare.At, $"'{unshare.ValueAt}' might not be a share of '{unshare.SlotAt}'"));
                    return;
                }
                case KOwn { Kind: "dropshare" } dropShare:
                    Shares(Code(dropShare.Obj), -1);
                    return;
                case KOwn { Kind: "drop" } drop:
                    Emit(new KMapUpdate { Map = "perm", Ref = Code(drop.Obj), Value = new KLit("false") });
                    return;
                case KNewObj n:
                {
                    var args = Arguments(n.Ctor, n.Args, n.ArgsAt);
                    // (a constructor exchanges permissions as any call does: about the new object, as this)
                    var sig = n.Ctor != null && _p.UsesPerm ? _program.Signature(n.Ctor) : null;
                    var given = sig == null ? null : Given(n.Ctor, new KVar(n.Var), args);
                    if (sig != null) foreach (var r in sig.Requires) Exhale(r.Expr, given, n.At, null);
                    Emit(new KNewObj { Var = n.Var, Type = n.Type, Ctor = n.Ctor, Args = args, ArgsAt = n.ArgsAt, At = n.At,
                                       Check = n.Ctor == null ? null : At("CSV1001", n.At, $"'{n.At}'") });
                    if (sig != null) foreach (var e in sig.Ensures) Inhale(e.Expr, given, null);
                    // (what its constructor left in its reference fields is allocated: it could store nothing else)
                    if (n.Ctor != null)
                        foreach (var f in InstanceFields(n.Type).Where(f => IsRef(FieldType(f)) && _p.Fields.Contains(f)))
                            Assume(Allocated(new KVar(n.Var), new KOp("sel", new KVar(FieldMap(f)), new KVar(n.Var))));
                    // (and its ghost sets of objects hold allocated ones)
                    if (n.Ctor != null)
                        foreach (var f in InstanceFields(n.Type).Where(f => IsObjSet(IsGhost(FieldType(f)) ? GhostOf(FieldType(f)) : FieldType(f)) && _p.Fields.Contains(f)))
                            Assume(new KOp("set.subset", new KOp("sel", new KVar(FieldMap(f)), new KVar(n.Var)), new KVar("$Alloc")));
                    ObjectInvariant(new KVar(n.Var), n.Type);
                    return;
                }
                case KStore { Memory: true } ms:
                    Emit(new KStore { Array = new KLit("null"), Index = Code(ms.Index), Value = Code(ms.Value), ArrayType = ms.ArrayType, At = ms.At, ArrayAt = ms.ArrayAt, Checked = true });
                    return;
                case KRow row when row.Ref == null:
                    Emit(row);
                    return;
                case KRow row:
                {
                    var r = Code(row.Ref);
                    if (row.At != null) WithinFrame(r, row.At);
                    // (the program's write of a whole row, Array.Fill's say, under cell permissions: all its cells held)
                    if (row.At != null && _p.UsesCells)
                    {
                        var i = new KVar("i$");
                        Assert(new KOp("||", new KOp("==", r, new KLit("null")), new KQuant { Forall = true, Var = "i$",
                                   Body = Implies(new KOp("&&", new KOp("<=", new KLit("0"), i), new KOp("<", i, new KOp("len", r))), new KOp(">=", Cell(r, i), new KLit("1.0"))) }),
                               At("CSV1016", row.At, $"'{row.At}' writes the whole array: this method needs Spec.Acc of all its cells"));
                    }
                    var v = Spec(row.Value, out _);
                    _facts.Clear();
                    Emit(new KRow { Map = row.Map, Ref = r, Value = v });
                    return;
                }
                case KFill fill:
                    Emit(new KFill { Map = fill.Map, Lo = Code(fill.Lo), Hi = Code(fill.Hi), Value = Code(fill.Value) });
                    return;
                case KMemCells mc:
                    if (!_p.UsesCells) return;
                    foreach (var c in mc.Cells)
                    {
                        var cells = new KCells { Arr = new KLit("null"), Lo = Code(c.Lo), Hi = Code(c.Hi), At = c.At };
                        if (mc.Grant) InhaleCells(new KLit("true"), cells);
                        else ChangeCells(new KLit("true"), cells, "-");
                    }
                    return;
                case KStore st:
                {
                    var value = Code(st.Value);
                    var a = Code(st.Array);
                    var i = Code(st.Index);
                    if (st.Unchecked) { if (!st.NoNull) Assert(new KOp("!=", a, new KLit("null")), NullAt(st.At, st.ArrayAt, $"'{st.ArrayAt}' might be null in '{st.At}'")); }
                    else InBounds(a, i, st.At, st.ArrayAt);
                    WithinFrame(a, st.At);
                    if (_p.UsesCells) Assert(new KOp(">=", Cell(a, i), new KLit("1.0")), At("CSV1016", st.At, $"'{st.At}' writes a cell this method has no Spec.Acc for"));
                    Emit(new KStore { Array = a, Index = i, Value = value, ArrayType = st.ArrayType, At = st.At, ArrayAt = st.ArrayAt, Checked = true });
                    return;
                }
                // (a library call's arrays: without cell permissions, where it may write, any; with them, those it's handed,
                // all of whose cells it may read or write, so all must be held, and only those change)
                case KLibraryArrays la:
                {
                    if (!_p.UsesCells)
                    {
                        if (la.Write) foreach (var (map, fresh) in la.Fresh) Emit(new KRow { Map = map, Ref = null, Value = new KVar(fresh) });
                        return;
                    }
                    // (handed other objects, one that may write arrays may write those it reaches through them, whose cells this
                    // method can't hold: CSV1016, and every array unknown after; one that only reads them, as any read)
                    if (!la.Plain && la.Write)
                    {
                        Assert(new KLit("false"), At("CSV1016", la.At, $"'{la.At}' may write arrays it reaches through the objects it's handed, whose cells this method can't hold"), notAssumedAfter: true);
                        foreach (var (map, fresh) in la.Fresh) Emit(new KRow { Map = map, Ref = null, Value = new KVar(fresh) });
                        return;
                    }
                    foreach (var (array, map, row) in la.Arrays)
                    {
                        var a = Code(array);
                        var i = new KVar("i$");
                        var inRange = new KOp("&&", new KOp("<=", new KLit("0"), i), new KOp("<", i, new KOp("len", a)));
                        Assert(new KOp("||", new KOp("==", a, new KLit("null")),
                                       new KQuant { Forall = true, Var = "i$", Body = Implies(inRange, la.Write ? new KOp(">=", Cell(a, i), new KLit("1.0")) : new KOp(">", Cell(a, i), new KLit("0.0"))) }),
                               At("CSV1016", la.At, la.Write ? $"'{la.At}' may write the array it's handed: this method needs Spec.Acc of all its cells"
                                                             : $"'{la.At}' reads the array it's handed: this method needs Spec.Acc or Spec.AccRead of all its cells"));
                        if (!la.Write) continue;
                        Emit(new KHavoc { Var = row });
                        Emit(new KRow { Map = map, Ref = a, Value = new KVar(row) });
                    }
                    return;
                }
                case KNew n:
                    Emit(new KNew { Var = n.Var, ArrayType = n.ArrayType, Size = Code(n.Size), Elements = n.Elements?.Select(Code).ToArray() });
                    // (a new array's cells are all in hand)
                    if (_p.UsesCells) Emit(new KAssign { Var = "cells", Value = new KOp("store", new KVar("cells"), new KVar(n.Var), new KLit("(lambda i$: int :: 1.0)")) });
                    return;
                case KCall c:
                    Call(c, decreases);
                    return;
                case KAssumeInvariant ai:
                {
                    var o = Code(ai.Obj);
                    if (HasObjectInvariant(ai.Type) && Invariant(ai.Type, o) is KExpr inv) Assume(new KOp("==>", Code(ai.When), new KOp("||", new KOp("==", o, new KLit("null")), inv)));
                    return;
                }
                case KAssume a:
                    Emit(new KAssume { Cond = Code(a.Cond) });
                    return;
                case KSpecStmt ss:
                {
                    // (a permission as a condition: in hand)
                    _held = true;
                    KExpr term;
                    List<KExpr> wf;
                    try { term = Spec(ss.Spec, out wf); }
                    finally { _held = false; }
                    Facts();
                    if (!ss.Free) WellDefined(wf, ss.ArgumentAt, null);
                    if (ss.Assume) Assume(term);
                    else Assert(term, At("CSV1004", ss.At, $"assertion '{ss.ArgumentAt}'"));
                    return;
                }
                default:
                    Emit(s);
                    return;
            }
        }

        /// <summary>A postcondition at a return: of the parameters the body assigns, their values now (in old(...), at entry).</summary>
        private KExpr AtReturn(KExpr e) => _p.AssignedParams.Count == 0 ? e : MathTerms.Map(e, x => x switch
        {
            KOp { Op: "old" } => x,
            KVar v when _p.AssignedParams.TryGetValue(v.Name, out var now) => new KVar(now),
            _ => null,
        });
    }
}
