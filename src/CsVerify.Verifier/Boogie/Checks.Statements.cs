using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using static CsVerify.Verifier.Boogie.KernelTypes;
using static CsVerify.Verifier.Boogie.MOp;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>Statements: each kernel statement's obligations; a return's postconditions.</summary>
    internal sealed partial class Checks
    {
        /// <summary>
        /// A return: the invariants of what it gives back holding; what may not be null not null; the permissions its
        /// postconditions give back in hand; the postconditions well-defined and holding, here.
        /// </summary>
        private void Return(KReturn ret, List<Clause> ensures)
        {
            InvariantsAtReturn(ret);
            NotNullAtReturn(ret);
            // the permissions the postconditions give back are in hand
            if (_p.UsesPerm)
            {
                _old = OldAtEntry;
                try
                {
                    foreach (var e in _rawEnsures)
                    {
                        Exhale(e, null, ret.At, null);
                    }
                }
                finally
                {
                    _old = null;
                }
            }
            var before = new List<MExpr>();
            foreach (var e in ensures)
            {
                foreach (var f in e.Facts)
                {
                    Assume(AtReturn(f));
                }
                WellDefined(e.Wf.Select(AtReturn).ToList(), e.Source.At, before);
                Assert(AtReturn(e.Math), At("CSV1002", ret.At, $"postcondition '{e.Source.At}' might not hold on this return path"));
                before.Add(AtReturn(e.Math));
            }
        }

        /// <summary>The views given back hold their invariants again; a constructor's object, its (an immutable object's: established by it).</summary>
        private void InvariantsAtReturn(KReturn ret)
        {
            var m = _p.Method;
            foreach (var param in m.Parameters.Where(x => IsView(x.Type) && x.RefKind is RefKind.Ref or RefKind.Out))
            {
                ProveInvariant(ViewOf(param.Type), new MVar(Local(param)), ret.At, $"when the view '{param.Name}' is given back");
            }
            if (_p.ThisIsView && !_p.IsCtor)
            {
                ProveInvariant(m.ContainingType, new MVar("this"), ret.At, $"when '{m.Name}' returns");
            }
            if (_p.IsCtor && HasObjectInvariant(m.ContainingType))
            {
                ProveInvariant(m.ContainingType, new MVar("this"), ret.At, $"when the constructor of {m.ContainingType.Name} returns");
            }
        }

        /// <summary>
        /// What its types say may not be null, not null at a return: a ref or out parameter; a constructor's fields (but
        /// the required ones, which its callers set); the result.
        /// </summary>
        private void NotNullAtReturn(KReturn ret)
        {
            var m = _p.Method;
            foreach (var param in m.Parameters.Where(x => x.RefKind is RefKind.Ref or RefKind.Out && IsNullable(x.Type) && NotNullable(x.Type)))
            {
                Assert(NotNull(new MVar(Local(param))), At("CSV1014", ret.At, $"'{param.Name}' might be null on return, but its type '{param.Type}' is not nullable"));
            }
            if (_p.IsCtor)
            {
                foreach (var field in InstanceFields(m.ContainingType).Where(NonNullField))
                {
                    if (!IsRequired(field) || m.GetAttributes().Any(a => a.AttributeClass?.Name == "SetsRequiredMembersAttribute"))
                    {
                        Assert(NotNull(Sel(FieldMap(field), new MVar("this"))),
                            At("CSV1014", ret.At, $"field '{field.Name}' is not nullable, but might be null when the constructor of {m.ContainingType.Name} returns"));
                    }
                }
            }
            if (Returns(m) != null && IsNullable(Returns(m)) && NotNullable(Returns(m)))
            {
                Assert(NotNull(new MVar("result")), At("CSV1014", ret.At, $"'{m.Name}' might return null, but its return type '{m.ReturnType}' is not nullable" +
                    NullReasons(ret.At is Microsoft.CodeAnalysis.CSharp.Syntax.ReturnStatementSyntax rs ? rs.Expression : ret.At is Microsoft.CodeAnalysis.CSharp.Syntax.ArrowExpressionClauseSyntax ar ? ar.Expression : ret.At)));
            }
        }

        // ------------------------------------------------------------------ statements

        private void Statement(KStmt s, List<MExpr> decreases)
        {
            switch (s)
            {
                case KAssign a:
                {
                    var value = Code(a.Value);
                    if (a.NotNullAt != null)
                    {
                        Assert(NotNull(value), At("CSV1014", a.NotNullAt, $"'{a.NotNullAt}' might store null, but '{a.NotNullName}' is not nullable"));
                    }
                    Emit(new MAssign
                    {
                        Var = a.Var,
                        Value = value,
                    });
                    return;
                }
                case KFieldStore fs:
                {
                    FieldStore(fs);
                    return;
                }
                case KOwn { Kind: "new" } own:
                {
                    ViewOfNew(own);
                    return;
                }
                case KOwn { Kind: "take" } take:
                {
                    Take(take);
                    return;
                }
                case KOwn { Kind: "give" } give:
                {
                    Give(give);
                    return;
                }
                case KOwn { Kind: "fromacc" } from:
                {
                    var o = Code(from.Obj);
                    Assert(Held(o), At("CSV1016", from.At, $"'{from.At}' has no permission in hand to make a view of"));
                    Emit(new MAssign
                    {
                        Var = from.View,
                        Value = o,
                    });
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
                    {
                        Assert(NotNull(v), At("CSV1013", th.At, $"'{th.At}' might be null: throwing it would throw a NullReferenceException"));
                    }
                    if (th.Seen)
                    {
                        Emit(new MAssign
                        {
                            Var = "ex$",
                            Value = v,
                        });
                    }
                    return;
                }
                case KInvoke iv:
                {
                    Invoke(iv);
                    return;
                }
                case KHavocAll ha when ha.Unless != null:
                    Emit(new MHavocAll
                    {
                        Unless = Code(ha.Unless),
                        ProgramState = ha.ProgramState,
                    });
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
                    Lambda(lam);
                    return;
                }
                case KAwait aw:
                    Emit(new MAwait
                    {
                        Keep = aw.Keep,
                        When = aw.When == null ? null : Code(aw.When),
                        Cells = _p.UsesCells,
                        Perm = _p.UsesPerm,
                    });
                    return;
                case KThrowExit _:
                    // leaving by an exception: its own clauses for the exception's type hold
                    foreach (var (type, cond, at) in _p.ThrowEnsures)
                    {
                        var holds = OldAtEntry(Spec(cond, out _));
                        _facts.Clear();
                        Assert(new MOp("==>", Is(new MVar("ex$"), type), holds), At("CSV1002", at, $"postcondition on throw '{at}' might not hold when '{_p.Method.Name}' throws"));
                    }
                    return;
                case KOwn { Kind: "pack" } pack:
                {
                    // a view packed: its invariant holds, and it is the package's now (not in hand to write with)
                    var x = Code(pack.Obj);
                    ProveInvariant(pack.Type, x, pack.At, $"when it is packed into {pack.Into.Name}");
                    Emit(new MMapUpdate
                    {
                        Map = "perm",
                        Ref = x,
                        Value = MLit.False,
                    });
                    Emit(new MMapUpdate
                    {
                        Map = "pkg",
                        Ref = x,
                        Value = MLit.True,
                    });
                    return;
                }
                case KOwn { Kind: "unpack" } unpack:
                {
                    Unpack(unpack);
                    return;
                }
                case KOwn { Kind: "share" } share:
                    // Own.Share(ref v, out s): s is a share of v's object; v keeps the rest, so in sum nothing changes here
                    Emit(new MAssign
                    {
                        Var = share.View,
                        Value = Code(share.Obj),
                    });
                    return;
                case KOwn { Kind: "unshare" } unshare:
                {
                    var v = Code(unshare.Obj);
                    Assert(Eq(Code(unshare.Value), v), At("CSV1016", unshare.At, $"'{unshare.ValueAt}' might not be a share of '{unshare.SlotAt}'"));
                    return;
                }
                case KOwn { Kind: "dropshare" } dropShare:
                    Shares(Code(dropShare.Obj), -1);
                    return;
                case KOwn { Kind: "drop" } drop:
                    Emit(new MMapUpdate
                    {
                        Map = "perm",
                        Ref = Code(drop.Obj),
                        Value = MLit.False,
                    });
                    return;
                case KNewObj n:
                {
                    NewObject(n);
                    return;
                }
                case KStore { Memory: true } ms:
                    Emit(new MStore
                    {
                        Array = MLit.Null,
                        Index = Code(ms.Index),
                        Value = Code(ms.Value),
                        ArrayType = ms.ArrayType,
                        At = ms.At,
                        ArrayAt = ms.ArrayAt,
                    });
                    return;
                case KRow row when row.Ref == null:
                    Emit(new MRow
                    {
                        Map = row.Map,
                        Value = MathTerms.Math(row.Value),
                        At = row.At,
                    });
                    return;
                case KRow row:
                {
                    RowWritten(row);
                    return;
                }
                case KFill fill:
                    Emit(new MFill
                    {
                        Map = fill.Map,
                        Lo = Code(fill.Lo),
                        Hi = Code(fill.Hi),
                        Value = Code(fill.Value),
                    });
                    return;
                case KMemCells mc:
                    if (!_p.UsesCells)
                    {
                        return;
                    }
                    foreach (var c in mc.Cells)
                    {
                        var cells = new MCells
                        {
                            Arr = MLit.Null,
                            Lo = Code(c.Lo),
                            Hi = Code(c.Hi),
                            At = c.At,
                        };
                        if (mc.Grant)
                        {
                            InhaleCells(MLit.True, cells);
                        }
                        else
                        {
                            ChangeCells(MLit.True, cells, "-");
                        }
                    }
                    return;
                case KStore st:
                {
                    ElementStore(st);
                    return;
                }
                // (a library call's arrays: without cell permissions, where it may write, any; with them, those it's handed,
                // all of whose cells it may read or write, so all must be held, and only those change)
                case KLibraryArrays la:
                {
                    LibraryArrays(la);
                    return;
                }
                case KNew n:
                    Emit(new MNew
                    {
                        Var = n.Var,
                        ArrayType = n.ArrayType,
                        Size = Code(n.Size),
                        Elements = n.Elements?.Select(Code).ToArray(),
                    });
                    // (a new array's cells are all in hand)
                    if (_p.UsesCells)
                    {
                        Emit(new MAssign
                        {
                            Var = "cells",
                            Value = Store("cells", new MVar(n.Var), new MLit("(lambda i$: int :: 1.0)")),
                        });
                    }
                    return;
                case KCall c:
                    Call(c, decreases);
                    return;
                case KAssumeInvariant ai:
                {
                    var o = Code(ai.Obj);
                    if (HasObjectInvariant(ai.Type) && Invariant(ai.Type, o) is MExpr inv)
                    {
                        Assume(new MOp("==>", Code(ai.When), OrElse(IsNull(o), inv)));
                    }
                    return;
                }
                case KAssume a:
                    Emit(new MAssume { Cond = Code(a.Cond) });
                    return;
                case KSpecStmt ss:
                {
                    SpecStatement(ss);
                    return;
                }
                // (what has no obligation of its own: the same at level 2)
                case KHavoc h:
                    Emit(new MHavoc { Var = h.Var });
                    return;
                case KHavocAll ha:
                    Emit(new MHavocAll { ProgramState = ha.ProgramState });
                    return;
                case KKeep k:
                    Emit(new MKeep
                    {
                        Id = k.Id,
                        After = k.After,
                        Keep = k.Keep,
                    });
                    return;
                case KAtomicSteps st:
                    Emit(new MAtomicSteps
                    {
                        Head = st.Head,
                        Maps = st.Maps,
                    });
                    return;
                case KNewExc ne:
                    Emit(new MNewExc
                    {
                        Var = ne.Var,
                        Type = ne.Type,
                    });
                    return;
                // (a way out that throws, where its condition, mathematics, fails)
                case KFork f when f.Call == null:
                    Emit(new MFork
                    {
                        Overflow = MathTerms.Math(f.Overflow),
                        Target = f.Target,
                        Exception = f.Exception,
                    });
                    return;
                default: throw new NotTranslated("a kernel statement Checks doesn't know: " + s.GetType().Name);
            }
        }

        private void FieldStore(KFieldStore fs)
        {
            var value = Code(fs.Value);
            var o = fs.Instance == null ? MLit.Null : Code(fs.Instance);
            if (fs.Instance != null && !fs.OnThis)
            {
                Assert(NotNull(o), NullAt(fs.At, fs.InstanceAt, $"'{fs.InstanceAt}' might be null in '{fs.At}'"));
            }
            if (fs.Instance != null && !IsOwnedField(fs.Field))
            {
                WithinFrame(o, fs.At);
            }
            if (IsOwnedField(fs.Field))
            {
                Assert(OrElse(_p.UsesFields ? OrElse(Whole(o), FieldHeld(o, fs.Field)) : Whole(o), Lent(o)), At("CSV1016", fs.At, $"'{fs.At}' changes an [Owned] {fs.Field.ContainingType.Name} without holding its view (Own<{fs.Field.ContainingType.Name}>, with no read shares out) or a frame lent to it"));
            }
            if (NonNullField(fs.Field))
            {
                Assert(NotNull(value), At("CSV1014", fs.At, $"'{fs.At}' might store null, but field '{fs.Field.Name}' is not nullable"));
            }
            Emit(new MFieldStore
            {
                Field = fs.Field,
                Instance = o,
                Value = value,
                OnThis = fs.OnThis,
                At = fs.At,
                InstanceAt = fs.InstanceAt,
            });
            return;
        }

        private void ViewOfNew(KOwn own)
        {
            // a view is made of a new object: its invariant holds, and nobody else has its view
            var o = Code(own.Obj);
            if (!own.Unchecked)
            {
                ProveInvariant(own.Type, o, own.At, "when its view is made");
            }
            Emit(new MAssign
            {
                Var = own.View,
                Value = o,
            });
            // (a new tree of its own)
            if (KernelTypes.Trees)
            {
                _p.Modifies.Add("$root");
                _p.AnyWrites.Add("$root");
                Emit(new MMapUpdate
                {
                    Map = "$root",
                    Ref = o,
                    Value = o,
                });
            }
            Receive(o);
            return;
        }

        private void Take(KOwn take)
        {
            // Own.Take(ref c.F, out v): the object c.F owns comes out with its view, its invariant held at rest; c.F is null;
            // c's tree splits: what was below the object is now in its own tree, or still in c's
            var c = Code(take.Obj);
            Assert(Whole(c), At("CSV1016", take.At, $"'{take.SlotAt}' changes an [Owned] {take.Field.ContainingType.Name} without holding its view"));
            var x = Sel(FieldMap(take.Field), c);
            Assert(NotNull(x), At("CSV1016", take.At, $"'{take.SlotAt}' might be null: there is nothing to take"));
            Emit(new MAssign
            {
                Var = take.View,
                Value = x,
            });
            var child = new MVar(take.View);
            // (what an [Owns] field holds is in its container's tree, and isn't its root)
            var root = new MVar("$root");
            Assume(AndAlso(Eq(new MOp("sel", root, child), new MOp("sel", root, c)), Ne(new MOp("sel", root, child), child)));
            var siblings = InstanceFields(take.Field.ContainingType).Where(g => SpecSymbols.IsOwnsField(g) && !SymbolEqualityComparer.Default.Equals(g, take.Field.OriginalDefinition)).Select(FieldMap).ToList();
            // (and so is what the container's other [Owns] fields hold, each a different object: they stay in its tree)
            foreach (var g in siblings)
            {
                var held = Sel(g, c);
                Assume(OrElse(IsNull(held),
                    AndAlso(AndAlso(Eq(new MOp("sel", root, held), new MOp("sel", root, c)), Ne(new MOp("sel", root, held), held)),
                        Ne(held, child))));
            }
            Emit(new MFieldStore
            {
                Field = take.Field,
                Instance = c,
                OnThis = true,
                Value = MLit.Null,
                At = take.At,
                InstanceAt = take.At,
            });
            _p.Modifies.Add("$root"); _p.AnyWrites.Add("$root");
            if (!_p.Locals.Any(l => l.Name == "split$"))
            {
                _p.Locals.Add(new KLocal
                {
                    Name = "split$",
                    Raw = "[Ref]bool",
                });
            }
            Emit(new MRoots
            {
                Container = c,
                Child = child,
                Siblings = siblings,
            });
            AssumeInvariant(take.Type, child);
            Receive(child);
            return;
        }

        private void Give(KOwn give)
        {
            // Own.Give(ref c.F, x, v): x and its tree join c's under c.F, which must be empty; v, x's view, is handed over
            var c = Code(give.Obj);
            var x = Code(give.Value);
            var v = Code(give.ViewValue);
            Assert(Whole(c), At("CSV1016", give.At, $"'{give.SlotAt}' changes an [Owned] {give.Field.ContainingType.Name} without holding its view"));
            Assert(IsNull(Sel(FieldMap(give.Field), c)), At("CSV1016", give.At, $"'{give.SlotAt}' might still own an object: take it first"));
            Assert(Eq(v, x), At("CSV1016", give.At, $"'{give.ViewAt}' might not be the view of '{give.ValueAt}'"));
            Assert(Whole(x), At("CSV1016", give.At, $"'{give.ValueAt}' might have read shares out: join them back (Own.Unshare) first"));
            Assert(Ne(Sel("$root", c), x), At("CSV1016", give.At, $"'{give.ValueAt}' might own the container: ownership would be a cycle"));
            ProveInvariant(give.Type, x, give.At, "when it is given to its owner");
            Emit(new MMapUpdate
            {
                Map = "perm",
                Ref = x,
                Value = MLit.False,
            });
            Emit(new MFieldStore
            {
                Field = give.Field,
                Instance = c,
                OnThis = true,
                Value = x,
                At = give.At,
                InstanceAt = give.At,
            });
            _p.Modifies.Add("$root"); _p.AnyWrites.Add("$root");
            Emit(new MRoots
            {
                Join = true,
                Container = c,
                Child = x,
            });
            return;
        }

        private void Invoke(KInvoke iv)
        {
            // (a call of a delegate: not null, and it accepts the arguments; what it gives is its $post)
            var d = Code(iv.Delegate);
            var args = iv.Args.Select(Code).ToArray();
            Assert(NotNull(d), NullAt(iv.At, iv.DelegateAt, $"'{iv.DelegateAt}' might be null in '{iv.At}'"));
            Assert(new MOp("$preS." + iv.Key, new[] { d, new MOp("$state") }.Concat(args).ToArray()),
                At("CSV1001", iv.At, $"'{iv.DelegateAt}' might not accept these arguments: say what it accepts with Spec.Requires(Spec.Pre({iv.DelegateAt}, ...))"));
            Emit(new MInvoke
            {
                Result = iv.Result,
                Delegate = d,
                Args = args,
                Key = iv.Key,
                At = iv.At,
                DelegateAt = iv.DelegateAt,
            });
            return;
        }

        private void Lambda(KLambda lam)
        {
            // (its facts are mathematics of its parameters and of what never changes)
            var r = new Dictionary<string, MExpr> { ["result"] = new MVar("q$r") };
            foreach (var kv in lam.Rename)
            {
                r[kv.Key] = MathTerms.Math(kv.Value);
            }
            MExpr M(KExpr x)
            {
                var v = Spec(x, out _);
                _facts.Clear();
                return v.Substitute(r);
            }
            Emit(new MLambda
            {
                Var = lam.Var,
                Key = lam.Key,
                Params = lam.Params,
                ResultType = lam.ResultType,
                NoChange = lam.NoChange,
                Steady = lam.Steady,
                Pre = lam.Pre == null ? null : M(lam.Pre),
                Posts = lam.Posts.Select(M).ToList(),
                PreS = lam.PreS == null ? null : M(lam.PreS),
                Reads = lam.Reads == null ? null : M(lam.Reads),
                Changes = lam.Changes == null ? null : M(lam.Changes),
                PostsS = lam.PostsS.Select(M).ToList(),
            });
            return;
        }

        private void Unpack(KOwn unpack)
        {
            // a view taken out of its package: in hand again, its invariant holding
            var x = Code(unpack.Obj);
            Assume(NotNull(x));
            Emit(new MMapUpdate
            {
                Map = "pkg",
                Ref = x,
                Value = MLit.False,
            });
            Emit(new MMapUpdate
            {
                Map = "perm",
                Ref = x,
                Value = MLit.True,
            });
            AssumeInvariant(unpack.Type, x);
            if (KernelTypes.Trees)
            {
                Assume(Eq(Sel("$root", x), x));
            }
            return;
        }

        private void NewObject(KNewObj n)
        {
            var args = Arguments(n.Ctor, n.Args, n.ArgsAt);
            // (a constructor exchanges permissions as any call does: about the new object, as this)
            var sig = n.Ctor != null && _p.UsesPerm ? _program.Signature(n.Ctor) : null;
            var given = sig == null ? null : Given(n.Ctor, new MVar(n.Var), args);
            if (sig != null)
            {
                foreach (var r in sig.Requires)
                {
                    Exhale(r.Expr, given, n.At, null);
                }
            }
            Emit(new MNewObj
            {
                Var = n.Var,
                Type = n.Type,
                Ctor = n.Ctor,
                Args = args,
                ArgsAt = n.ArgsAt,
                At = n.At,
                Check = n.Ctor == null ? null : At("CSV1001", n.At, $"'{n.At}'"),
            });
            if (sig != null)
            {
                foreach (var e in sig.Ensures)
                {
                    Inhale(e.Expr, given, null);
                }
            }
            // (what its constructor left in its reference fields is allocated: it could store nothing else)
            if (n.Ctor != null)
            {
                foreach (var f in InstanceFields(n.Type).Where(f => IsRef(FieldType(f)) && _p.Fields.Contains(f)))
                {
                    Assume(Allocated(new MVar(n.Var), Sel(FieldMap(f), new MVar(n.Var))));
                }
            }
            // (and its ghost sets of objects hold allocated ones)
            if (n.Ctor != null)
            {
                foreach (var f in InstanceFields(n.Type).Where(f => IsObjSet(IsGhost(FieldType(f)) ? GhostOf(FieldType(f)) : FieldType(f)) && _p.Fields.Contains(f)))
                {
                    Assume(new MOp("set.subset", Sel(FieldMap(f), new MVar(n.Var)), new MVar("$Alloc")));
                }
            }
            ObjectInvariant(new MVar(n.Var), n.Type);
            return;
        }

        private void RowWritten(KRow row)
        {
            var r = Code(row.Ref);
            if (row.At != null)
            {
                WithinFrame(r, row.At);
            }
            // (the program's write of a whole row, Array.Fill's say, under cell permissions: all its cells held)
            if (row.At != null && _p.UsesCells)
            {
                var i = new MVar("i$");
                Assert(OrElse(IsNull(r), MQuant.ForAll(
                    "i$",
                    Implies(AndAlso(new MOp("<=", MLit.Zero, i), new MOp("<", i, new MOp("len", r))), new MOp(">=", Cell(r, i), MLit.FullPermission)))),
                       At("CSV1016", row.At, $"'{row.At}' writes the whole array: this method needs Spec.Acc of all its cells"));
            }
            var v = Spec(row.Value, out _);
            _facts.Clear();
            Emit(new MRow
            {
                Map = row.Map,
                Ref = r,
                Value = v,
            });
            return;
        }

        private void ElementStore(KStore st)
        {
            var value = Code(st.Value);
            var a = Code(st.Array);
            var i = Code(st.Index);
            if (st.Unchecked)
            {
                if (!st.NoNull)
                {
                    Assert(NotNull(a), NullAt(st.At, st.ArrayAt, $"'{st.ArrayAt}' might be null in '{st.At}'"));
                }
            }
            else
            {
                InBounds(a, i, st.At, st.ArrayAt);
            }
            WithinFrame(a, st.At);
            if (_p.UsesCells)
            {
                Assert(new MOp(">=", Cell(a, i), MLit.FullPermission), At("CSV1016", st.At, $"'{st.At}' writes a cell this method has no Spec.Acc for"));
            }
            Emit(new MStore
            {
                Array = a,
                Index = i,
                Value = value,
                ArrayType = st.ArrayType,
                At = st.At,
                ArrayAt = st.ArrayAt,
            });
            return;
        }

        private void LibraryArrays(KLibraryArrays la)
        {
            if (!_p.UsesCells)
            {
                if (la.Write)
                {
                    foreach (var (map, fresh) in la.Fresh)
                    {
                        Emit(new MRow
                        {
                            Map = map,
                            Ref = null,
                            Value = new MVar(fresh),
                        });
                    }
                }
                return;
            }
            // (handed other objects, one that may write arrays may write those it reaches through them, whose cells this
            // method can't hold: CSV1016, and every array unknown after; one that only reads them, as any read)
            if (!la.Plain && la.Write)
            {
                Assert(MLit.False, At("CSV1016", la.At, $"'{la.At}' may write arrays it reaches through the objects it's handed, whose cells this method can't hold"), notAssumedAfter: true);
                foreach (var (map, fresh) in la.Fresh)
                {
                    Emit(new MRow
                    {
                        Map = map,
                        Ref = null,
                        Value = new MVar(fresh),
                    });
                }
                return;
            }
            foreach (var (array, map, row) in la.Arrays)
            {
                var a = Code(array);
                var i = new MVar("i$");
                var inRange = AndAlso(new MOp("<=", MLit.Zero, i), new MOp("<", i, new MOp("len", a)));
                Assert(OrElse(IsNull(a),
                               MQuant.ForAll(
                                   "i$",
                                   Implies(inRange, la.Write ? new MOp(">=", Cell(a, i), MLit.FullPermission) : new MOp(">", Cell(a, i), MLit.NoPermission)))),
                       At("CSV1016", la.At, la.Write ? $"'{la.At}' may write the array it's handed: this method needs Spec.Acc of all its cells"
                                                     : $"'{la.At}' reads the array it's handed: this method needs Spec.Acc or Spec.AccRead of all its cells"));
                if (!la.Write)
                {
                    continue;
                }
                Emit(new MHavoc { Var = row });
                Emit(new MRow
                {
                    Map = map,
                    Ref = a,
                    Value = new MVar(row),
                });
            }
            return;
        }

        private void SpecStatement(KSpecStmt ss)
        {
            // (a permission as a condition: in hand)
            _held = true;
            MExpr term;
            List<MExpr> wf;
            try
            {
                term = Spec(ss.Spec, out wf);
            }
            finally
            {
                _held = false;
            }
            Facts();
            if (!ss.Free)
            {
                WellDefined(wf, ss.ArgumentAt, null);
            }
            if (ss.Assume)
            {
                Assume(term);
            }
            else
            {
                Assert(term, At("CSV1004", ss.At, $"assertion '{ss.ArgumentAt}'"));
            }
            return;
        }

        /// <summary>A postcondition at a return: of the parameters the body assigns, their values now (in old(...), at entry).</summary>
        private MExpr AtReturn(MExpr e) => _p.AssignedParams.Count == 0 ? e : e.Rewrite(x => x switch
        {
            MOp { Op: "old" } => x,
            MVar v when _p.AssignedParams.TryGetValue(v.Name, out var now) => new MVar(now),
            _ => null,
        });
    }
}
