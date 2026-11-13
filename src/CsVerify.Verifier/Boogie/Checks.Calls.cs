using System;
using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using static CsVerify.Verifier.Boogie.KernelTypes;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>Calls: arguments, the callee's precondition, what holds after; old(...) at entry and before a call; joins.</summary>
    internal sealed partial class Checks
    {
        private void Call(KCall c, List<KExpr> decreases)
        {
            if (c.Phase == 2) { Join(c); return; }
            var callee = c.Callee;
            KExpr receiver = null;
            if (c.Receiver != null)
            {
                receiver = Code(c.Receiver);
                // (a struct's member: its receiver is a value, never null)
                if (!c.ReceiverIsThis && !IsStruct(callee.ContainingType)) Assert(new KOp("!=", receiver, new KLit("null")), NullAt(c.At, c.ReceiverAt, $"'{c.ReceiverAt}' might be null in '{c.At}'"));
            }
            var args = Arguments(callee, c.Args, c.ArgsAt);
            Termination(c, receiver, args, decreases);
            // the views it gets are handed over: whole, their invariants holding (a method of an [Owned] class gets its receiver's)
            bool ownedReceiver = receiver != null && IsOwnedClass(callee.ContainingType) && !_program.ContractOf(callee).IsPure;
            if (ownedReceiver)
            {
                Assert(new KOp("||", Whole(receiver), Lent(receiver)), At("CSV1016", c.At, $"'{c.At}' changes an [Owned] {callee.ContainingType.Name} without holding its view (Own<{callee.ContainingType.Name}>, with no read shares out) or a frame lent to it"));
                ProveInvariant(callee.ContainingType, receiver, c.At, $"when '{callee.Name}' is called on it");
            }
            // (a share, or a view lent read-only: whoever gets it relies on the invariant; a share by value goes with it)
            foreach (var param in callee.Parameters.Where(HoldsShare))
            {
                var x = args[param.Ordinal];
                ProveInvariant(ViewOf(param.Type), x, c.ArgsAt[param.Ordinal], $"when its view is handed to '{callee.Name}'");
                if (IsShare(param.Type) && param.RefKind == RefKind.None) Shares(x, -1);
            }
            // (a package goes with its views: by value for good, by ref until it comes back)
            foreach (var param in callee.Parameters.Where(x => IsPackage(x.Type) && x.RefKind is RefKind.None or RefKind.Ref))
                foreach (var f in PackageViews(param.Type))
                    Emit(new KMapUpdate { Map = "pkg", Ref = new KOp(FieldFunction(f), args[param.Ordinal]), Value = new KLit("false") });
            foreach (var param in callee.Parameters.Where(HoldsView))
            {
                var x = args[param.Ordinal];
                ProveInvariant(ViewOf(param.Type), x, c.ArgsAt[param.Ordinal], $"when its view is handed to '{callee.Name}'");
                Assert(Whole(x), At("CSV1016", c.ArgsAt[param.Ordinal], $"'{c.ArgsAt[param.Ordinal]}' might not be whole: join its read shares back (Own.Unshare) and get back any fields given away before handing the view over"));
                Emit(new KMapUpdate { Map = "perm", Ref = x, Value = new KLit("false") });
            }
            // the permissions its preconditions ask for are given to it; what the caller keeps, the call can't change
            var sig = _program.Signature(callee);
            var given = Given(callee, receiver, args);
            bool pure = _program.ContractOf(callee).IsPure;
            // (what reading its preconditions here gives: the unfoldings of functions under their quantifiers)
            foreach (var r in sig.Requires)
            {
                _facts.Clear();
                Subst(Spec(r.Expr, out _), given);
                foreach (var f in _facts.ToList()) Assume(Subst(f, given));
                _facts.Clear();
            }
            // (a tree it borrows through Spec.Modifies: its root's view in hand here, or a tree this method borrows)
            foreach (var root in sig.LentRoots)
            {
                var x = Subst(Spec(root, out _), given);
                _facts.Clear();
                Assert(new KOp("||", Whole(x), Lent(x)), At("CSV1016", c.At, $"'{callee.Name}' borrows a tree through Spec.Modifies, but its root's view is not in hand here"));
            }
            // (a frame of ours: the callee's within it, or it changes nothing a frame would tell)
            if (_p.Frame != null && !pure)
            {
                if (sig.Frame == null)
                {
                    Emit(new KAssert { Cond = new KLit("false"), UnlessWritesArrays = callee, UnlessKind = "arrays",
                                       Check = At("CSV1017", c.At, $"'{callee.Name}' may write arrays but has no Spec.Modifies frame, so this method's Spec.Modifies cannot be checked") });
                    Emit(new KAssert { Cond = new KLit("false"), UnlessWritesArrays = callee, UnlessKind = "fields",
                                       Check = At("CSV1017", c.At, $"'{callee.Name}' may write fields but has no Spec.Modifies frame, so this method's Spec.Modifies cannot be checked") });
                }
                else
                {
                    var theirs = Subst(Spec(sig.Frame, out _), given);
                    _facts.Clear();
                    var r = new KVar("r$");
                    Emit(new KAssert
                    {
                        Cond = new KQuant { Forall = true, Var = "r$", Type = "Ref", Range = null, Body = new KOp("==>", new KOp("sel", theirs, r),
                            new KOp("||", new KOp("sel", new KVar("w$entry"), r), new KOp("!", new KOp("sel", new KVar("alloc$entry"), r)))) },
                        UnlessWritesArrays = callee, UnlessKind = "any",
                        Check = At("CSV1017", c.At, $"Spec.Modifies of '{callee.Name}' might not be within this method's"),
                    });
                }
            }
            var gave = new List<(KExpr, KExpr)>();
            if (_p.UsesPerm && !pure) foreach (var r in sig.Requires) Exhale(r.Expr, given, c.At, gave);
            bool cellCall = _p.UsesCells && !pure && NamesCells(sig.Requires.Concat(sig.Ensures).Select(x => x.Expr));
            // (in array mode, a call that may write any array: which cells it writes is unknown)
            if (_p.ArrayMode && !cellCall && !pure)
                Emit(new KAssert { Cond = new KLit("false"), UnlessWritesArrays = callee, Check = At("CSV1016", c.At, $"'{callee.Name}' may write any array: give it a contract with Spec.Acc for the cells it writes") });
            // (a task's or thread's start: its preconditions checked here, as no Boogie call will; it returns at its join)
            if (c.Phase == 1)
            {
                foreach (var r in sig.Requires)
                {
                    var math = Subst(Spec(r.Expr, out _), given);
                    _facts.Clear();
                    Assert(math, At("CSV1001", c.At, $"'{c.At}' might throw: its precondition (precondition '{r.At}' of '{callee.Name}') might not hold"));
                }
                c.MathReceiver = receiver; c.MathArgs = args; c.GivenMap = given; c.Gave = gave; c.CellCall = cellCall; c.Pure = pure;
                return;
            }
            var frame = _p.UsesPerm ? new KCallFrame { Id = _frames++, Receiver = ownedReceiver ? receiver : null, Callee = callee, Cells = cellCall, Given = gave, Fields = _p.UsesFields } : null;
            // (what its preconditions say of snapshots: checked here, as Boogie's requires can't name them)
            if (_p.UsesPerm)
                foreach (var r in sig.Requires)
                {
                    var math = Subst(Spec(r.Expr, out _), given);
                    _facts.Clear();
                    if (Mentions(math, Snaps)) Assert(math, At("CSV1001", c.At, $"'{c.At}': its precondition '{r.At}'"));
                }
            // (where exceptions are seen: or it throws, and gives back only what its EnsuresOnThrow says)
            if (c.ThrowsTo != null)
                Emit(new KFork { Call = new KCall { Callee = callee, Receiver = receiver, Args = args, RefOuts = c.RefOuts }, Target = c.ThrowsTo });
            if (frame != null) Emit(frame);
            Emit(new KCall { Callee = callee, Receiver = receiver, ReceiverIsThis = c.ReceiverIsThis, ReceiverAt = c.ReceiverAt, Args = args, Result = c.Result, ThisOut = c.ThisOut, At = c.At, ArgsAt = c.ArgsAt,
                             RefOuts = c.RefOuts, Check = At("CSV1001", c.At, $"'{c.At}'") });
            AfterCall(c, callee, receiver, given, frame, sig, pure, ownedReceiver);
        }

        /// <summary>A task's or thread's join: its call, of its twin whose preconditions were checked at its start; what it gives back is in hand.</summary>
        private void Join(KCall c)
        {
            var st = c.Started;
            var callee = c.Callee;
            var sig = _program.Signature(callee);
            var frame = _p.UsesPerm ? new KCallFrame { Id = _frames++, Receiver = null, Callee = callee, Cells = st.CellCall, Given = st.Gave, Fields = _p.UsesFields } : null;
            if (frame != null) Emit(frame);
            Emit(new KCall { Callee = callee, Receiver = st.MathReceiver, ReceiverIsThis = st.ReceiverIsThis, ReceiverAt = st.ReceiverAt, Args = st.MathArgs, Result = c.Result, At = c.At,
                             ArgsAt = st.ArgsAt, RefOuts = c.RefOuts, Check = At("CSV1001", c.At, $"'{c.At}'"), Phase = 2 });
            AfterCall(c, callee, st.MathReceiver, st.GivenMap, frame, sig, st.Pure, false);
        }

        private void AfterCall(KCall c, IMethodSymbol callee, KExpr receiver, Dictionary<string, KExpr> given, KCallFrame frame, KProcedure sig, bool pure, bool ownedReceiver)
        {
            // and the views it gives back are in hand again, their invariants holding
            foreach (var (ordinal, var) in c.RefOuts.Where(x => IsView(callee.Parameters[x.param].Type)))
            {
                var v = new KVar(var);
                Assume(new KOp("!=", v, new KLit("null")));
                AssumeInvariant(ViewOf(callee.Parameters[ordinal].Type), v);
                Receive(v);
            }
            if (ownedReceiver) AssumeInvariant(callee.ContainingType, receiver);
            if (c.Result != null && Returns(callee) != null) ObjectInvariant(new KVar(c.Result), Returns(callee));
            foreach (var (ordinal, var) in c.RefOuts) ObjectInvariant(new KVar(var), callee.Parameters[ordinal].Type);
            // (the packages it gives back: its result, and its ref and out arguments)
            foreach (var (ordinal, var) in c.RefOuts.Where(x => IsPackage(callee.Parameters[x.param].Type))) Arrive(new KVar(var), callee.Parameters[ordinal].Type);
            if (c.Result != null && IsPackage(Returns(callee))) Arrive(new KVar(c.Result), Returns(callee));
            if (frame != null)
            {
                Emit(new KCallFrame { Id = frame.Id, After = true, Receiver = frame.Receiver, Callee = callee, Maps = frame.Maps, Cells = frame.Cells, Given = frame.Given, ElementMaps = frame.ElementMaps, Fields = frame.Fields, FieldIds = frame.FieldIds });
                // and those its postconditions give back are in hand (its result and ref and out arguments, as they came back)
                var back = new Dictionary<string, KExpr>(given);
                if (c.Result != null) back["result"] = new KVar(c.Result);
                if (c.ThisOut != null) back["this"] = new KVar(c.ThisOut);
                foreach (var (ordinal, var) in c.RefOuts) back[Local(callee.Parameters[ordinal])] = new KVar(var);
                _old = x => OldBefore(x, frame);
                try { if (!pure) foreach (var e in sig.Ensures) Inhale(e.Expr, back, null); }
                finally { _old = null; }
                foreach (var e in sig.Ensures)
                {
                    var math = Subst(Spec(e.Expr, out _), back);
                    _facts.Clear();
                    if (Mentions(math, Snaps)) Assume(OldBefore(math, frame));
                }
            }
        }

        /// <summary>old(...) of a procedure's snapshots is of those it had at entry.</summary>
        private static KExpr OldAtEntry(KExpr e) => e switch
        {
            KOp { Op: "old" } old => new KOp("old", Subst(old.Args[0], new Dictionary<string, KExpr> { ["psnap"] = new KVar("psnap$entry") })),
            KOp op => new KOp(op.Op, op.Args.Select(OldAtEntry).ToArray()),
            KQuant q => new KQuant { Forall = q.Forall, Var = q.Var, Type = q.Type, Range = q.Range == null ? null : OldAtEntry(q.Range), Body = OldAtEntry(q.Body), Trigger = q.Trigger?.Select(t => OldAtEntry(t)).ToArray() },
            // (an old(...) in a function's argument: Key(t, Spec.Old(Count(t))))
            KFnApp f => new KFnApp { Callee = f.Callee, Function = f.Function, Plain = f.Plain, MapsAt = f.MapsAt, Layer = f.Layer, Fields = f.Fields, Args = f.Args.Select(OldAtEntry).ToArray(), Snap = f.Snap == null ? null : OldAtEntry(f.Snap) },
            _ => e,
        };

        /// <summary>A callee's postcondition, in the caller after the call: old(...) of its snapshots is of the caller's before it (and of nothing else, here).</summary>
        private static KExpr OldBefore(KExpr e, KCallFrame frame) => e switch
        {
            KOp { Op: "old" } old => Before(old.Args[0], frame),
            KOp op => new KOp(op.Op, op.Args.Select(a => OldBefore(a, frame)).ToArray()),
            KQuant q => new KQuant { Forall = q.Forall, Var = q.Var, Type = q.Type, Range = q.Range == null ? null : OldBefore(q.Range, frame), Body = OldBefore(q.Body, frame), Trigger = q.Trigger?.Select(t => OldBefore(t, frame)).ToArray() },
            KFnApp f => new KFnApp { Callee = f.Callee, Function = f.Function, Plain = f.Plain, MapsAt = f.MapsAt, Layer = f.Layer, Fields = f.Fields, Args = f.Args.Select(a => OldBefore(a, frame)).ToArray(), Snap = f.Snap == null ? null : OldBefore(f.Snap, frame) },
            _ => e,
        };

        /// <summary>What a callee's old(...) reads, as it was just before the call: the snapshots the frame took then.</summary>
        private static KExpr Before(KExpr e, KCallFrame frame)
        {
            switch (e)
            {
                case KVar v when v.Name == "psnap": return new KVar($"s{frame.Id}$psnap");
                case KVar v when v.Name.StartsWith("$"):
                    frame.OldGlobals.Add(v.Name);
                    return new KVar($"s{frame.Id}{v.Name}");
                case KOp op: return new KOp(op.Op, op.Args.Select(a => Before(a, frame)).ToArray());
                case KQuant q: return new KQuant { Forall = q.Forall, Var = q.Var, Type = q.Type, Range = q.Range == null ? null : Before(q.Range, frame), Body = Before(q.Body, frame), Trigger = q.Trigger?.Select(t => Before(t, frame)).ToArray() };
                case KFnApp f when f.Snap != null: return new KFnApp { Callee = f.Callee, Function = f.Function, Plain = f.Plain, MapsAt = f.MapsAt, Args = f.Args.Select(a => Before(a, frame)).ToArray(), Snap = Before(f.Snap, frame) };
                // (a function of the memory, as it was: of the frame's snapshots of every map it takes)
                case KFnApp f when !f.Plain:
                    foreach (var map in ElementTypes.Select(ElementMap).Concat(f.Fields)) frame.OldGlobals.Add(map);
                    return new KFnApp { Callee = f.Callee, Function = f.Function, Plain = f.Plain, Layer = f.Layer, Fields = f.Fields, Args = f.Args.Select(a => Before(a, frame)).ToArray(), MapsAt = $"s{frame.Id}" };
                case KFnApp f:
                    return new KFnApp { Callee = f.Callee, Function = f.Function, Plain = true, Args = f.Args.Select(a => Before(a, frame)).ToArray() };
                default: return e;
            }
        }

        /// <summary>A call's arguments, each checked, then not null where its parameter may not be (CSV1014).</summary>
        private KExpr[] Arguments(IMethodSymbol callee, KExpr[] given, SyntaxNode[] at)
        {
            var args = new KExpr[given.Length];
            for (int k = 0; k < args.Length; k++)
            {
                args[k] = Code(given[k]);
                var param = callee != null && k < callee.Parameters.Length ? callee.Parameters[k] : null;
                if (param != null && param.RefKind != RefKind.Out && IsNullable(param.Type) && NotNullable(param.Type))
                    Assert(new KOp("!=", args[k], new KLit("null")), At("CSV1014", at[k], $"'{at[k]}' might be null, but parameter '{param.Name}' of '{callee.Name}' is not nullable"));
            }
            return args;
        }
    }
}
