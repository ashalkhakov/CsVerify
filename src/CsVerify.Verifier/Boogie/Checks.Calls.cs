using System.Collections.Generic;
using System.Linq;
using Microsoft.CodeAnalysis;
using static CsVerify.Verifier.Boogie.KernelTypes;
using static CsVerify.Verifier.Boogie.MOp;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>Calls: arguments, the callee's precondition, what holds after; old(...) at entry and before a call; joins.</summary>
    internal sealed partial class Checks
    {
        /// <summary>A call, as Checks has it so far: the kernel's, its receiver and arguments made, what its contract is of them.</summary>
        private sealed class CallAt
        {
            public KCall C;
            public IMethodSymbol Callee;
            public MExpr Receiver;
            public MExpr[] Args;
            /// <summary>A method of an [Owned] class that isn't [Pure]: its receiver's view is handed over.</summary>
            public bool OwnedReceiver;
            public KProcedure Sig;
            /// <summary>Its parameters, the receiver and the arguments.</summary>
            public Dictionary<string, MExpr> Given;
            public bool Pure;
            /// <summary>The permissions its preconditions took, each under its condition.</summary>
            public List<(MExpr, MExpr)> Gave;
            /// <summary>It takes cells (its contract names some): the cells it was given are all it changes.</summary>
            public bool CellCall;
        }

        /// <summary>
        /// A call: its receiver and arguments checked; its termination; the views it gets handed over; what its preconditions
        /// say read, their permissions given, its frame within ours; then the call (or, a task's start, its preconditions
        /// checked here, and its join later); what it gives back.
        /// </summary>
        private void Call(KCall c, List<MExpr> decreases)
        {
            if (c.Phase == 2)
            {
                Join(c);
                return;
            }
            var call = new CallAt
            {
                C = c,
                Callee = c.Callee,
                Receiver = CallReceiver(c),
            };
            call.Args = Arguments(call.Callee, c.Args, c.ArgsAt);
            Termination(c, call.Receiver, call.Args, decreases);
            HandOverViews(call);
            // the permissions its preconditions ask for are given to it; what the caller keeps, the call can't change
            call.Sig = _program.Signature(call.Callee);
            call.Given = Given(call.Callee, call.Receiver, call.Args);
            call.Pure = _program.ContractOf(call.Callee).IsPure;
            ReadPreconditions(call);
            LentTrees(call);
            WithinOurFrame(call);
            GivePermissions(call);
            // (a task's or thread's start: its preconditions checked here, as no Boogie call will; it returns at its join)
            if (c.Phase == 1)
            {
                StartPreconditions(call);
                _started[c] = (call.Receiver, call.Args, call.Given, call.Gave, call.CellCall, call.Pure);
                return;
            }
            var frame = _p.UsesPerm ? new MCallFrame
            {
                Id = _frames++,
                Receiver = call.OwnedReceiver ? call.Receiver : null,
                Callee = call.Callee,
                Cells = call.CellCall,
                Given = call.Gave,
                Fields = _p.UsesFields,
            } : null;
            SnapshotPreconditions(call);
            // (where exceptions are seen: or it throws, and gives back only what its EnsuresOnThrow says)
            if (c.ThrowsTo != null)
            {
                Emit(new MFork
                {
                    Call = new MCall
                    {
                        Callee = call.Callee,
                        Receiver = call.Receiver,
                        Args = call.Args,
                        RefOuts = c.RefOuts,
                    },
                    Target = c.ThrowsTo,
                });
            }
            if (frame != null)
            {
                Emit(frame);
            }
            Emit(new MCall
            {
                Callee = call.Callee,
                Receiver = call.Receiver,
                ReceiverIsThis = c.ReceiverIsThis,
                ReceiverAt = c.ReceiverAt,
                Args = call.Args,
                Result = c.Result,
                ThisOut = c.ThisOut,
                At = c.At,
                ArgsAt = c.ArgsAt,
                RefOuts = c.RefOuts,
                Check = At("CSV1001", c.At, $"'{c.At}'"),
            });
            AfterCall(c, call.Callee, call.Receiver, call.Given, frame, call.Sig, call.Pure, call.OwnedReceiver);
        }

        /// <summary>A call's receiver, checked not null (a struct's member's is a value, never null; this is never null).</summary>
        private MExpr CallReceiver(KCall c)
        {
            if (c.Receiver == null)
            {
                return null;
            }
            var receiver = Code(c.Receiver);
            if (!c.ReceiverIsThis && !IsStruct(c.Callee.ContainingType))
            {
                Assert(NotNull(receiver), NullAt(c.At, c.ReceiverAt, $"'{c.ReceiverAt}' might be null in '{c.At}'"));
            }
            return receiver;
        }

        /// <summary>
        /// The views it gets are handed over: whole, their invariants holding (a method of an [Owned] class gets its
        /// receiver's); a share, or a view lent read-only, its invariant holding; a package's views go with it.
        /// </summary>
        private void HandOverViews(CallAt call)
        {
            var (c, callee, args) = (call.C, call.Callee, call.Args);
            call.OwnedReceiver = call.Receiver != null && IsOwnedClass(callee.ContainingType) && !_program.ContractOf(callee).IsPure;
            if (call.OwnedReceiver)
            {
                Assert(OrElse(Whole(call.Receiver), Lent(call.Receiver)), At("CSV1016", c.At, $"'{c.At}' changes an [Owned] {callee.ContainingType.Name} without holding its view (Own<{callee.ContainingType.Name}>, with no read shares out) or a frame lent to it"));
                ProveInvariant(callee.ContainingType, call.Receiver, c.At, $"when '{callee.Name}' is called on it");
            }
            // (a share, or a view lent read-only: whoever gets it relies on the invariant; a share by value goes with it)
            foreach (var param in callee.Parameters.Where(HoldsShare))
            {
                var x = args[param.Ordinal];
                ProveInvariant(ViewOf(param.Type), x, c.ArgsAt[param.Ordinal], $"when its view is handed to '{callee.Name}'");
                if (IsShare(param.Type) && param.RefKind == RefKind.None)
                {
                    Shares(x, -1);
                }
            }
            // (a package goes with its views: by value for good, by ref until it comes back)
            foreach (var param in callee.Parameters.Where(x => IsPackage(x.Type) && x.RefKind is RefKind.None or RefKind.Ref))
            {
                foreach (var f in PackageViews(param.Type))
                {
                    Emit(MMapUpdate.Of("pkg", new MOp(FieldFunction(f), args[param.Ordinal]), MLit.False));
                }
            }
            foreach (var param in callee.Parameters.Where(HoldsView))
            {
                var x = args[param.Ordinal];
                ProveInvariant(ViewOf(param.Type), x, c.ArgsAt[param.Ordinal], $"when its view is handed to '{callee.Name}'");
                Assert(Whole(x), At("CSV1016", c.ArgsAt[param.Ordinal], $"'{c.ArgsAt[param.Ordinal]}' might not be whole: join its read shares back (Own.Unshare) and get back any fields given away before handing the view over"));
                Emit(MMapUpdate.Of("perm", x, MLit.False));
            }
        }

        /// <summary>What reading its preconditions here gives: the unfoldings of functions under their quantifiers.</summary>
        private void ReadPreconditions(CallAt call)
        {
            foreach (var r in call.Sig.Requires)
            {
                _facts.Clear();
                Spec(r.Expr, out _).Substitute(call.Given);
                foreach (var f in _facts.ToList())
                {
                    Assume(f.Substitute(call.Given));
                }
                _facts.Clear();
            }
        }

        /// <summary>A tree it borrows through Spec.Modifies: its root's view in hand here, or a tree this method borrows.</summary>
        private void LentTrees(CallAt call)
        {
            foreach (var root in call.Sig.LentRoots)
            {
                var x = Spec(root, out _).Substitute(call.Given);
                _facts.Clear();
                Assert(OrElse(Whole(x), Lent(x)), At("CSV1016", call.C.At, $"'{call.Callee.Name}' borrows a tree through Spec.Modifies, but its root's view is not in hand here"));
            }
        }

        /// <summary>Under a frame of ours: the callee's within it, or it changes nothing a frame would tell (decided once the program's writes are).</summary>
        private void WithinOurFrame(CallAt call)
        {
            if (_p.Frame == null || call.Pure)
            {
                return;
            }
            var (c, callee) = (call.C, call.Callee);
            if (call.Sig.Frame == null)
            {
                Emit(MAssert.Of(
                    MLit.False,
                    unlessWritesArrays: callee,
                    unlessKind: "arrays",
                    check: At("CSV1017", c.At, $"'{callee.Name}' may write arrays but has no Spec.Modifies frame, so this method's Spec.Modifies cannot be checked")));
                Emit(MAssert.Of(
                    MLit.False,
                    unlessWritesArrays: callee,
                    unlessKind: "fields",
                    check: At("CSV1017", c.At, $"'{callee.Name}' may write fields but has no Spec.Modifies frame, so this method's Spec.Modifies cannot be checked")));
                return;
            }
            var theirs = Spec(call.Sig.Frame, out _).Substitute(call.Given);
            _facts.Clear();
            var r = new MVar("r$");
            Emit(MAssert.Of(
                MQuant.ForAll(
             "r$",
             "Ref",
             Implies(Sel(theirs, r),
             OrElse(Sel("w$entry", r), Not(Sel("alloc$entry", r))))),
                unlessWritesArrays: callee,
                unlessKind: "any",
                check: At("CSV1017", c.At, $"Spec.Modifies of '{callee.Name}' might not be within this method's")));
        }

        /// <summary>
        /// The permissions its preconditions ask for, given up (each must be in hand); whether it takes cells; in array mode,
        /// a call that may write any array, of cells not known, reported.
        /// </summary>
        private void GivePermissions(CallAt call)
        {
            var (c, callee, sig) = (call.C, call.Callee, call.Sig);
            call.Gave = new List<(MExpr, MExpr)>();
            if (_p.UsesPerm && !call.Pure)
            {
                foreach (var r in sig.Requires)
                {
                    Exhale(r.Expr, call.Given, c.At, call.Gave);
                }
            }
            call.CellCall = _p.UsesCells && !call.Pure && NamesCells(sig.Requires.Concat(sig.Ensures).Select(x => x.Expr));
            if (_p.ArrayMode && !call.CellCall && !call.Pure)
            {
                Emit(MAssert.Of(
                    MLit.False,
                    unlessWritesArrays: callee,
                    check: At("CSV1016", c.At, $"'{callee.Name}' may write any array: give it a contract with Spec.Acc for the cells it writes")));
            }
        }

        /// <summary>A task's or thread's start: its preconditions checked here, as no Boogie call will.</summary>
        private void StartPreconditions(CallAt call)
        {
            foreach (var r in call.Sig.Requires)
            {
                var math = Spec(r.Expr, out _).Substitute(call.Given);
                _facts.Clear();
                Assert(math, At("CSV1001", call.C.At, $"'{call.C.At}' might throw: its precondition (precondition '{r.At}' of '{call.Callee.Name}') might not hold"));
            }
        }

        /// <summary>What its preconditions say of snapshots: checked here, as Boogie's requires can't name them.</summary>
        private void SnapshotPreconditions(CallAt call)
        {
            if (!_p.UsesPerm)
            {
                return;
            }
            foreach (var r in call.Sig.Requires)
            {
                var math = Spec(r.Expr, out _).Substitute(call.Given);
                _facts.Clear();
                if (math.Mentions(Snaps))
                {
                    Assert(math, At("CSV1001", call.C.At, $"'{call.C.At}': its precondition '{r.At}'"));
                }
            }
        }

        /// <summary>A task's or thread's join: its call, of its twin whose preconditions were checked at its start; what it gives back is in hand.</summary>
        private void Join(KCall c)
        {
            var st = c.Started;
            var (receiver, args, given, gave, cellCall, pure) = _started[st];
            var callee = c.Callee;
            var sig = _program.Signature(callee);
            var frame = _p.UsesPerm ? new MCallFrame
            {
                Id = _frames++,
                Receiver = null,
                Callee = callee,
                Cells = cellCall,
                Given = gave,
                Fields = _p.UsesFields,
            } : null;
            if (frame != null)
            {
                Emit(frame);
            }
            Emit(new MCall
            {
                Callee = callee,
                Receiver = receiver,
                ReceiverIsThis = st.ReceiverIsThis,
                ReceiverAt = st.ReceiverAt,
                Args = args,
                Result = c.Result,
                At = c.At,
                ArgsAt = st.ArgsAt,
                RefOuts = c.RefOuts,
                Check = At("CSV1001", c.At, $"'{c.At}'"),
                Phase = 2,
            });
            AfterCall(c, callee, receiver, given, frame, sig, pure, false);
        }

        /// <summary>A task's or thread's start, as Checks made it (by its kernel call): what its join needs.</summary>
        private readonly Dictionary<KCall, (MExpr receiver, MExpr[] args, Dictionary<string, MExpr> given, List<(MExpr, MExpr)> gave, bool cellCall, bool pure)> _started =
            new Dictionary<KCall, (MExpr, MExpr[], Dictionary<string, MExpr>, List<(MExpr, MExpr)>, bool, bool)>();

        /// <summary>After a call: what it gives back by value (views, invariants, packages); then, around a call that exchanges permissions, what its postconditions give.</summary>
        private void AfterCall(KCall c, IMethodSymbol callee, MExpr receiver, Dictionary<string, MExpr> given, MCallFrame frame, KProcedure sig, bool pure, bool ownedReceiver)
        {
            GivenBack(c, callee, receiver, ownedReceiver);
            if (frame != null)
            {
                PostconditionsGiveBack(c, callee, given, frame, sig, pure);
            }
        }

        /// <summary>
        /// The views it gives back in hand again, their invariants holding (its receiver's too); the objects it gives back
        /// holding their invariants; the packages it gives back arrived.
        /// </summary>
        private void GivenBack(KCall c, IMethodSymbol callee, MExpr receiver, bool ownedReceiver)
        {
            foreach (var (ordinal, var) in c.RefOuts.Where(x => IsView(callee.Parameters[x.param].Type)))
            {
                var v = new MVar(var);
                Assume(NotNull(v));
                AssumeInvariant(ViewOf(callee.Parameters[ordinal].Type), v);
                Receive(v);
            }
            if (ownedReceiver)
            {
                AssumeInvariant(callee.ContainingType, receiver);
            }
            if (c.Result != null && Returns(callee) != null)
            {
                ObjectInvariant(new MVar(c.Result), Returns(callee));
            }
            foreach (var (ordinal, var) in c.RefOuts)
            {
                ObjectInvariant(new MVar(var), callee.Parameters[ordinal].Type);
            }
            // (the packages it gives back: its result, and its ref and out arguments)
            foreach (var (ordinal, var) in c.RefOuts.Where(x => IsPackage(callee.Parameters[x.param].Type)))
            {
                Arrive(new MVar(var), callee.Parameters[ordinal].Type);
            }
            if (c.Result != null && IsPackage(Returns(callee)))
            {
                Arrive(new MVar(c.Result), Returns(callee));
            }
        }

        /// <summary>
        /// The call's frame closed; the permissions its postconditions give back in hand (of its result and ref and out
        /// arguments, as they came back; old(...) of before the call), and what they say of snapshots.
        /// </summary>
        private void PostconditionsGiveBack(KCall c, IMethodSymbol callee, Dictionary<string, MExpr> given, MCallFrame frame, KProcedure sig, bool pure)
        {
            Emit(new MCallFrame
            {
                Id = frame.Id,
                After = true,
                Receiver = frame.Receiver,
                Callee = callee,
                Maps = frame.Maps,
                Cells = frame.Cells,
                Given = frame.Given,
                ElementMaps = frame.ElementMaps,
                Fields = frame.Fields,
                FieldIds = frame.FieldIds,
            });
            var back = new Dictionary<string, MExpr>(given);
            if (c.Result != null)
            {
                back["result"] = new MVar(c.Result);
            }
            if (c.ThisOut != null)
            {
                back["this"] = new MVar(c.ThisOut);
            }
            foreach (var (ordinal, var) in c.RefOuts)
            {
                back[Local(callee.Parameters[ordinal])] = new MVar(var);
            }
            _old = x => OldBefore(x, frame);
            try
            {
                if (!pure)
                {
                    foreach (var e in sig.Ensures)
                    {
                        Inhale(e.Expr, back, null);
                    }
                }
            }
            finally
            {
                _old = null;
            }
            foreach (var e in sig.Ensures)
            {
                var math = Spec(e.Expr, out _).Substitute(back);
                _facts.Clear();
                if (math.Mentions(Snaps))
                {
                    Assume(OldBefore(math, frame));
                }
            }
        }

        /// <summary>old(...) of a procedure's snapshots is of those it had at entry.</summary>
        private static MExpr OldAtEntry(MExpr e) => e.Rewrite(x => x switch
        {
            // (also an old(...) in a function's argument: Key(t, Spec.Old(Count(t))))
            MOp { Op: "old" } old => Old(old.Args[0].Substitute(new Dictionary<string, MExpr> { ["psnap"] = new MVar("psnap$entry") })),
            _ => null,
        });

        /// <summary>A callee's postcondition, in the caller after the call: old(...) of its snapshots is of the caller's before it (and of nothing else, here).</summary>
        private static MExpr OldBefore(MExpr e, MCallFrame frame) => e.Rewrite(x => x switch
        {
            MOp { Op: "old" } old => Before(old.Args[0], frame),
            _ => null,
        });

        /// <summary>What a callee's old(...) reads, as it was just before the call: the snapshots the frame took then.</summary>
        private static MExpr Before(MExpr e, MCallFrame frame) => e.Rewrite(x =>
        {
            MExpr[] Args(MFnApp f) => f.Args.Select(a => Before(a, frame)).ToArray();
            switch (x)
            {
                case MVar v when v.Name == "psnap": return new MVar($"s{frame.Id}$psnap");
                case MVar v when v.Name.StartsWith("$"):
                    frame.OldGlobals.Add(v.Name);
                    return new MVar($"s{frame.Id}{v.Name}");
                // (a function over a predicate: of the snapshot as it was, at no layer and of no maps)
                case MFnApp f when f.Snap != null: return new MFnApp
                {
                    Callee = f.Callee,
                    Function = f.Function,
                    Plain = f.Plain,
                    MapsAt = f.MapsAt,
                    Args = Args(f),
                    Snap = Before(f.Snap, frame),
                };
                // (a function of the memory, as it was: of the frame's snapshots of every map it takes)
                case MFnApp f when !f.Plain:
                    foreach (var map in ElementTypes.Select(ElementMap).Concat(f.Fields))
                    {
                        frame.OldGlobals.Add(map);
                    }
                    return new MFnApp
                    {
                        Callee = f.Callee,
                        Function = f.Function,
                        Plain = f.Plain,
                        Layer = f.Layer,
                        Fields = f.Fields,
                        Args = Args(f),
                        MapsAt = $"s{frame.Id}",
                    };
                case MFnApp f:
                    return new MFnApp
                    {
                        Callee = f.Callee,
                        Function = f.Function,
                        Plain = true,
                        Args = Args(f),
                    };
                default: return null;
            }
        });

        /// <summary>A call's arguments, each checked, then not null where its parameter may not be (CSV1014).</summary>
        private MExpr[] Arguments(IMethodSymbol callee, KExpr[] given, SyntaxNode[] at)
        {
            var args = new MExpr[given.Length];
            for (int k = 0; k < args.Length; k++)
            {
                args[k] = Code(given[k]);
                var param = callee != null && k < callee.Parameters.Length ? callee.Parameters[k] : null;
                if (param != null && param.RefKind != RefKind.Out && IsNullable(param.Type) && NotNullable(param.Type))
                {
                    Assert(NotNull(args[k]), At("CSV1014", at[k], $"'{at[k]}' might be null, but parameter '{param.Name}' of '{callee.Name}' is not nullable"));
                }
            }
            return args;
        }
    }
}
