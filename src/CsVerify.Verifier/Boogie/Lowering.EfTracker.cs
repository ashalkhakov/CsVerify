using System.Collections.Generic;
using System.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.FlowAnalysis;
using Microsoft.CodeAnalysis.Operations;
using static CsVerify.Verifier.Boogie.KernelTypes;
using static CsVerify.Verifier.Boogie.KOp;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>
    /// Entity Framework Core's change tracker and transactions (StaticChecks.EfTracker,
    /// over the ghost state CsVerify.Ef.Tracker declares):
    /// - what a context tracks and how ($ef.State), its changes not saved ($ef.Unsaved), its open transaction ($ef.InTx):
    ///   maps of the program's state, which a call changes where its code does, and an await doesn't (CSV1036 has each
    ///   context this code's alone while it runs);
    /// - and the method's own record, none at entry (what its caller did isn't seen): a failed save or a rollback
    ///   (ef$failed), a save outside a transaction (ef$savedAlone), rows ExecuteUpdate changed behind the tracker
    ///   (ef$stale), what it read without tracking and their concurrency tokens (ef$read, ef$token...).
    /// Add, Attach, Update and Remove (and Entry(e).State) must not meet another tracked instance with the same key, and
    /// Update must not take along what the entity's navigations hold (CSV1033); SaveChanges must not follow a failed one
    /// or a rollback, nor write a stale row (CSV1033); Attach and Update find the tokens as read (CSV1034); two saves need
    /// one transaction, BeginTransaction none open, Commit the changes saved (CSV1035).
    /// </summary>
    internal sealed partial class Lowering
    {
        private const int EfDetached = 0, Unchanged = 1, Deleted = 2, Modified = 3, Added = 4;
        private const string StateMap = "$F.$ef.State", UnsavedMap = "$F.$ef.Unsaved", InTxMap = "$F.$ef.InTx";

        /// <summary>The method's own record (locals, set at entry), where the program references EF Core.</summary>
        private string _failed, _savedAlone, _stale, _read;

        /// <summary>The concurrency tokens a context read, of each entity and token: [Ref][Ref] of the token's value.</summary>
        private readonly Dictionary<(EfModel.Entity, int), string> _tokenRead = new Dictionary<(EfModel.Entity, int), string>();

        private static readonly KLit Null = new KLit("null");

        private static KExpr I(int v) => new KLit(v.ToString());

        /// <summary>The tracker's maps, models of the program (Lowering.Ef's EfNotYet calls this first).</summary>
        private void TrackerModels()
        {
            _p.Models[StateMap] = new ModelMap
            {
                Name = StateMap,
                Type = "[Ref][Ref]int",
            };
            _p.Models[UnsavedMap] = new ModelMap
            {
                Name = UnsavedMap,
                Type = "[Ref]bool",
            };
            _p.Models[InTxMap] = new ModelMap
            {
                Name = InTxMap,
                Type = "[Ref]bool",
            };
            _failed = "ef$failed"; _savedAlone = "ef$savedAlone"; _stale = "ef$stale"; _read = "ef$read";
            _p.Locals.Add(new KLocal
            {
                Name = _failed,
                Raw = "[Ref]bool",
            });
            _p.Locals.Add(new KLocal
            {
                Name = _savedAlone,
                Raw = "[Ref]bool",
            });
            _p.Locals.Add(new KLocal
            {
                Name = _stale,
                Raw = "[Ref][Ref]bool",
            });
            _p.Locals.Add(new KLocal
            {
                Name = _read,
                Raw = "[Ref][Ref]bool",
            });
        }

        /// <summary>At entry: nothing of the method's own record (each, for every context, false).</summary>
        private void TrackerEntry()
        {
            if (_failed == null)
            {
                return;
            }
            foreach (var x in new[] { _failed, _savedAlone })
            {
                Emit(new KAssign
                {
                    Var = x,
                    Value = new KOp("lambda", new KLit("c$: Ref"), new KLit("false")),
                });
            }
            foreach (var x in new[] { _stale, _read })
            {
                Emit(new KAssign
                {
                    Var = x,
                    Value = new KOp("lambda", new KLit("c$: Ref"), new KOp("lambda", new KLit("o$: Ref"), new KLit("false"))),
                });
            }
        }

        private string TokenRead(EfModel.Entity e, int j)
        {
            if (_tokenRead.TryGetValue((e, j), out var name))
            {
                return name;
            }
            name = "ef$token" + _tokenRead.Count;
            _p.Locals.Add(new KLocal
            {
                Name = name,
                Raw = "[Ref][Ref]" + TypeOf(e.Tokens[j].Type),
            });
            _tokenRead[(e, j)] = name;
            return name;
        }

        // ------------------------------------------------------------------ the maps

        private static KExpr States(KExpr c) => Sel(StateMap, c);
        private static KExpr State(KExpr c, KExpr o) => Sel(StateMap, c, o);
        private void SetStates(KExpr c, KExpr row) => Emit(new KRow
        {
            Map = StateMap,
            Ref = c,
            Value = row,
        });
        private static KExpr Unsaved(KExpr c) => Sel(UnsavedMap, c);
        private void SetUnsaved(KExpr c, KExpr v) => Emit(new KRow
        {
            Map = UnsavedMap,
            Ref = c,
            Value = v,
        });
        private static KExpr InTx(KExpr c) => Sel(InTxMap, c);
        private void SetInTx(KExpr c, KExpr v) => Emit(new KRow
        {
            Map = InTxMap,
            Ref = c,
            Value = v,
        });
        private KExpr Failed(KExpr c) => Sel(_failed, c);
        private void SetLocal(string map, KExpr c, KExpr v) => Emit(new KAssign
        {
            Var = map,
            Value = Store(map, c, v),
        });
        private void SetLocal(string map, KExpr c, KExpr o, KExpr v) =>
            Emit(new KAssign
            {
                Var = map,
                Value = Store(map, c, new KOp("store", Sel(map, c), o, v)),
            });

        /// <summary>An object of the entity's type (or one derived from it).</summary>
        private static KExpr Isa(KExpr o, EfModel.Entity e) => new KOp(IsaFunction(e.Type), o);

        public static string IsaFunction(ITypeSymbol t) => "$isa." + Ident(t.OriginalDefinition.ToDisplayString());

        private static KExpr And(IEnumerable<KExpr> parts) => parts.DefaultIfEmpty(new KLit("true")).Aggregate((a, b) => AndAlso(a, b));

        private KExpr KeyColumnsEqual(EfModel.Entity e, KExpr a, KExpr b)
        {
            foreach (var p in e.Key)
            {
                _p.Fields.Add(p.OriginalDefinition);
            }
            return And(e.Key.Select(p => IsString(p.Type) ? new KOp("streq", Column(p, a), Column(p, b)) : (KExpr)Eq(Column(p, a), Column(p, b))));
        }

        /// <summary>A key EF generates on insert, not set yet: a single integer key at 0.</summary>
        private KExpr KeyUnset(EfModel.Entity e, KExpr o) =>
            e.Key.Count == 1 && IsIntegral(e.Key[0].Type) && IsField(e.Key[0]) ? Eq(Column(e.Key[0], o), new KLit("0")) : new KLit("false");

        /// <summary>No other instance of the type with o's key is tracked by the context.</summary>
        private KExpr NoOtherWithKey(KExpr c, KExpr o, EfModel.Entity e)
        {
            if (e.Key.Count == 0)
            {
                return new KLit("true");
            }
            if (!e.Key.All(IsField))
            {
                return new KLit("false");
            }
            var y = new KVar("y$");
            var clash = And(new KExpr[] { Ne(State(c, y), I(EfDetached)), Ne(y, o), Isa(y, e), KeyColumnsEqual(e, y, o) });
            return KQuant.ForAll("y$", "Ref", Not(clash));
        }

        /// <summary>What o's navigations hold: nothing (each reference null, each collection null or empty)?</summary>
        private KExpr NavigationsEmpty(KExpr o, EfModel.Entity e)
        {
            var parts = new List<KExpr>();
            foreach (var p in e.References)
            {
                if (!IsField(p))
                {
                    return new KLit("false");
                }
                _p.Fields.Add(p.OriginalDefinition);
                parts.Add(Eq(Column(p, o), Null));
            }
            foreach (var p in e.Collections)
            {
                if (!IsField(p))
                {
                    return new KLit("false");
                }
                _p.Fields.Add(p.OriginalDefinition);
                var l = Column(p, o);
                if (IsList(p.Type))
                {
                    foreach (var m in ModelsOf((INamedTypeSymbol)p.Type))
                    {
                        _p.Models[m.Name] = m;
                    }
                    parts.Add(OrElse(Eq(l, Null), Eq(Sel(SizeMap, l), new KLit("0"))));
                }
                else
                {
                    parts.Add(Eq(l, Null));
                }
            }
            return And(parts);
        }

        private void TrackerCheck(KExpr cond, string id, SyntaxNode at, string message) =>
            Emit(new KCheck
            {
                Cond = cond,
                Id = id,
                At = at,
                Message = message,
            });

        /// <summary>A context SaveChanges failed on, or whose transaction rolled back, is done with (CSV1033).</summary>
        private void UsableContext(KExpr c, SyntaxNode at) =>
            TrackerCheck(Not(Failed(c)), "CSV1033", at,
                $"'{at}' uses a context after a failed SaveChanges or a rolled back transaction: what it tracks is no longer what the database holds. Use a new context");

        /// <summary>Where it may throw: the way it does (with what <paramref name="thrown"/> sets), then the way it doesn't.</summary>
        private void MayThrow(System.Action thrown = null, System.Action notThrown = null)
        {
            if (_cfgBlock != null && ThrowTarget(_cfgBlock.EnclosingRegion) is string target)
            {
                thrown?.Invoke();
                Emit(new KFork
                {
                    Overflow = new KLit("false"),
                    Target = target,
                    Exception = null,
                });
            }
            notThrown?.Invoke();
        }

        /// <summary>A context just made (new, or from an IDbContextFactory): it tracks nothing, and has nothing open.</summary>
        private void NewContext(KExpr c)
        {
            if (_failed == null)
            {
                return;
            }
            SetStates(c, new KOp("lambda", new KLit("o$: Ref"), I(EfDetached)));
            Emit(new KAssign
            {
                Var = _stale,
                Value = Store(_stale, c, new KOp("lambda", new KLit("o$: Ref"), new KLit("false"))),
            });
            SetUnsaved(c, new KLit("false"));
            SetInTx(c, new KLit("false"));
            SetLocal(_failed, c, new KLit("false"));
        }

        // ------------------------------------------------------------------ the operations

        /// <summary>The value of an operand, in a temporary: read once.</summary>
        private KExpr Once(IOperation op, ITypeSymbol type = null)
        {
            var v = Expr(op);
            if (v is KVar || v is KLit)
            {
                return v;
            }
            var t = Declare("t$" + _temps++, type ?? op.Type);
            Emit(new KAssign
            {
                Var = t,
                Value = v,
            });
            return new KVar(t);
        }

        private void NotNullHere(KExpr v, IOperation op, SyntaxNode at) =>
            Emit(new KCheck
            {
                Cond = Ne(v, Null),
                Id = "CSV1013",
                At = op.Syntax,
                Message = $"'{op.Syntax}' might be null in '{at}'",
            });

        /// <summary>The context a receiver stands for (a context, or a DbSet of one), with the DbSet's entity.</summary>
        private KExpr ContextOf(IOperation receiver, out EfModel.Entity setEntity)
        {
            setEntity = null;
            if (receiver == null)
            {
                return null;
            }
            receiver = Unconverted(receiver);
            if (KernelTypes.Ef.IsContextType(receiver.Type))
            {
                var c = Once(receiver);
                NotNullHere(c, receiver, receiver.Syntax.Parent ?? receiver.Syntax);
                return c;
            }
            if (TableOf(receiver) is DbTable t && !t.NoTracking && !t.IgnoreFilters && (receiver is IPropertyReferenceOperation || receiver is IInvocationOperation { TargetMethod.Name: "Set" }))
            {
                setEntity = t.Entity;
                var c = Once(((receiver as IPropertyReferenceOperation)?.Instance ?? ((IInvocationOperation)receiver).Instance), null);
                NotNullHere(c, (receiver as IPropertyReferenceOperation)?.Instance ?? ((IInvocationOperation)receiver).Instance, receiver.Syntax);
                return c;
            }
            return null;
        }

        private static string Plain(IMethodSymbol m) => m.Name.EndsWith("Async") ? m.Name.Substring(0, m.Name.Length - "Async".Length) : m.Name;

        /// <summary>
        /// The tracker's operations (Lowering.Ef's EfTrackerOp says which are read here): its value, or null for a call
        /// that isn't one. An ...Async one is read where it's awaited (<paramref name="awaited"/>), after other code ran.
        /// </summary>
        private (bool handled, KExpr value) TrackerCall(IInvocationOperation inv, bool awaited = false)
        {
            if (_failed == null || KernelTypes.Ef == null)
            {
                return (false, null);
            }
            var m = inv.TargetMethod;
            // (an ...Async one not awaited where it's called: what it does, and its task; CSV1036
            // is its static check's)
            if (m.Name.EndsWith("Async") && !awaited)
            {
                var (h, _) = TrackerCall(inv, awaited: true);
                if (!h)
                {
                    return (false, null);
                }
                var task = "t$" + _temps++;
                _p.Locals.Add(new KLocal
                {
                    Name = task,
                    Raw = "Ref",
                });
                Emit(new KHavoc { Var = task });
                Emit(new KAssume { Cond = Ne(new KVar(task), Null) });
                return (true, new KVar(task));
            }
            var name = Plain(m);
            var at = inv.Syntax;
            var args = inv.Arguments.OrderBy(a => a.Parameter.Ordinal).Where(a => !IsToken(a.Parameter.Type)).ToList();
            if (name is "ExecuteUpdate" or "ExecuteDelete" && IsEfMethod(m))
            {
                return (true, BulkUpdate(inv, args));
            }
            var receiver = TrackerReceiverOf(inv.Instance);
            // (a context disposed, by using or await using: nothing the kernel keeps of it changes)
            if (name == "Dispose" && args.Count == 0 && receiver != null && KernelTypes.Ef.IsContextType(receiver.Type))
            {
                Expr(receiver);
                return (true, null);
            }
            // (an entry: Entry(o).Reload())
            if (receiver is IInvocationOperation { TargetMethod.Name: "Entry" } entry && name == "Reload" && EntryOf(entry) is var (ec, eo, ee))
            {
                UsableContext(ec, at);
                foreach (var p in EfModel.PropertiesOf(ee.Type).Where(IsField))
                {
                    _p.Fields.Add(p.OriginalDefinition);
                    var v = Declare("t$" + _temps++, p.Type);
                    Emit(new KHavoc { Var = v });
                    Emit(new KFieldStore
                    {
                        Field = p.OriginalDefinition,
                        Instance = eo,
                        Value = new KVar(v),
                        At = at,
                        InstanceAt = at,
                    });
                }
                SetLocal(_stale, ec, eo, new KLit("false"));
                SetStates(ec, new KOp("store", States(ec), eo, I(Unchanged)));
                MayThrow();
                return (true, null);
            }
            // (Database: BeginTransaction; ChangeTracker: Clear)
            if (receiver is IPropertyReferenceOperation { Property.Name: "Database" or "ChangeTracker" } facade && facade.Instance != null && KernelTypes.Ef.IsContextType(facade.Instance.Type))
            {
                var c = Once(facade.Instance);
                NotNullHere(c, facade.Instance, at);
                if (facade.Property.Name == "Database" && name == "BeginTransaction" && args.Count == 0)
                {
                    UsableContext(c, at);
                    TrackerCheck(Not(InTx(c)), "CSV1035", at,
                        $"'{at}' begins a transaction where one may be open already, and EF throws: join it (if Database.CurrentTransaction is not null, use it)");
                    MayThrow();
                    SetInTx(c, new KLit("true"));
                    return (true, FreshRef(m.ReturnType is INamedTypeSymbol { Name: "Task", Arity: 1 } tt ? tt.TypeArguments[0] : m.ReturnType));
                }
                if (facade.Property.Name == "ChangeTracker" && name == "Clear" && args.Count == 0)
                {
                    SetStates(c, new KOp("lambda", new KLit("o$: Ref"), I(EfDetached)));
                    Emit(new KAssign
                    {
                        Var = _stale,
                        Value = Store(_stale, c, new KOp("lambda", new KLit("o$: Ref"), new KLit("false"))),
                    });
                    SetUnsaved(c, new KLit("false"));
                    return (true, null);
                }
                return (false, null);
            }
            // (a factory's new context: it tracks nothing, and has nothing open)
            if (name == "CreateDbContext" && receiver != null && IsEfFactory(receiver.Type) && args.Count == 0)
            {
                var f = Expr(receiver);
                NotNullHere(f, receiver, at);
                var ctxType = ((INamedTypeSymbol)receiver.Type).TypeArguments[0];
                var made = Declare("t$" + _temps++, ctxType);
                Emit(new KHavoc { Var = made });
                Emit(new KAssume { Cond = Ne(new KVar(made), Null) });
                NewContext(new KVar(made));
                MayThrow();
                return (true, new KVar(made));
            }
            // (a transaction: Commit, Rollback, Dispose)
            if (receiver is ILocalReferenceOperation txl && IsTransactionType(txl.Type) && TransactionContext(txl.Local) is IOperation txc)
            {
                var tx = Expr(receiver);
                NotNullHere(tx, receiver, at);
                var c = Once(txc);
                switch (name)
                {
                    case "Commit" when args.Count == 0:
                    {
                        TrackerCheck(Not(Unsaved(c)), "CSV1035", at, $"'{at}' commits with changes the context hasn't saved: they aren't in the transaction. SaveChanges first");
                        var was = Declare("t$" + _temps++, KernelTypes.Compilation.GetSpecialType(SpecialType.System_Boolean));
                        Emit(new KAssign
                        {
                            Var = was,
                            Value = Failed(c),
                        });
                        MayThrow(() =>
                        {
                            SetLocal(_failed, c, new KLit("true"));
                            SetInTx(c, new KLit("false"));
                        },
                                 () =>
                                 {
                                     SetLocal(_failed, c, new KVar(was));
                                     SetInTx(c, new KLit("false"));
                                 });
                        return (true, null);
                    }
                    case "Rollback" when args.Count == 0:
                    case "Dispose" when args.Count == 0:
                        // (a rollback, or a dispose of one not committed: the database as before, the tracker not)
                        SetLocal(_failed, c, OrElse(Failed(c), InTx(c)));
                        SetInTx(c, new KLit("false"));
                        return (true, null);
                }
                return (false, null);
            }
            var ctx = ContextOf(receiver, out var setEntity);
            if (ctx == null)
            {
                return (false, null);
            }
            switch (name)
            {
                case "Add" or "Attach" or "Update" or "Remove" when args.Count == 1:
                {
                    var arg = args[0].Value;
                    var e = KernelTypes.Ef.EntityOf(arg.Type is ITypeParameterSymbol ? m.TypeArguments.FirstOrDefault() ?? arg.Type : Unconverted(arg).Type) ?? setEntity;
                    if (e == null)
                    {
                        throw new NotTranslated("EF's " + m.Name + " of what isn't an entity");
                    }
                    var o = Once(Unconverted(arg));
                    NotNullHere(o, arg, at);
                    Track(name, ctx, o, e, at);
                    return (true, null);
                }
                case "SaveChanges" when args.Count == 0 || args.Count == 1 && args[0].Parameter.Type.SpecialType == SpecialType.System_Boolean:
                    foreach (var a in args)
                    {
                        Expr(a.Value);
                    }
                    return (true, SaveChanges(ctx, at));
                case "Find" when setEntity != null:
                    return (true, Find(inv, args, ctx, setEntity));
            }
            return (false, null);
        }

        /// <summary>A receiver, through what the control flow graph captured (a using's resource: its local).</summary>
        private IOperation TrackerReceiverOf(IOperation receiver)
        {
            if (receiver == null)
            {
                return null;
            }
            receiver = Unconverted(receiver);
            while (receiver is IFlowCaptureReferenceOperation r && _captured.TryGetValue(r.Id, out var v))
            {
                receiver = Unconverted(v);
            }
            return receiver;
        }

        private KExpr FreshRef(ITypeSymbol t)
        {
            var r = Declare("t$" + _temps++, t);
            Emit(new KHavoc { Var = r });
            Emit(new KAssume { Cond = Ne(new KVar(r), Null) });
            return new KVar(r);
        }

        private static bool IsTransactionType(ITypeSymbol t) =>
            t != null && (t.Name == "IDbContextTransaction" || t.AllInterfaces.Any(i => i.Name == "IDbContextTransaction"));

        /// <summary>Entry(o) on a context: the context, the entity, its type (null where it isn't one).</summary>
        private (KExpr c, KExpr o, EfModel.Entity e)? EntryOf(IInvocationOperation entry)
        {
            if (entry.Instance == null || !KernelTypes.Ef.IsContextType(entry.Instance.Type) || entry.Arguments.Length != 1)
            {
                return null;
            }
            var arg = Unconverted(entry.Arguments[0].Value);
            var e = KernelTypes.Ef.EntityOf(arg.Type);
            if (e == null)
            {
                return null;
            }
            var c = Once(entry.Instance);
            NotNullHere(c, entry.Instance, entry.Syntax);
            var o = Once(arg);
            NotNullHere(o, arg, entry.Syntax);
            return (c, o, e);
        }

        /// <summary>
        /// The context a transaction local is of: every value it's given is a BeginTransaction (awaited), the
        /// CurrentTransaction of the Database of one context (a parameter or a local the method doesn't assign again), or null.
        /// </summary>
        private IOperation TransactionContext(ILocalSymbol tx)
        {
            IOperation context = null;
            ISymbol of = null;
            bool ok = true;
            void Value(IOperation v)
            {
                v = Unconverted(v);
                switch (v)
                {
                    case IAwaitOperation aw: Value(aw.Operation); return;
                    case IConditionalOperation cond: Value(cond.WhenTrue); if (cond.WhenFalse != null)
                    {
                        Value(cond.WhenFalse);
                    } return;
                    case ILiteralOperation { ConstantValue: { HasValue: true, Value: null } }: return;
                    case IDefaultValueOperation: return;
                    case IInvocationOperation { TargetMethod.Name: "BeginTransaction" or "BeginTransactionAsync", Instance: IPropertyReferenceOperation { Property.Name: "Database", Instance: { } db } }:
                        Context(db); return;
                    case IPropertyReferenceOperation { Property.Name: "CurrentTransaction", Instance: IPropertyReferenceOperation { Property.Name: "Database", Instance: { } db2 } }:
                        Context(db2); return;
                    default: ok = false; return;
                }
            }
            void Context(IOperation db)
            {
                db = Unconverted(db);
                var s = db is IParameterReferenceOperation p ? (ISymbol)p.Parameter : db is ILocalReferenceOperation l ? l.Local : null;
                if (s == null || of != null && !SymbolEqualityComparer.Default.Equals(of, s))
                {
                    ok = false;
                    return;
                }
                of = s; context = db;
            }
            var root = _model.GetOperation(_decl);
            foreach (var op in root.DescendantsAndSelf())
            {
                if (op is IVariableDeclaratorOperation d && SymbolEqualityComparer.Default.Equals(d.Symbol, tx) && d.Initializer != null)
                {
                    Value(d.Initializer.Value);
                }
                if (op is ISimpleAssignmentOperation a && a.Target is ILocalReferenceOperation tl && SymbolEqualityComparer.Default.Equals(tl.Local, tx))
                {
                    Value(a.Value);
                }
            }
            // (the context, not assigned again)
            if (of != null && root.DescendantsAndSelf().OfType<IAssignmentOperation>().Any(a => a.Target is ILocalReferenceOperation al && SymbolEqualityComparer.Default.Equals(al.Local, of) &&
                !(a.Parent is IVariableInitializerOperation)) )
            {
                ok = false;
            }
            if (of is IParameterSymbol ps && root.DescendantsAndSelf().OfType<IAssignmentOperation>().Any(a => a.Target is IParameterReferenceOperation pr && SymbolEqualityComparer.Default.Equals(pr.Parameter, ps)))
            {
                ok = false;
            }
            return ok ? context : null;
        }

        /// <summary>Add, Attach, Update or Remove of one entity (or Entry(e).State set: as the state says).</summary>
        private void Track(string how, KExpr c, KExpr o, EfModel.Entity e, SyntaxNode at)
        {
            UsableContext(c, at);
            Emit(new KAssume { Cond = Isa(o, e) });
            var state = State(c, o);
            var unset = KeyUnset(e, o);
            // another instance of the same row already tracked: EF throws
            if (how != "Add" || e.Key.Count > 0)
            {
                TrackerCheck(OrElse(OrElse(Ne(state, I(EfDetached)), unset), NoOtherWithKey(c, o, e)), "CSV1033", at,
                    $"'{at}' may meet another {e.Type.Name} with the same key that the context already tracks, and EF throws: use the tracked one, or a context that tracks none");
            }
            // Update and Attach take the whole graph: what o's navigations hold is tracked too (and Update marks it modified)
            if (how == "Update")
            {
                TrackerCheck(NavigationsEmpty(o, e), "CSV1033", at,
                    $"'{at}' also marks what the {e.Type.Name}'s navigations hold as modified, and SaveChanges then writes every column of each: " +
                    "update only this entity (Entry(e).State = EntityState.Modified), or load the graph tracked and change what changes");
            }
            if (how is "Update" or "Attach")
            {
                TokensAsRead(c, o, e, at, "Attach first, then change it");
            }
            KExpr next = how switch
            {
                "Add" => I(Added),
                "Attach" => new KOp("ite", Eq(state, I(EfDetached)), new KOp("ite", unset, I(Added), I(Unchanged)), state),
                "Update" => new KOp("ite", unset, I(Added), new KOp("ite", Eq(state, I(Added)), state, I(Modified))),
                "Remove" => new KOp("ite", Eq(state, I(Added)), I(EfDetached), I(Deleted)),
                _ => state,
            };
            var empty = Declare("t$" + _temps++, KernelTypes.Compilation.GetSpecialType(SpecialType.System_Boolean));
            Emit(new KAssign
            {
                Var = empty,
                Value = NavigationsEmpty(o, e),
            });
            var unsetNow = Declare("t$" + _temps++, KernelTypes.Compilation.GetSpecialType(SpecialType.System_Boolean));
            Emit(new KAssign
            {
                Var = unsetNow,
                Value = unset,
            });
            // what o's navigations lead to may be tracked now too (unless they hold nothing)
            var others = new KVar(LinqMap("[Ref]int"));
            SetStates(c, new KOp("store", new KOp("ite", new KVar(empty), States(c), others), o, next));
            SetUnsaved(c, how == "Attach" ? OrElse(OrElse(Unsaved(c), new KVar(unsetNow)), Not(new KVar(empty))) : new KLit("true"));
        }

        /// <summary>Every concurrency token of o is the value the context read (where it read o) (CSV1034).</summary>
        private void TokensAsRead(KExpr c, KExpr o, EfModel.Entity e, SyntaxNode at, string then)
        {
            for (int j = 0; j < e.Tokens.Count; j++)
            {
                var token = e.Tokens[j];
                // (a token of a type the kernel doesn't have, a DateTime: not translated, CSV1902)
                if (!IsField(token))
                {
                    throw new NotTranslated($"{e.Type.Name}'s concurrency token {token.Name}, of {token.Type}");
                }
                _p.Fields.Add(token.OriginalDefinition);
                var read = Sel(_read, c, o);
                TrackerCheck(new KOp("==>", read, Eq(Column(token, o), Sel(TokenRead(e, j), c, o))), "CSV1034", at,
                    $"'{at}' takes {token.Name}, a concurrency token, as the value the row had when read, but it was changed since: EF would check the row against the new value. {then}");
            }
        }

        private KExpr SaveChanges(KExpr c, SyntaxNode at)
        {
            UsableContext(c, at);
            var y = new KVar("y$");
            // nothing ExecuteUpdate changed behind the tracker is written back
            TrackerCheck(KQuant.ForAll(
                "y$",
                "Ref",
                new KOp("==>", Eq(State(c, y), I(Modified)), Not(Sel(_stale, c, y)))),
                "CSV1033", at, $"'{at}' writes an entity that ExecuteUpdate or ExecuteDelete may have changed since it was read, overwriting what they wrote: reload it (Entry(e).Reload()) first");
            // two saves: one transaction around both, or the first stays if the second fails
            TrackerCheck(OrElse(InTx(c), Not(Sel(_savedAlone, c))), "CSV1035", at,
                $"'{at}' saves a second time on this context outside a transaction: if it fails, what the first saved stays. Begin a transaction before the first (Database.BeginTransaction), and commit after the last");
            // it may fail: then the context is done with
            var was = Declare("t$" + _temps++, KernelTypes.Compilation.GetSpecialType(SpecialType.System_Boolean));
            Emit(new KAssign
            {
                Var = was,
                Value = Failed(c),
            });
            MayThrow(() => SetLocal(_failed, c, new KLit("true")), () => SetLocal(_failed, c, new KVar(was)));
            // the database sets the row versions of what it writes
            KExpr Written(KExpr x) => OrElse(Eq(State(c, x), I(Added)), Eq(State(c, x), I(Modified)));
            foreach (var p in KernelTypes.Ef.Entities.SelectMany(e => e.RowVersions).Where(IsField).Select(p => p.OriginalDefinition).Distinct<IPropertySymbol>(SymbolEqualityComparer.Default))
            {
                _p.Fields.Add(p);
                var fresh = new KVar(LinqMap("[Ref]" + TypeOf(p.Type)));
                Emit(new KRow
                {
                    Map = FieldMap(p),
                    Ref = null,
                    Value = new KOp("lambda", new KLit("y$: Ref"), new KOp("ite", Written(y), new KOp("sel", fresh, y), Sel(FieldMap(p), y))),
                });
            }
            SetLocal(_savedAlone, c, OrElse(Sel(_savedAlone, c), Not(InTx(c))));
            SetStates(c, new KOp("lambda", new KLit("y$: Ref"), new KOp("ite", Written(y), I(Unchanged), new KOp("ite", Eq(State(c, y), I(Deleted)), I(EfDetached), State(c, y)))));
            SetUnsaved(c, new KLit("false"));
            var n = Declare("t$" + _temps++, KernelTypes.Compilation.GetSpecialType(SpecialType.System_Int32));
            Emit(new KHavoc { Var = n });
            Emit(new KAssume { Cond = new KOp("<=", new KLit("0"), new KVar(n)) });
            return new KVar(n);
        }

        /// <summary>Find(key), or Find(a, b) for a composite key, in the key's order: the tracked entity with that key, or the row read and tracked, or null.</summary>
        private KExpr Find(IInvocationOperation inv, List<IArgumentOperation> args, KExpr c, EfModel.Entity e)
        {
            if (e.Key.Count == 0 || !e.Key.All(IsField) || args.Count != 1)
            {
                throw new NotTranslated("EF's Find of " + e.Type.Name);
            }
            var keyArg = args[0].Value;
            var parts = keyArg is IArrayCreationOperation arr && arr.Initializer != null
                ? arr.Initializer.ElementValues.Select(v => Unconverted(v)).ToList()
                : e.Key.Count == 1 ? new List<IOperation> { Unconverted(keyArg) } : null;
            if (parts == null || parts.Count != e.Key.Count)
            {
                throw new NotTranslated("EF's Find of " + e.Type.Name + " by another key");
            }
            // (each value of its column's type: EF throws for another, which is not read)
            for (int j = 0; j < parts.Count; j++)
            {
                if (!SymbolEqualityComparer.Default.Equals(parts[j].Type, e.Key[j].Type))
                {
                    throw new NotTranslated("EF's Find by a value of another type");
                }
            }
            UsableContext(c, inv.Syntax);
            var ks = parts.Select(p => Once(p)).ToList();
            // (a reference, which may be null)
            var r = "t$" + _temps++;
            _p.Locals.Add(new KLocal
            {
                Name = r,
                Raw = "Ref",
            });
            Emit(new KHavoc { Var = r });
            var rv = new KVar(r);
            foreach (var p in e.Key)
            {
                _p.Fields.Add(p.OriginalDefinition);
            }
            // (the maps themselves: of what may be null)
            KExpr Col(IPropertySymbol p) => Sel(FieldMap(p.OriginalDefinition), rv);
            var match = And(e.Key.Select((p, j) => IsString(p.Type) ? new KOp("streq", Col(p), ks[j]) : (KExpr)Eq(Col(p), ks[j])));
            Emit(new KAssume { Cond = OrElse(Eq(rv, Null), AndAlso(Isa(rv, e), match)) });
            SetStates(c, new KOp("store", States(c), rv, new KOp("ite", Eq(State(c, rv), I(EfDetached)), I(Unchanged), State(c, rv))));
            MayThrow();
            return rv;
        }

        /// <summary>ExecuteUpdate or ExecuteDelete: rows changed in the database, not in the tracker.</summary>
        private KExpr BulkUpdate(IInvocationOperation inv, List<IArgumentOperation> args)
        {
            var source = args.FirstOrDefault()?.Value;
            var root = source == null ? null : RootTable(source);
            if (root == null)
            {
                throw new NotTranslated("EF's " + inv.TargetMethod.Name + " of a query not on a table");
            }
            var c = Once(root.Value.context);
            NotNullHere(c, root.Value.context, inv.Syntax);
            UsableContext(c, inv.Syntax);
            var y = new KVar("o$");
            Emit(new KAssign
            {
                Var = _stale,
                Value = Store(_stale, c, new KOp("lambda", new KLit("o$: Ref"),
                OrElse(AndAlso(Ne(State(c, y), I(EfDetached)), Isa(y, root.Value.entity)), Sel(_stale, c, y)))),
            });
            MayThrow();
            var n = Declare("t$" + _temps++, KernelTypes.Compilation.GetSpecialType(SpecialType.System_Int32));
            Emit(new KHavoc { Var = n });
            Emit(new KAssume { Cond = new KOp("<=", new KLit("0"), new KVar(n)) });
            return new KVar(n);
        }

        /// <summary>The table a query reads, through its first sources: its context's operand and its entity.</summary>
        private (IOperation context, EfModel.Entity entity)? RootTable(IOperation op)
        {
            for (int depth = 0; depth < 64 && op != null; depth++)
            {
                op = Unconverted(op);
                switch (op)
                {
                    case IPropertyReferenceOperation pr when DbSetEntity(pr.Type) is EfModel.Entity e && pr.Instance != null && KernelTypes.Ef.IsContextType(pr.Instance.Type):
                        return (pr.Instance, e);
                    case IInvocationOperation set when set.TargetMethod.Name == "Set" && set.Instance != null && DbSetEntity(set.Type) is EfModel.Entity se:
                        return (set.Instance, se);
                    case IInvocationOperation q:
                        op = q.Instance ?? q.Arguments.OrderBy(a => a.Parameter.Ordinal).FirstOrDefault()?.Value;
                        continue;
                    default:
                        return null;
                }
            }
            return null;
        }

        /// <summary>
        /// A local view (DbSet.Local) as it is now: each entity of its type the context tracks and doesn't delete
        /// (Unchanged, Modified or Added) once, in some order, and every one.
        /// </summary>
        private LSeq LocalView(IPropertyReferenceOperation local)
        {
            var set = Unconverted(local.Instance);
            if (_failed == null || !(TableOf(set) is DbTable t) || t.NoTracking || t.IgnoreFilters ||
                !(set is IPropertyReferenceOperation || set is IInvocationOperation { TargetMethod.Name: "Set" }))
            {
                throw new NotTranslated("EF's Local of " + set.Syntax);
            }
            var e = t.Entity;
            var ctxOp = (set as IPropertyReferenceOperation)?.Instance ?? ((IInvocationOperation)set).Instance;
            var c = Once(ctxOp);
            NotNullHere(c, ctxOp, local.Syntax);
            var at = local.Syntax;
            var el = new KVar(LinqMap("[int]Ref"));
            var idx = new KVar(LinqMap("[Ref]int"));
            var n = Declare("t$" + _temps++, KernelTypes.Compilation.GetSpecialType(SpecialType.System_Int32));
            Emit(new KHavoc { Var = n });
            var len = new KVar(n);
            KExpr El(KExpr i) => new KOp("sel", el, i);
            KExpr Live(KExpr y) => AndAlso(Ne(State(c, y), I(EfDetached)), Ne(State(c, y), I(Deleted)));
            KExpr Each(KExpr i) => And(new[] { Eq(new KOp("sel", idx, El(i)), i), Ne(El(i), Null), Isa(El(i), e), Live(El(i)) });
            var known = _known;
            _known = null;
            ShapeFact(new KOp("<=", new KLit("0"), len), at);
            ShapeFact(Over(new KLit("0"), len, Each), at);
            ShapeFact(new KOp("==>", new KOp("<", new KLit("0"), len), Each(new KLit("0"))), at);
            var y = new KVar("y$");
            ShapeFact(KQuant.ForAll(
                "y$",
                "Ref",
                new KOp("==>", AndAlso(Isa(y, e), Live(y)),
                And(new KExpr[] { new KOp("<=", new KLit("0"), new KOp("sel", idx, y)), new KOp("<", new KOp("sel", idx, y), len), Eq(El(new KOp("sel", idx, y)), y) }))), at);
            _known = known;
            return new LSeq
            {
                Length = len,
                Elem = El,
                Type = e.Type,
            };
        }

        private static bool IsLocalView(IOperation op) =>
            Unconverted(op) is IPropertyReferenceOperation { Property.Name: "Local", Instance: { } i } && DbSetEntity(Unconverted(i).Type) != null;

        // ------------------------------------------------------------------ properties, assignments, calls

        /// <summary>Database.CurrentTransaction, Entry(o).State: their values (null for another property).</summary>
        private KExpr TrackerRead(IPropertyReferenceOperation pr)
        {
            if (_failed == null || pr.Instance == null)
            {
                return null;
            }
            if (pr.Property.Name == "CurrentTransaction" && Unconverted(pr.Instance) is IPropertyReferenceOperation { Property.Name: "Database", Instance: { } db } && KernelTypes.Ef.IsContextType(db.Type))
            {
                var c = Once(db);
                NotNullHere(c, db, pr.Syntax);
                var t = Declare("t$" + _temps++, pr.Type);
                Emit(new KHavoc { Var = t });
                Emit(new KAssume { Cond = Eq(Ne(new KVar(t), Null), InTx(c)) });
                return new KVar(t);
            }
            if (pr.Property.Name == "State" && Unconverted(pr.Instance) is IInvocationOperation { TargetMethod.Name: "Entry" } entry && EntryOf(entry) is var (c2, o, _))
            {
                return State(c2, o);
            }
            // (a local view's Count)
            if (pr.Property.Name == "Count" && IsLocalView(pr.Instance))
            {
                return LocalView((IPropertyReferenceOperation)Unconverted(pr.Instance)).Length;
            }
            return null;
        }

        /// <summary>Entry(o).State = s: as Add, Attach, Update or Remove, by the state (Detached stops tracking). False for another assignment.</summary>
        private bool TrackerAssign(IOperation target, KExpr value)
        {
            if (_failed == null || !(target is IPropertyReferenceOperation { Property.Name: "State" } pr) ||
                !(Unconverted(pr.Instance) is IInvocationOperation { TargetMethod.Name: "Entry" } entry))
            {
                return false;
            }
            if (!(EntryOf(entry) is var (c, o, e)))
            {
                return false;
            }
            var at = target.Parent?.Syntax ?? target.Syntax;
            if (target.Parent is ISimpleAssignmentOperation a && a.Value.ConstantValue.HasValue && a.Value.ConstantValue.Value is int s)
            {
                switch (s)
                {
                    case Modified: TrackAs(c, o, e, Modified, at); return true;
                    case Added: Track("Add", c, o, e, at); return true;
                    case Deleted: Track("Remove", c, o, e, at); return true;
                    case Unchanged: TrackAs(c, o, e, Unchanged, at); return true;
                    case EfDetached: SetStates(c, new KOp("store", States(c), o, I(EfDetached))); return true;
                }
            }
            // (a state not known here: anything)
            SetStates(c, new KOp("store", States(c), o, value));
            var u = Declare("t$" + _temps++, KernelTypes.Compilation.GetSpecialType(SpecialType.System_Boolean));
            Emit(new KHavoc { Var = u });
            SetUnsaved(c, new KVar(u));
            return true;
        }

        /// <summary>Entry(o).State = Modified or Unchanged: this entity alone (not its graph), checked for a clash as Attach is.</summary>
        private void TrackAs(KExpr c, KExpr o, EfModel.Entity e, int state, SyntaxNode at)
        {
            UsableContext(c, at);
            Emit(new KAssume { Cond = Isa(o, e) });
            TrackerCheck(OrElse(Ne(State(c, o), I(EfDetached)), NoOtherWithKey(c, o, e)), "CSV1033", at,
                $"'{at}' may meet another {e.Type.Name} with the same key that the context already tracks, and EF throws: use the tracked one, or a context that tracks none");
            if (state == Modified)
            {
                TokensAsRead(c, o, e, at, "Mark it modified first, then change it");
            }
            SetStates(c, new KOp("store", States(c), o, I(state)));
            if (state == Modified)
            {
                SetUnsaved(c, new KLit("true"));
            }
        }

        /// <summary>
        /// A write of an entity's column: for every context tracking the entity unchanged, it is now modified, with changes
        /// to save. (A row version's write is checked in Lowering.Ef, CSV1034.)
        /// </summary>
        private void TrackerFieldWrite(ISymbol field, KExpr o, SyntaxNode at)
        {
            if (_failed == null || o == null || !(field is IPropertySymbol p) || KernelTypes.Ef.EntityOf(p.ContainingType) is not EfModel.Entity entity)
            {
                return;
            }
            // (a row version is the database's to set, CSV1034)
            if (entity.RowVersions.Contains(p.OriginalDefinition) || entity.RowVersions.Contains(p))
            {
                Emit(new KCheck
                {
                    Cond = new KLit("false"),
                    Id = "CSV1034",
                    At = at,
                    NotAssumedAfter = true,
                    Message = $"'{at}' writes {p.Name}, a row version: the database sets it on every write, and EF checks the row against the value read",
                });
            }
            var c = new KVar("c$");
            KExpr Was(KExpr x) => Sel(StateMap, x, o);
            Emit(new KRow
            {
                Map = UnsavedMap,
                Ref = null,
                Value = new KOp("lambda", new KLit("c$: Ref"), OrElse(Ne(Was(c), I(EfDetached)), Unsaved(c))),
            });
            Emit(new KRow
            {
                Map = StateMap,
                Ref = null,
                Value = new KOp("lambda", new KLit("c$: Ref"),
                new KOp("store", States(c), o, new KOp("ite", Eq(Was(c), I(Unchanged)), I(Modified), Was(c)))),
            });
        }

        /// <summary>Rows read with tracking: tracked from here on (unchanged, those it didn't track).</summary>
        private void TrackedRows(KExpr c, KExpr isRow)
        {
            if (_failed == null)
            {
                return;
            }
            var y = new KVar("y$");
            SetStates(c, new KOp("lambda", new KLit("y$: Ref"), new KOp("ite", AndAlso(isRow, Eq(State(c, y), I(EfDetached))), I(Unchanged), State(c, y))));
        }

        /// <summary>Rows read without tracking: read by the context, with their tokens as they are (for CSV1034).</summary>
        private void ReadRows(KExpr c, EfModel.Entity e, KExpr isRow)
        {
            if (_failed == null || e.Tokens.Count == 0)
            {
                return;
            }
            var y = new KVar("y$");
            Emit(new KAssign
            {
                Var = _read,
                Value = Store(_read, c, new KOp("lambda", new KLit("y$: Ref"), OrElse(isRow, Sel(_read, c, y)))),
            });
            for (int j = 0; j < e.Tokens.Count; j++)
            {
                // (a token of a type the kernel doesn't have isn't kept: an Attach or Update that would check it isn't translated)
                if (!IsField(e.Tokens[j]))
                {
                    continue;
                }
                var map = TokenRead(e, j);
                _p.Fields.Add(e.Tokens[j].OriginalDefinition);
                Emit(new KAssign
                {
                    Var = map,
                    Value = Store(map, c, new KOp("lambda", new KLit("y$: Ref"),
                    new KOp("ite", isRow, Sel(FieldMap(e.Tokens[j].OriginalDefinition), y), Sel(map, c, y)))),
                });
            }
        }

        /// <summary>What a method of the program may do to a context that outlasts it, read from its code (and its callees').</summary>
        private sealed class EfEffects { public bool Breaks, Saves, BulkUpdates; }

        private static readonly Dictionary<IMethodSymbol, EfEffects> _efEffects = new Dictionary<IMethodSymbol, EfEffects>(SymbolEqualityComparer.Default);

        private EfEffects EfEffectsOf(IMethodSymbol m)
        {
            m = m.OriginalDefinition;
            lock (_efEffects) if (_efEffects.TryGetValue(m, out var known))
            {
                return known;
            }
            var e = new EfEffects();
            lock (_efEffects) _efEffects[m] = e; // (a recursive call adds nothing)
            foreach (var r in m.DeclaringSyntaxReferences)
            {
                var node = r.GetSyntax();
                var model = KernelTypes.Compilation.GetSemanticModel(node.SyntaxTree);
                foreach (var inv in node.DescendantNodes().OfType<InvocationExpressionSyntax>())
                {
                    if (!(model.GetSymbolInfo(inv).Symbol is IMethodSymbol called))
                    {
                        continue;
                    }
                    var name = Plain(called);
                    // (in a try whose catch doesn't throw again: a failure there may be swallowed)
                    bool swallowed = inv.Ancestors().OfType<TryStatementSyntax>().Any(t => t.Block.Span.Contains(inv.Span) &&
                        t.Catches.Any(c => !c.Block.DescendantNodes().OfType<ThrowStatementSyntax>().Any()));
                    if (IsEfMethod(called) || called.ContainingType != null && KernelTypes.Ef.IsContextType(called.ContainingType) || IsTransactionType(called.ContainingType))
                    {
                        if (name == "SaveChanges")
                        {
                            e.Saves = true;
                            if (swallowed)
                            {
                                e.Breaks = true;
                            }
                        }
                        else if (name == "Commit" && swallowed || name == "Rollback")
                        {
                            e.Breaks = true;
                        }
                        else if (name is "ExecuteUpdate" or "ExecuteDelete")
                        {
                            e.BulkUpdates = true;
                        }
                    }
                    else if (called.DeclaringSyntaxReferences.Length > 0 && !SymbolEqualityComparer.Default.Equals(called.OriginalDefinition, m))
                    {
                        var inner = EfEffectsOf(called);
                        e.Saves |= inner.Saves;
                        e.BulkUpdates |= inner.BulkUpdates;
                        e.Breaks |= inner.Breaks || inner.Saves && swallowed;
                    }
                }
            }
            return e;
        }

        /// <summary>
        /// After a call of the program's: what it may have done to any context, in this method's record. It may have
        /// broken one, saved outside the transaction the caller had open, or changed rows the caller tracks.
        /// </summary>
        private void TrackerCallEffects(IMethodSymbol callee)
        {
            if (_failed == null || callee == null || callee.DeclaringSyntaxReferences.Length == 0)
            {
                return;
            }
            var e = EfEffectsOf(callee);
            var c = new KVar("c$");
            if (e.Breaks)
            {
                var may = new KVar(LinqMap("[Ref]bool"));
                Emit(new KAssign
                {
                    Var = _failed,
                    Value = new KOp("lambda", new KLit("c$: Ref"), OrElse(new KOp("sel", may, c), Failed(c))),
                });
            }
            if (e.Saves)
            {
                var may = new KVar(LinqMap("[Ref]bool"));
                Emit(new KAssign
                {
                    Var = _savedAlone,
                    Value = new KOp("lambda", new KLit("c$: Ref"),
                    OrElse(AndAlso(new KOp("sel", may, c), Not(InTx(c))), Sel(_savedAlone, c))),
                });
            }
            if (e.BulkUpdates)
            {
                var may = new KVar(LinqMap("[Ref][Ref]bool"));
                Emit(new KAssign
                {
                    Var = _stale,
                    Value = new KOp("lambda", new KLit("c$: Ref"), new KOp("lambda", new KLit("o$: Ref"),
                    OrElse(new KOp("sel", may, c, new KVar("o$")), Sel(_stale, c, new KVar("o$"))))),
                });
            }
        }
    }
}
