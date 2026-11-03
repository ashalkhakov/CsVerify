using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// ATS-style ownership of [Owned] objects. A view <c>Own&lt;C&gt;</c> is linear (the analyzer sees to that), so at
    /// most one piece of code holds an object's view at a time, and only that code may write the object's fields.
    /// A view's value is the object it owns. Consequences the verifier uses:
    /// <list type="bullet">
    /// <item>a write to an owned field needs a live view of the object in hand (CSV1016);</item>
    /// <item>a call changes an owned object only if its view goes in (by <c>ref</c> or by value), comes out, or the
    /// object is the receiver of one of its class's methods: no other object's fields need to be forgotten;</item>
    /// <item>the class's [Invariant] travels with the view: assumed where a view is received, proved where it is
    /// handed over or given back (CSV1015).</item>
    /// </list>
    /// Reads need no view: objects are garbage-collected, and while this code runs nobody else holds a view it lent.
    /// </summary>
    internal sealed partial class MethodVerifier
    {
        private static Term RootOf(Frame f, Term o) => T.Select(f.Root, T.Coerce(o, Sort.Int), Sort.Int);

        /// <summary>The footprint of o's ownership tree in state f: the objects with the same root (just o without ownership).</summary>
        private static Term TreeOf(Frame f, Term o) => f.Root == null
            ? T.Store(T.ZeroRow(), T.Coerce(o, Sort.Int), T.Int(1))
            : new Term($"(lambda ((y Int)) (ite (= (select {f.Root} y) {RootOf(f, o)}) 1 0))", Sort.Row);

        /// <summary>
        /// A [Pure] query of an [Owned] class without its own Spec.Reads reads its ownership tree: the frame rule
        /// then keeps its value across any change outside the tree.
        /// </summary>
        private static bool ReadsItsTree(Contract c) =>
            c.IsPure && c.Reads == null && !c.Method.IsStatic && SpecSymbols.IsOwned(c.Method.ContainingType) &&
            !SpecSymbols.IsInvariant(c.Method); // an invariant has a stricter rule of its own (CSV1015)

        /// <summary>An object whose view is in hand is the root of its ownership tree (no [Owns] field holds it).</summary>
        private void IsRoot(Frame f, Term o)
        {
            if (f.Root != null) _z3.Assume(T.Eq(RootOf(f, o), o));
        }

        private static bool IsOwnedField(ISymbol field) => !field.IsStatic && FieldEffects.IsHeapField(field) && SpecSymbols.IsOwned(field.ContainingType);

        /// <summary>Inside a (non-[Pure]) instance method of an owned class, <c>this</c> is held like a <c>ref</c> view.</summary>
        private bool ThisIsView => !_method.IsStatic && SpecSymbols.IsOwned(_method.ContainingType) && !_contract.IsPure;

        private static bool IsViewVariable(ISymbol s) =>
            (s is ILocalSymbol || s is IParameterSymbol) && SpecSymbols.IsViewType(TypeOf(s));

        /// <summary>A view variable comes alive: it owns an object no other live view owns. A share just adds its fraction.</summary>
        private void ViewAlive(ISymbol view, Term v, Frame f)
        {
            if (SpecSymbols.IsSharedType(TypeOf(view))) { Grant(f, v, ShareAmount); return; }
            foreach (var other in f.LiveViews.Where(o => !SymbolEqualityComparer.Default.Equals(o, view)).ToList())
                if (f.Vars.TryGetValue(other, out var ov)) _z3.Assume(T.Not(T.Eq(ov, v)));
            foreach (var s in f.LivePackages.Where(f.Vars.ContainsKey).ToList())
                foreach (var leaf in ViewsIn(f.Vars[s], TypeOf(s))) _z3.Assume(T.Not(T.Eq(leaf, v)));
            f.LiveViews.Add(view);
            Grant(f, v);
        }

        /// <summary>The [Owns] field an Own.Take/Own.Give slot names, and its container; null if it is something else.</summary>
        private (IFieldSymbol field, Term container)? OwnsSlot(IOperation slot, Frame f, SpecEnv spec, SyntaxNode at)
        {
            if (Unconverted(slot) is IFieldReferenceOperation fr && SpecSymbols.IsOwnsField(fr.Field) && fr.Instance != null &&
                SpecSymbols.IsOwned(fr.Field.ContainingType))
            {
                var c = Eval(fr.Instance, f, spec);
                Deref(fr.Instance, c, at);
                RequireWriteView(c, f, at, fr.Field.ContainingType);
                return (fr.Field, c);
            }
            Report("CSV1016", at, "Own.Take and Own.Give work on an [Owns] field of an [Owned] object", isError: true);
            return null;
        }

        /// <summary>
        /// <c>Own.Take(ref c.F, out var v)</c>: unfold. The object c.F owns comes out with its view (its invariant held
        /// at rest), c.F becomes null, and c's tree splits: what was below the object is now in its own tree.
        /// </summary>
        private Term OwnTake(IInvocationOperation inv, Frame f, SpecEnv spec)
        {
            if (!(OwnsSlot(inv.Arguments[0].Value, f, spec, inv.Syntax) is (IFieldSymbol field, Term c))) return Unknown(inv.Type);
            var x = T.Select(FieldMap(f, field), c, Sort.Int);
            Require(NotNull(x), "CSV1016", inv.Syntax, $"'{inv.Arguments[0].Value.Syntax}' might be null: there is nothing to take");
            var before = f.Root;
            var state = f.Clone();
            f.Fields[FieldEffects.Key(field)] = T.Store(FieldMap(f, field), c, T.Int(0));
            f.Link = new StateLink { Before = state, Changed = TreeOf(state, c) }; // only c's tree changed
            if (before != null)
            {
                // each object of c's tree other than c now belongs to c's or to x's tree (which, the verifier does not track)
                // (its other children stay: they are owned by c itself)
                var choice = _z3.Fresh("split", Sort.Row);
                var cRoot = RootOf(f, c);
                var siblings = string.Concat(FieldEffects.FieldsOf(field.ContainingType)
                    .Where(g => SpecSymbols.IsOwnsField(g) && !SymbolEqualityComparer.Default.Equals(g, FieldEffects.Key(field)))
                    .Select(g => $" (distinct y {T.Select(FieldMap(f, g), c, Sort.Int)})"));
                f.Root = _z3.Define("root", new Term($"(lambda ((y Int)) (ite (= y {x}) {x} (ite (and (= (select {before} y) {cRoot}) (distinct y {c}){siblings} (distinct (select {choice} y) 0)) {x} (select {before} y))))", Sort.Row));
            }
            AssumeOwnedInvariant(field.Type, x, f);
            Write(inv.Arguments[1].Value, x, f, spec);
            return x;
        }

        /// <summary>
        /// <c>Own.Give(ref c.F, x, v)</c>: fold. x and its tree join c's tree under c.F, which must be empty; v (x's
        /// view) is handed over, so x's invariant is proved. x may not be c's tree root, or c would own itself.
        /// </summary>
        private Term OwnGive(IInvocationOperation inv, Frame f, SpecEnv spec)
        {
            if (!(OwnsSlot(inv.Arguments[0].Value, f, spec, inv.Syntax) is (IFieldSymbol field, Term c))) return T.True;
            var x = Eval(inv.Arguments[1].Value, f, spec);
            var view = Eval(inv.Arguments[2].Value, f, spec);
            Require(T.Eq(T.Select(FieldMap(f, field), c, Sort.Int), T.Int(0)), "CSV1016", inv.Syntax,
                $"'{inv.Arguments[0].Value.Syntax}' might still own an object: take it first");
            Require(T.Eq(view, x), "CSV1016", inv.Syntax, $"'{inv.Arguments[2].Value.Syntax}' might not be the view of '{inv.Arguments[1].Value.Syntax}'");
            if (_codeMode && f.Perm != null)
                Require(CanWrite(f, x), "CSV1016", inv.Syntax, $"'{inv.Arguments[1].Value.Syntax}' might have read shares out: join them back (Own.Unshare) first");
            if (f.Root != null)
                Require(T.Not(T.Eq(RootOf(f, c), x)), "CSV1016", inv.Syntax, $"'{inv.Arguments[1].Value.Syntax}' might own the container: ownership would be a cycle");
            ProveOwnedInvariant(field.Type, x, f, inv.Syntax, "when it is given to its owner");
            if (VariableOf(inv.Arguments[2].Value) is ISymbol consumed) Release(f, consumed);
            var state = f.Clone();
            f.Fields[FieldEffects.Key(field)] = T.Store(FieldMap(f, field), c, x);
            f.Link = new StateLink { Before = state, Changed = TreeOf(state, c) }; // only c's tree changed (x joins it)
            if (f.Root != null)
                f.Root = _z3.Define("root", new Term($"(lambda ((y Int)) (ite (= (select {f.Root} y) {x}) {RootOf(f, c)} (select {f.Root} y)))", Sort.Row));
            return T.True;
        }

        /// <summary>
        /// Lending: the trees a method's Spec.Modifies names with Own.Tree(x). Its caller must hold x's tree (full
        /// permission to its root); the method gets write permission to the whole tree for the call.
        /// </summary>
        private List<Term> LentTrees(Contract c, Frame state, SpecEnv env)
        {
            var roots = new List<Term>();
            if (c.Modifies == null || state.Root == null) return roots;
            foreach (var tree in c.Modifies.DescendantsAndSelf().OfType<IInvocationOperation>()
                         .Where(i => SpecSymbols.IsCsVerifyType(i.TargetMethod.ContainingType, "Own") && i.TargetMethod.Name == "Tree"))
                roots.Add(RootOf(state, EvalForeignSpec(tree.Arguments[0].Value, state, env)));
            return roots;
        }

        // ------------------------------------------------------------------------------------------ packages

        /// <summary>
        /// <c>new Holder(view, obj)</c> for a [Linear] record struct: the views (and shares) going in are handed over,
        /// as to a call: their invariants hold, and the variables no longer hold them (nor their permissions).
        /// </summary>
        private void Pack(IObjectCreationOperation oc, Term[] args, Frame f)
        {
            foreach (var a in oc.Arguments)
            {
                if (a.Parameter != null && IsMemView(a.Parameter.Type) && VariableOf(a.Value) is ISymbol packedView) ReleaseMemView(f, packedView);
                if (a.Parameter == null || !SpecSymbols.IsViewType(a.Parameter.Type)) continue;
                ProveOwnedInvariant(OwnedType(a.Parameter.Type), args[a.Parameter.Ordinal], f, a.Syntax, $"when it is packed into {oc.Type.Name}");
                if (VariableOf(a.Value) is ISymbol packed) Release(f, packed);
            }
        }

        /// <summary>
        /// <c>var (view, obj) = holder;</c>: each part comes out of the package. A view comes alive again (with its
        /// permission), its object at rest: its invariant holds, and it is the root of its tree.
        /// </summary>
        private void Unpack(IOperation target, Term package, INamedTypeSymbol type, Frame f, SpecEnv spec)
        {
            if (target is IDeclarationExpressionOperation d) target = d.Expression;
            if (!(target is ITupleOperation tuple)) { Unsupported(target); return; }
            for (int i = 0; i < tuple.Elements.Length; i++)
            {
                var p = DataTypes.PositionalProperty(type, i);
                if (p == null) { Unsupported(target); return; }
                var item = Field(p, package, type);
                var element = tuple.Elements[i] is IDeclarationExpressionOperation de ? de.Expression : tuple.Elements[i];
                var elementType = p.Type;
                if (element is ITupleOperation && SpecSymbols.IsLinearPackage(elementType)) { Unpack(element, item, (INamedTypeSymbol)elementType, f, spec); continue; }
                if (element is IDiscardOperation) continue;
                if (SpecSymbols.IsViewType(elementType))
                {
                    AssumeOwnedInvariant(OwnedType(elementType), item, f);
                    if (SpecSymbols.IsOwnType(elementType)) IsRoot(f, item);
                }
                Write(element, T.Coerce(item, SortOf(element.Type)), f, spec);
            }
        }

        /// <summary>
        /// A package arrives (a parameter, a call's result or ref/out argument): its views are linear, so their
        /// objects are not null, none is another's, and none is that of a view in hand.
        /// </summary>
        private void ViewsArrive(Term v, ITypeSymbol type, Frame f, List<Term> others = null)
        {
            if (!SpecSymbols.IsLinearPackage(type)) return;
            _z3.Assume(NotNull(v)); // a struct: there is always one
            var leaves = ViewsIn(v, type).ToList();
            if (leaves.Count == 0) return;
            var held = ViewsHeld(f, v).Concat(others ?? new List<Term>()).ToList();
            for (int i = 0; i < leaves.Count; i++)
            {
                _z3.Assume(NotNull(leaves[i]));
                foreach (var h in held.Concat(leaves.Take(i))) _z3.Assume(T.Not(T.Eq(leaves[i], h)));
            }
            others?.AddRange(leaves);
        }

        /// <summary>The objects whose views are in hand: live view variables, and the views in live packages (but <paramref name="except"/>).</summary>
        private IEnumerable<Term> ViewsHeld(Frame f, Term except = null)
        {
            foreach (var s in f.LiveViews.Where(f.Vars.ContainsKey)) yield return f.Vars[s];
            foreach (var s in f.LivePackages.Where(f.Vars.ContainsKey))
                if (except == null || f.Vars[s].S != except.S)
                    foreach (var leaf in ViewsIn(f.Vars[s], TypeOf(s))) yield return leaf;
        }

        /// <summary>The objects whose views a value of this type carries: itself for a view, the parts of a package.</summary>
        private IEnumerable<Term> ViewsIn(Term v, ITypeSymbol type)
        {
            if (!SpecSymbols.IsLinearPackage(type)) yield break;
            var t = (INamedTypeSymbol)type;
            foreach (var p in Data.Fields(t))
            {
                var part = Selector(p, v);
                if (SpecSymbols.IsOwnType(p.Type)) yield return part;
                else foreach (var inner in ViewsIn(part, p.Type)) yield return inner;
            }
        }

        /// <summary>The local or parameter an operand names, if it is one.</summary>
        private static ISymbol VariableOf(IOperation op)
        {
            switch (Unconverted(op))
            {
                case ILocalReferenceOperation l: return l.Local;
                case IParameterReferenceOperation p: return p.Parameter;
                default: return null;
            }
        }

        private static ITypeSymbol OwnedType(ITypeSymbol ownType) => ((INamedTypeSymbol)ownType).TypeArguments[0];

        /// <summary>
        /// The fraction a read share holds (counting permissions): every share holds the same one, so a view with k
        /// shares out holds 1 - k·ε, and only with all of them back is it whole. Any positive amount would do.
        /// </summary>
        private const string ShareAmount = "0.000001";
        private const string FullAmount = "1.0";

        private static string AmountOf(ITypeSymbol viewType) => SpecSymbols.IsSharedType(viewType) ? ShareAmount : FullAmount;

        /// <summary>Full (write) permission to <paramref name="o"/> in state f.</summary>
        private static Term CanWrite(Frame f, Term o) => new Term($"(>= (select {f.Perm} {T.Coerce(o, Sort.Int)}) 1.0)", Sort.Bool);

        /// <summary>Permissions add up: what is held here of o is the sum of the views and shares of o in hand.</summary>
        private void Grant(Frame f, Term o, string amount = FullAmount) => Add(f, o, "+", amount);

        private void Revoke(Frame f, Term o, string amount = FullAmount) => Add(f, o, "-", amount);

        private void Add(Frame f, Term o, string op, string amount)
        {
            if (f.Perm == null) return;
            var i = T.Coerce(o, Sort.Int);
            f.Perm = _z3.Define("perm", new Term($"(store {f.Perm} {i} ({op} (select {f.Perm} {i}) {amount}))", Sort.Perm));
        }

        /// <summary>A view or share variable goes (consumed, moved, dropped): so does the permission it held.</summary>
        private void Release(Frame f, ISymbol view)
        {
            if (f.Vars.TryGetValue(view, out var o) && (f.LiveViews.Contains(view) || SpecSymbols.IsSharedType(TypeOf(view))))
                Revoke(f, o, AmountOf(TypeOf(view)));
            f.LiveViews.Remove(view);
        }

        /// <summary>Writing an [Owned] object needs full permission to it (CSV1016).</summary>
        private void RequireWriteView(Term o, Frame f, SyntaxNode at, ITypeSymbol type)
        {
            if (!_codeMode || _foreignSpec > 0 || f.Perm == null) return;
            Require(CanWrite(f, o), "CSV1016", at,
                $"'{at}' changes an [Owned] {type.Name} without holding its view (Own<{type.Name}>, with no read shares out) or a frame lent to it");
        }

        private Term OwnedInvariant(ITypeSymbol type, Term o, Frame f) =>
            T.And(DataTypes.Invariants(type).Select(inv =>
                AsBool(PureApply(_engine.ContractOf(inv), o, System.Array.Empty<Term>(), f.Heap, Sort.Bool, null, f))).ToArray());

        /// <summary>A view received: its object is not null (views are made for new objects) and satisfies its invariant.</summary>
        private void AssumeOwnedInvariant(ITypeSymbol type, Term o, Frame f)
        {
            _z3.Assume(NotNull(o));
            if (DataTypes.Invariants(type).Any()) _z3.Assume(OwnedInvariant(type, o, f));
        }

        private void ProveOwnedInvariant(ITypeSymbol type, Term o, Frame f, SyntaxNode at, string when)
        {
            if (DataTypes.Invariants(type).Any())
                Prove(OwnedInvariant(type, o, f), "CSV1015", at, $"invariant of {type.Name} might not hold {when}");
        }

        /// <summary>At entry: the views received (parameters, and <c>this</c> in the class's methods) are live, their invariants hold.</summary>
        private void EnterOwned(Frame f)
        {
            var received = new List<Term>();
            if (_engine.UsesOwnership) f.Perm = new Term("((as const (Array Int Real)) 0.0)", Sort.Perm);
            if (ThisIsView || _method.MethodKind == MethodKind.Constructor && SpecSymbols.IsOwned(_method.ContainingType)) Grant(f, f.This);
            foreach (var p in _method.Parameters.Where(p => SpecSymbols.IsViewType(p.Type) && p.RefKind != RefKind.Out))
            {
                AssumeOwnedInvariant(OwnedType(p.Type), f.Vars[p], f);
                // a share, or a view lent read-only (in), holds a fraction: it may alias other shares of the object
                if (SpecSymbols.IsSharedType(p.Type) || p.RefKind == RefKind.In) { Grant(f, f.Vars[p], ShareAmount); continue; }
                f.LiveViews.Add(p);
                Grant(f, f.Vars[p]);
                IsRoot(f, f.Vars[p]);
                // views are linear: two in hand at once own two different objects (and neither is lent read-only)
                foreach (var other in received) _z3.Assume(T.Not(T.Eq(other, f.Vars[p])));
                received.Add(f.Vars[p]);
            }
            foreach (var p in _method.Parameters.Where(p => SpecSymbols.IsOwnType(p.Type) && p.RefKind == RefKind.In))
                foreach (var other in received) _z3.Assume(T.Not(T.Eq(other, f.Vars[p])));
            // packages received: their views too are distinct from each other and from the views in hand
            var packed = new List<Term>();
            foreach (var p in _method.Parameters.Where(p => SpecSymbols.IsLinearPackage(p.Type) && p.RefKind != RefKind.Out && p.RefKind != RefKind.In))
            {
                ViewsArrive(f.Vars[p], p.Type, f, packed);
                f.LivePackages.Add(p);
            }
            if (ThisIsView && _method.MethodKind != MethodKind.Constructor) AssumeOwnedInvariant(_method.ContainingType, f.This, f);
            if (ThisIsView || _method.MethodKind == MethodKind.Constructor && SpecSymbols.IsOwned(_method.ContainingType)) IsRoot(f, f.This);
        }

        /// <summary>At a return: views given back (<c>ref</c>, <c>out</c>, and <c>this</c>) satisfy their invariants again.</summary>
        private void ExitOwned(Frame f, SyntaxNode at)
        {
            foreach (var p in _method.Parameters.Where(p => SpecSymbols.IsViewType(p.Type) && (p.RefKind == RefKind.Ref || p.RefKind == RefKind.Out)))
                if (f.Vars.TryGetValue(p, out var v)) ProveOwnedInvariant(OwnedType(p.Type), v, f, at, $"when the view '{p.Name}' is given back");
            if (ThisIsView && _method.MethodKind != MethodKind.Constructor)
                ProveOwnedInvariant(_method.ContainingType, f.This, f, at, $"when '{_method.Name}' returns");
        }

        /// <summary>
        /// Before a call: the views it receives are handed over (their invariants proved; by value, consumed), and
        /// a method of an owned class needs its receiver's view. Returns the objects the call may change.
        /// </summary>
        private List<Term> HandOver(IInvocationOperation inv, Term receiver, Term[] args, Frame f, Contract callee)
        {
            var m = callee.Method;
            var touched = new List<Term>();
            if (receiver != null && SpecSymbols.IsOwned(m.ContainingType) && !callee.IsPure && !m.IsStatic)
            {
                RequireWriteView(receiver, f, inv.Syntax, m.ContainingType);
                ProveOwnedInvariant(m.ContainingType, receiver, f, inv.Syntax, $"when '{m.Name}' is called on it");
                touched.Add(receiver);
            }
            foreach (var a in inv.Arguments)
            {
                var p = a.Parameter;
                // a package's views go with it: the call may change their objects
                if (p != null && p.RefKind != RefKind.Out && p.RefKind != RefKind.In) touched.AddRange(ViewsIn(args[p.Ordinal], p.Type));
                if (p == null || !SpecSymbols.IsViewType(p.Type) || p.RefKind == RefKind.Out) continue;
                // whoever receives a view or a share relies on the invariant, even if lent read-only
                ProveOwnedInvariant(OwnedType(p.Type), args[p.Ordinal], f, a.Syntax, $"when its view is handed to '{m.Name}'");
                if (p.RefKind == RefKind.In) continue;
                if (SpecSymbols.IsOwnType(p.Type))
                {
                    // a view goes whole, so the callee may write: every share must be back
                    if (_codeMode && f.Perm != null)
                        Require(CanWrite(f, args[p.Ordinal]), "CSV1016", a.Syntax, $"'{a.Value.Syntax}' might not be whole: join its read shares back (Own.Unshare) and get back any fields given away before handing the view over");
                    touched.Add(args[p.Ordinal]);
                }
                if (p.RefKind == RefKind.Ref) Revoke(f, args[p.Ordinal], AmountOf(p.Type)); // lent: what comes back is granted again
                if (p.RefKind == RefKind.None && VariableOf(a.Value) is ISymbol consumed) Release(f, consumed);
            }
            foreach (var a in inv.Arguments.Where(a => a.Parameter?.RefKind == RefKind.None && SpecSymbols.IsLinearPackage(a.Parameter.Type)))
                if (VariableOf(a.Value) is ISymbol given) f.LivePackages.Remove(given);
            // views of memory given by value or lent by ref: their cells go with them (what comes back is granted again)
            foreach (var a in inv.Arguments.Where(a => a.Parameter != null && IsMemView(a.Parameter.Type) &&
                                                       (a.Parameter.RefKind == RefKind.None || a.Parameter.RefKind == RefKind.Ref)))
                if (VariableOf(a.Value) is ISymbol lent) ReleaseMemView(f, lent);
            return touched;
        }

        /// <summary>After a call: the views that come back are live again with their invariants (and its receiver's).</summary>
        private void TakeBack(IInvocationOperation inv, Term receiver, Frame f, Contract callee)
        {
            var m = callee.Method;
            foreach (var a in inv.Arguments.Where(a => a.Parameter != null && SpecSymbols.IsViewType(a.Parameter.Type) &&
                                                       (a.Parameter.RefKind == RefKind.Ref || a.Parameter.RefKind == RefKind.Out)))
            {
                var v = Eval(a.Value, f);
                AssumeOwnedInvariant(OwnedType(a.Parameter.Type), v, f);
                if (SpecSymbols.IsOwnType(a.Parameter.Type)) IsRoot(f, v);
            }
            if (receiver != null && SpecSymbols.IsOwned(m.ContainingType) && !callee.IsPure && !m.IsStatic)
                AssumeOwnedInvariant(m.ContainingType, receiver, f);
        }

        /// <summary><c>Own.New(new C(...), out view)</c> and <c>Own.Drop(view)</c>.</summary>
        private Term OwnCall(IInvocationOperation inv, Frame f, SpecEnv spec)
        {
            var m = inv.TargetMethod;
            if (m.Name == "Tree") return TreeOf(f, Eval(inv.Arguments[0].Value, f, spec));
            if (m.Name == "Take") return OwnTake(inv, f, spec);
            if (m.Name == "Give") return OwnGive(inv, f, spec);
            if (m.Name == "ToAcc")
            {
                // the view goes, its permission stays in hand (as Spec.Acc)
                var view = inv.Arguments[0].Value;
                Eval(view, f, spec);
                if (VariableOf(view) is ISymbol gone) f.LiveViews.Remove(gone);
                return T.True;
            }
            if (m.Name == "FromAcc")
            {
                var target = Eval(inv.Arguments[0].Value, f, spec);
                var at = inv.Syntax;
                if (f.Perm != null)
                {
                    Require(CanWrite(f, target), "CSV1016", at, $"'{inv.Arguments[0].Value.Syntax}' has no permission in hand to make a view of");
                    Require(T.Eq(RootOf(f, target), target), "CSV1016", at, $"'{inv.Arguments[0].Value.Syntax}' is owned by another object: take it out instead");
                    foreach (var live in f.LiveViews.ToList())
                        if (f.Vars.TryGetValue(live, out var lv))
                            Require(T.Not(T.Eq(lv, target)), "CSV1016", at, $"'{live.Name}' might already be a view of '{inv.Arguments[0].Value.Syntax}'");
                    NotLent(target, T.True, f, at);
                }
                Revoke(f, target); // the view written next holds it
                Write(inv.Arguments[1].Value, target, f, spec);
                return T.True;
            }
            if (m.Name == "Share")
            {
                // the view keeps 1 - ε, the share gets ε: nothing changes in sum
                var v = Eval(inv.Arguments[0].Value, f, spec);
                Revoke(f, v, ShareAmount);
                Write(inv.Arguments[1].Value, v, f, spec);
                return T.True;
            }
            if (m.Name == "Unshare")
            {
                var v = Eval(inv.Arguments[0].Value, f, spec);
                var share = Eval(inv.Arguments[1].Value, f, spec);
                Require(T.Eq(share, v), "CSV1016", inv.Syntax, $"'{inv.Arguments[1].Value.Syntax}' might not be a share of '{inv.Arguments[0].Value.Syntax}'");
                if (VariableOf(inv.Arguments[1].Value) is ISymbol joined) Release(f, joined);
                Grant(f, v, ShareAmount);
                return T.True;
            }
            if (m.Name == "Drop")
            {
                var view = inv.Arguments[0].Value;
                Eval(view, f, spec);
                if (VariableOf(view) is ISymbol dropped) Release(f, dropped);
                return T.True;
            }
            // a view is made once, for a new object: from an existing one it would be a second view
            var arg = Unconverted(inv.Arguments[0].Value);
            if (!(arg is IObjectCreationOperation))
            {
                Report("CSV1016", inv.Syntax, "Own.New takes ownership of a new object only: its argument must be a 'new' expression", isError: true);
                return Unknown(inv.Type);
            }
            var obj = Eval(arg, f, spec);
            ProveOwnedInvariant(arg.Type, obj, f, inv.Syntax, "when its view is made");
            if (f.Root != null) f.Root = T.Store(f.Root, obj, obj); // a new tree of its own
            var outArg = inv.Arguments[1].Value;
            Write(outArg, obj, f, spec);
            return obj;
        }
    }
}
