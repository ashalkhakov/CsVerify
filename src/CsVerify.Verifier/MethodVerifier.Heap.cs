using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Heap fields (see <see cref="FieldEffects"/>): each is an SMT array from object to value. A frame holds the
    /// maps changed on its path; an unchanged one is the map as of the frame's epoch (the method's entry state,
    /// or the state after a call that may have written anything), shared by every path and by <c>Spec.Old</c>.
    /// </summary>
    internal sealed partial class MethodVerifier
    {
        private readonly Dictionary<string, Term> _fieldStates = new Dictionary<string, Term>();
        private int _fieldEpochs;
        // what began each epoch (a call, a loop): its maps, made when first read, are charged to it
        private readonly Dictionary<int, (string cause, string origin)> _epochCauses = new Dictionary<int, (string, string)>();
        // an epoch whose maps are the previous ones where a condition holds (a call through a list interface on a List)
        private readonly Dictionary<int, (Term keep, Frame before)> _epochKeeps = new Dictionary<int, (Term, Frame)>();

        // an epoch whose maps are the previous ones at some objects (those in confined locals, across an await)
        private readonly Dictionary<int, (IReadOnlyList<Term> objs, Frame before)> _epochKeepObjects = new Dictionary<int, (IReadOnlyList<Term>, Frame)>();

        /// <summary>Every field may change, except at the objects <paramref name="objs"/> (when not null).</summary>
        private void HavocAllFieldsKeeping(Frame f, IReadOnlyList<Term> objs)
        {
            if (objs == null || objs.Count == 0) { HavocAllFields(f); return; }
            var before = f.Clone();
            HavocAllFields(f);
            _epochKeepObjects[f.FieldEpoch] = (objs, before);
        }

        /// <summary>Every field may change, unless <paramref name="keep"/> holds: then each is as in <paramref name="before"/>.</summary>
        private void HavocAllFieldsUnless(Frame f, Term keep, Frame before)
        {
            HavocAllFields(f);
            _epochKeeps[f.FieldEpoch] = (keep, before);
        }

        /// <summary>
        /// A field's map: object to Int (to a set, for an ObjSet-valued ghost field such as Repr). A [Model] function
        /// is a field too: with a key, object to (key to value).
        /// </summary>
        private static Sort ValueSort(ISymbol field) =>
            field is IMethodSymbol model && model.Parameters.Length == 2 ? Sort.Row : SortOf(FieldType(field)) == Sort.Row ? Sort.Row : Sort.Int;

        private static Sort MapSort(ISymbol field) => ValueSort(field) == Sort.Row ? Sort.Heap : Sort.Row;

        private Term FreshMap(ISymbol field) => _z3.Fresh(field.Name + "$map", MapSort(field));

        private static Term DefaultValue(ISymbol field) => ValueSort(field) == Sort.Row ? T.ZeroRow() : T.Int(0);

        private Term FieldMap(Frame f, ISymbol field)
        {
            field = FieldEffects.Key(field);
            if (f.Fields.TryGetValue(field, out var map)) return map;
            var key = field.ToDisplayString() + "#" + f.FieldEpoch;
            if (!_fieldStates.TryGetValue(key, out map))
            {
                var (wasCause, wasOrigin) = (_z3.Cause, _z3.Origin);
                if (_epochCauses.TryGetValue(f.FieldEpoch, out var began)) (_z3.Cause, _z3.Origin) = began;
                try { _fieldStates[key] = map = FreshMap(field); }
                finally { (_z3.Cause, _z3.Origin) = (wasCause, wasOrigin); }
                if (_epochKeeps.TryGetValue(f.FieldEpoch, out var kept))
                    AssumeSide(T.Implies(kept.keep, T.Eq(map, FieldMap(kept.before, field))));
                if (_epochKeepObjects.TryGetValue(f.FieldEpoch, out var objects))
                    foreach (var o in objects.objs)
                        AssumeSide(T.Implies(NotNull(o), T.Eq(T.Select(map, o, ValueSort(field)), T.Select(FieldMap(objects.before, field), o, ValueSort(field)))));
            }
            return map;
        }

        /// <summary>The statics object, whose fields are the static fields (<see cref="FieldEffects.IsStaticField"/>).</summary>
        private static Term Statics => T.Int(0);

        private Term ReadField(ISymbol field, IOperation instance, ITypeSymbol type, SyntaxNode at, Frame f, SpecEnv spec)
        {
            if (FieldEffects.IsStaticField(field))
            {
                CheckFieldHeld(field, null, at, f);
                if (_framingTask != null && !NeverChanges(field)) NotGivenBack(T.False, at);
                var sv = T.Select(FieldMap(f, field), Statics, ValueSort(field));
                AssumeNonNullRead(field, null, sv);
                HasType(sv, type);
                return ValueSort(field) == Sort.Row ? sv : InRangeOf(T.Coerce(sv, SortOf(type)), type);
            }
            var o = Eval(instance, f, spec);
            Deref(instance, o, at);
            CheckRead(field, o, at);
            CheckFieldHeld(field, o, at, f);
            CheckFraming(o, field, f, at);
            var v = T.Select(FieldMap(f, field), o, ValueSort(field));
            AssumeNonNullRead(field, instance, v);
            // what an [Owns] field refers to is in the same ownership tree, and is not its root (it is owned)
            if (f.Root != null && SpecSymbols.IsOwnsField(field))
                AssumeSide(T.Implies(NotNull(v), T.And(T.Eq(RootOf(f, v), RootOf(f, o)), T.Not(T.Eq(RootOf(f, v), v)))));
            HasType(v, type);
            UnderGuards(() => AssumeImmutableInvariants(o, instance.Type, f));
            // a field of an allocated object refers to an allocated object
            if (f.Alloc != null && MayBeNullType(type))
                AssumeSide(T.Implies(T.And(InSet(f.Alloc, o), NotNull(v)), InSet(f.Alloc, v)));
            return ValueSort(field) == Sort.Row ? v : InRangeOf(T.Coerce(v, SortOf(type)), type);
        }

        private void WriteField(ISymbol field, IOperation instance, Term v, SyntaxNode at, Frame f, SpecEnv spec)
        {
            bool isStatic = FieldEffects.IsStaticField(field);
            var o = isStatic ? Statics : Eval(instance, f, spec);
            CheckFieldHeld(field, isStatic ? null : o, at, f);
            if (!isStatic)
            {
                Deref(instance, o, at);
                RequireWritePermission(field, o, f, at);
            }
            CheckNonNullWrite(field, v, at);
            var before = f.Clone();
            f.Fields[FieldEffects.Key(field)] = T.Store(FieldMap(f, field), o, T.Coerce(v, ValueSort(field)));
            f.Link = new StateLink { Before = before, Changed = T.Store(T.ZeroRow(), o, T.Int(1)) };
        }

        /// <summary>
        /// A field map after a call, defined object by object (y): a constant of its own and an axiom, not a lambda
        /// term. [Pure] applications take field maps as arguments, and two lambda terms for one state that differ
        /// only in how they were written (1 or 0 + 1 inside) are different arguments to Z3; constants are not.
        /// </summary>
        private Term Pointwise(string hint, Sort sort, string body)
        {
            var map = _z3.Fresh(hint + "$map", sort);
            _z3.Assume(new Term($"(forall ((y Int)) (! (= (select {map} y) {body}) :pattern ((select {map} y))))", Sort.Bool));
            return map;
        }

        /// <summary>Is object y in the footprint of predicate instance q: is its ownership tree's root?</summary>
        private static string InFootprint(Term owner, Term root, string y, Term q) =>
            $"(= (select {owner} (select {root} {y})) {q})";

        /// <summary>
        /// After a call: which instance owns an object may change for the objects it got (their trees), those in the
        /// footprints of the instances it got, and objects it allocates (it may fold them); for all, if that is not known.
        /// </summary>
        private void HavocOwners(Frame f, IReadOnlyList<Term> touched, IReadOnlyList<Term> touchedInst, IReadOnlyList<(Term obj, ISymbol field)> touchedFields)
        {
            if (f.Owner == null) return;
            if (touched == null) { f.Owner = _z3.Fresh("owner", Sort.Row); if (f.FOwner != null) f.FOwner = _z3.Fresh("fowner", Sort.Heap); return; }
            if (f.FOwner != null)
            {
                // a single field's owner changes where the call got the field, its object, or a footprint with it
                var fparts = touched.Select(t => $"(= (select {f.Root} y) {t})")
                    .Concat(touchedFields.Select(t => $"(and (= y {T.Coerce(t.obj, Sort.Int)}) (= k {FieldId(t.field)}))"))
                    .Concat(touchedInst.Select(q => $"(= (select (select {f.FOwner} y) k) {q})")).ToList();
                if (f.Alloc != null) fparts.Add($"(= (select {f.Alloc} y) 0)");
                if (fparts.Count > 0)
                    f.FOwner = _z3.Define("fowner", new Term($"(lambda ((y Int)) (lambda ((k Int)) (ite (or {string.Join(" ", fparts)}) (select (select {_z3.Fresh("fowner", Sort.Heap)} y) k) (select (select {f.FOwner} y) k))))", Sort.Heap));
            }
            var parts = touched.Select(t => $"(= (select {f.Root} y) {t})").Concat(touchedInst.Select(q => InFootprint(f.Owner, f.Root, "y", q))).ToList();
            if (f.Alloc != null) parts.Add($"(= (select {f.Alloc} y) 0)");
            if (parts.Count == 0) return;
            f.Owner = _z3.Define("owner", new Term($"(lambda ((y Int)) (ite (or {string.Join(" ", parts)}) (select {_z3.Fresh("owner", Sort.Row)} y) (select {f.Owner} y)))", Sort.Row));
        }

        /// <summary>
        /// After a call: the heap fields it may write have unknown values (an inferred frame condition). An owned
        /// field changes only at the objects whose views the call got or gave (<paramref name="touched"/>; null when
        /// that is not known), whatever the callee is.
        /// </summary>
        /// <param name="modifiable">for a callee with Spec.Modifies: the objects it may change (its frame, and objects
        /// allocated after the call began); every other object's fields stay as they were</param>
        /// <param name="touchedInst">predicate instances the call got: their footprints may change too</param>
        /// <param name="touchedFields">single fields the call got (Spec.Acc(o, nameof(F))): those change too</param>
        private void HavocFields(Frame f, IMethodSymbol callee, IReadOnlyList<Term> touched = null, Term modifiable = null, IReadOnlyList<Term> touchedInst = null,
            IReadOnlyList<(Term obj, ISymbol field)> touchedFields = null)
        {
            touchedInst ??= System.Array.Empty<Term>();
            touchedFields ??= System.Array.Empty<(Term, ISymbol)>();
            var fownerBefore = f.FOwner;
            if (f.Owner != null) f.Owner = _z3.Define("owner", f.Owner);
            if (f.Root != null) f.Root = _z3.Define("root", f.Root);
            var ownerBefore = f.Owner; // (footprints as they were when the call began)
            if (!_engine.ContractOf(callee).IsPure) HavocOwners(f, touched, touchedInst, touchedFields); // (a [Pure] call folds nothing)
            var (fields, all) = _engine.Fields.WritesOf(callee);
            if (fields.Count == 0 && !all) return;
            var owned = all ? _engine.Fields.OwnedFields() : fields.Where(IsOwnedField).ToList();
            // a tree lent through Spec.Modifies may have any owned field changed (the callee's own may be few)
            if (touched != null && touched.Count + touchedInst.Count + touchedFields.Count > 0 && owned.Count == 0) owned = _engine.Fields.OwnedFields().ToList();
            var before = f.Clone();
            before.Owner = ownerBefore;
            if (all && modifiable != null)
            {
                // a virtual call with a declared frame: whichever override runs writes only within it
                fields = new HashSet<ISymbol>(_engine.Fields.AllFields().Where(x => !IsOwnedField(x)), SymbolEqualityComparer.Default);
                owned = touched == null ? _engine.Fields.OwnedFields() : owned;
                all = false;
            }
            if (all) HavocAllFields(f, keepOwned: touched != null);
            foreach (var field in fields.Where(x => touched == null || !IsOwnedField(x)))
                f.Fields[field] = modifiable != null && !all && !IsOwnedField(field) && !FieldEffects.IsStaticField(field)
                    ? new Term($"({(MapSort(field) == Sort.Heap ? "cv_frameh" : "cv_frame")} {modifiable} {FieldMap(before, field)} {FreshMap(field)})", MapSort(field))
                    : FreshMap(field);
            // owned fields change at the objects whose views moved, which the link does not describe
            // (owned objects change only where views moved: with none handed over, none changed)
            // the frame rule needs to know what changed: the callee's frame for unowned fields (or none written), and
            // for owned ones the trees whose roots it got
            bool unownedKnown = !all && (modifiable != null || !fields.Any(x => !IsOwnedField(x)));
            bool ownedKnown = owned.Count == 0 || touched != null;
            if (unownedKnown && ownedKnown)
            {
                var parts = new List<string>();
                if (modifiable != null) parts.Add($"(distinct (select {modifiable} y) 0)");
                if (fields.Any(FieldEffects.IsStaticField)) parts.Add($"(= y {Statics})"); // (the statics object)
                if (owned.Count > 0 && touched != null)
                {
                    foreach (var t in touched) parts.Add(before.Root != null ? $"(= (select {before.Root} y) {t})" : $"(= y {t})");
                    foreach (var q in touchedInst) parts.Add(InFootprint(ownerBefore, before.Root, "y", q));
                    foreach (var field in owned)
                        if (FieldTouched(field, "y", fownerBefore, touchedFields, touchedInst) is string single) parts.Add(single);
                }
                f.Link = new StateLink { Before = before, Changed = new Term($"(lambda ((y Int)) (ite {(parts.Count == 0 ? "false" : parts.Count == 1 ? parts[0] : "(or " + string.Join(" ", parts) + ")")} 1 0))", Sort.Row) };
            }
            else f.Link = null;
            if (touched == null)
            {
                if (owned.Count > 0 && f.Root != null) f.Root = _z3.Fresh("root", Sort.Row);
                return;
            }
            if (owned.Count == 0) return;
            // the call may change the whole ownership trees whose roots it got (their subtrees), nothing else; an
            // object that can never be owned is always a root, so for its fields that is just the objects it got
            foreach (var field in owned.Where(x => f.Root == null || !_engine.Fields.CanBeOwned(x.ContainingType)))
            {
                var map = FieldMap(f, field);
                foreach (var o in touched) map = T.Store(map, o, _z3.Fresh(field.Name, ValueSort(field)));
                if (touchedInst.Count > 0)
                    map = Pointwise(field.Name, MapSort(field), $"(ite (or {string.Join(" ", touchedInst.Select(q => InFootprint(ownerBefore, before.Root, "y", q)))}) (select {FreshMap(field)} y) (select {map} y))");
                if (FieldTouched(field, "y", fownerBefore, touchedFields, touchedInst) is string single)
                    map = Pointwise(field.Name, MapSort(field), $"(ite {single} (select {FreshMap(field)} y) (select {map} y))");
                f.Fields[field] = map;
            }
            var inTrees = f.Root == null ? new List<ISymbol>() : owned.Where(x => _engine.Fields.CanBeOwned(x.ContainingType)).ToList();
            if (inTrees.Count == 0) return;
            if (f.Root == null)
            {
                foreach (var field in inTrees)
                {
                    var map = FieldMap(f, field);
                    foreach (var o in touched) map = T.Store(map, o, _z3.Fresh(field.Name, ValueSort(field)));
                    f.Fields[field] = map;
                }
                return;
            }
            string inTouched(string y) => touched.Count + touchedInst.Count == 0 ? "false"
                : "(or " + string.Join(" ", touched.Select(t => $"(= (select {f.Root} {y}) {t})").Concat(touchedInst.Select(q => InFootprint(ownerBefore, before.Root, y, q)))) + ")";
            foreach (var field in inTrees)
            {
                var changed = FieldTouched(field, "y", fownerBefore, touchedFields, touchedInst) is string single ? $"(or {inTouched("y")} {single})" : inTouched("y");
                f.Fields[field] = Pointwise(field.Name, MapSort(field), $"(ite {changed} (select {FreshMap(field)} y) (select {FieldMap(f, field)} y))");
            }
            f.Root = _z3.Define("root", new Term($"(lambda ((y Int)) (ite {inTouched("y")} (select {_z3.Fresh("root", Sort.Row)} y) (select {f.Root} y)))", Sort.Row));
        }

        private void HavocAllFields(Frame f, bool keepOwned = false)
        {
            var kept = keepOwned ? _engine.Fields.OwnedFields().ToDictionary(x => x, x => FieldMap(f, x), SymbolEqualityComparer.Default) : null;
            f.Link = null;
            f.Fields.Clear();
            f.FieldEpoch = ++_fieldEpochs;
            _epochCauses[f.FieldEpoch] = (_z3.Cause, _z3.Origin);
            if (kept != null) foreach (var kv in kept) f.Fields[kv.Key] = kv.Value;
        }

        /// <summary>
        /// The one rule for writing <c>o.F</c>. An [Owned] object: its view must be in hand (a live view, or
        /// <c>this</c> in its class's methods); nothing else will do, since whoever holds the view relies on it
        /// (CSV1016). Any other object: within the method's Spec.Modifies frame or allocated since entry, if the
        /// method has a frame (CSV1017); with no frame, the write is part of the method's inferred effect.
        /// </summary>
        private void RequireWritePermission(ISymbol field, Term o, Frame f, SyntaxNode at)
        {
            if (SpecSymbols.IsOwnsField(field) && _codeMode)
                Report("CSV1016", at, $"'{at}': an [Owns] field changes hands only through Own.Take and Own.Give", isError: true);
            if (IsOwnedField(field)) RequireWriteField(o, field, f, at);
            else CheckWrite(o, at);
        }

        private static bool HasInitializer(ISymbol field) =>
            field.DeclaringSyntaxReferences.Select(r => r.GetSyntax()).Any(s =>
                s is VariableDeclaratorSyntax v && v.Initializer != null || s is PropertyDeclarationSyntax p && p.Initializer != null);

        private static bool DeclaredIn(ISymbol field, ITypeSymbol type) =>
            SymbolEqualityComparer.Default.Equals(field.ContainingType.OriginalDefinition, type.OriginalDefinition);

        /// <summary>A constructor chaining to another source constructor (<c>this(...)</c>, or <c>base(...)</c> of a source class).</summary>
        private static ConstructorInitializerSyntax ChainedInitializer(IMethodSymbol ctor, SemanticModel model)
        {
            foreach (var cd in ctor.DeclaringSyntaxReferences.Select(r => r.GetSyntax()).OfType<ConstructorDeclarationSyntax>())
                if (cd.Initializer != null && model.Compilation.GetSemanticModel(cd.SyntaxTree).GetSymbolInfo(cd.Initializer).Symbol is IMethodSymbol target &&
                    target.DeclaringSyntaxReferences.Length > 0)
                    return cd.Initializer;
            return null;
        }

        /// <summary>
        /// Verifying a constructor: the new object's own fields start at their defaults, then the field
        /// initializers run, then the body.
        /// </summary>
        private void EnterConstructor(Frame f)
        {
            var type = _method.ContainingType;
            // a new object's fields all start at their defaults (its bases' too)
            foreach (var field in FieldEffects.FieldsOf(type))
                _z3.Assume(T.Eq(T.Select(FieldMap(f, field), f.This, ValueSort(field)), DefaultValue(field)));
            // with this(...) the other constructor runs the field initializers; with base(...) they run first, here
            var own = FieldEffects.FieldsOf(type).Where(s => DeclaredIn(s, type)).ToList();
            if (ChainedInitializer(_method, _model) is ConstructorInitializerSyntax chained && chained.ThisOrBaseKeyword.IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.ThisKeyword))
                own.Clear();
            bool wasCode = _codeMode;
            _codeMode = true;
            try
            {
                foreach (var field in own)
                {
                    var init = field.DeclaringSyntaxReferences.Select(r => r.GetSyntax()).Select(s =>
                        (SyntaxNode)(s as VariableDeclaratorSyntax)?.Initializer ?? (s as PropertyDeclarationSyntax)?.Initializer).FirstOrDefault(i => i != null);
                    if (init == null) continue;
                    if (!(_engine.ModelOf(init.SyntaxTree).GetOperation(init) is ISymbolInitializerOperation op)) { NotModeled(init, "unsupported initializer"); continue; }
                    var v = Eval(op.Value, f);
                    f.Fields[field] = T.Store(FieldMap(f, field), f.This, T.Coerce(v, ValueSort(field)));
                }
            }
            finally { _codeMode = wasCode; }
        }

        /// <summary>
        /// A constructor's <c>base(...)</c> or <c>this(...)</c>: a call on the object being built. Afterwards the fields
        /// the other constructor's class has (its bases' included) are whatever it made them, as its postcondition says.
        /// </summary>
        private void AfterChainedConstructor(Frame f, IMethodSymbol ctor, Term obj)
        {
            foreach (var field in FieldEffects.FieldsOf(ctor.ContainingType))
                f.Fields[field] = T.Store(FieldMap(f, field), obj, _z3.Fresh(field.Name, ValueSort(field)));
            AssumeChainedSetFields(f, ctor, obj);
            f.Link = null;
        }

        /// <summary>
        /// <c>new C(...)</c> of an ordinary class: a fresh object, distinct from every reference in scope. Its own
        /// fields are what the constructor or an initializer sets (unknown, unless the constructor's postcondition
        /// says) or else their defaults; whatever else the constructor writes is forgotten.
        /// </summary>
        private void SetNewObjectFields(Frame f, Term obj, ITypeSymbol type, IMethodSymbol ctor, Term modifiable)
        {
            foreach (var kv in f.Vars)
                if ((kv.Key is ILocalSymbol || kv.Key is IParameterSymbol) && MayBeNullType(TypeOf(kv.Key)) && kv.Value.Sort == Sort.Int)
                    AssumeSide(T.Not(T.Eq(obj, kv.Value)));
            if (f.This != null) AssumeSide(T.Not(T.Eq(obj, f.This)));
            if (ctor != null) HavocFields(f, ctor, null, modifiable);
            if (f.Alloc != null)
            {
                // allocated just now
                AssumeSide(T.Not(InSet(f.Alloc, obj)));
                f.Alloc = T.Store(f.Alloc, obj, T.Int(1));
            }
            var beforeInit = f.Clone();
            var set = ctor != null ? _engine.Fields.SelfWritesOf(ctor) : new HashSet<ISymbol>(SymbolEqualityComparer.Default);
            bool chains = ctor != null && ChainedInitializer(ctor, _model) != null;
            foreach (var field in FieldEffects.FieldsOf(type))
            {
                // (a non-null field is set somewhere: by the constructor, possibly through a callee, or the initializer)
                bool unknown = chains || set.Contains(field) || HasInitializer(field) || !DeclaredIn(field, type) || IsNonNullField(field);
                var value = unknown ? _z3.Fresh(field.Name, ValueSort(field)) : DefaultValue(field);
                f.Fields[field] = T.Store(FieldMap(f, field), obj, value);
            }
            f.Link = new StateLink { Before = beforeInit, Changed = T.Store(T.ZeroRow(), obj, T.Int(1)) };
        }
    }
}
