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

        /// <summary>A field's map: object to Int (to a set, for an ObjSet-valued ghost field such as Repr).</summary>
        private static Sort ValueSort(ISymbol field) =>
            SortOf(field is IFieldSymbol fd ? fd.Type : ((IPropertySymbol)field).Type) == Sort.Row ? Sort.Row : Sort.Int;

        private static Sort MapSort(ISymbol field) => ValueSort(field) == Sort.Row ? Sort.Heap : Sort.Row;

        private Term FreshMap(ISymbol field) => _z3.Fresh(field.Name + "$map", MapSort(field));

        private static Term DefaultValue(ISymbol field) => ValueSort(field) == Sort.Row ? T.ZeroRow() : T.Int(0);

        private Term FieldMap(Frame f, ISymbol field)
        {
            field = FieldEffects.Key(field);
            if (f.Fields.TryGetValue(field, out var map)) return map;
            var key = field.ToDisplayString() + "#" + f.FieldEpoch;
            if (!_fieldStates.TryGetValue(key, out map))
                _fieldStates[key] = map = FreshMap(field);
            return map;
        }

        private Term ReadField(ISymbol field, IOperation instance, ITypeSymbol type, SyntaxNode at, Frame f, SpecEnv spec)
        {
            var o = Eval(instance, f, spec);
            Deref(instance, o, at);
            CheckRead(field, o, at);
            var v = T.Select(FieldMap(f, field), o, ValueSort(field));
            // what an [Owns] field refers to is in the same ownership tree, and is not its root (it is owned)
            if (f.Root != null && SpecSymbols.IsOwnsField(field))
                AssumeSide(T.Implies(NotNull(v), T.And(T.Eq(RootOf(f, v), RootOf(f, o)), T.Not(T.Eq(RootOf(f, v), v)))));
            HasType(v, type);
            // a field of an allocated object refers to an allocated object
            if (f.Alloc != null && MayBeNullType(type))
                AssumeSide(T.Implies(T.And(InSet(f.Alloc, o), NotNull(v)), InSet(f.Alloc, v)));
            return ValueSort(field) == Sort.Row ? v : InRangeOf(T.Coerce(v, SortOf(type)), type);
        }

        private void WriteField(ISymbol field, IOperation instance, Term v, SyntaxNode at, Frame f, SpecEnv spec)
        {
            var o = Eval(instance, f, spec);
            Deref(instance, o, at);
            RequireWritePermission(field, o, f, at);
            var before = f.Clone();
            f.Fields[FieldEffects.Key(field)] = T.Store(FieldMap(f, field), o, T.Coerce(v, ValueSort(field)));
            f.Link = new StateLink { Before = before, Changed = T.Store(T.ZeroRow(), o, T.Int(1)) };
        }

        /// <summary>
        /// After a call: the heap fields it may write have unknown values (an inferred frame condition). An owned
        /// field changes only at the objects whose views the call got or gave (<paramref name="touched"/>; null when
        /// that is not known), whatever the callee is.
        /// </summary>
        /// <param name="modifiable">for a callee with Spec.Modifies: the objects it may change (its frame, and objects
        /// allocated after the call began); every other object's fields stay as they were</param>
        private void HavocFields(Frame f, IMethodSymbol callee, IReadOnlyList<Term> touched = null, Term modifiable = null)
        {
            var (fields, all) = _engine.Fields.WritesOf(callee);
            if (fields.Count == 0 && !all) return;
            var owned = all ? _engine.Fields.OwnedFields() : fields.Where(IsOwnedField).ToList();
            var before = f.Clone();
            if (all && modifiable != null)
            {
                // a virtual call with a declared frame: whichever override runs writes only within it
                fields = new HashSet<ISymbol>(_engine.Fields.AllFields().Where(x => !IsOwnedField(x)), SymbolEqualityComparer.Default);
                owned = touched == null ? _engine.Fields.OwnedFields() : owned;
                all = false;
            }
            if (all) HavocAllFields(f, keepOwned: touched != null);
            foreach (var field in fields.Where(x => touched == null || !IsOwnedField(x)))
                f.Fields[field] = modifiable != null && !all && !IsOwnedField(field)
                    ? new Term($"({(MapSort(field) == Sort.Heap ? "cv_frameh" : "cv_frame")} {modifiable} {FieldMap(before, field)} {FreshMap(field)})", MapSort(field))
                    : FreshMap(field);
            // owned fields change at the objects whose views moved, which the link does not describe
            f.Link = modifiable != null && !all && owned.Count == 0 ? new StateLink { Before = before, Changed = modifiable } : null;
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
            string inTouched(string y) => touched.Count == 0 ? "false" : "(or " + string.Join(" ", touched.Select(t => $"(= (select {f.Root} {y}) {t})")) + ")";
            foreach (var field in inTrees)
                f.Fields[field] = new Term($"(lambda ((y Int)) (ite {inTouched("y")} (select {FreshMap(field)} y) (select {FieldMap(f, field)} y)))", MapSort(field));
            f.Root = new Term($"(lambda ((y Int)) (ite {inTouched("y")} (select {_z3.Fresh("root", Sort.Row)} y) (select {f.Root} y)))", Sort.Row);
        }

        private void HavocAllFields(Frame f, bool keepOwned = false)
        {
            var kept = keepOwned ? _engine.Fields.OwnedFields().ToDictionary(x => x, x => FieldMap(f, x), SymbolEqualityComparer.Default) : null;
            f.Link = null;
            f.Fields.Clear();
            f.FieldEpoch = ++_fieldEpochs;
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
            if (IsOwnedField(field)) RequireWriteView(o, f, at, field.ContainingType);
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
            if (ChainedInitializer(_method, _model) is ConstructorInitializerSyntax chained)
            {
                NotModeled(chained, "constructor chaining (this(...), or base(...) of a source class) is not supported yet");
                return;
            }
            var own = FieldEffects.FieldsOf(type).Where(s => DeclaredIn(s, type)).ToList();
            foreach (var field in own)
                _z3.Assume(T.Eq(T.Select(FieldMap(f, field), f.This, ValueSort(field)), DefaultValue(field)));
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
                bool unknown = chains || set.Contains(field) || HasInitializer(field) || !DeclaredIn(field, type);
                var value = unknown ? _z3.Fresh(field.Name, ValueSort(field)) : DefaultValue(field);
                f.Fields[field] = T.Store(FieldMap(f, field), obj, value);
            }
            f.Link = new StateLink { Before = beforeInit, Changed = T.Store(T.ZeroRow(), obj, T.Int(1)) };
        }
    }
}
