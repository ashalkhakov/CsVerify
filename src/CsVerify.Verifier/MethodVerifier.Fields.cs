using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Permissions to single fields of [Owned] objects (Viper's <c>acc(o.f)</c>): <c>Spec.Acc(o, nameof(C.F))</c>.
    /// The whole-object mask (Frame.Perm: views, Spec.Acc(o)) stays as it is; Frame.FPerm holds fields one by one,
    /// object -> field -> amount. Writing o.F needs either. Giving a field out of a whole object splits it (the
    /// other fields stay, one by one); holding every field again makes the object whole. A folded field records
    /// its instance in Frame.FOwner (object -> field -> instance), so a call changes only the fields it gets.
    /// Fields of sealed classes without an [Invariant] only, and not [Owns] fields: invariants and ownership trees
    /// are about whole objects.
    /// </summary>
    internal sealed partial class MethodVerifier
    {
        private int FieldId(ISymbol field) => _engine.FieldId(FieldEffects.Key(field));

        /// <summary>Instances given away at calls whose predicates hold single fields (only those can own one).</summary>
        private readonly HashSet<string> _instancesWithFields = new HashSet<string>();
        private readonly Dictionary<IMethodSymbol, bool> _predicateHasFields = new Dictionary<IMethodSymbol, bool>(SymbolEqualityComparer.Default);

        /// <summary>Does a predicate's body (or one it names, transitively) hold a single field?</summary>
        private bool PredicateHasFields(IMethodSymbol pred)
        {
            pred = pred.OriginalDefinition;
            if (_predicateHasFields.TryGetValue(pred, out var known)) return known;
            _predicateHasFields[pred] = false; // (recursion: no more than what the rest says)
            var body = _engine.ContractOf(pred).PureBody;
            bool has = body != null && body.DescendantsAndSelf().Any(o =>
                IsAccCall(o, out var acc) && acc.Arguments.Length == 2 && !(Unconverted(acc.Arguments[0].Value).Type is IArrayTypeSymbol) ||
                IsPredicateCall(o, out var inner) && PredicateHasFields(inner.TargetMethod));
            return _predicateHasFields[pred] = has;
        }

        private static string FieldAmount(Frame f, Term o, int k) => $"(select (select {f.FPerm} {T.Coerce(o, Sort.Int)}) {k})";

        /// <summary>Write permission to o.F in f: the whole object, or that field.</summary>
        private Term CanWriteField(Frame f, Term o, ISymbol field) =>
            f.FPerm == null ? CanWrite(f, o) : T.Or(CanWrite(f, o), new Term($"(>= {FieldAmount(f, o, FieldId(field))} 1.0)", Sort.Bool));

        private void ChangeField(Frame f, Term o, int k, Term guard, string op)
        {
            var i = T.Coerce(o, Sort.Int);
            f.FPerm = _z3.Define("fperm", new Term($"(store {f.FPerm} {i} (store (select {f.FPerm} {i}) {k} ({op} {FieldAmount(f, o, k)} (ite {guard} 1.0 0.0))))", Sort.PermHeap));
        }

        /// <summary>The fields a whole object of this type has (the ones a split hands out one by one).</summary>
        private static List<ISymbol> WholeFields(ITypeSymbol type) =>
            FieldEffects.FieldsOf(type).Where(x => FieldEffects.IsHeapField(x)).Select(FieldEffects.Key).Distinct(SymbolEqualityComparer.Default).ToList();

        /// <summary>The field of Spec.Acc(o, name), or null (reported) if it cannot have a permission of its own.</summary>
        private ISymbol AccField(ITypeSymbol type, string name, SyntaxNode at)
        {
            var field = WholeFields(type).FirstOrDefault(x => x.Name == name);
            string why = field == null ? $"{type.Name} has no field '{name}'"
                : !(type is INamedTypeSymbol n && n.IsSealed) ? $"{type.Name} is not sealed (a subclass would have fields this cannot account for)"
                : DataTypes.Invariants(type).Any() ? $"{type.Name} has an [Invariant], which is about the whole object"
                : SpecSymbols.IsOwnsField(field) ? $"'{name}' is an [Owns] field: ownership trees change hands whole"
                : null;
            if (why == null) return field;
            Report("CSV1016", at, $"Spec.Acc of a single field: {why}", isError: true);
            return null;
        }

        /// <summary>Gives o.F up (at a call, a return, a fold): from the field's own permission, or split off the whole object.</summary>
        private void GiveField(Frame f, Term o, ISymbol field, Term guard, SyntaxNode at, string what)
        {
            int k = FieldId(field);
            Require(T.Implies(guard, CanWriteField(f, o, field)), "CSV1016", at, what);
            var own = new Term($"(>= {FieldAmount(f, o, k)} 1.0)", Sort.Bool);
            var split = T.And(guard, T.Not(own));
            // the whole object goes, every other field comes back one by one
            f.Perm = Change(f.Perm, o, split, "-");
            foreach (var other in WholeFields(field.ContainingType).Where(x => FieldId(x) != k))
                ChangeField(f, o, FieldId(other), split, "+");
            ChangeField(f, o, k, T.And(guard, own), "-");
        }

        /// <summary>Receives o.F (at entry, after a call, an unfold); with every field in hand the object is whole again.</summary>
        private void TakeField(Frame f, Term o, ISymbol field, Term guard)
        {
            int k = FieldId(field);
            // nobody else can hold it: not the whole object, not the field
            _z3.Assume(T.Implies(guard, T.And(NotNull(o), BelowWhole(f, o), new Term($"(< {FieldAmount(f, o, k)} 1.0)", Sort.Bool))));
            ChangeField(f, o, k, guard, "+");
            var fields = WholeFields(field.ContainingType);
            var all = T.And(new[] { guard }.Concat(fields.Select(x => new Term($"(>= {FieldAmount(f, o, FieldId(x))} 1.0)", Sort.Bool))).ToArray());
            foreach (var x in fields) ChangeField(f, o, FieldId(x), all, "-");
            f.Perm = Change(f.Perm, o, all, "+");
        }

        /// <summary>No single field of o is in hand (a whole object received is nobody else's, field by field either).</summary>
        private Term NoFieldsHeld(Frame f, Term o, ITypeSymbol type) =>
            f.FPerm == null ? T.True : T.And(WholeFields(type).Select(x => new Term($"(< {FieldAmount(f, o, FieldId(x))} 1.0)", Sort.Bool)).ToArray());

        /// <summary>Folds o.F into instance p: its owner is p.</summary>
        private void FoldField(Frame f, Term o, ISymbol field, Term guard, Term p)
        {
            var i = T.Coerce(o, Sort.Int);
            int k = FieldId(field);
            f.FOwner = _z3.Define("fowner", new Term($"(store {f.FOwner} {i} (store (select {f.FOwner} {i}) {k} (ite {guard} {p} (select (select {f.FOwner} {i}) {k}))))", Sort.Heap));
        }

        /// <summary>A write of an owned field: the whole object's permission, or the field's.</summary>
        private void RequireWriteField(Term o, ISymbol field, Frame f, SyntaxNode at)
        {
            if (!_codeMode || _foreignSpec > 0 || f.Perm == null) return;
            Require(CanWriteField(f, o, field), "CSV1016", at,
                $"'{at}' changes an [Owned] {field.ContainingType.Name} without holding its view (Own<{field.ContainingType.Name}>, with no read shares out), Spec.Acc for the field, or a frame lent to it");
        }

        /// <summary>In a predicate's body: a read of o.F needs a permission to it to its left (the object's, or the field's).</summary>
        private void CheckFraming(Term o, ISymbol field, Frame f, SyntaxNode at)
        {
            if (!_framingCheck || f.Perm == null) return;
            var whole = $"(> (select {f.Perm} {T.Coerce(o, Sort.Int)}) 0.0)";
            var own = f.FPerm != null ? $"(> {FieldAmount(f, o, FieldId(field))} 0.0)" : "false";
            Require(new Term($"(or {whole} {own})", Sort.Bool), "CSV1016", at,
                $"'{at}' reads an object this predicate has no Spec.Acc for (to its left): its value could change while the predicate is folded");
        }

        /// <summary>For the havoc after a call: is (y, field) given away, as a field (y one of <paramref name="fields"/>) or in a footprint?</summary>
        private string FieldTouched(ISymbol field, string y, Term fownerBefore, IReadOnlyList<(Term obj, ISymbol field)> fields, IReadOnlyList<Term> touchedInst)
        {
            int k = FieldId(field);
            var parts = fields.Where(t => FieldId(t.field) == k).Select(t => $"(= {y} {T.Coerce(t.obj, Sort.Int)})").ToList();
            if (fownerBefore != null)
                parts.AddRange(touchedInst.Where(q => _instancesWithFields.Contains(q.S)).Select(q => $"(= (select (select {fownerBefore} {y}) {k}) {q})"));
            return parts.Count == 0 ? null : parts.Count == 1 ? parts[0] : $"(or {string.Join(" ", parts)})";
        }
    }
}
