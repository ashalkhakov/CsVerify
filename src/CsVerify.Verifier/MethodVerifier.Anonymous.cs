using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Tuples and anonymous objects (<c>new { x, y = x * 2 }</c>, and what query syntax makes for <c>let</c> and a second
    /// <c>from</c>) as values: one constructor per anonymous type, applied to the members' values, which selectors read
    /// back. Objects with equal members are the same term, as their Equals has them equal (so GroupBy and Distinct by
    /// one work); <c>==</c> between two anonymous objects compares references, which is not modeled (unknown); they are
    /// not null. A tuple's constructor is its type's (without its names), read by <c>tuple.ItemN</c>. (A value made by a
    /// constructor, not a fresh constant: in a lambda a query applies, a constant would be one for every element. Its
    /// parts are read back by side facts where it is made, as a fresh tuple's were.)
    /// </summary>
    internal sealed partial class MethodVerifier
    {
        private static List<IPropertySymbol> AnonymousMembers(INamedTypeSymbol type) =>
            type.GetMembers().OfType<IPropertySymbol>().ToList();

        private static string AnonymousName(ITypeSymbol type) => "anon:" + type.ToDisplayString();

        private Term AnonymousObject(IAnonymousObjectCreationOperation ao, Frame f, SpecEnv spec)
        {
            var type = (INamedTypeSymbol)ao.Type;
            var members = AnonymousMembers(type);
            var args = new Term[members.Count];
            foreach (var init in ao.Initializers)
            {
                if (!(init is ISimpleAssignmentOperation a && a.Target is IPropertyReferenceOperation target)) { Unsupported(init); return Unknown(type); }
                int k = members.FindIndex(p => SymbolEqualityComparer.Default.Equals(p, target.Property));
                args[k] = T.Coerce(Eval(a.Value, f, spec), Sort.Int);
            }
            for (int k = 0; k < args.Length; k++) args[k] ??= T.Int(0);
            var name = AnonymousName(type);
            // the object of its parts (a function of them, so of an element where a query makes one), each read back
            var made = _z3.Apply(name, Sort.Int, args);
            _anonymousParts[made.S] = args;
            ReadBack(name, made, args, m => NotNull(m), (m, k) => v => T.Eq(_z3.Apply(name + "." + members[k].Name, Sort.Int, new[] { m }), v));
            return made;
        }

        /// <summary>
        /// The facts of a value made by a constructor: in code, of this one (side facts); inside a query, where it is
        /// made for each element under a quantifier, an axiom for the constructor (once, for as long as its scope lasts).
        /// </summary>
        private void ReadBack(string name, Term made, Term[] args, Func<Term, Term> always, Func<Term, int, Func<Term, Term>> part)
        {
            int arity = args.Length;
            if (_queryContexts.Count == 0)
            {
                if (always != null) AssumeSide(always(made));
                for (int k = 0; k < arity; k++) AssumeSide(part(made, k)(args[k]));
                return;
            }
            _z3.AssumeOnce(name, () =>
            {
                var vars = Enumerable.Range(0, arity).Select(_ => new Term(_z3.FreshName("m"), Sort.Int)).ToArray();
                var m = _z3.Apply(name, Sort.Int, vars);
                var facts = new List<Term>();
                if (always != null) facts.Add(always(m));
                for (int k = 0; k < arity; k++) facts.Add(part(m, k)(vars[k]));
                var body = T.And(facts.ToArray());
                return vars.Length == 0 ? body
                    : new Term($"(forall ({string.Join(" ", vars.Select(v => $"({v.S} Int)"))}) (! {body.S} :pattern ({m.S})))", Sort.Bool);
            });
        }

        // the parts of the anonymous objects made, by their terms: a member read of one is its part, a query's handle
        // too (GroupJoin's matches in new { x, ys }), which a selector's value would not be
        private readonly Dictionary<string, Term[]> _anonymousParts = new Dictionary<string, Term[]>();

        private Term TupleValue(ITupleOperation tuple, Frame f, SpecEnv spec)
        {
            var type = (INamedTypeSymbol)tuple.Type;
            var fields = type.TupleElements;
            var args = tuple.Elements.Select(e => Eval(e, f, spec)).ToArray();
            var name = "tuple:" + (type.TupleUnderlyingType ?? type).ToDisplayString();
            var ints = args.Select(a => T.Coerce(a, Sort.Int)).ToArray();
            var made = _z3.Apply(name, Sort.Int, ints);
            ReadBack(name, made, ints, null, (m, k) => v => T.Eq(T.Coerce(TupleItem(m, fields[k]), Sort.Int), v));
            return made;
        }

        /// <summary><c>t.y</c> of an anonymous object: its selector (null for other properties).</summary>
        private Term AnonymousMember(IPropertyReferenceOperation pr, Frame f, SpecEnv spec)
        {
            if (pr.Instance == null || pr.Property.ContainingType?.IsAnonymousType != true) return null;
            var t = T.Coerce(Eval(pr.Instance, f, spec), Sort.Int);
            Deref(pr.Instance, t, pr.Syntax);
            var read = _anonymousParts.TryGetValue(t.S, out var parts)
                ? parts[AnonymousMembers(pr.Property.ContainingType).FindIndex(p => p.Name == pr.Property.Name)]
                : _z3.Apply(AnonymousName(pr.Property.ContainingType) + "." + pr.Property.Name, Sort.Int, new[] { t });
            if (_queries.ContainsKey(read.S)) AssumeSide(NotNull(read)); // (a query it carries, GroupJoin's matches: an object)
            return InRangeOf(T.Coerce(read, SortOf(pr.Type)), pr.Type);
        }
    }
}
