using System;
using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using static CsVerify.Verifier.Boogie.KernelTypes;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>Object invariants: proved and assumed.</summary>
    internal sealed partial class Checks
    {
        /// <summary>
        /// An invariant, or what one of its class's invariants calls: while it is verified, the invariant isn't assumed
        /// (a helper could otherwise be proved from the very invariant it defines).
        /// </summary>
        private static bool DefinesInvariant(IMethodSymbol m)
        {
            var invariants = DataTypes.Invariants(m.ContainingType).Select(i => i.OriginalDefinition).ToList();
            if (invariants.Any(i => SymbolEqualityComparer.Default.Equals(i, m.OriginalDefinition))) return true;
            return invariants.SelectMany(i => i.DeclaringSyntaxReferences).Select(r => r.GetSyntax())
                .Any(n => n.DescendantNodes().OfType<Microsoft.CodeAnalysis.CSharp.Syntax.IdentifierNameSyntax>().Any(id => id.Identifier.Text == m.Name));
        }

        /// <summary>An immutable object (or null) of a class with invariants: they hold, as they did when it was built.</summary>
        private void ObjectInvariant(KExpr o, ITypeSymbol type)
        {
            if (!HasObjectInvariant(type) || !(Invariant(type, o) is KExpr inv)) return;
            Assume(new KOp("||", new KOp("==", o, new KLit("null")), inv));
        }

        /// <summary>The class's [Invariant]s of o (null if it has none).</summary>
        private KExpr Invariant(ITypeSymbol type, KExpr o)
        {
            var parts = new List<KExpr>();
            foreach (var inv in DataTypes.Invariants(type))
            {
                var m = inv.OriginalDefinition;
                if (!_program.IsFunction(m)) throw new NotTranslated("the invariant " + m.Name);
                parts.Add(new KFnApp { Callee = m, Function = FunctionName(m), Fields = _program.FunctionFields(m), Args = new[] { o } });
            }
            return parts.Count == 0 ? null : And(parts);
        }

        private void ProveInvariant(ITypeSymbol type, KExpr o, SyntaxNode at, string when)
        {
            if (Invariant(type, o) is KExpr inv) Assert(inv, At("CSV1015", at, $"invariant of {type.Name} might not hold {when}"));
        }

        private void AssumeInvariant(ITypeSymbol type, KExpr o)
        {
            if (Invariant(type, o) is KExpr inv) Assume(inv);
            // (what a view's object refers to was there before it: allocated, so nothing built later is any of it)
            if (KernelTypes.Trees && IsOwnedClass(type))
                foreach (var g in InstanceFields(type).Where(g => IsRef(FieldType(g))))
                    Assume(Allocated(o, new KOp("sel", new KVar(FieldMap(g)), o)));
        }
    }
}
