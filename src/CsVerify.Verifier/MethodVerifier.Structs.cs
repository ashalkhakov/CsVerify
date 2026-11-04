using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.FlowAnalysis;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Mutable fields (and settable auto-properties) of the program's structs. A struct is a value: each member is an
    /// uninterpreted function of it, as a readonly field is, and <c>s.X = v</c> makes s a new value whose X is v and
    /// whose other members are s's. That is value semantics exactly: a copy (<c>var t = s</c>, an argument) is the
    /// old value and does not change. The value is written back to where it lives: a local or parameter (a ref
    /// parameter is the caller's variable), a ref local, an array cell, an enclosing struct's member, or
    /// <c>this</c> in the struct's constructor. A struct held in a class's field, and a struct method other than a
    /// constructor that writes <c>this</c>, are not supported (the caller would not see the change).
    /// </summary>
    internal sealed partial class MethodVerifier
    {
        /// <summary>An instance field or auto-property of a struct of the program (not a data record or a view).</summary>
        private bool IsStructMember(ISymbol s)
        {
            if (s == null || s.IsStatic || !(s.ContainingType is INamedTypeSymbol t) || t.TypeKind != TypeKind.Struct) return false;
            if (t.DeclaringSyntaxReferences.Length == 0 || t.ContainingNamespace?.ToDisplayString() == SpecSymbols.Namespace ||
                Data.IsData(t) || SpecSymbols.IsLinearPackage(t) || SpecSymbols.IsViewType(t)) return false;
            switch (s)
            {
                case IFieldSymbol f: return !f.IsConst && !f.IsImplicitlyDeclared;
                case IPropertySymbol p:
                    return !p.IsIndexer && p.DeclaringSyntaxReferences.Length > 0 &&
                           p.DeclaringSyntaxReferences.All(r => r.GetSyntax() is PropertyDeclarationSyntax pd && pd.AccessorList != null &&
                                                                pd.AccessorList.Accessors.All(a => a.Body == null && a.ExpressionBody == null));
                default: return false;
            }
        }

        private static ITypeSymbol MemberType(ISymbol s) => s is IFieldSymbol f ? f.Type : ((IPropertySymbol)s).Type;

        /// <summary>Member <paramref name="member"/> of struct value <paramref name="v"/>.</summary>
        private Term StructMember(ISymbol member, Term v)
        {
            var def = member.OriginalDefinition;
            return _z3.Apply(def.ToDisplayString(), SortOf(MemberType(def)), new[] { v });
        }

        /// <summary><c>container.member = v</c>: container becomes a new value, the same but for member.</summary>
        private void WriteStructMember(IOperation container, ISymbol member, Term v, SyntaxNode at, Frame f, SpecEnv spec)
        {
            switch (Unconverted(container))
            {
                case IInstanceReferenceOperation _ when _method.MethodKind != MethodKind.Constructor:
                    NotModeled(at, $"'{at}' writes this struct in place: only its constructor may (a caller would not see the change)");
                    return;
                case IFieldReferenceOperation cf when !IsStructMember(cf.Field):
                case IPropertyReferenceOperation cp when !IsStructMember(cp.Property):
                    NotModeled(at, $"'{at}' writes a struct held in an object's field in place: copy it out, change the copy, and store it back");
                    return;
            }
            var old = Eval(container, f, spec);
            var updated = _z3.Fresh("struct", Sort.Int);
            _z3.Assume(T.Eq(StructMember(member, updated), T.Coerce(v, SortOf(MemberType(member.OriginalDefinition)))));
            foreach (var other in member.ContainingType.GetMembers().Where(o => IsStructMember(o) && !SymbolEqualityComparer.Default.Equals(o, member)))
                _z3.Assume(T.Eq(StructMember(other, updated), StructMember(other, old)));
            if (Unconverted(container) is IInstanceReferenceOperation) f.This = updated;
            else if (Unconverted(container) is IFlowCaptureReferenceOperation r &&
                     (!(_captured.TryGetValue(r.Id, out var c) && IsVariableReference(c)) || r.Syntax.AncestorsAndSelf().OfType<WithExpressionSyntax>().Any()))
                f.Captures[r.Id] = updated; // a new value being initialized: new S { X = 1 }, or s with { X = 1 } (a copy of s)
            else Write(container, updated, f, spec);
        }
    }
}
