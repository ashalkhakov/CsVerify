using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Fields of non-nullable reference type (<c>Rule rp</c>, not <c>Rule? rp</c>) are never null once their object
    /// is built: every write proves it (CSV1014), so every read may assume it. An object is built when its
    /// constructor returns, which must have set all such fields but the <c>required</c> ones, which the compiler
    /// makes every object initializer set (and a <c>[SetsRequiredMembers]</c> constructor must set too); until then
    /// <c>this</c> may not escape (CSV1015). A static field is never null when it starts with an object (an initializer
    /// creating one); every write keeps it so. Array elements promise nothing (<c>new Rule[n]</c> holds nulls).
    /// </summary>
    internal sealed partial class MethodVerifier
    {
        private static ITypeSymbol FieldType(ISymbol field) =>
            field.OriginalDefinition is IFieldSymbol fd ? fd.Type : field.OriginalDefinition is IMethodSymbol model ? model.ReturnType : ((IPropertySymbol)field.OriginalDefinition).Type;

        /// <summary>A heap field whose value, once its object is built, is never null.</summary>
        internal bool IsNonNullField(ISymbol field)
        {
            if (!FieldEffects.IsHeapField(field) || !IsNonNullableType(FieldType(field))) return false;
            return !field.IsStatic || StartsWithObject(field);
        }

        /// <summary>
        /// A static field whose initializer makes an object, is a string literal, or calls a method whose return type
        /// is not nullable (which its return statements prove, or the library declares): not null to begin with.
        /// </summary>
        internal bool StartsWithObject(ISymbol field)
        {
            return field.DeclaringSyntaxReferences.Select(r => r.GetSyntax()).OfType<VariableDeclaratorSyntax>().Any(v =>
                v.Initializer?.Value is BaseObjectCreationExpressionSyntax || v.Initializer?.Value is ArrayCreationExpressionSyntax ||
                v.Initializer?.Value is ImplicitArrayCreationExpressionSyntax || v.Initializer?.Value is CollectionExpressionSyntax ||
                v.Initializer?.Value is LiteralExpressionSyntax l && l.IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.StringLiteralExpression) ||
                v.Initializer?.Value is InvocationExpressionSyntax call &&
                _engine.ModelOf(call.SyntaxTree).GetSymbolInfo(call).Symbol is IMethodSymbol m && IsNonNullableReturn(m));
        }

        private static bool IsRequired(ISymbol field) => field is IFieldSymbol f ? f.IsRequired : field is IPropertySymbol p && p.IsRequired;

        /// <summary>The non-null fields a constructor must set itself.</summary>
        private System.Collections.Generic.IEnumerable<ISymbol> SetByConstructor(IMethodSymbol ctor) =>
            FieldEffects.FieldsOf(ctor.ContainingType).Where(IsNonNullField)
                .Where(x => !IsRequired(x) || ctor.GetAttributes().Any(a => a.AttributeClass?.Name == "SetsRequiredMembersAttribute"));

        private bool HasNonNullFields(ITypeSymbol type) => FieldEffects.FieldsOf(type).Any(IsNonNullField);

        /// <summary>Reading a non-null field: not null, unless it is this object's own, still being built.</summary>
        private void AssumeNonNullRead(ISymbol field, IOperation instance, Term v)
        {
            if (!IsNonNullField(field)) return;
            if (instance is IInstanceReferenceOperation && _method.MethodKind == MethodKind.Constructor) return;
            AssumeSide(NotNull(v));
        }

        /// <summary>
        /// A static readonly field (not a heap field: it is set once) that starts with an object never changes, so it
        /// is never null (a static constructor could set it again, but only to what it then proves).
        /// </summary>
        private bool IsNonNullReadonlyStatic(IFieldSymbol field) =>
            field.IsStatic && field.IsReadOnly && IsNonNullableType(field.OriginalDefinition.Type) && StartsWithObject(field) &&
            !(field.ContainingType.StaticConstructors.Any(c => c.DeclaringSyntaxReferences.Length > 0));

        /// <summary>
        /// A local or parameter of non-nullable type (<c>Config ptr</c>; not <c>var</c>, whose type is nullable): every
        /// write proves the value is not null, so it stays not null where a loop forgets its value.
        /// </summary>
        private void CheckNonNullVariable(ISymbol variable, Term v, SyntaxNode at)
        {
            if (!_codeMode || v.Sort != Sort.Int) return;
            if (IsNonNullVariable(variable)) Prove(NotNull(v), "CSV1014", at, $"'{at}' might store null, but '{variable.Name}' is not nullable");
        }

        private static bool IsNonNullVariable(ISymbol variable) =>
            variable is ILocalSymbol l ? IsNonNullableType(l.Type) && l.RefKind == RefKind.None
            : variable is IParameterSymbol p && p.RefKind == RefKind.None && IsNonNullable(p);

        private void CheckNonNullWrite(ISymbol field, Term v, SyntaxNode at)
        {
            if (IsNonNullField(field) && _codeMode)
                Prove(NotNull(v), "CSV1014", at, $"'{at}' might store null, but field '{field.Name}' is not nullable");
        }

        /// <summary>When a constructor returns: the non-null fields it must set are set.</summary>
        private void ProveConstructorSetFields(Frame f, SyntaxNode at)
        {
            if (_method.MethodKind != MethodKind.Constructor || _method.IsStatic || f.This == null) return;
            foreach (var field in SetByConstructor(_method))
                Prove(NotNull(T.Select(FieldMap(f, field), f.This, ValueSort(field))), "CSV1014", at,
                    $"field '{field.Name}' is not nullable, but might be null when the constructor of {_method.ContainingType.Name} returns");
        }

        /// <summary>After <c>this(...)</c> or <c>base(...)</c>: the fields that constructor sets are not null.</summary>
        private void AssumeChainedSetFields(Frame f, IMethodSymbol ctor, Term obj)
        {
            foreach (var field in SetByConstructor(ctor))
                _z3.Assume(NotNull(T.Select(FieldMap(f, field), obj, ValueSort(field))));
        }
    }
}
