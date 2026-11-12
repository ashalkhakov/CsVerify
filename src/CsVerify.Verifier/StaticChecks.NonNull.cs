using System.Collections.Generic;
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
    internal sealed partial class StaticChecks
    {
        private static ITypeSymbol FieldType(ISymbol field) =>
            field.OriginalDefinition is IFieldSymbol fd ? fd.Type : field.OriginalDefinition is IMethodSymbol model ? model.ReturnType : ((IPropertySymbol)field.OriginalDefinition).Type;

        /// <summary>
        /// <c>required</c> (every object initializer sets it, the compiler checks), or <c>[JsonRequired]</c> (the
        /// deserializer sets it or throws: trusted, for objects that System.Text.Json builds).
        /// </summary>
        private static bool IsRequired(ISymbol field) =>
            (field is IFieldSymbol f ? f.IsRequired : field is IPropertySymbol p && p.IsRequired) ||
            field.GetAttributes().Any(a => a.AttributeClass?.Name == "JsonRequiredAttribute" &&
                                           a.AttributeClass.ContainingNamespace?.ToDisplayString() == "System.Text.Json.Serialization");

        /// <summary>
        /// A class whose instance constructor has no body of its own (it has none, or a primary constructor) is never
        /// verified as a method, so its fields' initializers are checked here: each non-nullable field (not
        /// <c>required</c>) must start not null. Its initializer must make an object or array, be a string literal
        /// or interpolation, call a method that returns non-null, or be a non-nullable parameter of the primary
        /// constructor. <c>= null!</c>, or no initializer, is reported (CSV1014).
        /// </summary>
        internal static IEnumerable<(ISymbol field, SyntaxNode at, string message)> ImplicitConstructorNulls(INamedTypeSymbol type, System.Func<SyntaxTree, SemanticModel> modelOf)
        {
            if (type.TypeKind != TypeKind.Class || type.IsStatic || type.IsRecord) yield break;
            if (type.InstanceConstructors.Any(c => c.DeclaringSyntaxReferences.Any(r => r.GetSyntax() is ConstructorDeclarationSyntax))) yield break;
            foreach (var field in FieldEffects.FieldsOf(type).Where(x => !x.IsStatic && SymbolEqualityComparer.Default.Equals(x.ContainingType, type)))
            {
                if (!FieldEffects.IsHeapField(field) || !IsNonNullableType(FieldType(field)) || IsRequired(field)) continue;
                var decl = field.DeclaringSyntaxReferences.Select(r => r.GetSyntax()).FirstOrDefault();
                if (decl == null) continue;
                var init = decl switch
                {
                    VariableDeclaratorSyntax v => v.Initializer?.Value,
                    PropertyDeclarationSyntax pd => pd.Initializer?.Value,
                    _ => null,
                };
                if (init == null)
                    yield return (field, decl, $"'{field.Name}' is not nullable, but {type.Name}'s constructor leaves it null: give it an initializer, make it required, or write a constructor that sets it");
                else if (!StartsNotNull(init, modelOf(init.SyntaxTree)))
                    yield return (field, init, $"'{field.Name}' is not nullable, but its initializer '{init}' might be null when {type.Name}'s constructor returns");
            }
        }

        private static bool StartsNotNull(ExpressionSyntax init, SemanticModel model)
        {
            switch (init)
            {
                case BaseObjectCreationExpressionSyntax _:
                case ArrayCreationExpressionSyntax _:
                case ImplicitArrayCreationExpressionSyntax _:
                case CollectionExpressionSyntax _:
                case InterpolatedStringExpressionSyntax _:
                    return true;
                case LiteralExpressionSyntax l: return l.IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.StringLiteralExpression);
                case ParenthesizedExpressionSyntax paren: return StartsNotNull(paren.Expression, model);
                case InvocationExpressionSyntax call:
                    return model.GetSymbolInfo(call).Symbol is IMethodSymbol m && IsNonNullableReturn(m) && !(model.GetOperation(call) is null);
                case IdentifierNameSyntax id:
                    // a primary constructor's parameter: each caller proves it is not null
                    return model.GetSymbolInfo(id).Symbol is IParameterSymbol ps && ps.RefKind == RefKind.None && IsNonNullableType(ps.Type);
                case MemberAccessExpressionSyntax ma when ma.Name.Identifier.Text == "Empty":
                    // string.Empty, Array.Empty<T>() is a call
                    return model.GetSymbolInfo(ma).Symbol is IFieldSymbol f && f.ContainingType.SpecialType == SpecialType.System_String;
                default: return false;
            }
        }
    }
}
