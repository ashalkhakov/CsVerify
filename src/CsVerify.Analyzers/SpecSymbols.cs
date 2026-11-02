using System.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace CsVerify.Analyzers
{
    /// <summary>
    /// Recognizes the CsVerify specification library by name, so analyzers and verifier work whether the user
    /// references the CsVerify.Spec assembly or compiles its sources.
    /// </summary>
    public static class SpecSymbols
    {
        public const string Namespace = "CsVerify";
        public const string SpecSymbol = "CSVERIFY_SPEC";

        public static bool IsCsVerifyType(ITypeSymbol type, string metadataName) =>
            type != null && type.OriginalDefinition.MetadataName == metadataName &&
            type.ContainingNamespace?.ToDisplayString() == Namespace;

        public static bool IsSpecClass(ITypeSymbol type) => IsCsVerifyType(type, "Spec");
        public static bool IsGhostType(ITypeSymbol type) => IsCsVerifyType(type, "Ghost`1");
        public static bool IsGhostOf(IMethodSymbol m) => m != null && m.Name == "Of" && IsCsVerifyType(m.ContainingType, "Ghost");

        public static bool HasAttribute(ISymbol symbol, string name) =>
            symbol != null && symbol.GetAttributes().Any(a =>
                a.AttributeClass?.Name == name && a.AttributeClass.ContainingNamespace?.ToDisplayString() == Namespace);

        public static bool IsLemma(ISymbol s) => HasAttribute(s, "LemmaAttribute");
        public static bool IsGhostFunction(ISymbol s) => HasAttribute(s, "GhostFunctionAttribute");
        /// <summary>[Pure] or [GhostFunction]: a mathematical function the verifier may use in specifications.</summary>
        public static bool IsPure(ISymbol s) => HasAttribute(s, "PureAttribute") || IsGhostFunction(s);
        public static bool IsSeqType(ITypeSymbol type) => IsCsVerifyType(type, "Seq`1") || IsCsVerifyType(type, "Seq");

        public static bool IsTrusted(ISymbol s)
        {
            for (var cur = s; cur != null; cur = cur.ContainingSymbol)
                if (HasAttribute(cur, "TrustedAttribute")) return true;
            return false;
        }

        public static bool IsLinear(ITypeSymbol type)
        {
            for (var t = type; t != null; t = t.BaseType)
                if (HasAttribute(t.OriginalDefinition, "LinearAttribute")) return true;
            return false;
        }

        /// <summary>A method whose arguments are ghost: specification statements, Ghost.Of, lemmas.</summary>
        public static bool IsGhostMethod(IMethodSymbol m) =>
            m != null && (IsSpecClass(m.ContainingType) || IsGhostOf(m) || IsLemma(m.OriginalDefinition) ||
                          IsGhostFunction(m.OriginalDefinition) || IsSeqType(m.ContainingType));

        /// <summary>
        /// True when <paramref name="node"/> sits where ghost values are legal: inside the arguments of a ghost
        /// method call, or in the body of a lemma.
        /// </summary>
        public static bool IsInGhostContext(SyntaxNode node, SemanticModel model)
        {
            for (var cur = node; cur != null; cur = cur.Parent)
            {
                switch (cur)
                {
                    case ArgumentSyntax arg when arg.Parent?.Parent is InvocationExpressionSyntax inv:
                        if (model.GetSymbolInfo(inv).Symbol is IMethodSymbol m && IsGhostMethod(m)) return true;
                        break;
                    case MethodDeclarationSyntax md:
                        var declared = model.GetDeclaredSymbol(md);
                        return IsLemma(declared) || IsGhostFunction(declared);
                    case LocalFunctionStatementSyntax lf:
                        if (IsLemma(model.GetDeclaredSymbol(lf))) return true;
                        break;
                }
            }
            return false;
        }

        /// <summary>The outermost Spec statement (void Spec.* call) that is <paramref name="node"/> or contains it in its arguments.</summary>
        public static InvocationExpressionSyntax EnclosingSpecCall(SyntaxNode node, SemanticModel model)
        {
            InvocationExpressionSyntax found = null;
            for (var cur = node; cur != null; cur = cur.Parent)
            {
                var inv = cur as InvocationExpressionSyntax ??
                          (cur is ArgumentSyntax arg ? arg.Parent?.Parent as InvocationExpressionSyntax : null);
                if (inv != null && (cur == inv || cur.Parent?.Parent == inv) &&
                    model.GetSymbolInfo(inv).Symbol is IMethodSymbol m && IsSpecClass(m.ContainingType) && m.ReturnsVoid)
                    found = inv;
                if (cur is MemberDeclarationSyntax) break;
            }
            return found;
        }
    }
}
