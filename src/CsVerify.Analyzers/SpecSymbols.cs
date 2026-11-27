using System.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Operations;

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
        public static bool IsInvariant(ISymbol s) => HasAttribute(s, "InvariantAttribute");
        public static bool IsPredicate(ISymbol s) => HasAttribute(s, "PredicateAttribute");
        public static bool IsOwnType(ITypeSymbol type) => IsCsVerifyType(type, "Own`1");
        public static bool IsSharedType(ITypeSymbol type) => IsCsVerifyType(type, "Shared`1");
        /// <summary>A view or a read share of one: Own&lt;T&gt; or Shared&lt;T&gt;.</summary>
        public static bool IsViewType(ITypeSymbol type) => IsOwnType(type) || IsSharedType(type);

        /// <summary>The interface or abstract class a [ContractClassFor] class gives contracts for; null if it is not one.</summary>
        public static INamedTypeSymbol ContractClassTarget(ITypeSymbol type) =>
            type?.GetAttributes().FirstOrDefault(a => a.AttributeClass?.Name == "ContractClassForAttribute" &&
                                                       a.AttributeClass.ContainingNamespace?.ToDisplayString() == Namespace)
                ?.ConstructorArguments.FirstOrDefault().Value as INamedTypeSymbol;
        /// <summary>The external type a [ContractsFor] stub gives contracts for; null if it is not one.</summary>
        public static INamedTypeSymbol ContractsForTarget(ITypeSymbol type) =>
            type?.GetAttributes().FirstOrDefault(a => a.AttributeClass?.Name == "ContractsForAttribute" &&
                                                       a.AttributeClass.ContainingNamespace?.ToDisplayString() == Namespace)
                ?.ConstructorArguments.FirstOrDefault().Value as INamedTypeSymbol;
        /// <summary>A class of contracts, not code: a [ContractClassFor] or [ContractsFor] class.</summary>
        public static bool IsContractsClass(ITypeSymbol type) => ContractClassTarget(type) != null || ContractsForTarget(type) != null;
        /// <summary>A [Model] function: ghost state of an external object.</summary>
        public static bool IsModel(ISymbol s) => s is IMethodSymbol && HasAttribute(s, "ModelAttribute");
        public static bool IsOwnsField(ISymbol field) => field is IFieldSymbol && HasAttribute(field, "OwnsAttribute");

        /// <summary>A class marked [Owned], or derived from one.</summary>
        public static bool IsOwned(ITypeSymbol type)
        {
            for (var t = type as INamedTypeSymbol; t != null; t = t.BaseType)
            {
                if (HasAttribute(t, "OwnedAttribute"))
                {
                    return true;
                }
            }
            return false;
        }

        /// <summary>
        /// A record class whose whole state (its own and its bases') is init-only positional properties, and the
        /// properties an abstract base's constructor stores its parameters in (StoredParameters).
        /// </summary>
        public static bool IsValueRecord(ITypeSymbol type)
        {
            for (var t = type as INamedTypeSymbol; t != null && t.SpecialType != SpecialType.System_Object; t = t.BaseType)
            {
                if (IsLinearPackage(t))
                {
                    return true;
                }
                if (!t.IsRecord || t.TypeKind != TypeKind.Class)
                {
                    return false;
                }
                var stored = StoredParameters(t.OriginalDefinition);
                foreach (var f in t.OriginalDefinition.GetMembers().OfType<IFieldSymbol>())
                {
                    if (!f.IsStatic && !(f.AssociatedSymbol is IPropertySymbol p && p.SetMethod?.IsInitOnly != false &&
                                         p.DeclaringSyntaxReferences.Length > 0 &&
                                         (p.DeclaringSyntaxReferences.All(r => r.GetSyntax() is ParameterSyntax) || stored != null && stored.ContainsKey(p))))
                    {
                        return false;
                    }
                }
            }
            return true;
        }

        /// <summary>
        /// A record's one constructor, where all it does is store its parameters, each in a get-only auto-property of
        /// the record's (private protected Command(DateTime now) => Now = now;): a primary constructor written out. Of
        /// an abstract record, or of a case under a record base; a case's may check its arguments first (StoredChecks).
        /// The parameter each property holds; null where the record has no such constructor.
        /// </summary>
        public static System.Collections.Generic.Dictionary<IPropertySymbol, IParameterSymbol> StoredParameters(INamedTypeSymbol t) => StoredBy(t)?.Parameters;

        /// <summary>
        /// What such a constructor checks before it stores: if (c) throw ...;, P = c ? p : throw ..., P = p ?? throw ...
        /// Each a condition of its parameters alone, and whether it throws where the condition holds or where it
        /// doesn't (Null: where the parameter is null). The record's value is built where none throws.
        /// </summary>
        public static System.Collections.Generic.IReadOnlyList<(ExpressionSyntax Condition, bool ThrowsWhen, IParameterSymbol Null)> StoredChecks(INamedTypeSymbol t) =>
            StoredBy(t)?.Checks ?? (System.Collections.Generic.IReadOnlyList<(ExpressionSyntax, bool, IParameterSymbol)>)System.Array.Empty<(ExpressionSyntax, bool, IParameterSymbol)>();

        private sealed class StoredConstructor
        {
            public System.Collections.Generic.Dictionary<IPropertySymbol, IParameterSymbol> Parameters;
            public System.Collections.Generic.List<(ExpressionSyntax Condition, bool ThrowsWhen, IParameterSymbol Null)> Checks = new System.Collections.Generic.List<(ExpressionSyntax, bool, IParameterSymbol)>();
        }

        private static readonly System.Runtime.CompilerServices.ConditionalWeakTable<INamedTypeSymbol, StoredConstructor[]> _storedBy =
            new System.Runtime.CompilerServices.ConditionalWeakTable<INamedTypeSymbol, StoredConstructor[]>();

        private static StoredConstructor StoredBy(INamedTypeSymbol t) => t == null ? null : _storedBy.GetValue(t, x => new[] { ReadStored(x) })[0];

        private static StoredConstructor ReadStored(INamedTypeSymbol t)
        {
            // (an abstract record, or a case of a record's: a sealed record of no record base is an object of its own)
            bool isCase = t.IsSealed && t.BaseType is { IsRecord: true, SpecialType: not SpecialType.System_Object };
            if (!t.IsRecord || !(t.IsAbstract || isCase) || t.TypeKind != TypeKind.Class)
            {
                return null;
            }
            var declared = t.InstanceConstructors.Where(c => !c.IsImplicitlyDeclared).ToList();
            if (declared.Count != 1 || declared[0].Parameters.Length == 0 || declared[0].Parameters.Any(p => p.RefKind != RefKind.None || p.IsParams) ||
                declared[0].DeclaringSyntaxReferences.Length != 1 ||
                !(declared[0].DeclaringSyntaxReferences[0].GetSyntax() is ConstructorDeclarationSyntax { Initializer: null } syntax))
            {
                return null;
            }
            var ctor = declared[0];
            var statements = syntax.ExpressionBody != null
                ? new StatementSyntax[] { Microsoft.CodeAnalysis.CSharp.SyntaxFactory.ExpressionStatement(syntax.ExpressionBody.Expression) }
                : syntax.Body?.Statements.ToArray();
            if (statements == null)
            {
                return null;
            }
            var made = new StoredConstructor { Parameters = new System.Collections.Generic.Dictionary<IPropertySymbol, IParameterSymbol>(SymbolEqualityComparer.Default) };
            IParameterSymbol Parameter(ExpressionSyntax e) => e is IdentifierNameSyntax r ? ctor.Parameters.FirstOrDefault(p => p.Name == r.Identifier.ValueText) : null;
            // (of its parameters alone: nothing of the record being built)
            bool OfParameters(ExpressionSyntax e) => !e.DescendantNodesAndSelf().Any(n => n is ThisExpressionSyntax || n is BaseExpressionSyntax ||
                n is IdentifierNameSyntax id && !(id.Parent is MemberAccessExpressionSyntax ma && ma.Name == id) && !(id.Parent is NameColonSyntax) &&
                !ctor.Parameters.Any(p => p.Name == id.Identifier.ValueText) && t.GetMembers(id.Identifier.ValueText).Any(m => !m.IsStatic));
            foreach (var st in statements)
            {
                // (a check: if (c) throw ...;)
                if (st is IfStatementSyntax { Else: null } guard && (guard.Statement is ThrowStatementSyntax || guard.Statement is BlockSyntax { Statements: { Count: 1 } only } && only[0] is ThrowStatementSyntax))
                {
                    if (!isCase || !OfParameters(guard.Condition))
                    {
                        return null;
                    }
                    made.Checks.Add((guard.Condition, true, null));
                    continue;
                }
                if (!((st as ExpressionStatementSyntax)?.Expression is AssignmentExpressionSyntax { RawKind: (int)Microsoft.CodeAnalysis.CSharp.SyntaxKind.SimpleAssignmentExpression } a))
                {
                    return null;
                }
                // (a name a parameter has is the parameter; any other, or this.P, the record's member)
                var member = a.Left switch
                {
                    IdentifierNameSyntax id when !ctor.Parameters.Any(p => p.Name == id.Identifier.ValueText) => id.Identifier.ValueText,
                    MemberAccessExpressionSyntax { Expression: ThisExpressionSyntax, Name: IdentifierNameSyntax name } => name.Identifier.ValueText,
                    _ => null,
                };
                // (the parameter, or the parameter where a check of it holds: c ? p : throw ..., p ?? throw ...)
                var value = a.Right;
                while (value is ParenthesizedExpressionSyntax paren)
                {
                    value = paren.Expression;
                }
                var from = Parameter(value);
                if (from == null && isCase && value is ConditionalExpressionSyntax { WhenFalse: ThrowExpressionSyntax } kept && Parameter(kept.WhenTrue) is IParameterSymbol whenTrue && OfParameters(kept.Condition))
                {
                    from = whenTrue;
                    made.Checks.Add((kept.Condition, false, null));
                }
                else if (from == null && isCase && value is BinaryExpressionSyntax { RawKind: (int)Microsoft.CodeAnalysis.CSharp.SyntaxKind.CoalesceExpression, Right: ThrowExpressionSyntax } coalesce &&
                         Parameter(coalesce.Left) is IParameterSymbol given)
                {
                    from = given;
                    made.Checks.Add((coalesce.Left, true, given));
                }
                var into = member == null ? null : t.GetMembers(member).OfType<IPropertySymbol>().FirstOrDefault();
                if (from == null || into == null || !IsGetOnlyAuto(into) || made.Parameters.ContainsKey(into) ||
                    !SymbolEqualityComparer.Default.Equals(into.Type, from.Type) ||
                    !(SymbolEqualityComparer.IncludeNullability.Equals(into.Type, from.Type) || made.Checks.Any(c => SymbolEqualityComparer.Default.Equals(c.Null, from))))
                {
                    return null;
                }
                made.Parameters[into] = from;
            }
            return made;
        }

        /// <summary>An instance auto-property with a getter alone and no initializer: set by a constructor, never after.</summary>
        private static bool IsGetOnlyAuto(IPropertySymbol p) =>
            !p.IsStatic && !p.IsAbstract && !p.IsVirtual && !p.IsOverride && p.SetMethod == null && p.GetMethod != null &&
            p.DeclaringSyntaxReferences.Length == 1 &&
            p.DeclaringSyntaxReferences[0].GetSyntax() is PropertyDeclarationSyntax { ExpressionBody: null, Initializer: null, AccessorList: { } accessors } &&
            accessors.Accessors.All(x => x.Body == null && x.ExpressionBody == null);
        /// <summary>[Pure] or [GhostFunction]: a mathematical function the verifier may use in specifications.</summary>
        public static bool IsPure(ISymbol s) => HasAttribute(s, "PureAttribute") || IsGhostFunction(s) ||
            s is IMethodSymbol m && (
                m.MethodKind == MethodKind.PropertyGet && m.AssociatedSymbol is IPropertySymbol p && HasAttribute(p, "PureAttribute") || // a [Pure] property's getter
                // an override or implementation of a [Pure] query is one too (its body must then be pure)
                m.OverriddenMethod != null && IsPure(m.OverriddenMethod) ||
                !m.IsStatic && m.ContainingType != null && m.ContainingType.AllInterfaces.SelectMany(i => i.GetMembers().OfType<IMethodSymbol>())
                    .Any(im => SymbolEqualityComparer.Default.Equals(m.ContainingType.FindImplementationForInterfaceMember(im), m) && IsPure(im)));
        /// <summary>A ghost collection: Seq&lt;T&gt; (and its static class Seq), Map&lt;K, V&gt; (and Map), ObjSet or Bag.</summary>
        public static bool IsSeqType(ITypeSymbol type) => IsCsVerifyType(type, "Seq`1") || IsCsVerifyType(type, "Seq") ||
            IsCsVerifyType(type, "Map`2") || IsCsVerifyType(type, "Map") || IsObjSet(type) || IsBag(type);
        public static bool IsBag(ITypeSymbol type) => IsCsVerifyType(type, "Bag");
        public static bool IsObjSet(ITypeSymbol type) => IsCsVerifyType(type, "ObjSet");

        public static bool IsTrusted(ISymbol s)
        {
            for (var cur = s; cur != null; cur = cur.ContainingSymbol)
            {
                if (HasAttribute(cur, "TrustedAttribute"))
                {
                    return true;
                }
            }
            return false;
        }

        /// <summary>
        /// A package of linear values: a user's [Linear] positional readonly record struct (say, a view together with
        /// the object it owns). Built with <c>new</c>, which consumes what goes in; taken apart by deconstruction.
        /// </summary>
        public static bool IsLinearPackage(ITypeSymbol type) =>
            type is INamedTypeSymbol t && t.TypeKind == TypeKind.Struct && t.IsRecord && t.IsReadOnly &&
            HasAttribute(t.OriginalDefinition, "LinearAttribute") && t.ContainingNamespace?.ToDisplayString() != Namespace;

        public static bool IsLinear(ITypeSymbol type)
        {
            for (var t = type; t != null; t = t.BaseType)
            {
                if (HasAttribute(t.OriginalDefinition, "LinearAttribute"))
                {
                    return true;
                }
            }
            return false;
        }

        /// <summary>A method whose arguments are ghost: specification statements, Ghost.Of, lemmas.</summary>
        public static bool IsGhostMethod(IMethodSymbol m) =>
            m != null && (IsSpecClass(m.ContainingType) || IsGhostOf(m) || IsLemma(m.OriginalDefinition) ||
                          IsGhostFunction(m.OriginalDefinition) || IsPredicate(m.OriginalDefinition) || IsModel(m.ReducedFrom ?? m.OriginalDefinition) ||
                          IsSeqType(m.ContainingType));

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
                        if (model.GetSymbolInfo(inv).Symbol is IMethodSymbol m && IsGhostMethod(m))
                        {
                            return true;
                        }
                        break;
                    case MethodDeclarationSyntax md:
                        var declared = model.GetDeclaredSymbol(md);
                        // (a stub's bodies are contracts, never run)
                        return IsLemma(declared) || IsGhostFunction(declared) || IsPredicate(declared) || IsModel(declared) ||
                               declared != null && IsContractsClass(declared.ContainingType);
                    case LocalFunctionStatementSyntax lf:
                        if (IsLemma(model.GetDeclaredSymbol(lf)))
                        {
                            return true;
                        }
                        break;
                }
            }
            return false;
        }

        /// <summary>The method whose body contains <paramref name="node"/> (not a lambda or local function's).</summary>
        public static IMethodSymbol EnclosingMember(SyntaxNode node, SemanticModel model)
        {
            for (var cur = node; cur != null; cur = cur.Parent)
            {
                if (cur is BaseMethodDeclarationSyntax || cur is AccessorDeclarationSyntax || cur is LocalFunctionStatementSyntax)
                {
                    return model.GetDeclaredSymbol(cur) as IMethodSymbol;
                }
            }
            return null;
        }

        /// <summary>Lemmas, [Pure] and [GhostFunction] methods: code that must be side-effect free and total.</summary>
        public static bool IsProofMethod(ISymbol m) => m != null && (IsLemma(m) || IsPure(m));

        /// <summary>
        /// Code that must not have side effects: specification arguments, and the bodies of lemmas, [Pure] and
        /// [GhostFunction] methods ([Trusted] ones excepted: their bodies are not part of the proof).
        /// </summary>
        public static bool MustBePure(SyntaxNode node, SemanticModel model)
        {
            if (node.AncestorsAndSelf().OfType<AttributeListSyntax>().Any())
            {
                return false;
            }
            var member = EnclosingMember(node, model);
            if (member != null && IsTrusted(member))
            {
                return false;
            }
            return IsProofMethod(member) || IsInGhostContext(node, model);
        }

        /// <summary>
        /// Methods ghost and pure code may call: the spec library's ghost members, lemmas, pure functions, System.Math,
        /// and an array's GetLength (its lengths never change).
        /// </summary>
        /// <summary>
        /// DateTime's and TimeSpan's arithmetic by name, on their ticks, which their + and - are: d.Add(t), d.Subtract(t)
        /// (of a TimeSpan or a DateTime), d.AddTicks(n), t.Add(u), t.Subtract(u). Functions of their values.
        /// </summary>
        public static bool IsTickArithmetic(IMethodSymbol m) =>
            m is { IsStatic: false, Parameters.Length: 1 } && m.ContainingType?.ContainingNamespace?.ToDisplayString() == "System" &&
            (m.ContainingType.Name == "DateTime" && (m.Name is "Add" or "Subtract" || m.Name == "AddTicks" && m.Parameters[0].Type.SpecialType == SpecialType.System_Int64) ||
             m.ContainingType.Name == "TimeSpan" && m.Name is "Add" or "Subtract");

        public static bool IsPureCallee(IMethodSymbol m) =>
            m != null && (IsGhostMethod(m) || IsProofMethod(m.OriginalDefinition) || m.ContainingType?.ToDisplayString() == "System.Math" ||
                          m.Name is "GetLength" or "Empty" && m.ContainingType?.SpecialType == SpecialType.System_Array ||
                          m.ContainingType?.ToDisplayString() == "System.MathF" ||
                          m.IsStatic && (m.ContainingType?.SpecialType == SpecialType.System_Double || m.ContainingType?.SpecialType == SpecialType.System_Single) ||
                          OrderedCompareTo(m) ||
                          m.IsStatic && m.ContainingType?.SpecialType == SpecialType.System_Char && m.Name.StartsWith("IsAscii", System.StringComparison.Ordinal));

        /// <summary>
        /// An equality or an order of a type parameter's values, which every implementation must keep to (Equals an
        /// equivalence, GetHashCode the same of equal values, CompareTo a total order): EqualityComparer&lt;T&gt;.Default's
        /// Equals and GetHashCode, Comparer&lt;T&gt;.Default.Compare, object.Equals(a, b), and a.Equals(b), a.GetHashCode()
        /// and a.CompareTo(b) of a T not null. "Equals", "GetHashCode" or "Compare", its values in order; else null.
        /// </summary>
        public static string GenericLaw(IInvocationOperation op, out IOperation[] values)
        {
            values = null;
            var m = op?.TargetMethod;
            if (m == null)
            {
                return null;
            }
            var args = op.Arguments.OrderBy(a => a.Parameter.Ordinal).Select(a => Unconverted(a.Value)).ToArray();
            ITypeSymbol t = null;
            string law = null;
            var owner = m.ContainingType?.OriginalDefinition.ToDisplayString();
            if (owner is "System.Collections.Generic.EqualityComparer<T>" or "System.Collections.Generic.Comparer<T>" &&
                op.Instance is IPropertyReferenceOperation { Property.Name: "Default", Instance: null })
            {
                t = m.ContainingType.TypeArguments[0];
                law = owner.Contains("EqualityComparer") ? m.Name switch { "Equals" when args.Length == 2 => "Equals", "GetHashCode" when args.Length == 1 => "GetHashCode", _ => null }
                    : m.Name == "Compare" && args.Length == 2 ? "Compare" : null;
                values = args;
            }
            else if (m.IsStatic && m.Name == "Equals" && m.ContainingType?.SpecialType == SpecialType.System_Object && args.Length == 2)
            {
                t = args[0].Type;
                law = "Equals";
                values = args;
            }
            else if (!m.IsStatic && op.Instance?.Type is ITypeParameterSymbol r && NotNullParameter(r))
            {
                t = r;
                values = new[] { op.Instance }.Concat(args).ToArray();
                law = m.Name switch
                {
                    "Equals" when args.Length == 1 && (m.ContainingType.SpecialType == SpecialType.System_Object || IsLawInterface(m.ContainingType, "IEquatable", r)) => "Equals",
                    "GetHashCode" when args.Length == 0 && m.ContainingType.SpecialType == SpecialType.System_Object => "GetHashCode",
                    "CompareTo" when args.Length == 1 && IsLawInterface(m.ContainingType, "IComparable", r) => "Compare",
                    _ => null,
                };
            }
            if (law == null || !(t is ITypeParameterSymbol) || values.Any(v => !SymbolEqualityComparer.Default.Equals(v.Type, t)))
            {
                values = null;
                return null;
            }
            return law;
        }

        /// <summary>A type parameter whose values aren't null: a struct's, notnull's, or one of IEquatable&lt;T&gt; or IComparable&lt;T&gt;.</summary>
        private static bool NotNullParameter(ITypeParameterSymbol t) =>
            t.HasValueTypeConstraint || t.HasNotNullConstraint || t.HasUnmanagedTypeConstraint ||
            t.ConstraintTypes.Any(c => IsLawInterface(c, "IEquatable", t) || IsLawInterface(c, "IComparable", t));

        /// <summary>IEquatable&lt;T&gt; or IComparable&lt;T&gt; of this T.</summary>
        public static bool IsLawInterface(ITypeSymbol i, string name, ITypeSymbol t) =>
            i is INamedTypeSymbol { Arity: 1 } n && n.Name == name && n.ContainingNamespace?.ToDisplayString() == "System" &&
            SymbolEqualityComparer.Default.Equals(n.TypeArguments[0], t);

        private static IOperation Unconverted(IOperation v) => v is IConversionOperation { IsImplicit: true } c ? Unconverted(c.Operand) : v;

        /// <summary>x.CompareTo(y) of an integer, a char, a decimal, a DateTime or a TimeSpan: their order, a value.</summary>
        private static bool OrderedCompareTo(IMethodSymbol m) =>
            m.Name == "CompareTo" && !m.IsStatic && m.Parameters.Length == 1 && SymbolEqualityComparer.Default.Equals(m.Parameters[0].Type, m.ContainingType) &&
            (m.ContainingType.SpecialType is SpecialType.System_SByte or SpecialType.System_Byte or SpecialType.System_Int16 or SpecialType.System_UInt16 or
                 SpecialType.System_Int32 or SpecialType.System_UInt32 or SpecialType.System_Int64 or SpecialType.System_UInt64 or SpecialType.System_Char or
                 SpecialType.System_Decimal or SpecialType.System_DateTime ||
             m.ContainingType.ToDisplayString() == "System.TimeSpan");

        /// <summary>The outermost Spec statement (void Spec.* call) that is <paramref name="node"/> or contains it in its arguments.</summary>
        /// <summary>The contracts of a body: what each states of its parameters, before its statements run.</summary>
        public static readonly string[] ContractNames = { "Requires", "Ensures", "EnsuresOnThrow", "Decreases", "Modifies", "Reads" };

        /// <summary>
        /// A local of the body that a contract statement's argument names (declared in the body, outside the contract):
        /// a contract is of the parameters, so it has no value there. Null if there is none.
        /// </summary>
        public static ILocalSymbol BodyLocalIn(IOperation contract, SyntaxNode statement)
        {
            var body = statement.Parent;
            foreach (var r in contract.DescendantsAndSelf().OfType<ILocalReferenceOperation>())
            {
                var at = r.Local.DeclaringSyntaxReferences.FirstOrDefault()?.Span;
                if (at is { } span && body != null && body.Span.Contains(span) && !statement.Span.Contains(span))
                {
                    return r.Local;
                }
            }
            return null;
        }

        public static InvocationExpressionSyntax EnclosingSpecCall(SyntaxNode node, SemanticModel model)
        {
            InvocationExpressionSyntax found = null;
            for (var cur = node; cur != null; cur = cur.Parent)
            {
                var inv = cur as InvocationExpressionSyntax ??
                          (cur is ArgumentSyntax arg ? arg.Parent?.Parent as InvocationExpressionSyntax : null);
                if (inv != null && (cur == inv || cur.Parent?.Parent == inv) &&
                    model.GetSymbolInfo(inv).Symbol is IMethodSymbol m && IsSpecClass(m.ContainingType) && m.ReturnsVoid)
                {
                    found = inv;
                }
                if (cur is MemberDeclarationSyntax)
                {
                    break;
                }
            }
            return found;
        }
    }
}
