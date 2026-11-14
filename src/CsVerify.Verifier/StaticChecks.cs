using System;
using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.FlowAnalysis;
using Microsoft.CodeAnalysis.Operations;
using Microsoft.CodeAnalysis.Text;

namespace CsVerify.Verifier
{
    /// <summary>
    /// The checks made from a method's syntax and declarations alone, for every method, Boogie's or not: locking and
    /// lock levels, atomics and try-lock flags, concurrency marks, Entity Framework's contexts, the dependence of a data
    /// type's invariant, and the warnings they give (docs/boogie.md, "How it's checked"). What needs a proof is the
    /// Boogie engine's.
    /// </summary>
    internal sealed partial class StaticChecks
    {

        private readonly Engine _engine;
        private readonly Contract _contract;
        private readonly IMethodSymbol _method;
        private readonly SemanticModel _model;
        private readonly MethodResult _result;
        private readonly HashSet<SyntaxNode> _contractStatements = new HashSet<SyntaxNode>();
        private readonly HashSet<(string, TextSpan)> _reported = new HashSet<(string, TextSpan)>();

        /// <summary>
        /// Lemmas and [Pure]/[GhostFunction] methods are proofs and definitions: they must terminate on every path,
        /// or a lemma that loops forever would "prove" anything and a definition f(x) = f(x) + 1 would be false.
        /// </summary>
        private bool ProofCode => (_contract.IsLemma || _contract.IsPure) && !_contract.IsTrusted;

        public StaticChecks(Engine engine, Contract contract, MethodResult result)
        {
            _engine = engine;
            _contract = contract;
            _method = contract.Method;
            _model = contract.Model;
            _result = result;
        }

        // ================================================================================== driver

        /// <summary>A lambda's or local function's flow graph, from its enclosing method's (Engine's nested functions).</summary>
        public ControlFlowGraph NestedGraph;

        public void Run()
        {
            var body = _model.GetOperation(_contract.Declaration);
            ControlFlowGraph cfg;
            if (NestedGraph != null) cfg = NestedGraph;
            else switch (body)
            {
                case IMethodBodyOperation mb: cfg = ControlFlowGraph.Create(mb); break;
                case IConstructorBodyOperation cb: cfg = ControlFlowGraph.Create(cb); break;
                case IBlockOperation block: cfg = ControlFlowGraph.Create(block); break; // an expression-bodied property
                default: return;
            }
            FindContractStatements();
            CheckLocking();
            CheckLockLevels();
            CheckAtomics();
            CheckFlagUses();
            CheckContextConcurrency();
            CheckConcurrentMarks();
            if (SpecSymbols.IsPredicate(_method)) return;
            if (SpecSymbols.IsInvariant(_method) && !Data.IsData(_method.ContainingType) && !SpecSymbols.IsOwned(_method.ContainingType) && !IsImmutableClass(_method.ContainingType))
                Warn(MethodLocationNode(), $"[Invariant] '{_method.Name}' is not used: {_method.ContainingType.Name} is mutable. Make it immutable (readonly fields) or [Owned], or state the invariant as a Valid() precondition (Dafny style)");
            if (SpecSymbols.IsInvariant(_method) && (Data.IsData(_method.ContainingType) || SpecSymbols.IsOwned(_method.ContainingType) || IsImmutableClass(_method.ContainingType)) &&
                _engine.Fields.InvariantDependence(_method, !Data.IsData(_method.ContainingType)) is string why)
                Report("CSV1015", MethodLocationNode(), $"invariant '{_method.Name}' could be broken behind its back: {why}", isError: true);
            if (ProofCode && _method.IsAsync) NotModeled(MethodLocationNode(), "a lemma or [Pure] function cannot be async");
        }

        private void FindContractStatements()
        {
            BlockSyntax block = (_contract.Declaration as BaseMethodDeclarationSyntax)?.Body ?? (_contract.Declaration as AccessorDeclarationSyntax)?.Body ??
                                (_contract.Declaration as LocalFunctionStatementSyntax)?.Body ?? (_contract.Declaration as AnonymousFunctionExpressionSyntax)?.Block;
            if (block == null) return;
            foreach (var s in block.Statements.OfType<ExpressionStatementSyntax>())
                if (s.Expression is InvocationExpressionSyntax inv && SpecName(inv) is string n && (n == "Requires" || n == "Ensures" || n == "EnsuresOnThrow" || n == "Decreases" || n == "Modifies" || n == "Reads"))
                    _contractStatements.Add(inv);
        }

        private string SpecName(InvocationExpressionSyntax inv) =>
            _model.GetSymbolInfo(inv).Symbol is IMethodSymbol m && SpecSymbols.IsSpecClass(m.ContainingType) ? m.Name : null;

        private SyntaxNode MethodLocationNode() => _contract.Declaration;

        private void Report(string id, SyntaxNode at, string message, bool isError, IReadOnlyCollection<string> causes = null)
        {
            if (isError && !_engine.Options.Checked(id)) return;
            if (!_reported.Add((id, at.Span))) return;
            _result.Diagnostics.Add(new VerificationDiagnostic(id, isError, message, at.GetLocation().GetLineSpan())
            {
                Causes = causes ?? (IReadOnlyCollection<string>)Array.Empty<string>(),
            });
        }

        private static int LineOf(SyntaxNode at) => at.GetLocation().GetLineSpan().StartLinePosition.Line + 1;

        private void Warn(SyntaxNode at, string message) => Report("CSV1900", at, message, isError: false);

        /// <summary>
        /// Something the verifier cannot model soundly: a path it does not follow, an effect it does not track. The
        /// method is then not verified (an error), instead of reporting "ok" for what was not checked.
        /// </summary>
        private void NotModeled(SyntaxNode at, string message)
        {
            // within a check profile, a warning: the method is verified around it, with its value unknown
            bool degrade = _engine.Options.CheckKinds != null;
            int before = _result.Diagnostics.Count;
            Report("CSV1901", at, degrade ? message + " (not modeled: treated as unknown)" : message, isError: !degrade);
            if (degrade && _result.Diagnostics.Count > before) _result.Unmodeled++;
        }

        internal static bool IsSequence(ITypeSymbol t) =>
            t is IArrayTypeSymbol || t?.SpecialType == SpecialType.System_String || t?.SpecialType == SpecialType.System_Array ||
            (t is INamedTypeSymbol n && (n.OriginalDefinition.ToDisplayString() == "System.Span<T>" || n.OriginalDefinition.ToDisplayString() == "System.ReadOnlySpan<T>"));

        /// <summary>
        /// A sequence whose elements a holder can change: an array (System.Array too) or a span, not a string or a
        /// read-only span.
        /// </summary>
        internal static bool IsWritableSequence(ITypeSymbol t) =>
            t is IArrayTypeSymbol || t?.SpecialType == SpecialType.System_Array ||
            t is INamedTypeSymbol n && n.OriginalDefinition.ToDisplayString() == "System.Span<T>";

        /// <summary>The operand under implicit reference conversions (reference == converts both sides to object).</summary>
        private static IOperation Unconverted(IOperation op)
        {
            while (op is IConversionOperation c && c.IsImplicit && c.Conversion.IsReference) op = c.Operand;
            return op;
        }

        /// <summary>
        /// A library out parameter <c>[MaybeNullWhen(b)] out TValue value</c>, with TValue a non-nullable type: not null
        /// when the method returns !b (null if the parameter says nothing of the kind).
        /// </summary>
        internal static bool? NotNullWhen(IParameterSymbol p) =>
            IsNonNullableType(p.Type) && p.OriginalDefinition.GetAttributes().FirstOrDefault(x =>
                x.AttributeClass?.ToDisplayString() == "System.Diagnostics.CodeAnalysis.MaybeNullWhenAttribute") is AttributeData mnw &&
            mnw.ConstructorArguments.Length == 1 && mnw.ConstructorArguments[0].Value is bool maybeNullWhen
                ? !maybeNullWhen : (bool?)null;

        /// <summary>Drop and Concat as array lambdas: definitions, not quantified axioms, so they cost Z3 nothing until used.</summary>
        public const string SeqTheory =
            "(define-fun cv_drop ((a (Array Int Int)) (n Int)) (Array Int Int) (lambda ((i Int)) (select a (+ n i))))\n" +
            "(define-fun cv_concat ((a (Array Int Int)) (n Int) (b (Array Int Int))) (Array Int Int) (lambda ((i Int)) (ite (< i n) (select a i) (select b (- i n)))))\n" +
            // object sets (ObjSet) are arrays to 0/1, like sequences
            "(define-fun cv_union ((a (Array Int Int)) (b (Array Int Int))) (Array Int Int) (lambda ((i Int)) (ite (or (distinct (select a i) 0) (distinct (select b i) 0)) 1 0)))\n" +
            "(define-fun cv_subset ((a (Array Int Int)) (b (Array Int Int))) Bool (forall ((i Int)) (=> (distinct (select a i) 0) (distinct (select b i) 0))))\n" +
            "(define-fun cv_disjoint ((a (Array Int Int)) (b (Array Int Int))) Bool (forall ((i Int)) (not (and (distinct (select a i) 0) (distinct (select b i) 0)))))\n" +
            // what a call with Spec.Modifies(w) may change: objects in w, and objects not allocated before it
            "(define-fun cv_mod ((w (Array Int Int)) (alloc (Array Int Int))) (Array Int Int) (lambda ((i Int)) (ite (or (distinct (select w i) 0) (= (select alloc i) 0)) 1 0)))\n" +
            "(define-fun cv_frame ((m (Array Int Int)) (old (Array Int Int)) (new (Array Int Int))) (Array Int Int) (lambda ((i Int)) (ite (distinct (select m i) 0) (select new i) (select old i))))\n" +
            "(define-fun cv_frameh ((m (Array Int Int)) (old (Array Int (Array Int Int))) (new (Array Int (Array Int Int)))) (Array Int (Array Int Int)) (lambda ((i Int)) (ite (distinct (select m i) 0) (select new i) (select old i))))\n" +
            // multisets (Bag): arrays from value to count. cv_bag(r, n) is the multiset of r[0..n); writing r[i]
            // inside the prefix trades the old element for the new one, outside it changes nothing. Each axiom is
            // triggered only by the multiset of a written array, so they cannot loop.
            "(define-fun cv_badd ((m (Array Int Int)) (x Int)) (Array Int Int) (store m x (+ (select m x) 1)))\n" +
            "(define-fun cv_bremove ((m (Array Int Int)) (x Int)) (Array Int Int) (store m x (- (select m x) 1)))\n" +
            "(define-fun cv_bunion ((a (Array Int Int)) (b (Array Int Int))) (Array Int Int) (lambda ((i Int)) (+ (select a i) (select b i))))\n" +
            "(declare-fun cv_bag ((Array Int Int) Int) (Array Int Int))\n" +
            "(assert (forall ((r (Array Int Int))) (! (= (cv_bag r 0) ((as const (Array Int Int)) 0)) :pattern ((cv_bag r 0)))))\n" +
            "(assert (forall ((r (Array Int Int)) (i Int) (v Int) (n Int)) (! (=> (and (<= 0 i) (< i n)) (= (cv_bag (store r i v) n) (cv_badd (cv_bremove (cv_bag r n) (select r i)) v))) :pattern ((cv_bag (store r i v) n)))))\n" +
            "(assert (forall ((r (Array Int Int)) (i Int) (v Int) (n Int)) (! (=> (or (< i 0) (<= n i)) (= (cv_bag (store r i v) n) (cv_bag r n))) :pattern ((cv_bag (store r i v) n)))))";

        /// <summary>
        /// A value of this type may be null at run time: a reference (array, string, class, interface, delegate) or a
        /// type parameter that is not a value type. Ghosts, sequences and views are values.
        /// </summary>
        private static bool MayBeNullType(ITypeSymbol t) =>
            t != null && !SpecSymbols.IsGhostType(t) && !SpecSymbols.IsSeqType(t) &&
            (t.IsReferenceType || (t is ITypeParameterSymbol tp && !tp.HasValueTypeConstraint && !tp.HasUnmanagedTypeConstraint));

        /// <summary>
        /// The declared type promises a value that is not null: a non-nullable reference type in an enabled nullable
        /// context. An oblivious type (nullable disabled), <c>T?</c> and a type parameter (it may be instantiated with
        /// a nullable type) promise nothing.
        /// </summary>
        private static bool IsNonNullableType(ITypeSymbol t) =>
            SpecSymbols.IsGhostType(t) ? IsNonNullableType(((INamedTypeSymbol)t).TypeArguments[0]) // Ghost<T>: T's
            : MayBeNullType(t) && !(t is ITypeParameterSymbol) && t.NullableAnnotation == NullableAnnotation.NotAnnotated;

        internal static bool IsNonNullable(IParameterSymbol p) =>
            (IsNonNullableType(p.OriginalDefinition.Type) || p.OriginalDefinition.Type is ITypeParameterSymbol { HasNotNullConstraint: true } && p.OriginalDefinition.NullableAnnotation != NullableAnnotation.Annotated && MayBeNullType(p.Type)) && !HasAttribute(p.OriginalDefinition.GetAttributes(), "AllowNullAttribute") ||
            // (query syntax's own: the object its previous clause made, or the group of group ... into g)
            p.ContainingSymbol is IMethodSymbol { MethodKind: MethodKind.AnonymousFunction } fn &&
            !(fn.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() is Microsoft.CodeAnalysis.CSharp.Syntax.AnonymousFunctionExpressionSyntax) &&
            (p.Type.IsAnonymousType || p.Type.OriginalDefinition.ToDisplayString() == "System.Linq.IGrouping<TKey, TElement>");

        internal static bool IsNonNullableReturn(IMethodSymbol m) =>
            !m.ReturnsVoid && (m.IsAsync ? AsyncResultType(m.OriginalDefinition) is ITypeSymbol t && IsNonNullableType(t) // (what it returns: its task's result)
                                         : IsNonNullableType(m.OriginalDefinition.ReturnType)) &&
            !HasAttribute(m.OriginalDefinition.GetReturnTypeAttributes(), "MaybeNullAttribute");

        private static bool HasAttribute(IEnumerable<AttributeData> attributes, string name) =>
            attributes.Any(a => a.AttributeClass?.ToDisplayString() == "System.Diagnostics.CodeAnalysis." + name);
    }
}
