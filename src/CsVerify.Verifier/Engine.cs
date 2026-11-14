using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Diagnostics;
using Microsoft.CodeAnalysis.FlowAnalysis;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    public sealed class VerifierOptions
    {
        /// <summary>
        /// Bounded integers (the default): run-time integer arithmetic and narrowing conversions are C#'s, so
        /// overflow is reported unless it throws (checked) or wraps on purpose (unchecked). False makes every
        /// integer mathematical, which is unsound for code that can overflow.
        /// </summary>
        public bool CheckOverflow = true;
        /// <summary>
        /// The nullable context the sources are compiled in (the project's &lt;Nullable&gt;). Non-nullable reference
        /// types are contracts; oblivious ones (nullable disabled) are maybe-null, so only an enabled context lets
        /// the verifier know anything is not null.
        /// </summary>
        public NullableContextOptions Nullable = NullableContextOptions.Enable;
        public int TimeoutMs = 10000;
        public int MaxPaths = 5000;
        /// <summary>
        /// The most time a method's verification may take, all rounds included (milliseconds; 0 for no limit). Past it,
        /// its remaining obligations are not proved (CSV1901): the method is reported not verified, never verified.
        /// </summary>
        public int MethodBudgetMs;
        /// <summary>Verify only the methods whose name (Type.Method) contains one of these; all, if empty.</summary>
        public List<string> Only = new List<string>();
        internal bool Selects(string method) => Only.Count == 0 || Only.Any(o => method.Contains(o, StringComparison.Ordinal));
        public string Z3Path;
        /// <summary>Where to write the Boogie program the engine verifies (to read the translation), if anywhere.</summary>
        public string BoogieOut;
        public List<string> Defines = new List<string>();
        public List<string> References = new List<string>();
        /// <summary>The kinds of check proved (<see cref="Verifier.Checks"/>); null for all. The rest are assumed.</summary>
        public HashSet<string> CheckKinds;
        /// <summary>Is an obligation (or a diagnostic) with this id checked in the profile?</summary>
        internal bool Checked(string id) => CheckKinds == null || !(Verifier.Checks.KindOf(id) is string kind) || CheckKinds.Contains(kind);
    }

    public sealed class VerificationDiagnostic
    {
        public readonly string Id;
        public readonly bool IsError;
        public readonly string Message;
        public readonly FileLinePositionSpan Span;

        public VerificationDiagnostic(string id, bool isError, string message, FileLinePositionSpan span)
        {
            Id = id; IsError = isError; Message = message; Span = span;
        }

        public int Line => Span.StartLinePosition.Line + 1;

        /// <summary>
        /// For a failed obligation, where the unknown values its condition mentions come from (the library report):
        /// "library M" (a library member without a contract: its result, or what it may have changed), "source M" (a
        /// method of the program without postconditions), "a loop without invariants". Empty if it mentions none.
        /// </summary>
        public IReadOnlyCollection<string> Causes = Array.Empty<string>();

        public override string ToString() =>
            $"{Span.Path}({Span.StartLinePosition.Line + 1},{Span.StartLinePosition.Character + 1}): {(IsError ? "error" : "warning")} {Id}: {Message}";
    }

    public sealed class MethodResult
    {
        public string Name;
        /// <summary>Where it is declared (file and line): which of several overloads it is.</summary>
        public string Declared;
        public int Obligations, Proved;
        /// <summary>How long verifying it took, all rounds included.</summary>
        public long Milliseconds;
        public readonly List<VerificationDiagnostic> Diagnostics = new List<VerificationDiagnostic>();
        /// <summary>The external members whose (trusted) stub contracts the proof of this method assumed.</summary>
        public readonly SortedSet<string> Assumptions = new SortedSet<string>(StringComparer.Ordinal);
        /// <summary>The calls (and property reads) in this method of library members without a contract: each
        /// member, and where (file and position).</summary>
        public readonly HashSet<(string member, string at)> LibraryCalls = new HashSet<(string, string)>();
        /// <summary>Obligations outside the check profile: assumed, not proved.</summary>
        public int AssumedObligations;
        /// <summary>Constructs the verifier does not model, treated as unknown values (only within a check profile).</summary>
        public int Unmodeled;
        public bool Verified => Diagnostics.All(d => !d.IsError);
        /// <summary>A lambda's or a local function's flow graph (its enclosing method's gives it).</summary>
        internal Microsoft.CodeAnalysis.FlowAnalysis.ControlFlowGraph Graph;

        /// <summary>Starts the method's results over (for a run again: see Engine.RunMethod).</summary>
        internal void Clear()
        {
            Obligations = Proved = AssumedObligations = Unmodeled = 0;
            Diagnostics.Clear();
            Assumptions.Clear();
            LibraryCalls.Clear();
        }
    }

    public sealed class VerificationResult
    {
        public readonly List<MethodResult> Methods = new List<MethodResult>();
        public readonly List<VerificationDiagnostic> CompilationErrors = new List<VerificationDiagnostic>();
        /// <summary>Why Boogie verified nothing, when it failed (its methods are then not verified, CSV1902, with this reason).</summary>
        public string BoogieFailure;
        /// <summary>Analyzer errors outside any method body (a linear field in a non-linear type, say).</summary>
        public readonly List<VerificationDiagnostic> AnalyzerErrors = new List<VerificationDiagnostic>();
        /// <summary>The external members whose (trusted) stub contracts some proof assumed.</summary>
        public readonly SortedSet<string> Assumptions = new SortedSet<string>(StringComparer.Ordinal);
        public IEnumerable<VerificationDiagnostic> Diagnostics =>
            CompilationErrors.Concat(AnalyzerErrors).Concat(Methods.SelectMany(m => m.Diagnostics));
        public bool Success => !Diagnostics.Any(d => d.IsError);
        public MethodResult this[string name] => Methods.FirstOrDefault(m => m.Name == name || m.Name.EndsWith("." + name));

        /// <summary>The results of programs verified separately, as one.</summary>
        public static VerificationResult Combine(IReadOnlyList<VerificationResult> results)
        {
            if (results.Count == 1) return results[0];
            var all = new VerificationResult();
            foreach (var r in results)
            {
                all.Methods.AddRange(r.Methods);
                all.CompilationErrors.AddRange(r.CompilationErrors);
                all.AnalyzerErrors.AddRange(r.AnalyzerErrors);
                all.Assumptions.UnionWith(r.Assumptions);
            }
            return all;
        }
    }

    /// <summary>Builds the compilation (with CSVERIFY_SPEC defined) and verifies every method with a body.</summary>
    public sealed class Engine : IDisposable
    {
        public readonly VerifierOptions Options;
        private readonly Compilation _compilation;
        internal Compilation Compilation => _compilation;
        private readonly Dictionary<IMethodSymbol, Contract> _contracts = new Dictionary<IMethodSymbol, Contract>(SymbolEqualityComparer.Default);

        internal readonly DataTypes Data;
        internal readonly FieldEffects Fields;
        internal readonly IReadOnlyList<INamedTypeSymbol> SourceTypes;
        /// <summary>Does the program use dynamic frames (Spec.Modifies/Reads/Fresh, ObjSet)? Allocation is tracked only then.</summary>
        internal readonly bool UsesDynamicFrames;
        internal readonly LockGuards Locks;
        internal readonly LockLevels Levels;
        /// <summary>The Entity Framework Core model, or null for a program that doesn't reference EF Core.</summary>
        internal readonly EfModel Ef;

        internal readonly Atomics Atomics;
        /// <summary>Are there [Owned] classes? Then the ownership-tree map Root is tracked.</summary>
        internal readonly bool UsesOwnership;
        /// <summary>The program uses ATS's manual memory (Mem, Ptr and the views of its cells).</summary>
        internal readonly bool UsesMemory;
        /// <summary>The program speaks of permissions (Spec.Acc): to objects, or to array cells.</summary>
        internal readonly bool UsesPermissions;
        private readonly Dictionary<ISymbol, int> _fieldIds = new Dictionary<ISymbol, int>(SymbolEqualityComparer.Default);

        /// <summary>A number for each field, for masks indexed by field (permissions to single fields).</summary>
        internal int FieldId(ISymbol field)
        {
            if (!_fieldIds.TryGetValue(field, out var id)) _fieldIds[field] = id = _fieldIds.Count + 1;
            return id;
        }

        /// <summary>The [Predicate] methods of the program.</summary>
        internal readonly List<IMethodSymbol> Predicates;

        /// <summary>The [ContractsFor] stubs: contracts for members without sources, and [Model] functions.</summary>
        internal readonly ContractStubs Stubs;

        /// <summary>
        /// The [Model] functions the program may use: ghost fields of external objects (empty unless the sources
        /// mention a type some stub specifies, or a model function, so nothing changes for programs that do not).
        /// </summary>
        internal readonly IReadOnlyList<IMethodSymbol> Models;

        internal IReadOnlyList<SyntaxTree> UserTrees { get; }

        private Engine(Compilation compilation, VerifierOptions options, IEnumerable<SyntaxTree> userTrees)
        {
            UserTrees = userTrees.ToList();
            _compilation = compilation;
            Stubs = ContractStubs.For(compilation);
            // (and the list interfaces, which read a List's models: StaticChecks.Interfaces)
            var names = new HashSet<string>(Stubs.Models.Select(m => m.Name)
                .Concat(Stubs.Models.Select(m => m.Parameters[0].Type.Name))
                .Concat(new[] { "IReadOnlyList", "IList", "IReadOnlyCollection", "ICollection" }));
            Models = userTrees.Any(t => t.GetRoot().DescendantNodes().OfType<SimpleNameSyntax>().Any(n => names.Contains(n.Identifier.Text)))
                ? Stubs.Models : new List<IMethodSymbol>();
            Data = new DataTypes(compilation, userTrees);
            Fields = new FieldEffects(this);
            Locks = new LockGuards(compilation, userTrees);
            UsesDynamicFrames = userTrees.Any(t => t.GetRoot().DescendantNodes().OfType<IdentifierNameSyntax>()
                .Any(n => n.Identifier.Text == "Modifies" || n.Identifier.Text == "Reads" || n.Identifier.Text == "Fresh" || n.Identifier.Text == "ObjSet"))
                || Models.Count > 0; // (stubs frame model state with Spec.Modifies)
            SourceTypes = userTrees.SelectMany(t => t.GetRoot().DescendantNodes().OfType<BaseTypeDeclarationSyntax>()
                .Select(d => compilation.GetSemanticModel(t).GetDeclaredSymbol(d)).OfType<INamedTypeSymbol>()).ToList();
            Levels = new LockLevels(compilation, Locks, SourceTypes);
            Atomics = new Atomics(SourceTypes);
            Ef = EfModel.For(compilation, UserTrees, SourceTypes);
            Predicates = SourceTypes.SelectMany(t => t.GetMembers().OfType<IMethodSymbol>()).Where(SpecSymbols.IsPredicate).ToList();
            // (a predicate needs the permission state even with no [Owned] class: over arrays alone, say)
            UsesOwnership = SourceTypes.Any(SpecSymbols.IsOwned) || Predicates.Count > 0;
            UsesMemory = userTrees.Any(t => t.GetRoot().DescendantNodes().OfType<IdentifierNameSyntax>()
                .Any(n => n.Identifier.Text == "PointsTo" || n.Identifier.Text == "ArrayView" || n.Identifier.Text == "ArrayHole" || n.Identifier.Text == "Mem"));
            UsesPermissions = userTrees.Any(t => t.GetRoot().DescendantNodes().OfType<IdentifierNameSyntax>().Any(n => n.Identifier.Text == "Acc" || n.Identifier.Text == "AccRead"));

            Options = options;
            // (Z3, which Boogie runs: there, or this says it isn't)
            Z3.Find(options.Z3Path);
        }

        public void Dispose() { }

        private readonly Dictionary<IMethodSymbol, bool> _writesHeap = new Dictionary<IMethodSymbol, bool>(SymbolEqualityComparer.Default);

        /// <summary>
        /// Inferred frame condition: may a call change array contents? True when the body (transitively) writes an
        /// element or passes one by ref; for code without source, when it takes an array or span.
        /// </summary>
        internal bool MayWriteHeap(IMethodSymbol m)
        {
            var key = (m.ReducedFrom ?? m).OriginalDefinition;
            // a library method as called: what a generic one may do depends on its type arguments
            if (key.DeclaringSyntaxReferences.Length == 0) key = m.ReducedFrom ?? m;
            if (_writesHeap.TryGetValue(key, out var known)) return known;
            var c = ContractOf(key.OriginalDefinition);
            if (c.IsPure || c.IsLemma) return _writesHeap[key] = false;
            // Mem and Ptr change only Mem's memory, whose cells change by their own rule (StaticChecks.KeepHeldMemory)
            if (SpecSymbols.IsCsVerifyType(key.ContainingType, "Mem") || SpecSymbols.IsCsVerifyType(key.ContainingType, "Ptr`1"))
                return _writesHeap[key] = false;
            // which override runs is not known: any of them may write arrays (a stubbed library member's own
            // overrides in the library are trusted to keep its contract; the sources' are looked at)
            if (IsOverridable(key) && c.IsStub)
            {
                _writesHeap[key] = false; // (for recursion while computing)
                return _writesHeap[key] = key.Parameters.Any(p => StaticChecks.IsWritableSequence(p.Type)) || Fields.RunsUserCode(key) ||
                                          Fields.Overrides(key).Any(MayWriteHeap);
            }
            if (IsOverridable(key)) return _writesHeap[key] = true;
            // a library method: through arrays (or spans) it is handed, not strings, or user code it runs (a delegate writing arrays it captured)
            if (!c.HasSource || c.IsStub) return _writesHeap[key] = key.Parameters.Any(p => StaticChecks.IsWritableSequence(p.Type)) || Fields.RunsUserCode(key);
            _writesHeap[key] = false; // assume no for recursive calls while computing
            bool writes = false;
            foreach (var n in c.Declaration.DescendantNodes())
            {
                foreach (var written in WrittenBy(n))
                {
                    var target = written;
                    // (a struct's member inside an array element writes the element: a[i].X = 1)
                    while (target is MemberAccessExpressionSyntax ma && c.Model.GetSymbolInfo(ma).Symbol is ISymbol ms && !ms.IsStatic &&
                           ms.ContainingType?.TypeKind == TypeKind.Struct)
                        target = ma.Expression;
                    if (target is ElementAccessExpressionSyntax ea && !IsOwnNewArray(ea.Expression, c)) writes = true;
                }
                if (n is InvocationExpressionSyntax inv && c.Model.GetSymbolInfo(inv).Symbol is IMethodSymbol callee &&
                    !SpecSymbols.IsSpecClass(callee.ContainingType) && MayWriteHeap(callee)) writes = true;
                if (writes) break;
            }
            return _writesHeap[key] = writes;
        }

        /// <summary>
        /// What a piece of syntax may write through. A ref to an element counts as a write when it is taken: from then on
        /// a write needs no element access (<c>ref int r = ref a[0]; r = 1;</c>), and a method can return the ref.
        /// </summary>
        private static IEnumerable<ExpressionSyntax> WrittenBy(SyntaxNode n)
        {
            switch (n)
            {
                case AssignmentExpressionSyntax a: return Parts(a.Left);
                case ForEachVariableStatementSyntax fe: return Parts(fe.Variable);
                case RefExpressionSyntax r: return new[] { r.Expression };
                // (only ++ and --: !a[i], -a[i] and a[i]! read)
                case PrefixUnaryExpressionSyntax pre when pre.IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.PreIncrementExpression) ||
                                                          pre.IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.PreDecrementExpression): return new[] { pre.Operand };
                case PostfixUnaryExpressionSyntax post when post.IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.PostIncrementExpression) ||
                                                            post.IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.PostDecrementExpression): return new[] { post.Operand };
                case ArgumentSyntax arg when !arg.RefKindKeyword.IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.None): return new[] { arg.Expression };
                default: return Enumerable.Empty<ExpressionSyntax>();
            }
        }

        /// <summary>An assignment's targets: <c>(a[0], a[1]) = ...</c> has two.</summary>
        private static IEnumerable<ExpressionSyntax> Parts(ExpressionSyntax target) =>
            target is TupleExpressionSyntax t ? t.Arguments.SelectMany(x => Parts(x.Expression)) : new[] { target };

        /// <summary>
        /// A local that only ever holds an array this method allocated: a write through it changes nothing that existed
        /// when the method was called. All it is assigned is a new array or another such local (or a choice of them). Passed
        /// by ref, it might hold any array. Captured by a lambda or a local function, a write might run after the method
        /// returns, when the caller already has the array and believes what it knew of it.
        /// </summary>
        private static bool IsOwnNewArray(ExpressionSyntax array, Contract c)
        {
            while (array is ParenthesizedExpressionSyntax p) array = p.Expression;
            return array is IdentifierNameSyntax id && c.Model.GetSymbolInfo(id).Symbol is ILocalSymbol local &&
                   HoldsOnlyNewArrays(local, c, new HashSet<ILocalSymbol>(SymbolEqualityComparer.Default));
        }

        /// <summary>(visiting: locals assigned from each other hold only new arrays if nothing else gets in)</summary>
        private static bool HoldsOnlyNewArrays(ILocalSymbol local, Contract c, HashSet<ILocalSymbol> visiting)
        {
            if (!visiting.Add(local)) return true;
            if (local.IsRef || local.Type.TypeKind != TypeKind.Array ||
                !(local.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() is VariableDeclaratorSyntax declarator) ||
                // (captured from around a local function: the method around it has it, and this looks only inside)
                !c.Declaration.Contains(declarator)) return false;
            bool Same(ExpressionSyntax e) => e is IdentifierNameSyntax n && SymbolEqualityComparer.Default.Equals(c.Model.GetSymbolInfo(n).Symbol, local);
            bool Allowed(ExpressionSyntax e)
            {
                switch (e)
                {
                    case ArrayCreationExpressionSyntax _:
                    case ImplicitArrayCreationExpressionSyntax _:
                        return true;
                    case ParenthesizedExpressionSyntax p: return Allowed(p.Expression);
                    case ConditionalExpressionSyntax q: return Allowed(q.WhenTrue) && Allowed(q.WhenFalse);
                    case IdentifierNameSyntax n: return c.Model.GetSymbolInfo(n).Symbol is ILocalSymbol other && HoldsOnlyNewArrays(other, c, visiting);
                    default: return false;
                }
            }
            if (declarator.Initializer != null && !Allowed(declarator.Initializer.Value)) return false;
            foreach (var n in c.Declaration.DescendantNodes())
                switch (n)
                {
                    case AssignmentExpressionSyntax a when Same(a.Left):
                        if (!Allowed(a.Right)) return false;
                        break;
                    // (assigned in a tuple or by a foreach: from something this doesn't follow)
                    case AssignmentExpressionSyntax a when Parts(a.Left).Skip(1).Any() && Parts(a.Left).Any(Same): return false;
                    case ForEachVariableStatementSyntax fe when Parts(fe.Variable).Any(Same): return false;
                    case ArgumentSyntax arg when !arg.RefKindKeyword.IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.None) && Same(arg.Expression): return false;
                    case RefExpressionSyntax r when Same(r.Expression): return false;
                    // (a specification's lambda never runs)
                    case AnonymousFunctionExpressionSyntax f when SpecSymbols.EnclosingSpecCall(f, c.Model) == null && f.DescendantNodes().OfType<IdentifierNameSyntax>().Any(Same): return false;
                    case LocalFunctionStatementSyntax f when f.DescendantNodes().OfType<IdentifierNameSyntax>().Any(Same): return false;
                }
            return true;
        }

        private readonly Dictionary<IMethodSymbol, bool> _touchesArrays = new Dictionary<IMethodSymbol, bool>(SymbolEqualityComparer.Default);

        /// <summary>
        /// May a call read or write array (or span) contents, in code, directly or through anything it calls? A
        /// method that does not can be handed an array element by ref: copying the cell in and out is then what
        /// happens, since nothing else looks at the cell while the callee has it. Specifications and lemmas are
        /// ghost and do not count. A library method may when it is handed anything but values and strings.
        /// </summary>
        internal bool MayTouchArrays(IMethodSymbol m)
        {
            var key = (m.ReducedFrom ?? m).OriginalDefinition;
            if (key.DeclaringSyntaxReferences.Length == 0) key = m.ReducedFrom ?? m;
            if (_touchesArrays.TryGetValue(key, out var known)) return known;
            var c = ContractOf(key.OriginalDefinition);
            if (c.IsLemma) return _touchesArrays[key] = false;
            if (IsOverridable(key)) return _touchesArrays[key] = true;
            if (!c.HasSource)
            {
                bool Reaches(ITypeSymbol t) => t != null && !t.IsValueType && t.SpecialType != SpecialType.System_String;
                return _touchesArrays[key] = Fields.RunsUserCode(key) || key.Parameters.Any(p => Reaches(p.Type)) ||
                                             !key.IsStatic && Reaches(key.ContainingType) || key.IsGenericMethod;
            }
            _touchesArrays[key] = false; // assume no for recursive calls while computing
            var body = c.Model.GetOperation(c.Declaration);
            // (no operation tree: an auto-property's accessor touches nothing, anything else cannot be told)
            bool touches = body == null && !(c.Declaration is AccessorDeclarationSyntax ad && ad.Body == null && ad.ExpressionBody == null);
            foreach (var op in body?.DescendantsAndSelf() ?? Enumerable.Empty<IOperation>())
            {
                if (SpecSymbols.EnclosingSpecCall(op.Syntax, c.Model) != null) continue;
                IMethodSymbol callee = null;
                switch (op)
                {
                    case IArrayElementReferenceOperation _: touches = true; break;
                    // a sequence's indexer reads its contents, its Length does not
                    case IPropertyReferenceOperation pr when pr.Instance != null && StaticChecks.IsSequence(pr.Instance.Type): touches = pr.Property.IsIndexer; break;
                    case IPropertyReferenceOperation pr:
                        touches = new[] { pr.Property.GetMethod, pr.Property.SetMethod }.Any(x => x != null && MayTouchArrays(x));
                        break;
                    case IInvocationOperation inv: callee = inv.TargetMethod; break;
                    case IObjectCreationOperation oc: callee = oc.Constructor; break;
                    case IBinaryOperation b: callee = b.OperatorMethod; break;
                    case IUnaryOperation u: callee = u.OperatorMethod; break;
                    case IConversionOperation cv: callee = cv.OperatorMethod; break;
                    case IIncrementOrDecrementOperation id: callee = id.OperatorMethod; break;
                    case ICompoundAssignmentOperation ca: callee = ca.OperatorMethod; break;
                    case IForEachLoopOperation fe when fe.Syntax is CommonForEachStatementSyntax fs:
                        var info = c.Model.GetForEachStatementInfo(fs);
                        touches = new[] { info.GetEnumeratorMethod, info.MoveNextMethod, info.CurrentProperty?.GetMethod, info.DisposeMethod }
                            .Any(x => x != null && MayTouchArrays(x)) || Unwrap(fe.Collection).Type is IArrayTypeSymbol;
                        break;
                }
                if (callee != null && !SpecSymbols.IsSpecClass(callee.ContainingType) && MayTouchArrays(callee)) touches = true;
                if (touches) break;
            }
            return _touchesArrays[key] = touches;
        }

        private static IOperation Unwrap(IOperation op)
        {
            while (op is IConversionOperation c && c.IsImplicit) op = c.Operand;
            return op;
        }

        private readonly Dictionary<IMethodSymbol, HashSet<IMethodSymbol>> _callees = new Dictionary<IMethodSymbol, HashSet<IMethodSymbol>>(SymbolEqualityComparer.Default);

        /// <summary>
        /// Is a call from <paramref name="caller"/> to <paramref name="callee"/> recursive: does the callee (directly or
        /// through other methods) call the caller back? Calls inside specifications are ghost and do not count.
        /// </summary>
        internal bool IsRecursiveCall(IMethodSymbol caller, IMethodSymbol callee)
        {
            caller = (caller.ReducedFrom ?? caller).OriginalDefinition;
            callee = (callee.ReducedFrom ?? callee).OriginalDefinition;
            var seen = new HashSet<IMethodSymbol>(SymbolEqualityComparer.Default);
            var work = new Stack<IMethodSymbol>();
            work.Push(callee);
            while (work.Count > 0)
            {
                var m = work.Pop();
                if (SymbolEqualityComparer.Default.Equals(m, caller)) return true;
                if (!seen.Add(m)) continue;
                foreach (var next in CalleesOf(m)) work.Push(next);
            }
            return false;
        }

        private HashSet<IMethodSymbol> CalleesOf(IMethodSymbol m)
        {
            if (_callees.TryGetValue(m, out var known)) return known;
            var result = new HashSet<IMethodSymbol>(SymbolEqualityComparer.Default);
            _callees[m] = result;
            var c = ContractOf(m);
            if (!c.HasSource) return result;
            foreach (var inv in c.Declaration.DescendantNodes().OfType<InvocationExpressionSyntax>())
                if (c.Model.GetSymbolInfo(inv).Symbol is IMethodSymbol callee && SpecSymbols.EnclosingSpecCall(inv, c.Model) == null)
                    result.Add((callee.ReducedFrom ?? callee).OriginalDefinition);
            return result;
        }

        internal SemanticModel ModelOf(SyntaxTree tree) => _compilation.GetSemanticModel(tree);

        private HashSet<IMethodSymbol> _underInvariants;

        /// <summary>
        /// Does an [Invariant] method depend on this one (calls it, in code or specifications, directly or not)? Then
        /// verifying it may not assume invariants: the invariant would be proved at construction with facts that
        /// were themselves derived from it.
        /// </summary>
        internal bool IsUnderInvariant(IMethodSymbol m)
        {
            if (_underInvariants == null)
            {
                _underInvariants = new HashSet<IMethodSymbol>(SymbolEqualityComparer.Default);
                var work = new Stack<IMethodSymbol>();
                foreach (var tree in _compilation.SyntaxTrees)
                {
                    var model = _compilation.GetSemanticModel(tree);
                    foreach (var decl in tree.GetRoot().DescendantNodes().OfType<MethodDeclarationSyntax>())
                        if (model.GetDeclaredSymbol(decl) is IMethodSymbol im && SpecSymbols.IsInvariant(im)) work.Push(im);
                }
                while (work.Count > 0)
                {
                    var next = work.Pop();
                    if (!_underInvariants.Add(next)) continue;
                    var c = ContractOf(next);
                    if (!c.HasSource) continue;
                    foreach (var inv in c.Declaration.DescendantNodes().OfType<InvocationExpressionSyntax>())
                        if (c.Model.GetSymbolInfo(inv).Symbol is IMethodSymbol callee)
                            work.Push((callee.ReducedFrom ?? callee).OriginalDefinition);
                }
            }
            return _underInvariants.Contains((m.ReducedFrom ?? m).OriginalDefinition);
        }

        private readonly Dictionary<IMethodSymbol, Contract> _libraryContracts = new Dictionary<IMethodSymbol, Contract>(SymbolEqualityComparer.Default);

        /// <summary>A library member's contract as if it had no stub: what an async stub's member gives when not awaited.</summary>
        internal Contract LibraryContractOf(IMethodSymbol m)
        {
            var key = (m.ReducedFrom ?? m).OriginalDefinition;
            return _libraryContracts.TryGetValue(key, out var c) ? c : _libraryContracts[key] = Contract.Read(key, _compilation);
        }

        private StartedDelegates _startedDelegates;
        internal StartedDelegates StartedDelegates => _startedDelegates ??= new StartedDelegates(this, _compilation);

        internal Contract ContractOf(IMethodSymbol m)
        {
            var key = (m.ReducedFrom ?? m).OriginalDefinition;
            if (_contracts.TryGetValue(key, out var c)) return c;
            // a member without sources, specified by a stub
            if (key.DeclaringSyntaxReferences.Length == 0 && StubOrInherited(key) is IMethodSymbol stub)
                return _contracts[key] = Contract.ReadStub(key, stub, _compilation);
            // a contract class's member, named in its own specifications, stands for the member it specifies
            if (SpecSymbols.ContractClassTarget(key.ContainingType) != null && SpecifiedMember(key) is IMethodSymbol target)
                return _contracts[key] = ContractOf(target);
            _contracts[key] = c = Contract.Read(key, _compilation);
            // behavioural subtyping: an abstract or interface member's contract comes from its contract class, and
            // an override or implementation inherits the contracts of what it overrides or implements
            var spec = ContractClassMethod(key);
            var bases = BaseMembers(key).Select(ContractOf);
            // a delegate type's contract is its contract class's Invoke; a lambda made one inherits it, as an override does
            if (key.MethodKind == MethodKind.DelegateInvoke && DelegateContractMethod(key) is IMethodSymbol invoke) { spec = invoke; c.OfDelegate = true; }
            if (key.MethodKind == MethodKind.AnonymousFunction && DelegateTypeOf(key)?.DelegateInvokeMethod is IMethodSymbol made && ContractOf(made).OfDelegate)
                bases = bases.Append(ContractOf(made));
            c.Inherit(spec != null ? Contract.Read(spec, _compilation) : null, bases.ToList());
            return c;
        }

        /// <summary>The Invoke of a delegate type's [ContractClassFor] class.</summary>
        private IMethodSymbol DelegateContractMethod(IMethodSymbol invoke) =>
            ContractClassOf(invoke.ContainingType)?.GetMembers("Invoke").OfType<IMethodSymbol>().FirstOrDefault(o => o.Parameters.Length == invoke.Parameters.Length);

        /// <summary>The delegate type a lambda is made into, if it's made into one.</summary>
        internal INamedTypeSymbol DelegateTypeOf(IMethodSymbol lambda)
        {
            if (lambda.MethodKind != MethodKind.AnonymousFunction || !(lambda.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() is AnonymousFunctionExpressionSyntax syntax)) return null;
            var op = _compilation.GetSemanticModel(syntax.SyntaxTree).GetOperation(syntax);
            while (op?.Parent is IConversionOperation || op?.Parent is IParenthesizedOperation) op = op.Parent;
            return op?.Parent is IDelegateCreationOperation dc ? dc.Type as INamedTypeSymbol : (op?.Type as INamedTypeSymbol);
        }

        /// <summary>Does calling a delegate of this type prove and assume a contract?</summary>
        internal bool HasDelegateContract(ITypeSymbol type) =>
            type is INamedTypeSymbol { TypeKind: TypeKind.Delegate } d && d.DelegateInvokeMethod != null && ContractOf(d.DelegateInvokeMethod).OfDelegate;

        /// <summary>
        /// The stub of a library member, or else of the member it overrides (StreamWriter.Write(string) keeps
        /// TextWriter.Write(string)'s contract: behavioural subtyping, trusted for the library's own overrides).
        /// </summary>
        private IMethodSymbol StubOrInherited(IMethodSymbol m)
        {
            for (var cur = m; cur != null && cur.DeclaringSyntaxReferences.Length == 0; cur = cur.OverriddenMethod?.OriginalDefinition)
                if (Stubs.StubOf(cur) is IMethodSymbol stub) return stub;
            return null;
        }

        /// <summary>Does this library member have a contract from a stub (its own, or the member's it overrides)?</summary>
        internal bool HasStub(IMethodSymbol m) =>
            m != null && (m.ReducedFrom ?? m).OriginalDefinition is IMethodSymbol key && key.DeclaringSyntaxReferences.Length == 0 && StubOrInherited(key) != null;

        private Dictionary<INamedTypeSymbol, INamedTypeSymbol> _contractClasses;

        /// <summary>The [ContractClassFor] class of an interface or abstract class, if any.</summary>
        internal INamedTypeSymbol ContractClassOf(INamedTypeSymbol type)
        {
            if (_contractClasses == null)
            {
                _contractClasses = new Dictionary<INamedTypeSymbol, INamedTypeSymbol>(SymbolEqualityComparer.Default);
                foreach (var t in SourceTypes)
                    if (SpecSymbols.ContractClassTarget(t) is INamedTypeSymbol target) _contractClasses[target.OriginalDefinition] = t;
            }
            return type != null && _contractClasses.TryGetValue(type.OriginalDefinition, out var cc) ? cc : null;
        }

        /// <summary>The contract-class method that specifies an interface or abstract member.</summary>
        private IMethodSymbol ContractClassMethod(IMethodSymbol m)
        {
            if (!(m.IsAbstract || m.ContainingType?.TypeKind == TypeKind.Interface) || !(ContractClassOf(m.ContainingType) is INamedTypeSymbol cc)) return null;
            if (m.ContainingType.TypeKind == TypeKind.Interface)
            {
                // (a generic interface's member, of the instantiation the contract class implements: IKey<T> of KeyContract<T>)
                var def = m.OriginalDefinition;
                var im = cc.AllInterfaces.Where(i => SymbolEqualityComparer.Default.Equals(i.OriginalDefinition, def.ContainingType))
                    .SelectMany(i => i.GetMembers(def.Name)).OfType<IMethodSymbol>().FirstOrDefault(x => SymbolEqualityComparer.Default.Equals(x.OriginalDefinition, def));
                return cc.FindImplementationForInterfaceMember(im ?? m) as IMethodSymbol;
            }
            return cc.GetMembers(m.Name).OfType<IMethodSymbol>().FirstOrDefault(o => SymbolEqualityComparer.Default.Equals(o.OverriddenMethod?.OriginalDefinition, m));
        }

        /// <summary>The interface or abstract member a contract class's method specifies.</summary>
        private static IMethodSymbol SpecifiedMember(IMethodSymbol m)
        {
            if (m.OverriddenMethod != null) return m.OverriddenMethod.OriginalDefinition;
            foreach (var iface in m.ContainingType.AllInterfaces)
                foreach (var im in iface.GetMembers().OfType<IMethodSymbol>())
                    if (SymbolEqualityComparer.Default.Equals(m.ContainingType.FindImplementationForInterfaceMember(im)?.OriginalDefinition, m))
                        return im.OriginalDefinition;
            return null;
        }

        /// <summary>The members a method overrides or implements (one level: their own contracts carry the rest).</summary>
        internal IEnumerable<IMethodSymbol> BaseMembers(IMethodSymbol m)
        {
            if (m.IsStatic || m.ContainingType == null || SpecSymbols.ContractClassTarget(m.ContainingType) != null) yield break;
            if (m.OverriddenMethod != null) yield return m.OverriddenMethod.OriginalDefinition;
            foreach (var iface in m.ContainingType.AllInterfaces)
                foreach (var im in iface.GetMembers().OfType<IMethodSymbol>())
                    if (SymbolEqualityComparer.Default.Equals(m.ContainingType.FindImplementationForInterfaceMember(im)?.OriginalDefinition, m))
                        yield return im.OriginalDefinition;
        }

        /// <summary>
        /// For the Boogie engine, which doesn't check races yet: the method doesn't run alongside other code, and reads
        /// no field a lock guards.
        /// </summary>
        private static bool Sequential(Engine engine, IMethodSymbol method, SyntaxNode decl, SemanticModel model) =>
            !decl.DescendantNodes().OfType<Microsoft.CodeAnalysis.CSharp.Syntax.SimpleNameSyntax>()
                .Any(n => model.GetSymbolInfo(n).Symbol is ISymbol s && (s is IFieldSymbol || s is IPropertySymbol) && engine.Locks.GuardOf(s) is ISymbol g &&
                          // (a lock statement's lock, an object: Boogie's; a semaphore or a flag: not yet)
                          !Boogie.KernelTypes.IsLockObject(g) && !engine.Locks.IsFlag(g) && !(g is IFieldSymbol gf && engine.Locks.IsMutexGate(gf)));

        /// <summary>A member whose body is not known at the call: virtual, abstract, an interface member (not sealed).</summary>
        internal static bool IsOverridable(IMethodSymbol m) =>
            (m.IsVirtual || m.IsAbstract || m.IsOverride || m.ContainingType?.TypeKind == TypeKind.Interface) &&
            !m.IsSealed && m.ContainingType?.IsSealed != true && !m.IsStatic;

        public static VerificationResult VerifyFiles(IEnumerable<string> paths, VerifierOptions options) =>
            VerifySources(paths.Select(p => (p, File.ReadAllText(p))), options);

        public static VerificationResult VerifySources(IEnumerable<(string path, string text)> sources, VerifierOptions options)
        {
            var parse = new CSharpParseOptions(LanguageVersion.Latest,
                preprocessorSymbols: new[] { SpecSymbols.SpecSymbol }.Concat(options.Defines));
            var userTrees = sources.Select(s => CSharpSyntaxTree.ParseText(s.text, parse, s.path)).ToList();
            var references = References(options).ToList();
            var specTrees = SpecTrees(parse, ReferencesEfCore(references));
            var compilation = CSharpCompilation.Create("CsVerifyTarget", userTrees.Concat(specTrees), references,
                new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary, allowUnsafe: true, nullableContextOptions: options.Nullable));

            var result = new VerificationResult();
            foreach (var d in compilation.GetDiagnostics().Where(d => d.Severity == DiagnosticSeverity.Error))
                result.CompilationErrors.Add(new VerificationDiagnostic(d.Id, true, d.GetMessage(), d.Location.GetLineSpan()));
            if (result.CompilationErrors.Count > 0) return result;

            var declarations = new List<(SyntaxNode decl, MethodResult result)>();
            using var engine = new Engine(compilation, options, userTrees);
            Boogie.KernelTypes.Data = engine.Data;
            Boogie.KernelTypes.Compilation = compilation;
            Boogie.KernelTypes.RefArrays = Boogie.KernelTypes.NamesRefArrays(compilation);
            Boogie.KernelTypes.FloatArrays = Boogie.KernelTypes.NamesFloatArrays(compilation);
            Boogie.KernelTypes.ScalarArrays = Boogie.KernelTypes.NamesScalarArrays(compilation, userTrees);
            Boogie.KernelTypes.StaticReadonlyIds = new Dictionary<string, int>();
            Boogie.KernelTypes.StaticReadonlyNonNull = new HashSet<int>();
            Boogie.KernelTypes.Locks = engine.Locks;
            Boogie.KernelTypes.SteppedBy = m => engine.Atomics.SteppedBy(m).Where(f => Atomics.StepOf(f) != null);
            Boogie.KernelTypes.Started = engine.StartedDelegates;
            Boogie.KernelTypes.Levels = engine.Levels;
            Boogie.KernelTypes.MayWriteHeap = engine.MayWriteHeap;
            Boogie.KernelTypes.AsyncStub = m => m.DeclaringSyntaxReferences.Length == 0 && engine.ContractOf(m) is Contract sc && sc.IsStub && sc.Stub?.IsAsync == true;
            Boogie.KernelTypes.NestedGraphs = new Dictionary<IMethodSymbol, ControlFlowGraph>(SymbolEqualityComparer.Default);
            Boogie.KernelTypes.WritesFieldsAt = engine.Fields.WritesFieldsAt;
            Boogie.KernelTypes.RunsUserCode = engine.Fields.RunsUserCode;
            Boogie.KernelTypes.Ef = engine.Ef;
            Boogie.KernelTypes.FieldWrites = m => engine.Fields.WritesOf(m).fields;
            Boogie.KernelTypes.FieldReads = engine.Fields.ReadsOf;
            Boogie.KernelTypes.FieldEffectsOf = m => { var (f, all) = engine.Fields.WritesOf(m); return (f, all); };
            Boogie.KernelTypes.MayTouchArrays = engine.MayTouchArrays;
            Boogie.KernelTypes.Trees = userTrees.Any(t => t.GetRoot().DescendantNodes().OfType<Microsoft.CodeAnalysis.CSharp.Syntax.FieldDeclarationSyntax>()
                .Any(f => f.AttributeLists.SelectMany(l => l.Attributes).Any(a => a.Name.ToString() is "Owns" or "OwnsAttribute")));
            var forBoogie = new List<(IMethodSymbol method, Contract contract, SyntaxNode decl, MethodResult result)>();
            var boogieAccessors = new HashSet<SyntaxNode>();
            // (the Spec library's trusted lemmas the program calls, Ieee's: procedures of their contracts, as a trusted method of its own is)
            var libraryLemmas = new HashSet<IMethodSymbol>(SymbolEqualityComparer.Default);
            foreach (var tree in userTrees)
            {
                var model = compilation.GetSemanticModel(tree);
                foreach (var inv in tree.GetRoot().DescendantNodes().OfType<InvocationExpressionSyntax>())
                    if (model.GetSymbolInfo(inv).Symbol is IMethodSymbol lm && lm.ContainingNamespace?.ToDisplayString() == SpecSymbols.Namespace && SpecSymbols.IsTrusted(lm) &&
                        lm.DeclaringSyntaxReferences.Length == 1 && !userTrees.Contains(lm.DeclaringSyntaxReferences[0].SyntaxTree) && libraryLemmas.Add(lm.OriginalDefinition) &&
                        Boogie.BoogieTranslator.Candidate(lm.OriginalDefinition, engine.ContractOf(lm.OriginalDefinition), asContract: true))
                        forBoogie.Add((lm.OriginalDefinition, engine.ContractOf(lm.OriginalDefinition), lm.DeclaringSyntaxReferences[0].GetSyntax(), new MethodResult { Name = null }));
            }
            foreach (var tree in userTrees)
            {
                var model = compilation.GetSemanticModel(tree);
                // a delegate type with a contract: for Boogie, its Invoke is a procedure of it alone, as an abstract member is
                foreach (var dd in tree.GetRoot().DescendantNodes().OfType<DelegateDeclarationSyntax>())
                    if (model.GetDeclaredSymbol(dd) is INamedTypeSymbol dt && dt.DelegateInvokeMethod is IMethodSymbol di &&
                        engine.HasDelegateContract(dt) && Boogie.BoogieTranslator.Candidate(di, engine.ContractOf(di)))
                        forBoogie.Add((di, engine.ContractOf(di), dd, new MethodResult { Name = null }));
                foreach (var decl in tree.GetRoot().DescendantNodes().OfType<BaseMethodDeclarationSyntax>())
                {
                    if (decl.Body == null && decl.ExpressionBody == null)
                    {
                        // an abstract member: for Boogie, a procedure with no body, which calls through the base go to
                        // (nothing of its own to verify: it has no result)
                        if (model.GetDeclaredSymbol(decl) is IMethodSymbol am && am.IsAbstract && Boogie.BoogieTranslator.Candidate(am, engine.ContractOf(am)))
                            forBoogie.Add((am, engine.ContractOf(am), decl, new MethodResult { Name = null }));
                        continue;
                    }
                    if (!(model.GetDeclaredSymbol(decl) is IMethodSymbol method)) continue;
                    // (a trusted method: its body skipped, its contract its callers' procedure, nothing of it verified)
                    if (SpecSymbols.IsTrusted(method))
                    {
                        if (Boogie.BoogieTranslator.Candidate(method, engine.ContractOf(method), asContract: true)) forBoogie.Add((method, engine.ContractOf(method), decl, new MethodResult { Name = null }));
                        continue;
                    }
                    if (SpecSymbols.IsContractsClass(method.ContainingType) || SpecSymbols.IsModel(method)) continue; // contracts, not code
                    var contract = engine.ContractOf(method);
                    var span = decl.GetLocation().GetLineSpan();
                    var mr = new MethodResult { Name = method.ContainingType.Name + "." + method.Name, Declared = span.Path + ":" + (span.StartLinePosition.Line + 1) };
                    // (its lambdas and local functions, each a unit of its own: selected or not, as it is)
                    if (!options.Selects(mr.Name)) { RunNested(engine, decl, model, mr.Name, result, declarations, options, forBoogie); continue; }
                    result.Methods.Add(mr);
                    declarations.Add((decl, mr));
                    if (Boogie.BoogieTranslator.Candidate(method, contract) && Sequential(engine, method, decl, model)) forBoogie.Add((method, contract, decl, mr));
                    else NotVerified(engine, contract, mr, decl.GetLocation(), null, Boogie.BoogieTranslator.Candidate(method, contract) ? "a field guarded by a semaphore or a flag" : Boogie.BoogieTranslator.WhyNot(method, contract));
                    // its lambdas and local functions, each a unit of its own
                    RunNested(engine, decl, model, mr.Name, result, declarations, options, forBoogie);
                }
            }
            // accessors with code: properties are methods too (Boogie's, where they are in its subset; an abstract or an
            // interface one is a procedure of its contract, which has nothing of its own to verify)
            foreach (var tree in userTrees)
            {
                var model = compilation.GetSemanticModel(tree);
                foreach (var node in tree.GetRoot().DescendantNodes())
                {
                    IMethodSymbol accessor = node switch
                    {
                        AccessorDeclarationSyntax acc => model.GetDeclaredSymbol(acc) as IMethodSymbol,
                        ArrowExpressionClauseSyntax arrow when arrow.Parent is BasePropertyDeclarationSyntax prop => (model.GetDeclaredSymbol(prop) as IPropertySymbol)?.GetMethod,
                        _ => null,
                    };
                    if (accessor == null || SpecSymbols.IsTrusted(accessor) || SpecSymbols.IsContractsClass(accessor.ContainingType) ||
                        accessor.ContainingType?.ContainingNamespace?.ToDisplayString() == SpecSymbols.Namespace) continue;
                    bool hasCode = node is ArrowExpressionClauseSyntax || node is AccessorDeclarationSyntax a && (a.Body != null || a.ExpressionBody != null);
                    if (!hasCode && !accessor.IsAbstract) continue; // (an auto-property's: a field)
                    var contract = engine.ContractOf(accessor);
                    if (!Boogie.BoogieTranslator.Candidate(accessor, contract) || !Sequential(engine, accessor, node, model))
                    {
                        Trace($"not translated to Boogie: {accessor.ContainingType.Name}.{accessor.Name}: {(Boogie.BoogieTranslator.Candidate(accessor, contract) ? "a field guarded by a semaphore or a flag" : Boogie.BoogieTranslator.WhyNot(accessor, contract))}");
                        continue;
                    }
                    var span = node.GetLocation().GetLineSpan();
                    var mr = new MethodResult { Name = hasCode ? accessor.ContainingType.Name + "." + accessor.Name : null, Declared = span.Path + ":" + (span.StartLinePosition.Line + 1) };
                    if (hasCode && !options.Selects(mr.Name)) continue;
                    if (hasCode) { result.Methods.Add(mr); declarations.Add((node, mr)); boogieAccessors.Add(node); }
                    forBoogie.Add((accessor, contract, node, mr));
                }
            }
            // the lambdas and local functions in properties' code
            foreach (var tree in userTrees)
            {
                var model = compilation.GetSemanticModel(tree);
                foreach (var node in tree.GetRoot().DescendantNodes())
                {
                    IMethodSymbol accessor = node switch
                    {
                        AccessorDeclarationSyntax acc when acc.Body != null || acc.ExpressionBody != null => model.GetDeclaredSymbol(acc) as IMethodSymbol,
                        ArrowExpressionClauseSyntax arrow when arrow.Parent is BasePropertyDeclarationSyntax prop => (model.GetDeclaredSymbol(prop) as IPropertySymbol)?.GetMethod,
                        _ => null,
                    };
                    if (accessor == null || SpecSymbols.IsTrusted(accessor) || SpecSymbols.IsContractsClass(accessor.ContainingType) ||
                        accessor.ContainingType?.ContainingNamespace?.ToDisplayString() == SpecSymbols.Namespace) continue;
                    RunNested(engine, node, model, accessor.ContainingType.Name + "." + accessor.Name, result, declarations, options, forBoogie);
                }
            }
            // the lambdas in field and property initializers (static readonly Pricing Flat = q => 100 * q): no method has them
            foreach (var tree in userTrees)
            {
                var model = compilation.GetSemanticModel(tree);
                foreach (var init in tree.GetRoot().DescendantNodes().OfType<EqualsValueClauseSyntax>())
                {
                    if (!(init.Parent is VariableDeclaratorSyntax && init.Parent.Parent?.Parent is FieldDeclarationSyntax || init.Parent is PropertyDeclarationSyntax)) continue;
                    if (!init.DescendantNodes().OfType<AnonymousFunctionExpressionSyntax>().Any()) continue;
                    var member = init.Parent is VariableDeclaratorSyntax vd ? model.GetDeclaredSymbol(vd) : model.GetDeclaredSymbol(init.Parent);
                    if (member?.ContainingType == null || SpecSymbols.IsContractsClass(member.ContainingType)) continue;
                    RunNested(engine, init, model, member.ContainingType.Name + "." + member.Name, result, declarations, options, forBoogie);
                }
            }
            if (forBoogie.Count > 0) result.BoogieFailure = RunBoogie(engine, compilation, forBoogie);
            // accessors with code: properties are methods too
            foreach (var tree in userTrees)
            {
                var model = compilation.GetSemanticModel(tree);
                foreach (var node in tree.GetRoot().DescendantNodes())
                {
                    IMethodSymbol accessor = node switch
                    {
                        AccessorDeclarationSyntax acc when acc.Body != null || acc.ExpressionBody != null => model.GetDeclaredSymbol(acc) as IMethodSymbol,
                        ArrowExpressionClauseSyntax arrow when arrow.Parent is BasePropertyDeclarationSyntax prop => (model.GetDeclaredSymbol(prop) as IPropertySymbol)?.GetMethod,
                        _ => null,
                    };
                    if (accessor == null || SpecSymbols.IsTrusted(accessor) || SpecSymbols.IsContractsClass(accessor.ContainingType) ||
                        accessor.ContainingType?.ContainingNamespace?.ToDisplayString() == SpecSymbols.Namespace) continue;
                    // (Boogie's: verified there, or as always if it couldn't; its lambdas, as always)
                    if (boogieAccessors.Contains(node)) continue;
                    var where = node.GetLocation().GetLineSpan();
                    var mr = new MethodResult { Name = accessor.ContainingType.Name + "." + accessor.Name, Declared = where.Path + ":" + (where.StartLinePosition.Line + 1) };
                    if (!options.Selects(mr.Name)) continue;
                    result.Methods.Add(mr);
                    declarations.Add((node, mr));
                    NotVerified(engine, engine.ContractOf(accessor), mr, node.GetLocation(), null,
                                Boogie.BoogieTranslator.Candidate(accessor, engine.ContractOf(accessor)) ? "a field guarded by a semaphore or a flag" : Boogie.BoogieTranslator.WhyNot(accessor, engine.ContractOf(accessor)));
                }
            }
            // classes with no constructor body of their own: their fields' initializers, which no method verifies
            if (options.Checked("CSV1014"))
                foreach (var tree in userTrees)
                {
                    var model = compilation.GetSemanticModel(tree);
                    foreach (var cd in tree.GetRoot().DescendantNodes().OfType<ClassDeclarationSyntax>())
                    {
                        if (!(model.GetDeclaredSymbol(cd) is INamedTypeSymbol type) || SpecSymbols.IsContractsClass(type)) continue;
                        var nulls = StaticChecks.ImplicitConstructorNulls(type, t => compilation.GetSemanticModel(t)).ToList();
                        var mr = new MethodResult { Name = type.Name + "..ctor" };
                        if (nulls.Count == 0 || !options.Selects(mr.Name)) continue;
                        mr.Obligations = nulls.Count;
                        foreach (var (_, at, message) in nulls)
                            mr.Diagnostics.Add(new VerificationDiagnostic("CSV1014", true, message, at.GetLocation().GetLineSpan()));
                        result.Methods.Add(mr);
                    }
                }
            // a stub that specifies nothing (a typo in a name or a parameter type) would silently leave a member unspecified
            foreach (var (stubMethod, message) in engine.Stubs.Errors)
            {
                var location = stubMethod?.Locations.FirstOrDefault();
                if (location == null || !userTrees.Contains(location.SourceTree) && !(location.SourceTree?.FilePath.StartsWith("<CsVerify.Spec>") == true)) continue;
                result.AnalyzerErrors.Add(new VerificationDiagnostic("CSV1021", true, message, location.GetLineSpan()));
            }
            result.Assumptions.UnionWith(result.Methods.SelectMany(mr => mr.Assumptions));
            AddAnalyzerErrors(compilation, userTrees, declarations, result, options);
            return result;
        }

        /// <summary>
        /// Runs the CsVerify analyzers over the same compilation. Their checks (linearity, ghost hygiene, purity of
        /// proofs) are premises of the verification, so their errors count against the method they are in.
        /// </summary>
        /// <summary>
        /// Verifies one method. Facts inferred for loops without invariants (StaticChecks.LoopFacts) are assumed at
        /// their heads; a run in which one might not hold at a back edge is redone without it, until a run assumes only
        /// facts it also proved. (After a few rounds, the last is run with none.)
        /// </summary>
        /// <summary>
        /// The lambdas and local functions of a method (nested in each other too), with their flow graphs: each is
        /// verified as a method of its own. Its parameters are as its delegate type declares them, and what it captures
        /// is some value of its type, since it may run at any time. Lambdas in specifications are ghost, not code.
        /// </summary>
        /// <summary>The lambdas and local functions in a property's code or an initializer, each verified as a unit of its own.</summary>
        private static void RunNested(Engine engine, SyntaxNode code, SemanticModel model, string owner, VerificationResult result,
                                      List<(SyntaxNode decl, MethodResult result)> declarations, VerifierOptions options,
                                      List<(IMethodSymbol method, Contract contract, SyntaxNode decl, MethodResult result)> forBoogie)
        {
            foreach (var (nested, graph) in NestedFunctions(code, model))
            {
                // (nothing but a call with permissions: it is proved where it starts)
                var syntax = nested.DeclaringSyntaxReferences[0].GetSyntax();
                if (syntax is AnonymousFunctionExpressionSyntax started && engine.StartedDelegates.CallOf(started) != null) continue;
                var where = nested.Locations[0].GetLineSpan();
                if (Boogie.KernelTypes.NestedGraphs != null) Boogie.KernelTypes.NestedGraphs[nested.OriginalDefinition] = graph;
                var nmr = new MethodResult { Name = owner + "." + NestedName(nested), Graph = graph,
                                             Declared = where.Path + ":" + (where.StartLinePosition.Line + 1) + ":" + (where.StartLinePosition.Character + 1) };
                if (!options.Selects(nmr.Name)) continue;
                result.Methods.Add(nmr);
                declarations.Add((syntax, nmr));
                var contract = engine.ContractOf(nested);
                if (Boogie.BoogieTranslator.Candidate(nested, contract) && Sequential(engine, nested, syntax, model)) forBoogie.Add((nested, contract, syntax, nmr));
                else NotVerified(engine, contract, nmr, nested.Locations[0], graph, Boogie.BoogieTranslator.Candidate(nested, contract) ? "a field guarded by a semaphore or a flag" : Boogie.BoogieTranslator.WhyNot(nested, contract));
            }
        }

        private static IEnumerable<(IMethodSymbol symbol, ControlFlowGraph graph)> NestedFunctions(SyntaxNode decl, SemanticModel model)
        {
            ControlFlowGraph root;
            switch (model.GetOperation(decl))
            {
                case IMethodBodyOperation mb: root = ControlFlowGraph.Create(mb); break;
                case IConstructorBodyOperation cb: root = ControlFlowGraph.Create(cb); break;
                case IFieldInitializerOperation fi: root = ControlFlowGraph.Create(fi); break;
                case IPropertyInitializerOperation pi: root = ControlFlowGraph.Create(pi); break;
                case IBlockOperation b when b.Parent == null: root = ControlFlowGraph.Create(b); break;
                default: yield break;
            }
            var todo = new Stack<ControlFlowGraph>();
            todo.Push(root);
            while (todo.Count > 0)
            {
                var g = todo.Pop();
                foreach (var lf in g.LocalFunctions)
                {
                    var lg = g.GetLocalFunctionControlFlowGraph(lf);
                    todo.Push(lg);
                    if (!SpecSymbols.IsTrusted(lf)) yield return (lf, lg);
                }
                foreach (var fa in g.Blocks.SelectMany(b => b.Operations.Concat(b.BranchValue != null ? new[] { b.BranchValue } : new IOperation[0]))
                             .SelectMany(o => o.DescendantsAndSelf()).OfType<IFlowAnonymousFunctionOperation>())
                {
                    var ag = g.GetAnonymousFunctionControlFlowGraph(fa);
                    todo.Push(ag);
                    if (!SpecSymbols.IsInGhostContext(fa.Syntax, model)) yield return (fa.Symbol, ag);
                }
            }
        }

        private static readonly object TraceLock = new object();

        /// <summary>
        /// Why a method isn't translated to Boogie, or isn't decided: on stderr with CSVERIFY_TRACE, and appended to the file
        /// CSVERIFY_TRACE_FILE names (a test run's, whose stderr isn't shown).
        /// </summary>
        private static void Trace(string line)
        {
            if (Environment.GetEnvironmentVariable("CSVERIFY_TRACE") != null) Console.Error.WriteLine(line);
            if (Environment.GetEnvironmentVariable("CSVERIFY_TRACE_FILE") is string file)
                lock (TraceLock) System.IO.File.AppendAllText(file, line + "\n");
        }

        private static string NestedName(IMethodSymbol m) =>
            m.MethodKind == MethodKind.LocalFunction ? m.Name : "<lambda:" + (m.Locations[0].GetLineSpan().StartLinePosition.Line + 1) + ">";

        /// <summary>
        /// The methods held back for Boogie: those whose bodies translate (and whose callees do), as one program, verified
        /// by it; the rest as always. If Boogie fails, they are all verified as always, and that is said.
        /// </summary>
        private static string RunBoogie(Engine engine, CSharpCompilation compilation, List<(IMethodSymbol method, Contract contract, SyntaxNode decl, MethodResult result)> held)
        {
            var clock = System.Diagnostics.Stopwatch.StartNew();
            var included = held.ToList();
            // (those whose bodies don't translate but whose contracts do: procedures of their contracts alone, which
            // their callers call; their bodies are verified as always)
            var opaque = new HashSet<MethodResult>(held.Where(x => SpecSymbols.IsTrusted(x.method)).Select(x => x.result));
            var why = new Dictionary<MethodResult, string>();
            Boogie.BoogieTranslator translator;
            // (a method that doesn't translate leaves out those that call it: until none is left out)
            while (true)
            {
                translator = new Boogie.BoogieTranslator(engine.Options.CheckOverflow);
                translator.Prelude();
                translator.ContractOf = engine.ContractOf;
                // (and memory views hold cells, as Spec.Acc of an array's does)
                translator.UsesPermissions = engine.UsesPermissions || compilation.SyntaxTrees.Any(t => t.GetRoot().DescendantNodes().OfType<IdentifierNameSyntax>()
                    .Any(n => n.Identifier.Text is "PointsTo" or "ArrayView" or "ArrayHole"));
                translator.ExceptionType = compilation.GetTypeByMetadataName("System.Exception");
                translator.OverridesOf = m => engine.Fields.Overrides(m);
                translator.UsesFieldPermissions = engine.UsesPermissions && compilation.SyntaxTrees.Any(t => t.GetRoot().DescendantNodes().OfType<Microsoft.CodeAnalysis.CSharp.Syntax.InvocationExpressionSyntax>()
                    .Any(i => i.Expression.ToString().EndsWith("Acc") && i.ArgumentList.Arguments.Count == 2 && i.ArgumentList.Arguments[1].Expression.ToString().StartsWith("nameof")));
                translator.Declare(included.Select(x => (x.method, x.decl, (SemanticModel)compilation.GetSemanticModel(x.decl.SyntaxTree))));
                var refused = new List<(IMethodSymbol, Contract, SyntaxNode, MethodResult)>();
                foreach (var x in included)
                {
                    var model = compilation.GetSemanticModel(x.decl.SyntaxTree);
                    if (!opaque.Contains(x.result))
                        try { translator.Procedure(x.method, x.contract, x.decl, model, x.result, x.result.Graph); continue; }
                        catch (Boogie.NotTranslated nt)
                        {
                            Trace($"not translated to Boogie: {x.result.Name ?? x.method.ContainingType.Name + "." + x.method.Name + " (abstract)"}: {nt.Message}");
                            why[x.result] = nt.Message;
                            if (x.result.Name == null) { refused.Add(x); continue; }
                            opaque.Add(x.result);
                            // (a lambda: nothing calls it, so no contract of it is needed; a local function's calls do)
                            if (x.method.MethodKind == MethodKind.AnonymousFunction) continue;
                        }
                    try { translator.ContractOnly(x.method, x.contract, x.decl, model, x.result, x.result.Graph); }
                    catch (Boogie.NotTranslated nc)
                    {
                        refused.Add(x);
                        opaque.Remove(x.result);
                        if (!why.ContainsKey(x.result)) why[x.result] = nc.Message;
                        Trace($"not translated to Boogie, nor its contract: {x.result.Name}: {nc.Message}");
                    }
                }
                if (refused.Count == 0) break;
                included = included.Except(refused).ToList();
            }
            translator.Finish();
            if (engine.Options.BoogieOut != null) System.IO.File.WriteAllText(engine.Options.BoogieOut, translator.Text);
            // (a method a callee's refusal left out: its calls weren't translated)
            foreach (var x in held.Except(included).Concat(included.Where(x => opaque.Contains(x.result))).Where(x => x.result.Name != null))
                NotVerified(engine, x.contract, x.result, x.decl.GetLocation(), x.result.Graph, why.TryGetValue(x.result, out var w) ? w : "a call of a method that isn't translated");
            included = included.Where(x => !opaque.Contains(x.result)).ToList();
            if (included.Count == 0) return null;
            List<(MethodResult method, VerificationDiagnostic diagnostic)> failures;
            try
            {
                // (once more if the run itself fails, as it can when the machine is loaded: talking to the solver times out)
                try { failures = Boogie.BoogieRunner.Verify(translator, Z3.Find(engine.Options.Z3Path), engine.Options.TimeoutMs); }
                catch (Exception first) when (!(first is InvalidOperationException))
                {
                    failures = Boogie.BoogieRunner.Verify(translator, Z3.Find(engine.Options.Z3Path), engine.Options.TimeoutMs * 2);
                }
            }
            catch (Exception e)
            {
                if (Environment.GetEnvironmentVariable("CSVERIFY_TRACE") != null) Console.Error.WriteLine("Boogie failed: " + e);
                foreach (var x in included.Where(x => x.result.Name != null))
                    NotVerified(engine, x.contract, x.result, x.decl.GetLocation(), x.result.Graph, "Boogie failed: " + e.Message.Split('\n')[0]);
                return e.GetType().Name + ": " + e.Message + "\n" + string.Join("\n", (e.StackTrace ?? "").Split('\n').Take(6));
            }
            foreach (var x in included)
            {
                var mine = failures.Where(f => f.method == x.result).Select(f => f.diagnostic).ToList();
                // (Boogie couldn't decide it, in the time it had: not verified, what it did decide reported)
                var undecided = mine.FirstOrDefault(d => d.Id == "CSV1900");
                if (undecided != null)
                {
                    mine = mine.Where(d => d.Id != "CSV1900").ToList();
                    Trace($"undecided by Boogie: {x.result.Name}: {undecided.Message}");
                }
                // (the library's members its code calls, as its translation listed them: kept)
                var libraryCalls = x.result.LibraryCalls.ToList();
                var assumed = x.result.Assumptions.ToList();
                x.result.Clear();
                x.result.LibraryCalls.UnionWith(libraryCalls);
                x.result.Assumptions.UnionWith(assumed);
                // (a failed check of a warning's: the warning, CSV1900, not an error)
                mine = mine.Select(d => d.Id == Boogie.Lowering.Warning ? new VerificationDiagnostic("CSV1900", false, d.Message.Replace(" (boogie)", ""), d.Span) : d).ToList();
                // (outside the check profile: assumed, not proved; Boogie assumes what it asserts, so it is)
                if (engine.Options.CheckKinds != null)
                    x.result.AssumedObligations += translator.Lines.Values.Distinct().Count(c => c.Method == x.result && Checks.KindOf(c.Id) != null && !engine.Options.Checked(c.Id));
                // (within a check profile, a construct not modeled is a warning, its value unknown)
                if (engine.Options.CheckKinds != null)
                    mine = mine.Select(d =>
                    {
                        if (d.Id != "CSV1901" || !d.IsError) return d;
                        x.result.Unmodeled++;
                        return new VerificationDiagnostic("CSV1901", false, d.Message.Replace(" (boogie)", "") + " (not modeled: treated as unknown)", d.Span);
                    }).ToList();
                mine = mine.Where(d => !d.IsError || engine.Options.Checked(d.Id)).ToList();
                x.result.Diagnostics.AddRange(mine);
                if (undecided != null)
                    x.result.Diagnostics.Add(new VerificationDiagnostic("CSV1902", true, $"'{x.result.Name}' is not verified: Boogie couldn't decide it in time ({undecided.Message})", x.decl.GetLocation().GetLineSpan()));
                // (what's checked from the syntax and the declarations, as for any method: locking, concurrency marks, ...)
                if (x.result.Name != null)
                {
                    var staticResult = new MethodResult();
                    try { new StaticChecks(engine, x.contract, staticResult) { NestedGraph = x.result.Graph }.Run(); }
                    catch (Exception e) { staticResult.Diagnostics.Add(new VerificationDiagnostic("CSV1999", true, "internal verifier error: " + e.Message, x.decl.GetLocation().GetLineSpan())); }
                    x.result.Diagnostics.AddRange(staticResult.Diagnostics);
                }
                x.result.Diagnostics.AddRange(translator.Warnings(x.result));
                x.result.Obligations = translator.Obligations.TryGetValue(x.result, out var n) ? n : 0;
                x.result.Proved = Math.Max(0, x.result.Obligations - mine.Count(d => d.IsError));
                x.result.Milliseconds = clock.ElapsedMilliseconds / included.Count;
                // (past its time budget: not verified, never verified)
                if (engine.Options.MethodBudgetMs > 0 && x.result.Milliseconds > engine.Options.MethodBudgetMs)
                    x.result.Diagnostics.Add(new VerificationDiagnostic("CSV1901", true,
                        $"time budget ({engine.Options.MethodBudgetMs} ms) reached; the rest of '{x.result.Name}' is not verified", x.decl.GetLocation().GetLineSpan()));
            }
            return null;
        }

        /// <summary>
        /// A method Boogie doesn't verify (its body isn't translated, or Boogie couldn't decide it): what's checked from
        /// the syntax and the declarations, and CSV1902, an error, saying why.
        /// </summary>
        private static void NotVerified(Engine engine, Contract contract, MethodResult mr, Location at, ControlFlowGraph nested, string reason)
        {
            mr.Clear();
            var staticResult = new MethodResult();
            try { new StaticChecks(engine, contract, staticResult) { NestedGraph = nested }.Run(); }
            catch (Exception e) { staticResult.Diagnostics.Add(new VerificationDiagnostic("CSV1999", true, "internal verifier error: " + e.Message, at.GetLineSpan())); }
            mr.Diagnostics.AddRange(staticResult.Diagnostics);
            mr.Diagnostics.Add(new VerificationDiagnostic("CSV1902", true, $"'{mr.Name}' is not verified: {reason}", at.GetLineSpan()));
            Trace($"not verified: {mr.Name}: {reason}");
        }

        private static void AddAnalyzerErrors(Compilation compilation, List<SyntaxTree> userTrees,
            List<(SyntaxNode decl, MethodResult result)> declarations, VerificationResult result, VerifierOptions options)
        {
            var analyzers = System.Collections.Immutable.ImmutableArray.Create<Microsoft.CodeAnalysis.Diagnostics.DiagnosticAnalyzer>(
                new LinearityAnalyzer(), new GhostAnalyzer(), new PurityAnalyzer(), new DisposalAnalyzer());
            var diagnostics = compilation.WithAnalyzers(analyzers).GetAnalyzerDiagnosticsAsync().GetAwaiter().GetResult();
            foreach (var d in diagnostics.Where(d => d.Severity == DiagnosticSeverity.Error && userTrees.Contains(d.Location.SourceTree) && options.Checked(d.Id)))
            {
                var vd = new VerificationDiagnostic(d.Id, true, d.GetMessage(), d.Location.GetLineSpan());
                var owner = declarations.FirstOrDefault(x => x.decl.SyntaxTree == d.Location.SourceTree && x.decl.FullSpan.Contains(d.Location.SourceSpan));
                if (owner.result != null)
                {
                    // (a method with an analyzer error isn't verified: that it isn't translated isn't news, CSV1902 goes)
                    owner.result.Diagnostics.RemoveAll(x => x.Id == "CSV1902");
                    owner.result.Diagnostics.Add(vd);
                }
                else result.AnalyzerErrors.Add(vd);
            }
        }

        // Syntax trees and metadata are immutable: one copy serves every verification in the process (a test run
        // verifies hundreds of programs at once; a copy each held gigabytes).
        private static readonly System.Collections.Concurrent.ConcurrentDictionary<string, IReadOnlyList<SyntaxTree>> _specTrees =
            new System.Collections.Concurrent.ConcurrentDictionary<string, IReadOnlyList<SyntaxTree>>();
        private static readonly Lazy<IReadOnlyList<MetadataReference>> _framework =
            new Lazy<IReadOnlyList<MetadataReference>>(() => LoadFrameworkReferences().ToList());

        /// <summary>The Spec library's sources (and EF Core's model, with EF Core), parsed once per set of preprocessor symbols.</summary>
        private static IReadOnlyList<SyntaxTree> SpecTrees(CSharpParseOptions parse, bool efCore) =>
            _specTrees.GetOrAdd(parse.LanguageVersion + "|" + efCore + "|" + string.Join(",", parse.PreprocessorSymbolNames.OrderBy(x => x)),
                _ => SpecSources(efCore).Select(s => CSharpSyntaxTree.ParseText(s.text, parse, s.name)).ToList());

        internal static IEnumerable<(string name, string text)> SpecSources(bool efCore = false)
        {
            var asm = typeof(Engine).Assembly;
            foreach (var name in asm.GetManifestResourceNames().Where(n => (n.StartsWith("CsVerify.Spec.") || efCore && n.StartsWith("CsVerify.Ef.")) && n.EndsWith(".cs")))
            {
                using var reader = new StreamReader(asm.GetManifestResourceStream(name));
                var prefix = name.StartsWith("CsVerify.Ef.") ? "CsVerify.Ef." : "CsVerify.Spec.";
                yield return ("<" + prefix.TrimEnd('.') + ">/" + name.Substring(prefix.Length), reader.ReadToEnd());
            }
        }

        /// <summary>Does the program reference Entity Framework Core (so its model is compiled in)?</summary>
        private static bool ReferencesEfCore(IEnumerable<MetadataReference> references) =>
            references.OfType<PortableExecutableReference>().Any(r => Path.GetFileName(r.FilePath ?? "") == "Microsoft.EntityFrameworkCore.dll");

        private static IEnumerable<MetadataReference> References(VerifierOptions options)
        {
            // Only the shared framework: the Spec library comes in as source (see SpecSources).
            var framework = FrameworkReferences().ToList();
            foreach (var r in framework) yield return r;
            // (a reference assembly of the framework's, from a project's references, would make its types ambiguous)
            var have = new HashSet<string>(framework.OfType<PortableExecutableReference>().Select(r => Path.GetFileName(r.FilePath ?? "")), StringComparer.OrdinalIgnoreCase);
            foreach (var r in options.References)
                if (!have.Contains(Path.GetFileName(r)))
                    yield return MetadataReference.CreateFromFile(r);
        }

        public static IEnumerable<MetadataReference> FrameworkReferences() => _framework.Value;

        private static IEnumerable<MetadataReference> LoadFrameworkReferences()
        {
            var frameworkDir = Path.GetDirectoryName(typeof(object).Assembly.Location);
            var tpa = ((string)AppContext.GetData("TRUSTED_PLATFORM_ASSEMBLIES") ?? "").Split(Path.PathSeparator);
            foreach (var path in tpa.Where(p => Path.GetDirectoryName(p) == frameworkDir && p.EndsWith(".dll")))
                yield return MetadataReference.CreateFromFile(path);
        }
    }
}
