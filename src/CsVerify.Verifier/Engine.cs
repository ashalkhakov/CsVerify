using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;
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
        public List<string> Defines = new List<string>();
        public List<string> References = new List<string>();
        public System.Text.StringBuilder SmtLog;
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
        public readonly SmtSolver Solver;
        private readonly Compilation _compilation;
        private readonly Dictionary<IMethodSymbol, Contract> _contracts = new Dictionary<IMethodSymbol, Contract>(SymbolEqualityComparer.Default);

        internal readonly DataTypes Data;
        internal readonly FieldEffects Fields;
        internal readonly IReadOnlyList<INamedTypeSymbol> SourceTypes;
        /// <summary>Does the program use dynamic frames (Spec.Modifies/Reads/Fresh, ObjSet)? Allocation is tracked only then.</summary>
        internal readonly bool UsesDynamicFrames;
        internal readonly LockGuards Locks;
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
            // (and the list interfaces, which read a List's models: MethodVerifier.Interfaces)
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
            Predicates = SourceTypes.SelectMany(t => t.GetMembers().OfType<IMethodSymbol>()).Where(SpecSymbols.IsPredicate).ToList();
            // (a predicate needs the permission state even with no [Owned] class: over arrays alone, say)
            UsesOwnership = SourceTypes.Any(SpecSymbols.IsOwned) || Predicates.Count > 0;
            UsesMemory = userTrees.Any(t => t.GetRoot().DescendantNodes().OfType<IdentifierNameSyntax>()
                .Any(n => n.Identifier.Text == "PointsTo" || n.Identifier.Text == "ArrayView" || n.Identifier.Text == "ArrayHole" || n.Identifier.Text == "Mem"));
            UsesPermissions = userTrees.Any(t => t.GetRoot().DescendantNodes().OfType<IdentifierNameSyntax>().Any(n => n.Identifier.Text == "Acc" || n.Identifier.Text == "AccRead"));

            Options = options;
            Solver = new SmtSolver(SmtSolver.FindZ3(options.Z3Path), options.TimeoutMs) { Log = options.SmtLog };
            Solver.Preamble(MethodVerifier.SeqTheory);
            Solver.Preamble(MethodVerifier.FloatTheory);
            if (userTrees.Any(t => t.GetRoot().DescendantNodes().OfType<ArrayRankSpecifierSyntax>().Any(r => r.Rank > 1)))
                Solver.Preamble(MethodVerifier.CellTheory); // rectangular arrays' cells
        }

        public void Dispose() => Solver.Dispose();

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
            // Mem and Ptr change only Mem's memory, whose cells change by their own rule (MethodVerifier.KeepHeldMemory)
            if (SpecSymbols.IsCsVerifyType(key.ContainingType, "Mem") || SpecSymbols.IsCsVerifyType(key.ContainingType, "Ptr`1"))
                return _writesHeap[key] = false;
            // which override runs is not known: any of them may write arrays (a stubbed library member's own
            // overrides in the library are trusted to keep its contract; the sources' are looked at)
            if (IsOverridable(key) && c.IsStub)
            {
                _writesHeap[key] = false; // (for recursion while computing)
                return _writesHeap[key] = key.Parameters.Any(p => MethodVerifier.IsWritableSequence(p.Type)) || Fields.RunsUserCode(key) ||
                                          Fields.Overrides(key).Any(MayWriteHeap);
            }
            if (IsOverridable(key)) return _writesHeap[key] = true;
            // a library method: through arrays (or spans) it is handed, not strings, or user code it runs (a delegate writing arrays it captured)
            if (!c.HasSource || c.IsStub) return _writesHeap[key] = key.Parameters.Any(p => MethodVerifier.IsWritableSequence(p.Type)) || Fields.RunsUserCode(key);
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
                    case IPropertyReferenceOperation pr when pr.Instance != null && MethodVerifier.IsSequence(pr.Instance.Type): touches = pr.Property.IsIndexer; break;
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
            c.Inherit(spec != null ? Contract.Read(spec, _compilation) : null, BaseMembers(key).Select(ContractOf));
            return c;
        }

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
                return cc.FindImplementationForInterfaceMember(m) as IMethodSymbol;
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
            var specTrees = SpecTrees(parse);
            var compilation = CSharpCompilation.Create("CsVerifyTarget", userTrees.Concat(specTrees), References(options),
                new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary, allowUnsafe: true, nullableContextOptions: options.Nullable));

            var result = new VerificationResult();
            foreach (var d in compilation.GetDiagnostics().Where(d => d.Severity == DiagnosticSeverity.Error))
                result.CompilationErrors.Add(new VerificationDiagnostic(d.Id, true, d.GetMessage(), d.Location.GetLineSpan()));
            if (result.CompilationErrors.Count > 0) return result;

            var declarations = new List<(SyntaxNode decl, MethodResult result)>();
            using var engine = new Engine(compilation, options, userTrees);
            foreach (var tree in userTrees)
            {
                var model = compilation.GetSemanticModel(tree);
                foreach (var decl in tree.GetRoot().DescendantNodes().OfType<BaseMethodDeclarationSyntax>())
                {
                    if (decl.Body == null && decl.ExpressionBody == null) continue;
                    if (!(model.GetDeclaredSymbol(decl) is IMethodSymbol method) || SpecSymbols.IsTrusted(method)) continue;
                    if (SpecSymbols.IsContractsClass(method.ContainingType) || SpecSymbols.IsModel(method)) continue; // contracts, not code
                    var contract = engine.ContractOf(method);
                    var mr = new MethodResult { Name = method.ContainingType.Name + "." + method.Name };
                    if (!options.Selects(mr.Name)) continue;
                    result.Methods.Add(mr);
                    declarations.Add((decl, mr));
                    RunMethod(engine, contract, mr, decl.GetLocation());
                    // its lambdas and local functions, each a unit of its own
                    foreach (var (nested, graph) in NestedFunctions(decl, model))
                    {
                        // (nothing but a call with permissions: it is proved where it starts)
                        if (nested.DeclaringSyntaxReferences[0].GetSyntax() is AnonymousFunctionExpressionSyntax started && engine.StartedDelegates.CallOf(started) != null) continue;
                        var nmr = new MethodResult { Name = mr.Name + "." + NestedName(nested) };
                        if (!options.Selects(nmr.Name)) continue;
                        result.Methods.Add(nmr);
                        declarations.Add((nested.DeclaringSyntaxReferences[0].GetSyntax(), nmr));
                        RunMethod(engine, engine.ContractOf(nested), nmr, nested.Locations[0], graph);
                    }
                }
            }
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
                    var mr = new MethodResult { Name = accessor.ContainingType.Name + "." + accessor.Name };
                    if (!options.Selects(mr.Name)) continue;
                    result.Methods.Add(mr);
                    declarations.Add((node, mr));
                    RunMethod(engine, engine.ContractOf(accessor), mr, node.GetLocation());
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
                        var nulls = MethodVerifier.ImplicitConstructorNulls(type, t => compilation.GetSemanticModel(t)).ToList();
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
        /// Verifies one method. Facts inferred for loops without invariants (MethodVerifier.LoopFacts) are assumed at
        /// their heads; a run in which one might not hold at a back edge is redone without it, until a run assumes only
        /// facts it also proved. (After a few rounds, the last is run with none.)
        /// </summary>
        /// <summary>
        /// The lambdas and local functions of a method (nested in each other too), with their flow graphs: each is
        /// verified as a method of its own. Its parameters are as its delegate type declares them, and what it captures
        /// is some value of its type, since it may run at any time. Lambdas in specifications are ghost, not code.
        /// </summary>
        private static IEnumerable<(IMethodSymbol symbol, ControlFlowGraph graph)> NestedFunctions(BaseMethodDeclarationSyntax decl, SemanticModel model)
        {
            ControlFlowGraph root;
            switch (model.GetOperation(decl))
            {
                case IMethodBodyOperation mb: root = ControlFlowGraph.Create(mb); break;
                case IConstructorBodyOperation cb: root = ControlFlowGraph.Create(cb); break;
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

        private static string NestedName(IMethodSymbol m) =>
            m.MethodKind == MethodKind.LocalFunction ? m.Name : "<lambda:" + (m.Locations[0].GetLineSpan().StartLinePosition.Line + 1) + ">";

        private static void RunMethod(Engine engine, Contract contract, MethodResult mr, Location at, ControlFlowGraph nested = null)
        {
            var clock = System.Diagnostics.Stopwatch.StartNew();
            long deadline = engine.Options.MethodBudgetMs > 0
                ? System.Diagnostics.Stopwatch.GetTimestamp() + engine.Options.MethodBudgetMs * System.Diagnostics.Stopwatch.Frequency / 1000 : 0;
            try { RunRounds(engine, contract, mr, at, nested, deadline); }
            finally { mr.Milliseconds = clock.ElapsedMilliseconds; }
        }

        private static void RunRounds(Engine engine, Contract contract, MethodResult mr, Location at, ControlFlowGraph nested, long deadline)
        {
            const int Rounds = 8;
            var excluded = new HashSet<string>(StringComparer.Ordinal);
            for (int round = 0; ; round++)
            {
                mr.Clear();
                engine.Solver.Reset();
                var verifier = new MethodVerifier(engine, contract, mr, round == Rounds ? null : excluded) { NestedGraph = nested, Deadline = deadline };
                if (round == Rounds) verifier.InferNoLoopFacts = true;
                bool failed = false;
                try { verifier.Run(); }
                catch (Exception e)
                {
                    mr.Diagnostics.Add(new VerificationDiagnostic("CSV1999", true, "internal verifier error: " + (Environment.GetEnvironmentVariable("CSVERIFY_TRACE") != null ? e.ToString() : e.Message), at.GetLineSpan()));
                    failed = true;
                }
                foreach (var err in engine.Solver.Errors)
                    mr.Diagnostics.Add(new VerificationDiagnostic("CSV1999", true, "solver error: " + err, at.GetLineSpan()));
                engine.Solver.Errors.Clear();
                foreach (var hang in engine.Solver.Hangs)
                    mr.Diagnostics.Add(new VerificationDiagnostic("CSV1998", true, hang, at.GetLineSpan()));
                engine.Solver.Hangs.Clear();
                if (failed || verifier.FailedLoopFacts.Count == 0 || round == Rounds || verifier.OverBudget) return;
                excluded.UnionWith(verifier.FailedLoopFacts);
            }
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
                if (owner.result != null) owner.result.Diagnostics.Add(vd);
                else result.AnalyzerErrors.Add(vd);
            }
        }

        // Syntax trees and metadata are immutable: one copy serves every verification in the process (a test run
        // verifies hundreds of programs at once; a copy each held gigabytes).
        private static readonly System.Collections.Concurrent.ConcurrentDictionary<string, IReadOnlyList<SyntaxTree>> _specTrees =
            new System.Collections.Concurrent.ConcurrentDictionary<string, IReadOnlyList<SyntaxTree>>();
        private static readonly Lazy<IReadOnlyList<MetadataReference>> _framework =
            new Lazy<IReadOnlyList<MetadataReference>>(() => LoadFrameworkReferences().ToList());

        /// <summary>The Spec library's sources, parsed once per set of preprocessor symbols.</summary>
        private static IReadOnlyList<SyntaxTree> SpecTrees(CSharpParseOptions parse) =>
            _specTrees.GetOrAdd(parse.LanguageVersion + "|" + string.Join(",", parse.PreprocessorSymbolNames.OrderBy(x => x)),
                _ => SpecSources().Select(s => CSharpSyntaxTree.ParseText(s.text, parse, s.name)).ToList());

        internal static IEnumerable<(string name, string text)> SpecSources()
        {
            var asm = typeof(Engine).Assembly;
            foreach (var name in asm.GetManifestResourceNames().Where(n => n.StartsWith("CsVerify.Spec.") && n.EndsWith(".cs")))
            {
                using var reader = new StreamReader(asm.GetManifestResourceStream(name));
                yield return ("<CsVerify.Spec>/" + name.Substring("CsVerify.Spec.".Length), reader.ReadToEnd());
            }
        }

        private static IEnumerable<MetadataReference> References(VerifierOptions options)
        {
            // Only the shared framework: the Spec library comes in as source (see SpecSources).
            foreach (var r in FrameworkReferences()) yield return r;
            foreach (var r in options.References)
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
