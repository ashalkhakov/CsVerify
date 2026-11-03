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

namespace CsVerify.Verifier
{
    public sealed class VerifierOptions
    {
        /// <summary>Check that integer arithmetic and narrowing conversions stay in range of their C# type.</summary>
        public bool CheckOverflow;
        /// <summary>
        /// The nullable context the sources are compiled in (the project's &lt;Nullable&gt;). Non-nullable reference
        /// types are contracts; oblivious ones (nullable disabled) are maybe-null, so only an enabled context lets
        /// the verifier know anything is not null.
        /// </summary>
        public NullableContextOptions Nullable = NullableContextOptions.Enable;
        public int TimeoutMs = 10000;
        public int MaxPaths = 5000;
        public string Z3Path;
        public List<string> Defines = new List<string>();
        public List<string> References = new List<string>();
        public System.Text.StringBuilder SmtLog;
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

        public override string ToString() =>
            $"{Span.Path}({Span.StartLinePosition.Line + 1},{Span.StartLinePosition.Character + 1}): {(IsError ? "error" : "warning")} {Id}: {Message}";
    }

    public sealed class MethodResult
    {
        public string Name;
        public int Obligations, Proved;
        public readonly List<VerificationDiagnostic> Diagnostics = new List<VerificationDiagnostic>();
        public bool Verified => Diagnostics.All(d => !d.IsError);
    }

    public sealed class VerificationResult
    {
        public readonly List<MethodResult> Methods = new List<MethodResult>();
        public readonly List<VerificationDiagnostic> CompilationErrors = new List<VerificationDiagnostic>();
        /// <summary>Analyzer errors outside any method body (a linear field in a non-linear type, say).</summary>
        public readonly List<VerificationDiagnostic> AnalyzerErrors = new List<VerificationDiagnostic>();
        public IEnumerable<VerificationDiagnostic> Diagnostics =>
            CompilationErrors.Concat(AnalyzerErrors).Concat(Methods.SelectMany(m => m.Diagnostics));
        public bool Success => !Diagnostics.Any(d => d.IsError);
        public MethodResult this[string name] => Methods.FirstOrDefault(m => m.Name == name || m.Name.EndsWith("." + name));
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

        private Engine(Compilation compilation, VerifierOptions options, IEnumerable<SyntaxTree> userTrees)
        {
            _compilation = compilation;
            Data = new DataTypes(compilation, userTrees);
            Fields = new FieldEffects(this);
            SourceTypes = userTrees.SelectMany(t => t.GetRoot().DescendantNodes().OfType<BaseTypeDeclarationSyntax>()
                .Select(d => compilation.GetSemanticModel(t).GetDeclaredSymbol(d)).OfType<INamedTypeSymbol>()).ToList();
            Options = options;
            Solver = new SmtSolver(SmtSolver.FindZ3(options.Z3Path), options.TimeoutMs) { Log = options.SmtLog };
            Solver.Preamble(MethodVerifier.SeqTheory);
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
            if (_writesHeap.TryGetValue(key, out var known)) return known;
            var c = ContractOf(key);
            if (c.IsPure || c.IsLemma) return _writesHeap[key] = false;
            if (!c.HasSource) return _writesHeap[key] = key.Parameters.Any(p => MethodVerifier.IsSequence(p.Type));
            _writesHeap[key] = false; // assume no for recursive calls while computing
            bool writes = false;
            foreach (var n in c.Declaration.DescendantNodes())
            {
                ExpressionSyntax target = n switch
                {
                    AssignmentExpressionSyntax a => a.Left,
                    PrefixUnaryExpressionSyntax pre => pre.Operand,
                    PostfixUnaryExpressionSyntax post => post.Operand,
                    ArgumentSyntax arg when !arg.RefKindKeyword.IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.None) => arg.Expression,
                    _ => null,
                };
                if (target is ElementAccessExpressionSyntax) writes = true;
                if (n is InvocationExpressionSyntax inv && c.Model.GetSymbolInfo(inv).Symbol is IMethodSymbol callee &&
                    !SpecSymbols.IsSpecClass(callee.ContainingType) && MayWriteHeap(callee)) writes = true;
                if (writes) break;
            }
            return _writesHeap[key] = writes;
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

        internal Contract ContractOf(IMethodSymbol m)
        {
            var key = (m.ReducedFrom ?? m).OriginalDefinition;
            if (!_contracts.TryGetValue(key, out var c)) _contracts[key] = c = Contract.Read(key, _compilation);
            return c;
        }

        public static VerificationResult VerifyFiles(IEnumerable<string> paths, VerifierOptions options) =>
            VerifySources(paths.Select(p => (p, File.ReadAllText(p))), options);

        public static VerificationResult VerifySources(IEnumerable<(string path, string text)> sources, VerifierOptions options)
        {
            var parse = new CSharpParseOptions(LanguageVersion.Latest,
                preprocessorSymbols: new[] { SpecSymbols.SpecSymbol }.Concat(options.Defines));
            var userTrees = sources.Select(s => CSharpSyntaxTree.ParseText(s.text, parse, s.path)).ToList();
            var specTrees = SpecSources().Select(s => CSharpSyntaxTree.ParseText(s.text, parse, s.name)).ToList();
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
                    var contract = engine.ContractOf(method);
                    var mr = new MethodResult { Name = method.ContainingType.Name + "." + method.Name };
                    result.Methods.Add(mr);
                    declarations.Add((decl, mr));
                    engine.Solver.Reset();
                    try { new MethodVerifier(engine, contract, mr).Run(); }
                    catch (Exception e)
                    {
                        mr.Diagnostics.Add(new VerificationDiagnostic("CSV1999", true, "internal verifier error: " + e.Message,
                            decl.GetLocation().GetLineSpan()));
                    }
                    foreach (var err in engine.Solver.Errors)
                        mr.Diagnostics.Add(new VerificationDiagnostic("CSV1999", true, "solver error: " + err, decl.GetLocation().GetLineSpan()));
                    engine.Solver.Errors.Clear();
                }
            }
            AddAnalyzerErrors(compilation, userTrees, declarations, result);
            return result;
        }

        /// <summary>
        /// Runs the CsVerify analyzers over the same compilation. Their checks (linearity, ghost hygiene, purity of
        /// proofs) are premises of the verification, so their errors count against the method they are in.
        /// </summary>
        private static void AddAnalyzerErrors(Compilation compilation, List<SyntaxTree> userTrees,
            List<(SyntaxNode decl, MethodResult result)> declarations, VerificationResult result)
        {
            var analyzers = System.Collections.Immutable.ImmutableArray.Create<Microsoft.CodeAnalysis.Diagnostics.DiagnosticAnalyzer>(
                new LinearityAnalyzer(), new GhostAnalyzer(), new PurityAnalyzer());
            var diagnostics = compilation.WithAnalyzers(analyzers).GetAnalyzerDiagnosticsAsync().GetAwaiter().GetResult();
            foreach (var d in diagnostics.Where(d => d.Severity == DiagnosticSeverity.Error && userTrees.Contains(d.Location.SourceTree)))
            {
                var vd = new VerificationDiagnostic(d.Id, true, d.GetMessage(), d.Location.GetLineSpan());
                var owner = declarations.FirstOrDefault(x => x.decl.SyntaxTree == d.Location.SourceTree && x.decl.FullSpan.Contains(d.Location.SourceSpan));
                if (owner.result != null) owner.result.Diagnostics.Add(vd);
                else result.AnalyzerErrors.Add(vd);
            }
        }

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

        public static IEnumerable<MetadataReference> FrameworkReferences()
        {
            var frameworkDir = Path.GetDirectoryName(typeof(object).Assembly.Location);
            var tpa = ((string)AppContext.GetData("TRUSTED_PLATFORM_ASSEMBLIES") ?? "").Split(Path.PathSeparator);
            foreach (var path in tpa.Where(p => Path.GetDirectoryName(p) == frameworkDir && p.EndsWith(".dll")))
                yield return MetadataReference.CreateFromFile(path);
        }
    }
}
