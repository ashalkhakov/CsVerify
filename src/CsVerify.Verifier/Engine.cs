using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace CsVerify.Verifier
{
    public sealed class VerifierOptions
    {
        /// <summary>Check that integer arithmetic and narrowing conversions stay in range of their C# type.</summary>
        public bool CheckOverflow;
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
        public IEnumerable<VerificationDiagnostic> Diagnostics => CompilationErrors.Concat(Methods.SelectMany(m => m.Diagnostics));
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

        private Engine(Compilation compilation, VerifierOptions options)
        {
            _compilation = compilation;
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
                new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary, allowUnsafe: true, nullableContextOptions: NullableContextOptions.Disable));

            var result = new VerificationResult();
            foreach (var d in compilation.GetDiagnostics().Where(d => d.Severity == DiagnosticSeverity.Error))
                result.CompilationErrors.Add(new VerificationDiagnostic(d.Id, true, d.GetMessage(), d.Location.GetLineSpan()));
            if (result.CompilationErrors.Count > 0) return result;

            using var engine = new Engine(compilation, options);
            foreach (var tree in userTrees)
            {
                var model = compilation.GetSemanticModel(tree);
                foreach (var decl in tree.GetRoot().DescendantNodes().OfType<BaseMethodDeclarationSyntax>())
                {
                    if (decl.Body == null && decl.ExpressionBody == null) continue;
                    if (!(model.GetDeclaredSymbol(decl) is IMethodSymbol method) || SpecSymbols.IsTrusted(method)) continue;
                    if (SpecSymbols.IsGhostFunction(method)) continue; // a definition, used by unfolding; nothing to prove
                    var contract = engine.ContractOf(method);
                    var mr = new MethodResult { Name = method.ContainingType.Name + "." + method.Name };
                    result.Methods.Add(mr);
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
            return result;
        }

        private static IEnumerable<(string name, string text)> SpecSources()
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
            var frameworkDir = Path.GetDirectoryName(typeof(object).Assembly.Location);
            var tpa = ((string)AppContext.GetData("TRUSTED_PLATFORM_ASSEMBLIES") ?? "").Split(Path.PathSeparator);
            foreach (var path in tpa.Where(p => Path.GetDirectoryName(p) == frameworkDir && p.EndsWith(".dll")))
                yield return MetadataReference.CreateFromFile(path);
            foreach (var r in options.References)
                yield return MetadataReference.CreateFromFile(r);
        }
    }
}
