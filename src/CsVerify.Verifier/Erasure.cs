using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Text;

namespace CsVerify.Verifier
{
    /// <summary>One erased source file: where it came from, where it goes, its text.</summary>
    public sealed class ErasedFile
    {
        public string OriginalPath, OutputName, Text;
    }

    public sealed class ErasureResult
    {
        public readonly List<ErasedFile> Files = new List<ErasedFile>();
        /// <summary>Errors compiling the erased program: ghost code the program still depends on at run time.</summary>
        public readonly List<VerificationDiagnostic> Errors = new List<VerificationDiagnostic>();
        public bool Success => Errors.Count == 0;
    }

    /// <summary>
    /// Proof erasure, as ATS does it: removes everything static from the program, and checks that what is left
    /// still compiles. Normally <c>[Conditional]</c> removes specifications and lemma calls, and the JIT inlines the
    /// empty view functions; this pass removes the rest too, so the build carries no proofs at all:
    /// <list type="bullet">
    /// <item>specification statements, lemmas and [GhostFunction]s, and calls to them;</item>
    /// <item>proof types: <c>Ghost&lt;T&gt;</c>, <c>Seq&lt;T&gt;</c>, and data-less <c>[Linear]</c> structs (views such as
    /// <c>PointsTo&lt;T&gt;</c>, <c>ArrayView&lt;T&gt;</c>): their parameters, arguments, locals, fields and properties;
    /// a method returning one returns <c>void</c>;</item>
    /// <item>trusted view functions that only take and give proofs (<c>Mem.Split</c>, <c>Join</c>, ...), and calls to them.</item>
    /// </list>
    /// The Spec library goes through the same pass and becomes a small runtime (pointers and memory, no ghost types),
    /// compiled into the program instead of the CsVerify assembly. If the erased program does not compile, it still
    /// depends on a proof: that is an error, reported at the original source line (every erased file keeps the
    /// original's line numbers and starts with a <c>#line</c> directive naming it).
    /// </summary>
    public static class Erasure
    {
        public const string RuntimeFolder = "CsVerify.Runtime";

        public static ErasureResult Erase(IEnumerable<(string path, string text)> sources, IReadOnlyList<string> references, IEnumerable<string> defines)
        {
            // Bind with CSVERIFY_SPEC defined, like the verifier, so specification arguments have semantics too.
            var parse = new CSharpParseOptions(LanguageVersion.Latest, preprocessorSymbols: new[] { SpecSymbols.SpecSymbol }.Concat(defines));
            var userTrees = sources.Select(s => CSharpSyntaxTree.ParseText(s.text, parse, s.path)).ToList();
            var specTrees = Engine.SpecSources().Select(s => CSharpSyntaxTree.ParseText(s.text, parse, s.name)).ToList();
            var refs = ReferencesFor(references);
            var compilation = CSharpCompilation.Create("CsVerifyErasure", userTrees.Concat(specTrees), refs,
                new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary, allowUnsafe: true, nullableContextOptions: NullableContextOptions.Disable));

            var result = new ErasureResult();
            foreach (var d in compilation.GetDiagnostics().Where(d => d.Severity == DiagnosticSeverity.Error))
                result.Errors.Add(new VerificationDiagnostic(d.Id, true, d.GetMessage(), d.Location.GetLineSpan()));
            if (!result.Success) return result;

            int n = 0;
            foreach (var tree in userTrees)
                result.Files.Add(new ErasedFile
                {
                    OriginalPath = tree.FilePath,
                    OutputName = $"{n++:D3}_{Path.GetFileName(tree.FilePath)}",
                    Text = new FileEraser(tree, compilation.GetSemanticModel(tree), library: false).Run(),
                });
            foreach (var tree in specTrees)
                result.Files.Add(new ErasedFile
                {
                    OriginalPath = tree.FilePath,
                    OutputName = Path.Combine(RuntimeFolder, Path.GetFileName(tree.FilePath)),
                    Text = new FileEraser(tree, compilation.GetSemanticModel(tree), library: true).Run(),
                });

            // The check: the erased program compiles on its own, without CSVERIFY_SPEC and without the CsVerify assembly.
            var erasedParse = new CSharpParseOptions(LanguageVersion.Latest, preprocessorSymbols: defines);
            var erased = CSharpCompilation.Create("CsVerifyErased",
                result.Files.Select(f => CSharpSyntaxTree.ParseText(f.Text, erasedParse, f.OutputName)), refs,
                new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary, allowUnsafe: true, nullableContextOptions: NullableContextOptions.Disable));
            foreach (var d in erased.GetDiagnostics().Where(d => d.Severity == DiagnosticSeverity.Error))
                result.Errors.Add(new VerificationDiagnostic("CSV2001", true,
                    $"the erased program does not compile ({d.Id}: {d.GetMessage()}): run-time code depends on ghost code", d.Location.GetMappedLineSpan()));
            return result;
        }

        /// <summary>The project's references minus the CsVerify assembly itself (the runtime comes in as source).</summary>
        internal static List<MetadataReference> ReferencesFor(IReadOnlyList<string> references)
        {
            if (references.Count == 0) return Engine.FrameworkReferences().ToList();
            return references
                .Where(r => !IsCsVerifyAssembly(r))
                .Select(r => (MetadataReference)MetadataReference.CreateFromFile(r)).ToList();
        }

        public static bool IsCsVerifyAssembly(string path)
        {
            var name = Path.GetFileNameWithoutExtension(path);
            return name == "CsVerify" || name == "CsVerify.Spec";
        }

        // =============================================================================================== proof types

        /// <summary>
        /// A type that carries no run-time data and exists only for the proof: ghost values, ghost sequences, and
        /// [Linear] structs whose instance fields are all proof types (views and tokens).
        /// </summary>
        internal static bool IsProofType(ITypeSymbol type) => IsProofType(type, new HashSet<ITypeSymbol>(SymbolEqualityComparer.Default));

        private static bool IsProofType(ITypeSymbol type, HashSet<ITypeSymbol> seen)
        {
            if (!(type is INamedTypeSymbol named)) return false;
            if (SpecSymbols.IsGhostType(named) || SpecSymbols.IsSeqType(named)) return true;
            if (!named.IsValueType || !SpecSymbols.IsLinear(named)) return false;
            if (!seen.Add(named.OriginalDefinition)) return true;
            return named.GetMembers().OfType<IFieldSymbol>().Where(f => !f.IsStatic).All(f => IsProofType(f.Type, seen));
        }

        /// <summary>
        /// A method that disappears with its calls: a lemma, a [GhostFunction], a member of the Spec class or of
        /// <c>Ghost</c>, or a [Trusted] view function that only consumes and produces proofs.
        /// </summary>
        internal static bool IsErasedMethod(IMethodSymbol m)
        {
            if (m == null) return false;
            m = m.ReducedFrom ?? m.OriginalDefinition;
            if (SpecSymbols.IsLemma(m) || SpecSymbols.IsGhostFunction(m) || SpecSymbols.IsPredicate(m) || SpecSymbols.IsSpecClass(m.ContainingType) ||
                SpecSymbols.IsGhostOf(m) || SpecSymbols.IsSeqType(m.ContainingType))
                return true;
            if (!SpecSymbols.IsTrusted(m)) return false;
            bool proofResult = !m.ReturnsVoid && IsProofType(m.ReturnType);
            bool proofParams = m.Parameters.All(p => IsProofType(p.Type));
            return proofParams && (proofResult || (m.ReturnsVoid && m.Parameters.Length > 0));
        }

        // =============================================================================================== one file

        /// <summary>
        /// Erases one file by text edits on the original: deletions keep their newlines, so every remaining line stays
        /// where it was and diagnostics map back through a single <c>#line</c>.
        /// </summary>
        private sealed class FileEraser
        {
            private readonly SyntaxTree _tree;
            private readonly SemanticModel _model;
            private readonly bool _library;
            private readonly SourceText _text;
            private readonly List<(TextSpan span, string replacement)> _edits = new List<(TextSpan, string)>();

            public FileEraser(SyntaxTree tree, SemanticModel model, bool library)
            {
                _tree = tree;
                _model = model;
                _library = library;
                _text = tree.GetText();
            }

            public string Run()
            {
                var root = _tree.GetRoot();
                foreach (var node in root.DescendantNodes())
                {
                    switch (node)
                    {
                        case BaseTypeDeclarationSyntax type: TypeDeclaration(type); break;
                        case MemberDeclarationSyntax member: Member(member); break;
                        case LocalFunctionStatementSyntax lf: Signature(lf.ParameterList, lf.ReturnType, lf.Body, lf.ExpressionBody, lf.SemicolonToken); break;
                        case StatementSyntax stmt: Statement(stmt); break;
                        case ArgumentListSyntax args: Arguments(args); break;
                    }
                }
                return Apply();
            }

            private void TypeDeclaration(BaseTypeDeclarationSyntax type)
            {
                // a package keeps its run-time parts: its proof-typed positional parameters go
                if (type is RecordDeclarationSyntax record && record.ParameterList != null && _model.GetDeclaredSymbol(type) is INamedTypeSymbol rt && !IsProofType(rt))
                    RemoveFromList(record.ParameterList.Parameters, p => p.Type != null && _model.GetTypeInfo(p.Type).Type is ITypeSymbol pt && IsProofType(pt));
                if (!_library) return;
                // the runtime keeps no ghost types: a leftover use of one in the program is a compile error
                if (_model.GetDeclaredSymbol(type) is INamedTypeSymbol t &&
                    (IsProofType(t) || SpecSymbols.IsSpecClass(t) || SpecSymbols.IsSeqType(t) ||
                     SpecSymbols.IsCsVerifyType(t, "Ghost") || SpecSymbols.IsCsVerifyType(t, "GhostException")))
                    Delete(type.FullSpan);
            }

            private void Member(MemberDeclarationSyntax member)
            {
                switch (member)
                {
                    case BaseMethodDeclarationSyntax method:
                        var symbol = _model.GetDeclaredSymbol(method) as IMethodSymbol;
                        if (IsErasedMethod(symbol)) { Delete(method.FullSpan); return; }
                        Signature(method.ParameterList, (method as MethodDeclarationSyntax)?.ReturnType, method.Body, method.ExpressionBody,
                            (method as MethodDeclarationSyntax)?.SemicolonToken ?? default);
                        break;
                    case FieldDeclarationSyntax field:
                        if (_model.GetTypeInfo(field.Declaration.Type).Type is ITypeSymbol ft && IsProofType(ft)) Delete(field.FullSpan);
                        break;
                    case PropertyDeclarationSyntax property:
                        if (_model.GetTypeInfo(property.Type).Type is ITypeSymbol pt && IsProofType(pt)) Delete(property.FullSpan);
                        break;
                }
            }

            /// <summary>Proof parameters go; a proof result becomes void.</summary>
            private void Signature(ParameterListSyntax parameters, TypeSyntax returnType, BlockSyntax body, ArrowExpressionClauseSyntax arrow, SyntaxToken semicolon)
            {
                RemoveFromList(parameters.Parameters, p => p.Type != null && _model.GetTypeInfo(p.Type).Type is ITypeSymbol t && IsProofType(t));
                if (returnType == null || !(_model.GetTypeInfo(returnType).Type is ITypeSymbol rt) || !IsProofType(rt)) return;
                Replace(returnType.Span, "void");
                if (arrow != null && !IsKeptCall(arrow.Expression))
                {
                    Replace(arrow.Span, "{ }");
                    if (!semicolon.IsKind(SyntaxKind.None)) Replace(semicolon.Span, " ");
                }
            }

            private void Statement(StatementSyntax stmt)
            {
                switch (stmt)
                {
                    case ExpressionStatementSyntax es:
                        switch (es.Expression)
                        {
                            case InvocationExpressionSyntax inv when IsErasedMethod(_model.GetSymbolInfo(inv).Symbol as IMethodSymbol):
                                DeleteStatement(es);
                                break;
                            case AssignmentExpressionSyntax unpack when (unpack.Left is DeclarationExpressionSyntax || unpack.Left is TupleExpressionSyntax) &&
                                                                        SpecSymbols.IsLinearPackage(_model.GetTypeInfo(unpack.Right).Type):
                                Unpack(es, unpack);
                                break;
                            case AssignmentExpressionSyntax asg when IsProof(asg.Left):
                                // a view moved or produced: keep a call that does real work, drop the rest
                                if (IsKeptCall(asg.Right)) Delete(TextSpan.FromBounds(es.SpanStart, asg.Right.SpanStart));
                                else DeleteStatement(es);
                                break;
                        }
                        break;
                    case LocalDeclarationStatementSyntax decl when _model.GetTypeInfo(decl.Declaration.Type).Type is ITypeSymbol lt && IsProofType(lt):
                        var init = decl.Declaration.Variables.Count == 1 ? decl.Declaration.Variables[0].Initializer?.Value : null;
                        if (init != null && IsKeptCall(init)) Delete(TextSpan.FromBounds(decl.SpanStart, init.SpanStart));
                        else Delete(decl.Span);
                        break;
                    case ReturnStatementSyntax ret when ret.Expression != null && IsProof(ret.Expression):
                        if (IsKeptCall(ret.Expression))
                        {
                            Replace(ret.ReturnKeyword.Span, "{");
                            Replace(ret.SemicolonToken.Span, "; return; }");
                        }
                        else Replace(ret.Span, "return;");
                        break;
                }
            }

            /// <summary>
            /// <c>var (view, obj) = package;</c>: the proof parts are not there at run time. What is left is a smaller
            /// deconstruction, or for one part a read of its property (C# has no one-element deconstruction).
            /// </summary>
            private void Unpack(ExpressionStatementSyntax stmt, AssignmentExpressionSyntax unpack)
            {
                var type = (INamedTypeSymbol)_model.GetTypeInfo(unpack.Right).Type;
                bool declared = unpack.Left is DeclarationExpressionSyntax;
                var parts = declared
                    ? ((ParenthesizedVariableDesignationSyntax)((DeclarationExpressionSyntax)unpack.Left).Designation).Variables.Select(v => "var " + v.ToString()).ToList()
                    : ((TupleExpressionSyntax)unpack.Left).Arguments.Select(a => a.Expression.ToString()).ToList();
                var kept = new List<(string target, string property)>();
                for (int i = 0; i < parts.Count; i++)
                {
                    var p = DataTypes.PositionalProperty(type, i);
                    if (p != null && !IsProofType(p.Type)) kept.Add((parts[i], p.Name));
                }
                if (kept.Count == parts.Count) return;
                var right = unpack.Right.ToString();
                string text = kept.Count == 0 ? "_ = " + right + ";"
                    : kept.Count == 1 ? $"{kept[0].target} = ({right}).{kept[0].property};"
                    : $"({string.Join(", ", kept.Select(k => k.target))}) = {right};";
                Replace(stmt.Span, text);
            }

            private void Arguments(ArgumentListSyntax args)
            {
                if (!(args.Parent is ExpressionSyntax call) || !(_model.GetSymbolInfo(call).Symbol is IMethodSymbol m)) return;
                if (IsErasedMethod(m)) return; // the whole call goes
                RemoveFromList(args.Arguments, a =>
                {
                    var p = ParameterOf(a, m);
                    return p != null && IsProofType(p.Type);
                });
            }

            private static IParameterSymbol ParameterOf(ArgumentSyntax a, IMethodSymbol m)
            {
                if (a.NameColon != null) return m.Parameters.FirstOrDefault(p => p.Name == a.NameColon.Name.Identifier.ValueText);
                var list = (ArgumentListSyntax)a.Parent;
                int i = list.Arguments.IndexOf(a);
                return i < m.Parameters.Length ? m.Parameters[i] : m.Parameters.LastOrDefault(p => p.IsParams);
            }

            private bool IsProof(ExpressionSyntax e) => _model.GetTypeInfo(e).Type is ITypeSymbol t && IsProofType(t);

            /// <summary>A call that stays after erasure (it has run-time effects), even though its result was a proof.</summary>
            private bool IsKeptCall(ExpressionSyntax e) =>
                e is InvocationExpressionSyntax inv && _model.GetSymbolInfo(inv).Symbol is IMethodSymbol m && !IsErasedMethod(m);

            /// <summary>Removes the matching items of a comma-separated list, with the right commas.</summary>
            private void RemoveFromList<T>(SeparatedSyntaxList<T> list, Func<T, bool> remove) where T : SyntaxNode
            {
                var gone = list.Select(remove).ToArray();
                if (!gone.Any(g => g)) return;
                if (gone.All(g => g)) { Delete(TextSpan.FromBounds(list[0].SpanStart, list[list.Count - 1].Span.End)); return; }
                for (int i = 0; i < list.Count; i++)
                {
                    if (!gone[i]) continue;
                    bool keptAfter = gone.Skip(i + 1).Any(g => !g);
                    Delete(keptAfter
                        ? TextSpan.FromBounds(list[i].SpanStart, list[i + 1].SpanStart)                      // "x, "
                        : TextSpan.FromBounds(list.GetSeparator(i - 1).SpanStart, list[i].Span.End));        // ", x"
                }
            }

            private void Delete(TextSpan span) => _edits.Add((span, null));

            /// <summary>In a block a statement can go; as the body of an if/while/else it becomes an empty block.</summary>
            private void DeleteStatement(StatementSyntax stmt)
            {
                if (stmt.Parent is BlockSyntax || stmt.Parent is SwitchSectionSyntax) Delete(stmt.Span);
                else Replace(stmt.Span, "{ }");
            }
            private void Replace(TextSpan span, string text) => _edits.Add((span, text));

            private string Apply()
            {
                var text = _text.ToString();
                var sb = new StringBuilder();
                // the program's files map back to the originals; the runtime is generated code with nothing to map to
                if (_library) sb.Append("// <auto-generated/> CsVerify runtime: the Spec library with every proof erased\n");
                else sb.Append("#line 1 \"").Append(_tree.FilePath.Replace("\\", "\\\\")).Append("\"\n");
                int pos = 0;
                foreach (var (span, replacement) in _edits.OrderBy(e => e.span.Start).ThenByDescending(e => e.span.Length))
                {
                    if (span.Start < pos) continue; // inside a region already deleted or replaced
                    sb.Append(text, pos, span.Start - pos);
                    // a deletion keeps the line breaks it spans, so the lines after it keep their numbers
                    sb.Append(replacement ?? new string(text.Substring(span.Start, span.Length).Where(c => c == '\n').ToArray()));
                    pos = span.End;
                }
                sb.Append(text, pos, text.Length - pos);
                return sb.ToString();
            }
        }
    }
}
