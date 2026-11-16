using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Runtime.Loader;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.Diagnostics;

namespace CsVerify.Verifier
{
    /// <summary>
    /// The project's source generators ([GeneratedRegex], [LoggerMessage], ...), run on the compilation as the compiler
    /// runs them: the analyzer assemblies MSBuild passes (@(Analyzer)), with the project's analyzer config (its
    /// build properties, its .editorconfig).
    /// </summary>
    internal static class Generators
    {
        /// <summary>The compilation with what the generators add, and the trees they added; warnings, of generators that didn't load or failed.</summary>
        public static (CSharpCompilation compilation, List<SyntaxTree> added) Run(CSharpCompilation compilation, CSharpParseOptions parse,
            IReadOnlyList<string> analyzers, IReadOnlyList<string> configs, List<string> warnings)
        {
            var generators = new List<ISourceGenerator>();
            foreach (var path in analyzers.Where(File.Exists))
            {
                var reference = new AnalyzerFileReference(Path.GetFullPath(path), Loader.Instance);
                reference.AnalyzerLoadFailed += (_, e) => warnings.Add($"source generator {Path.GetFileName(path)} not run: {e.Message}");
                generators.AddRange(reference.GetGenerators(LanguageNames.CSharp));
            }
            if (generators.Count == 0)
            {
                return (compilation, new List<SyntaxTree>());
            }
            var driver = CSharpGeneratorDriver.Create(generators, parseOptions: parse, optionsProvider: Options(configs.Where(File.Exists)));
            driver.RunGeneratorsAndUpdateCompilation(compilation, out var updated, out var diagnostics);
            foreach (var d in diagnostics.Where(d => d.Severity == DiagnosticSeverity.Error || d.Severity == DiagnosticSeverity.Warning && d.Id.StartsWith("CS8785")))
            {
                warnings.Add("source generator: " + d.GetMessage());
            }
            var before = compilation.SyntaxTrees.ToHashSet();
            return ((CSharpCompilation)updated, updated.SyntaxTrees.Where(t => !before.Contains(t)).ToList());
        }

        private static AnalyzerConfigOptionsProvider Options(IEnumerable<string> configs)
        {
            var set = AnalyzerConfigSet.Create(configs.Select(p => AnalyzerConfig.Parse(File.ReadAllText(p), Path.GetFullPath(p))).ToList());
            return new ConfigProvider(set);
        }

        private sealed class ConfigProvider : AnalyzerConfigOptionsProvider
        {
            private readonly AnalyzerConfigSet _set;

            public ConfigProvider(AnalyzerConfigSet set)
            {
                _set = set;
                GlobalOptions = new Config(set.GlobalConfigOptions.AnalyzerOptions);
            }

            public override AnalyzerConfigOptions GlobalOptions { get; }

            public override AnalyzerConfigOptions GetOptions(SyntaxTree tree) => For(tree.FilePath);

            public override AnalyzerConfigOptions GetOptions(AdditionalText text) => For(text.Path);

            private AnalyzerConfigOptions For(string path) =>
                string.IsNullOrEmpty(path) || !Path.IsPathRooted(path) ? GlobalOptions : new Config(_set.GetOptionsForSourcePath(path).AnalyzerOptions);
        }

        private sealed class Config : AnalyzerConfigOptions
        {
            private readonly ImmutableDictionary<string, string> _values;

            public Config(ImmutableDictionary<string, string> values) => _values = values;

            public override bool TryGetValue(string key, out string value) => _values.TryGetValue(key, out value);

            public override IEnumerable<string> Keys => _values.Keys;
        }

        /// <summary>
        /// Loads a generator and the assemblies next to it into a context of its own; Roslyn's and the framework's are
        /// the verifier's, so the generator's types are the ones the driver knows. Each assembly once per process.
        /// </summary>
        private sealed class Loader : AssemblyLoadContext, IAnalyzerAssemblyLoader
        {
            public static readonly Loader Instance = new Loader();

            private readonly HashSet<string> _directories = new HashSet<string>(StringComparer.OrdinalIgnoreCase);
            private readonly Dictionary<string, Assembly> _loaded = new Dictionary<string, Assembly>(StringComparer.OrdinalIgnoreCase);

            private Loader() : base("csverify-generators") { }

            public void AddDependencyLocation(string fullPath)
            {
                lock (_directories) _directories.Add(Path.GetDirectoryName(fullPath));
            }

            public Assembly LoadFromPath(string fullPath)
            {
                lock (_loaded)
                {
                    AddDependencyLocation(fullPath);
                    return _loaded.TryGetValue(fullPath, out var a) ? a : _loaded[fullPath] = LoadFromAssemblyPath(fullPath);
                }
            }

            protected override Assembly Load(AssemblyName name)
            {
                // (Roslyn and the framework: the verifier's)
                if (Default.Assemblies.Any(a => a.GetName().Name == name.Name) || name.Name.StartsWith("Microsoft.CodeAnalysis") || name.Name.StartsWith("System."))
                {
                    return null;
                }
                string[] directories;
                lock (_directories) directories = _directories.ToArray();
                var file = directories.Select(d => Path.Combine(d, name.Name + ".dll")).FirstOrDefault(File.Exists);
                return file == null ? null : LoadFromPath(file);
            }
        }
    }
}
