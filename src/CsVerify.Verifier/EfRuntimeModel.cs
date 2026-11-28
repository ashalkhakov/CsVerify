using System;
using System.Collections;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Runtime.Loader;
using Microsoft.CodeAnalysis;

namespace CsVerify.Verifier
{
    /// <summary>
    /// EF's own model of the program's contexts: the program is emitted and loaded apart from the verifier, with the
    /// EF Core it references; each context is made as EF's design-time tools make one, and its design-time model is
    /// read by reflection. That is the model EF runs with, whatever way the program configures it (conventions,
    /// attributes, configuration classes, loops over the entity types, constants, a provider's conventions). Where a
    /// context can't be made, Failure says why, and the verifier reads the configuration's source instead.
    /// </summary>
    internal sealed class EfRuntimeModel
    {
        internal sealed class Property
        {
            public string Name, Column, ClrType;
            public bool Shadow, Nullable, Converted, Token, RowVersion;
        }

        internal sealed class Index
        {
            public List<string> Properties;
            /// <summary>The filter's SQL, or null.</summary>
            public string Filter;
            /// <summary>
            /// The filter's conjuncts [C] &lt;&gt; v, each as C's property and the value of the property's type the model
            /// stores as v: "none" (its converter reads v as no value: it throws), "null", "default" (a value type's),
            /// "number:n" (an integer's, an enum member's), "string:" (the empty string).
            /// </summary>
            public List<(string Property, string Value)> Excluded = new List<(string, string)>();
        }

        internal sealed class ForeignKey
        {
            public string Dependent, Principal;
            public List<string> Properties, PrincipalKey;
            public bool Unique, Required;
            /// <summary>The navigations of the two ends, where they have one.</summary>
            public string ToPrincipal, ToDependent;
        }

        internal sealed class Entity
        {
            /// <summary>The CLR type's full name, as metadata has it.</summary>
            public string Type;
            public List<string> Key;
            public List<List<string>> AlternateKeys = new List<List<string>>();
            public List<Index> UniqueIndexes = new List<Index>();
            public List<Property> Properties = new List<Property>();
            public List<string> AutoIncluded = new List<string>();
            /// <summary>The bool columns the entity's query filter keeps only where false (a soft delete's flag).</summary>
            public List<string> FilteredFalse = new List<string>();
        }

        public readonly Dictionary<string, Entity> Entities = new Dictionary<string, Entity>();
        /// <summary>The types EF's model has as owned ones (their owners' columns).</summary>
        public readonly HashSet<string> Owned = new HashSet<string>();
        public readonly List<ForeignKey> ForeignKeys = new List<ForeignKey>();
        /// <summary>The contexts read.</summary>
        public readonly List<string> Contexts = new List<string>();
        /// <summary>Why a context's model couldn't be read: the context and the reason.</summary>
        public readonly List<(string context, string why)> Failures = new List<(string, string)>();
        /// <summary>A service a context asked its host for where its model was built, which a stand-in answered: the context and the service.</summary>
        public readonly List<(string context, string service)> StoodIn = new List<(string, string)>();

        /// <summary>The models of the contexts given, of the compilation as emitted.</summary>
        public static EfRuntimeModel Read(Compilation compilation, IEnumerable<INamedTypeSymbol> contexts, IEnumerable<string> providersNamed, IReadOnlyList<string> nativeLibraries)
        {
            var model = new EfRuntimeModel();
            var wanted = contexts.ToList();
            if (wanted.Count == 0)
            {
                return model;
            }
            // (a context with no OnConfiguring of its own: in the copy emitted here, one that configures what the context
            // was made without, a provider and its host's services; the program's own isn't changed)
            var member = (Microsoft.CodeAnalysis.CSharp.Syntax.MemberDeclarationSyntax)Microsoft.CodeAnalysis.CSharp.SyntaxFactory.ParseMemberDeclaration(
                "protected override void OnConfiguring(global::Microsoft.EntityFrameworkCore.DbContextOptionsBuilder b) { base.OnConfiguring(b); global::__CsVerifyEf.Configure?.Invoke(b); }");
            var declarations = wanted.Where(c => !c.GetMembers("OnConfiguring").Any())
                .Select(c => c.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax()).OfType<Microsoft.CodeAnalysis.CSharp.Syntax.ClassDeclarationSyntax>().ToList();
            // (the copy of a compilation, the program's or a project's it references, with its contexts' hooks: the
            // compilation itself where it declares none of them, or where the copy doesn't compile)
            Compilation Hooked(Compilation c)
            {
                var its = declarations.Where(d => c.ContainsSyntaxTree(d.SyntaxTree)).ToList();
                if (its.Count == 0 || !(c.SyntaxTrees.FirstOrDefault() is SyntaxTree first))
                {
                    return c;
                }
                var copy = c;
                var changed = new List<SyntaxTree>();
                foreach (var group in its.GroupBy(d => d.SyntaxTree))
                {
                    var tree = group.Key;
                    changed.Add(tree.WithRootAndOptions(tree.GetRoot().ReplaceNodes(group, (d, _) => d.AddMembers(member)), tree.Options));
                    copy = copy.ReplaceSyntaxTree(tree, changed.Last());
                }
                changed.Add(first.WithRootAndOptions(
                    Microsoft.CodeAnalysis.CSharp.SyntaxFactory.ParseCompilationUnit("internal static class __CsVerifyEf { public static global::System.Action<object> Configure; }"), first.Options).WithFilePath("__CsVerifyEf.cs"));
                copy = copy.AddSyntaxTrees(changed.Last());
                return changed.Any(t => copy.GetSemanticModel(t).GetDiagnostics().Any(d => d.Severity == DiagnosticSeverity.Error)) ? c : copy;
            }
            foreach (var project in compilation.References.OfType<CompilationReference>().ToList())
            {
                var copy = Hooked(project.Compilation);
                if (copy != project.Compilation)
                {
                    compilation = compilation.ReplaceReference(project, copy.ToMetadataReference(project.Properties.Aliases, project.Properties.EmbedInteropTypes));
                }
            }
            compilation = Hooked(compilation);
            var providers = providersNamed.ToList();
            var load = new Loader(compilation, nativeLibraries);
            load.Configure = b =>
            {
                if (!(bool)Get(b, "IsConfigured"))
                {
                    load.Provider(b, providers);
                }
                load.UseHost(b);
            };
            try
            {
                Assembly program;
                try
                {
                    program = load.Program();
                }
                catch (Exception e)
                {
                    model.Failures.AddRange(wanted.Select(c => (EfModel.MetadataName(c), "the program couldn't be loaded: " + Inner(e).Message.Split('\n')[0] + NotLoaded(load))));
                    return model;
                }
                var trace = Environment.GetEnvironmentVariable("CSVERIFY_EF_MODEL_TRACE") != null;
                foreach (var name in wanted.Select(EfModel.MetadataName))
                {
                    // (as EF's tools make it: by the program's factory, with the program's provider. Where that can't build
                    // the model (a factory that reads a configuration there is none of here, a provider that needs what this
                    // machine doesn't have): by its constructor, and then with the verifier's own provider)
                    Exception failure = null;
                    load.UsedFactory = load.UsedNeutral = false;
                    foreach (var (factory, neutralOnly) in new[] { (true, false), (false, false), (false, true) })
                    {
                        if (!factory && (neutralOnly ? load.UsedNeutral : !load.UsedFactory))
                        {
                            continue;
                        }
                        load.NoFactory = !factory;
                        load.NeutralOnly = neutralOnly;
                        var stoodIn = load.Host.StoodIn.Count;
                        try
                        {
                            var type = program.GetType(name) ?? load.Find(name);
                            var context = Make(type ?? throw new InvalidOperationException("its type isn't found"), load, providers);
                            try
                            {
                                // (EF's model, built before any of it is read: a model that can't be built leaves nothing read)
                                var built = DesignTimeModel(context);
                                model.ReadModel(built, load);
                                model.Contexts.Add(name);
                                model.StoodIn.AddRange(load.Host.StoodIn.Skip(stoodIn).Distinct().Select(service => (name, service)));
                                if (trace)
                                {
                                    Console.Error.WriteLine($"[ef-model] {name}: built {(load.UsedFactory ? "by the program's factory" : load.UsedNeutral ? "with the verifier's own provider (of no database)" : "with the program's provider")}");
                                }
                            }
                            finally
                            {
                                (context as IDisposable)?.Dispose();
                            }
                            failure = null;
                            break;
                        }
                        catch (Exception e)
                        {
                            if (trace)
                            {
                                Console.Error.WriteLine(Inner(e));
                            }
                            failure ??= Inner(e);
                        }
                    }
                    load.NoFactory = load.NeutralOnly = false;
                    if (failure != null)
                    {
                        model.Failures.Add((name, failure.Message.Split('\n')[0] + NotLoaded(load)));
                    }
                }
            }
            finally
            {
                if (Environment.GetEnvironmentVariable("CSVERIFY_EF_MODEL_TRACE") != null)
                {
                    foreach (var (reference, why) in load.Shared.Failed)
                    {
                        Console.Error.WriteLine($"[ef-model] not loaded: {reference}: {why}");
                    }
                }
                load.Unload();
            }
            return model;
        }

        /// <summary>What a failure owes to references that couldn't be loaded: how many, and the first, with why.</summary>
        private static string NotLoaded(Loader load) =>
            load.Shared.Failed.Count == 0 ? ""
            : $"; {load.Shared.Failed.Count} of the program's references couldn't be loaded, the first '{load.Shared.Failed.First().Key}': {load.Shared.Failed.First().Value}";

        private static Exception Inner(Exception e)
        {
            while (e is TargetInvocationException or TypeInitializationException && e.InnerException != null)
            {
                e = e.InnerException;
            }
            return e;
        }

        // ------------------------------------------------------------------ loading

        /// <summary>
        /// What the program references (EF Core, a provider, the libraries they need), loaded once for a set of references
        /// and kept: verifying again with the same ones reuses it.
        /// </summary>
        private sealed class References : AssemblyLoadContext
        {
            private static readonly Dictionary<string, References> Cache = new Dictionary<string, References>();
            private readonly Dictionary<string, string> _paths = new Dictionary<string, string>(StringComparer.OrdinalIgnoreCase);
            private List<MethodInfo> _providers;

            public static References For(IEnumerable<string> paths, IReadOnlyList<string> nativeLibraries)
            {
                var all = paths.Select(Path.GetFullPath).Distinct().OrderBy(p => p, StringComparer.Ordinal).ToList();
                var natives = nativeLibraries.Where(File.Exists).Select(Path.GetFullPath).Distinct().OrderBy(p => p, StringComparer.Ordinal).ToList();
                var key = string.Join("|", all.Select(p => p + "@" + File.GetLastWriteTimeUtc(p).Ticks).Concat(natives));
                lock (Cache)
                {
                    return Cache.TryGetValue(key, out var found) ? found : Cache[key] = new References(all, natives);
                }
            }

            private readonly List<string> _natives;

            /// <summary>
            /// A native library a reference loads (a provider's, SQLite's e_sqlite3): the one the program's packages
            /// bring for this machine, among those the build names (--native) or, without them, in the packages beside
            /// the references' (a package's runtimes/RID/native folder).
            /// </summary>
            protected override IntPtr LoadUnmanagedDll(string name)
            {
                var files = new[] { name, name + ".dll", "lib" + name + ".dylib", name + ".dylib", "lib" + name + ".so", name + ".so" };
                var rid = System.Runtime.InteropServices.RuntimeInformation.RuntimeIdentifier;
                // (this machine's, then its system's whatever the processor, then any of its kind)
                var rids = new List<string> { rid };
                if (rid.LastIndexOf('-') is int dash && dash > 0)
                {
                    rids.Add(rid.Substring(0, dash));
                }
                rids.Add(OperatingSystem.IsWindows() ? "win" : "unix");
                var candidates = _natives.ToList();
                if (candidates.Count == 0)
                {
                    // (an application's output folder: runtimes/RID/native beside the references)
                    foreach (var dir in _paths.Values.Select(Path.GetDirectoryName).Where(d => d != null).Distinct().ToList())
                    {
                        var runtimes = Path.Combine(dir, "runtimes");
                        if (Directory.Exists(runtimes))
                        {
                            candidates.AddRange(Directory.EnumerateFiles(runtimes, "*", SearchOption.AllDirectories).Where(f => files.Contains(Path.GetFileName(f), StringComparer.OrdinalIgnoreCase)));
                        }
                    }
                    // (a package folder is root/id/version: the others of the same root)
                    foreach (var root in _paths.Values.Select(PackagesRoot).Where(r => r != null).Distinct().ToList())
                    {
                        foreach (var package in Directory.EnumerateDirectories(root))
                        {
                            foreach (var version in Directory.EnumerateDirectories(package))
                            {
                                var runtimes = Path.Combine(version, "runtimes");
                                if (Directory.Exists(runtimes))
                                {
                                    candidates.AddRange(Directory.EnumerateFiles(runtimes, "*", SearchOption.AllDirectories).Where(f => files.Contains(Path.GetFileName(f), StringComparer.OrdinalIgnoreCase)));
                                }
                            }
                        }
                    }
                }
                foreach (var r in rids)
                {
                    var sep = Path.DirectorySeparatorChar;
                    var found = candidates.FirstOrDefault(f => files.Contains(Path.GetFileName(f), StringComparer.OrdinalIgnoreCase) &&
                                                               f.Contains(sep + "runtimes" + sep + r + sep + "native" + sep, StringComparison.OrdinalIgnoreCase));
                    if (found != null && System.Runtime.InteropServices.NativeLibrary.TryLoad(found, out var handle))
                    {
                        return handle;
                    }
                }
                return IntPtr.Zero;
            }

            internal static string PackagesRoot(string reference)
            {
                // (root/id/version/lib/tfm/x.dll)
                var tfm = Path.GetDirectoryName(reference);
                var lib = Path.GetDirectoryName(tfm);
                var version = Path.GetDirectoryName(lib);
                var id = Path.GetDirectoryName(version);
                var root = Path.GetDirectoryName(id);
                return root != null && Path.GetFileName(lib) is "lib" or "ref" && Directory.Exists(root) ? root : null;
            }

            private References(List<string> paths, List<string> natives) : base("csverify-ef-references")
            {
                _natives = natives;
                // (the runtime's own assemblies are the verifier's: one loaded again here would be other types, a second
                // System.Linq.Expressions say, which EF's model then couldn't be read through)
                var runtime = Path.GetDirectoryName(typeof(object).Assembly.Location) ?? "";
                foreach (var path in paths)
                {
                    if (File.Exists(Path.Combine(runtime, Path.GetFileName(path))))
                    {
                        continue;
                    }
                    // (a reference assembly, a targeting pack's or a package's ref folder's, has no code: the assembly
                    // that runs in its place)
                    var name = Path.GetFileNameWithoutExtension(path);
                    if (Implementation(path) is string runs)
                    {
                        _paths.TryAdd(name, runs);
                    }
                    else
                    {
                        _failed.TryAdd(name, "a reference assembly whose implementation isn't found (" + path + ")");
                    }
                }
                // (a provider beside EF Core that the program doesn't reference itself, as an application's output folder has it)
                if (_paths.TryGetValue("Microsoft.EntityFrameworkCore", out var ef) && Path.GetDirectoryName(ef) is string dir)
                {
                    foreach (var beside in Directory.EnumerateFiles(dir, "*.EntityFrameworkCore.*.dll"))
                    {
                        _paths.TryAdd(Path.GetFileNameWithoutExtension(beside), beside);
                    }
                }
            }

            private readonly Dictionary<string, string> _failed = new Dictionary<string, string>(StringComparer.OrdinalIgnoreCase);

            /// <summary>The references that couldn't be loaded, each with why: said where a model can't be built for it.</summary>
            public IReadOnlyDictionary<string, string> Failed => _failed;

            public void AddFailure(string name, Exception e) => _failed.TryAdd(name, Inner(e).GetType().Name + ": " + Inner(e).Message.Split('\n')[0]);

            public IEnumerable<Assembly> All()
            {
                foreach (var a in _paths.Keys.ToList())
                {
                    Assembly loaded = null;
                    try
                    {
                        loaded = LoadFromAssemblyName(new AssemblyName(a));
                    }
                    catch (Exception e)
                    {
                        AddFailure(a, e);
                    }
                    if (loaded != null)
                    {
                        yield return loaded;
                    }
                }
            }

            protected override Assembly Load(AssemblyName name)
            {
                if (name.Name == null)
                {
                    return null;
                }
                if (!_paths.TryGetValue(name.Name, out var path))
                {
                    // (what a reference needs that the program doesn't name: beside it)
                    path = _paths.Values.Select(p => Path.Combine(Path.GetDirectoryName(p) ?? "", name.Name + ".dll")).FirstOrDefault(File.Exists);
                    if (path == null)
                    {
                        return null;
                    }
                }
                // (what is beside a reference may be a reference assembly too)
                return Implementation(path) is string runs ? LoadFromAssemblyPath(runs) : null;
            }

            /// <summary>Does the assembly say it is a reference assembly (ReferenceAssemblyAttribute): metadata without code?</summary>
            private static bool IsReferenceAssembly(string path)
            {
                try
                {
                    using var stream = File.OpenRead(path);
                    using var pe = new System.Reflection.PortableExecutable.PEReader(stream);
                    if (!pe.HasMetadata)
                    {
                        return false;
                    }
                    var md = System.Reflection.Metadata.PEReaderExtensions.GetMetadataReader(pe);
                    foreach (var handle in md.GetAssemblyDefinition().GetCustomAttributes())
                    {
                        var ctor = md.GetCustomAttribute(handle).Constructor;
                        if (ctor.Kind == System.Reflection.Metadata.HandleKind.MemberReference &&
                            md.GetMemberReference((System.Reflection.Metadata.MemberReferenceHandle)ctor).Parent is { Kind: System.Reflection.Metadata.HandleKind.TypeReference } parent &&
                            md.GetString(md.GetTypeReference((System.Reflection.Metadata.TypeReferenceHandle)parent).Name) == "ReferenceAssemblyAttribute")
                        {
                            return true;
                        }
                    }
                    return false;
                }
                catch (Exception)
                {
                    return false;
                }
            }

            /// <summary>
            /// The assembly that runs for a reference: itself, unless it is a reference assembly. Then, for a targeting
            /// pack's (packs/Name.Ref/version/ref/tfm/x.dll), the shared framework's of that name (shared/Name/version/x.dll:
            /// the pack's version, else the latest of its major version), in the pack's dotnet or the running one; for a
            /// package's ref folder, its lib folder's; else any shared framework's of the running dotnet. Null where none is.
            /// </summary>
            private static string Implementation(string path)
            {
                if (!IsReferenceAssembly(path))
                {
                    return path;
                }
                var file = Path.GetFileName(path);
                var running = Path.GetDirectoryName(Path.GetDirectoryName(Path.GetDirectoryName(Path.GetDirectoryName(typeof(object).Assembly.Location))));
                var parts = path.Split(Path.DirectorySeparatorChar, Path.AltDirectorySeparatorChar);
                int packs = Array.FindLastIndex(parts, x => string.Equals(x, "packs", StringComparison.OrdinalIgnoreCase));
                if (packs >= 0 && packs + 2 < parts.Length && parts[packs + 1].EndsWith(".Ref", StringComparison.OrdinalIgnoreCase))
                {
                    var framework = parts[packs + 1].Substring(0, parts[packs + 1].Length - ".Ref".Length);
                    var version = parts[packs + 2];
                    var root = string.Join(Path.DirectorySeparatorChar.ToString(), parts.Take(packs));
                    foreach (var dotnet in new[] { root, running }.Where(d => !string.IsNullOrEmpty(d)).Distinct())
                    {
                        var shared = Path.Combine(dotnet, "shared", framework);
                        if (!Directory.Exists(shared))
                        {
                            continue;
                        }
                        var major = version.Split('.')[0];
                        var versions = Directory.GetDirectories(shared).Select(Path.GetFileName).ToList();
                        foreach (var v in new[] { version }.Concat(versions.Where(v => v.Split('.')[0] == major).OrderByDescending(ParsedVersion)))
                        {
                            var candidate = Path.Combine(shared, v, file);
                            if (File.Exists(candidate))
                            {
                                return candidate;
                            }
                        }
                    }
                }
                var sep = Path.DirectorySeparatorChar;
                var inRef = path.LastIndexOf(sep + "ref" + sep, StringComparison.OrdinalIgnoreCase);
                if (inRef >= 0)
                {
                    var lib = path.Substring(0, inRef) + sep + "lib" + sep + path.Substring(inRef + 5);
                    if (File.Exists(lib) && !IsReferenceAssembly(lib))
                    {
                        return lib;
                    }
                }
                if (running != null && Directory.Exists(Path.Combine(running, "shared")))
                {
                    foreach (var framework in Directory.GetDirectories(Path.Combine(running, "shared")))
                    {
                        foreach (var version in Directory.GetDirectories(framework).OrderByDescending(v => ParsedVersion(Path.GetFileName(v))))
                        {
                            var candidate = Path.Combine(version, file);
                            if (File.Exists(candidate))
                            {
                                return candidate;
                            }
                        }
                    }
                }
                return null;
            }

            private static Version ParsedVersion(string v) => Version.TryParse(v.Split('-')[0], out var parsed) ? parsed : new Version(0, 0);

            /// <summary>
            /// The provider's options: Use...(builder, connection string) of a provider among the references, the one the
            /// program names first, a database's before the in-memory one. A provider only builds the model here: it is
            /// never connected to.
            /// </summary>
            public bool Provider(object builder, List<string> providersNamed)
            {
                if (_providers == null)
                {
                    var found = new List<MethodInfo>();
                    foreach (var a in All())
                    {
                        foreach (var t in Types(a).Where(x => x.IsPublic).Where(t => t.IsAbstract && t.IsSealed && (t.Name.EndsWith("DbContextOptionsBuilderExtensions") || t.Name.EndsWith("DbContextOptionsExtensions"))))
                        {
                            found.AddRange(t.GetMethods(BindingFlags.Public | BindingFlags.Static).Where(m =>
                                m.Name.StartsWith("Use") && !m.IsGenericMethodDefinition && m.GetParameters() is { Length: >= 2 } ps &&
                                ps[0].ParameterType.FullName == "Microsoft.EntityFrameworkCore.DbContextOptionsBuilder" && ps[1].ParameterType == typeof(string) &&
                                ps.Skip(2).All(p => p.IsOptional || !p.ParameterType.IsValueType)));
                        }
                    }
                    _providers = found;
                }
                int Rank(MethodInfo m) => (providersNamed.Contains(m.Name) ? 0 : 2) + (m.Name is "UseInMemoryDatabase" or "UseSqlite" ? 1 : 0);
                foreach (var use in _providers.OrderBy(Rank).ThenBy(m => m.GetParameters().Length))
                {
                    try
                    {
                        use.Invoke(null, use.GetParameters().Select((p, i) => i == 0 ? builder : i == 1 ? (object)(use.Name == "UseInMemoryDatabase" ? "csverify" : "Data Source=csverify") : null).ToArray());
                        return true;
                    }
                    catch (Exception)
                    {
                    }
                }
                return false;
            }
        }

        /// <summary>The program and the projects it references, emitted and loaded for this reading alone.</summary>
        private sealed class Loader : AssemblyLoadContext
        {
            private readonly Compilation _compilation;
            private readonly Dictionary<string, Compilation> _projects = new Dictionary<string, Compilation>(StringComparer.OrdinalIgnoreCase);
            private readonly Dictionary<string, Assembly> _emitted = new Dictionary<string, Assembly>(StringComparer.OrdinalIgnoreCase);
            public readonly References Shared;
            private readonly List<string> _paths = new List<string>();
            private MethodInfo _neutral;
            /// <summary>Why the verifier's own provider can't be used; null while it can, or wasn't asked for.</summary>
            public string NoNeutral;
            /// <summary>Another try, where the first couldn't build the model: not by the program's factory; only with the verifier's own provider.</summary>
            public bool NoFactory, NeutralOnly;
            /// <summary>How the last context was made: by the program's factory; with the verifier's own provider.</summary>
            public bool UsedFactory, UsedNeutral;
            /// <summary>The services a context asks its host for.</summary>
            public readonly EfHostServices Host;
            /// <summary>What a hooked context's OnConfiguring does, in each assembly emitted here that has one.</summary>
            public Action<object> Configure;
            private HashSet<string> _efs;

            public Loader(Compilation compilation, IReadOnlyList<string> nativeLibraries) : base("csverify-ef-model", isCollectible: true)
            {
                _compilation = compilation;
                Collect(compilation, _paths);
                // (a program that references EF Core alone: the verifier's own provider is a relational one, so EF's
                // relational package of the same version, where the packages folder EF Core came from has it)
                bool Named(string path, string name) => Path.GetFileName(path).Equals(name + ".dll", StringComparison.OrdinalIgnoreCase);
                if (!_paths.Any(p => Named(p, "Microsoft.EntityFrameworkCore.Relational")) && _paths.FirstOrDefault(p => Named(p, "Microsoft.EntityFrameworkCore")) is string core)
                {
                    // (root/microsoft.entityframeworkcore/version/lib/tfm/Microsoft.EntityFrameworkCore.dll)
                    var tfm = Path.GetDirectoryName(core);
                    var version = Path.GetDirectoryName(Path.GetDirectoryName(tfm));
                    var root = Path.GetDirectoryName(Path.GetDirectoryName(version));
                    if (root != null && Path.Combine(root, "microsoft.entityframeworkcore.relational", Path.GetFileName(version), "lib", Path.GetFileName(tfm),
                            "Microsoft.EntityFrameworkCore.Relational.dll") is var relational && File.Exists(relational))
                    {
                        _paths.Add(relational);
                    }
                }
                Shared = References.For(_paths, nativeLibraries);
                Host = new EfHostServices(MayBeAHosts, ProgramAssemblies, StandIn);
            }

            /// <summary>
            /// A service that may be a host's: not the runtime's, not EF's, and not of what EF builds on (its logging, its
            /// cache, dependency injection), which EF asks the host for itself and does without.
            /// </summary>
            private bool MayBeAHosts(Type service) => MayBeAHosts((service.IsGenericType ? service.GetGenericTypeDefinition() : service).Assembly);

            private bool MayBeAHosts(Assembly assembly)
            {
                var name = assembly.GetName().Name ?? "";
                if (assembly == typeof(object).Assembly || File.Exists(Path.Combine(Path.GetDirectoryName(typeof(object).Assembly.Location) ?? "", name + ".dll")))
                {
                    return false;
                }
                if (_efs == null)
                {
                    _efs = new HashSet<string>(StringComparer.OrdinalIgnoreCase);
                    var next = new Queue<Assembly>(Shared.All().Where(a => (a.GetName().Name ?? "").StartsWith("Microsoft.EntityFrameworkCore", StringComparison.OrdinalIgnoreCase)));
                    while (next.Count > 0)
                    {
                        var a = next.Dequeue();
                        if (!_efs.Add(a.GetName().Name ?? ""))
                        {
                            continue;
                        }
                        foreach (var r in a.GetReferencedAssemblies())
                        {
                            try
                            {
                                next.Enqueue(Shared.LoadFromAssemblyName(r));
                            }
                            catch (Exception)
                            {
                                _efs.Add(r.Name ?? "");
                            }
                        }
                    }
                }
                return !_efs.Contains(name);
            }

            /// <summary>The program's assemblies: what is emitted here, and the references that are no package's and no framework's (a project's output).</summary>
            private IEnumerable<Assembly> ProgramAssemblies()
            {
                var all = new List<Assembly>();
                foreach (var c in new[] { _compilation }.Concat(_projects.Values))
                {
                    try
                    {
                        all.Add(Emitted(c));
                    }
                    catch (Exception)
                    {
                    }
                }
                var dotnet = Path.GetFullPath(Path.Combine(Path.GetDirectoryName(typeof(object).Assembly.Location) ?? "", "..", "..", ".."));
                var outputs = _paths.Where(p => References.PackagesRoot(p) == null && !p.StartsWith(dotnet, StringComparison.OrdinalIgnoreCase))
                    .Select(Path.GetFileNameWithoutExtension).ToHashSet(StringComparer.OrdinalIgnoreCase);
                all.AddRange(Shared.All().Where(a => outputs.Contains(a.GetName().Name ?? "") && MayBeAHosts(a)));
                return all;
            }

            /// <summary>The host's services, of a builder that names none: DbContextOptionsBuilder.UseApplicationServiceProvider.</summary>
            public void UseHost(object builder)
            {
                try
                {
                    var core = Many(Get(Get(builder, "Options"), "Extensions")).FirstOrDefault(e => e.GetType().Name == "CoreOptionsExtension");
                    if (core != null && Get(core, "ApplicationServiceProvider") != null)
                    {
                        return;
                    }
                    var use = builder.GetType().GetMethods(BindingFlags.Public | BindingFlags.Instance)
                        .FirstOrDefault(m => m.Name == "UseApplicationServiceProvider" && m.GetParameters() is { Length: 1 } ps && ps[0].ParameterType == typeof(IServiceProvider));
                    use?.Invoke(builder, new object[] { Host });
                }
                catch (Exception e)
                {
                    if (Environment.GetEnvironmentVariable("CSVERIFY_EF_MODEL_TRACE") != null)
                    {
                        Console.Error.WriteLine("[ef-model] the host's services couldn't be named: " + Inner(e).Message.Split('\n')[0]);
                    }
                }
            }

            /// <summary>
            /// A provider's options: those of a provider among the program's references, as EF's tools would have it; where
            /// there is none (a library, whose host picks the database), the verifier's own, of no database.
            /// </summary>
            public bool Provider(object builder, List<string> providersNamed)
            {
                UsedNeutral = false;
                if (!NeutralOnly && Shared.Provider(builder, providersNamed))
                {
                    return true;
                }
                return UsedNeutral = Neutral(builder);
            }

            private Type _standIn;

            /// <summary>A stand-in's base, compiled into this context.</summary>
            private Type StandIn()
            {
                if (_standIn == null)
                {
                    var references = _compilation.References.Concat(_paths.Distinct(StringComparer.OrdinalIgnoreCase).Select(p => (MetadataReference)MetadataReference.CreateFromFile(p)));
                    var made = Microsoft.CodeAnalysis.CSharp.CSharpCompilation.Create("CsVerify.EfStandIn",
                        new[] { Microsoft.CodeAnalysis.CSharp.CSharpSyntaxTree.ParseText(EfNeutralProvider.StandInSource) }, references,
                        new Microsoft.CodeAnalysis.CSharp.CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary));
                    using var image = new MemoryStream();
                    var result = made.Emit(image);
                    if (!result.Success)
                    {
                        throw new InvalidOperationException(result.Diagnostics.First(d => d.Severity == DiagnosticSeverity.Error).GetMessage());
                    }
                    image.Position = 0;
                    _standIn = LoadFromStream(image).GetType(EfNeutralProvider.StandIn);
                }
                return _standIn;
            }

            /// <summary>The verifier's own provider (EfNeutralProvider), compiled against the program's EF Core.</summary>
            private bool Neutral(object builder)
            {
                if (_neutral == null && NoNeutral == null)
                {
                    try
                    {
                        var references = _paths.Distinct(StringComparer.OrdinalIgnoreCase).Select(p => (MetadataReference)MetadataReference.CreateFromFile(p)).ToList();
                        var probe = Microsoft.CodeAnalysis.CSharp.CSharpCompilation.Create("probe", references: references);
                        if (probe.GetTypeByMetadataName("Microsoft.EntityFrameworkCore.Infrastructure.RelationalOptionsExtension") == null)
                        {
                            NoNeutral = "the verifier's own needs Microsoft.EntityFrameworkCore.Relational, which the program doesn't reference and the packages folder doesn't have in EF Core's version";
                            return false;
                        }
                        var symbols = probe.GetTypeByMetadataName("Microsoft.EntityFrameworkCore.Storage.JsonTypeMapping") != null ? new[] { "EF7" } : new string[0];
                        var tree = Microsoft.CodeAnalysis.CSharp.CSharpSyntaxTree.ParseText(EfNeutralProvider.Source,
                            new Microsoft.CodeAnalysis.CSharp.CSharpParseOptions(Microsoft.CodeAnalysis.CSharp.LanguageVersion.Latest, preprocessorSymbols: symbols));
                        var provider = Microsoft.CodeAnalysis.CSharp.CSharpCompilation.Create("CsVerify.EfProvider", new[] { tree }, references,
                            new Microsoft.CodeAnalysis.CSharp.CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary));
                        using var image = new MemoryStream();
                        var result = provider.Emit(image);
                        if (!result.Success)
                        {
                            NoNeutral = "the verifier's own provider doesn't compile against the program's EF Core: " +
                                        result.Diagnostics.First(d => d.Severity == DiagnosticSeverity.Error).GetMessage();
                            return false;
                        }
                        image.Position = 0;
                        _neutral = LoadFromStream(image).GetType(EfNeutralProvider.Type).GetMethod("Use");
                    }
                    catch (Exception e)
                    {
                        NoNeutral = "the verifier's own provider couldn't be made: " + Inner(e).Message.Split('\n')[0];
                        return false;
                    }
                }
                if (_neutral == null)
                {
                    return false;
                }
                try
                {
                    _neutral.Invoke(null, new[] { builder });
                    return true;
                }
                catch (Exception e)
                {
                    NoNeutral = "the verifier's own provider couldn't be used: " + Inner(e).Message.Split('\n')[0];
                    return false;
                }
            }

            private void Collect(Compilation c, List<string> paths)
            {
                foreach (var r in c.References)
                {
                    if (r is PortableExecutableReference { FilePath: { } path } && File.Exists(path))
                    {
                        paths.Add(Path.GetFullPath(path));
                    }
                    else if (r is CompilationReference cr && _projects.TryAdd(cr.Compilation.AssemblyName ?? "", cr.Compilation))
                    {
                        Collect(cr.Compilation, paths);
                    }
                }
            }

            public Assembly Program() => Emitted(_compilation);

            /// <summary>A type by its metadata name, in what the program references.</summary>
            public Type Find(string name) =>
                _projects.Values.Select(p => Emitted(p).GetType(name)).Concat(Shared.All().Select(a => a.GetType(name))).FirstOrDefault(t => t != null);

            private Assembly Emitted(Compilation c)
            {
                var name = c.AssemblyName ?? "";
                if (_emitted.TryGetValue(name, out var done))
                {
                    return done;
                }
                using var image = new MemoryStream();
                var result = c.Emit(image);
                if (!result.Success)
                {
                    throw new InvalidOperationException(result.Diagnostics.FirstOrDefault(d => d.Severity == DiagnosticSeverity.Error)?.GetMessage() ?? "it doesn't compile");
                }
                image.Position = 0;
                var loaded = _emitted[name] = LoadFromStream(image);
                loaded.GetType("__CsVerifyEf")?.GetField("Configure")?.SetValue(null, Configure);
                return loaded;
            }

            protected override Assembly Load(AssemblyName name)
            {
                if (name.Name == null)
                {
                    return null;
                }
                if (_emitted.TryGetValue(name.Name, out var emitted))
                {
                    return emitted;
                }
                if (_projects.TryGetValue(name.Name, out var project))
                {
                    return Emitted(project);
                }
                try
                {
                    return Shared.LoadFromAssemblyName(name);
                }
                catch (Exception e)
                {
                    Shared.AddFailure(name.Name, e);
                    return null;
                }
            }
        }

        // ------------------------------------------------------------------ a context

        /// <summary>
        /// A context, as EF's design-time tools make one: by the program's IDesignTimeDbContextFactory for it; else by
        /// its constructor, given options of the provider the program references (which is never connected to), or of
        /// the verifier's own where it references none, and nothing for what else it takes.
        /// </summary>
        private static object Make(Type context, Loader load, List<string> providersNamed)
        {
            // (the context's assembly's, or the program's: a startup project's factory for a library project's context)
            var factory = new[] { context.Assembly, load.Program() }.Distinct().SelectMany(Types).FirstOrDefault(t => !t.IsAbstract && Interfaces(t).Any(i =>
                i.IsGenericType && i.GetGenericTypeDefinition().FullName == "Microsoft.EntityFrameworkCore.Design.IDesignTimeDbContextFactory`1" && i.GetGenericArguments()[0] == context));
            load.UsedFactory = load.UsedNeutral = false;
            if (factory != null && !load.NoFactory)
            {
                load.UsedFactory = true;
                return factory.GetMethod("CreateDbContext", new[] { typeof(string[]) }).Invoke(Activator.CreateInstance(factory), new object[] { Array.Empty<string>() });
            }
            var ef = context.BaseType;
            while (ef != null && ef.FullName != "Microsoft.EntityFrameworkCore.DbContext")
            {
                ef = ef.BaseType;
            }
            if (ef == null)
            {
                throw new InvalidOperationException("it isn't a DbContext");
            }
            var builderType = ef.Assembly.GetType("Microsoft.EntityFrameworkCore.DbContextOptionsBuilder`1").MakeGenericType(context);
            var builder = Activator.CreateInstance(builderType);
            var configured = load.Provider(builder, providersNamed);
            load.UseHost(builder);
            var options = Get(builder, "Options");
            Exception last = null;
            foreach (var ctor in context.GetConstructors(BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance)
                         .OrderByDescending(c => c.GetParameters().Any(p => p.ParameterType.IsInstanceOfType(options))).ThenBy(c => c.GetParameters().Length))
            {
                var ps = ctor.GetParameters();
                // (without a provider's options, only a context that configures itself, OnConfiguring)
                if (!configured && ps.Any(p => p.ParameterType.IsInstanceOfType(options)))
                {
                    continue;
                }
                try
                {
                    return ctor.Invoke(ps.Select(p => p.ParameterType.IsInstanceOfType(options) ? options : p.ParameterType.IsValueType ? Activator.CreateInstance(p.ParameterType) : null).ToArray());
                }
                catch (Exception e)
                {
                    last = Inner(e);
                }
            }
            throw new InvalidOperationException(last?.Message ?? (configured ? "it has no constructor the verifier can call"
                : "no database provider is found among the program's references" + (load.NoNeutral == null ? "" : ", and " + load.NoNeutral)));
        }

        /// <summary>An assembly's types that can be loaded: one that can't (a dependency the program doesn't have) doesn't hide the others.</summary>
        private static IEnumerable<Type> Types(Assembly a)
        {
            try
            {
                return a.GetTypes();
            }
            catch (ReflectionTypeLoadException e)
            {
                return e.Types.Where(t => t != null);
            }
        }

        private static Type[] Interfaces(Type t)
        {
            try
            {
                return t.GetInterfaces();
            }
            catch (Exception)
            {
                return Type.EmptyTypes;
            }
        }

        private static object DesignTimeModel(object context)
        {
            // (the context's service provider, IInfrastructure<IServiceProvider>.Instance: its design-time model)
            var services = context.GetType().GetInterfaces().FirstOrDefault(i => i.IsGenericType && i.GetGenericTypeDefinition().Name == "IInfrastructure`1" &&
                                                                                 i.GetGenericArguments()[0].FullName == "System.IServiceProvider");
            if (services?.GetProperty("Instance")?.GetValue(context) is IServiceProvider provider &&
                services.Assembly.GetType("Microsoft.EntityFrameworkCore.Metadata.IDesignTimeModel") is Type designTime && provider.GetService(designTime) is object service)
            {
                return Get(service, "Model");
            }
            return Get(context, "Model");
        }

        // ------------------------------------------------------------------ the model

        private void ReadModel(object model, Loader load)
        {
            var relational = load.Shared.All().FirstOrDefault(a => a.GetName().Name == "Microsoft.EntityFrameworkCore.Relational");
            foreach (var et in Many(Call(model, "GetEntityTypes")))
            {
                var clr = (Type)Get(et, "ClrType");
                if (clr != null && clr.FullName != null && Call(et, "FindOwnership") != null)
                {
                    Owned.Add(clr.FullName);
                }
                if (clr == null || clr.FullName == null || (bool)(Get(et, "HasSharedClrType") ?? false) || Call(et, "FindOwnership") != null || Entities.ContainsKey(clr.FullName))
                {
                    continue;
                }
                var e = new Entity { Type = clr.FullName };
                Entities[e.Type] = e;
                var mapped = new Dictionary<string, object>();
                foreach (var p in Many(Call(et, "GetProperties")))
                {
                    mapped[(string)Get(p, "Name")] = p;
                    var type = (Type)Get(p, "ClrType");
                    var generated = Get(p, "ValueGenerated")?.ToString();
                    bool token = (bool)Get(p, "IsConcurrencyToken");
                    e.Properties.Add(new Property
                    {
                        Name = (string)Get(p, "Name"),
                        Column = relational == null ? null : Extension(relational, "Microsoft.EntityFrameworkCore.RelationalPropertyExtensions", "GetColumnName", p) as string,
                        ClrType = type.FullName,
                        Shadow = (bool)Call(p, "IsShadowProperty"),
                        Nullable = (bool)Get(p, "IsNullable"),
                        Converted = Call(p, "GetValueConverter") != null,
                        Token = token,
                        RowVersion = token && generated == "OnAddOrUpdate",
                    });
                }
                foreach (var k in Many(Call(et, "GetKeys")))
                {
                    var names = Names(Get(k, "Properties"));
                    if ((bool)Call(k, "IsPrimaryKey"))
                    {
                        e.Key = names;
                    }
                    else
                    {
                        e.AlternateKeys.Add(names);
                    }
                }
                foreach (var ix in Many(Call(et, "GetIndexes")).Where(ix => (bool)Get(ix, "IsUnique")))
                {
                    e.UniqueIndexes.Add(new Index
                    {
                        Properties = Names(Get(ix, "Properties")),
                        Filter = relational == null ? null : Extension(relational, "Microsoft.EntityFrameworkCore.RelationalIndexExtensions", "GetFilter", ix) as string,
                    });
                    e.UniqueIndexes[^1].Excluded = Excluded(e.UniqueIndexes[^1].Filter, e, mapped);
                }
                foreach (var n in Many(Call(et, "GetNavigations")).Where(n => (bool)Get(n, "IsEagerLoaded")))
                {
                    e.AutoIncluded.Add((string)Get(n, "Name"));
                }
                for (var filtered = et; filtered != null; filtered = Get(filtered, "BaseType"))
                {
                    foreach (var filter in QueryFilters(filtered))
                    {
                        e.FilteredFalse.AddRange(False(filter.Body));
                    }
                }
                foreach (var fk in Many(Call(et, "GetDeclaredForeignKeys")))
                {
                    var principal = (Type)Get(Get(fk, "PrincipalEntityType"), "ClrType");
                    ForeignKeys.Add(new ForeignKey
                    {
                        Dependent = e.Type,
                        Principal = principal?.FullName,
                        Properties = Names(Get(fk, "Properties")),
                        PrincipalKey = Names(Get(Get(fk, "PrincipalKey"), "Properties")),
                        Unique = (bool)Get(fk, "IsUnique"),
                        Required = (bool)Get(fk, "IsRequired"),
                        ToPrincipal = Get(fk, "DependentToPrincipal") is { } dp ? (string)Get(dp, "Name") : null,
                        ToDependent = Get(fk, "PrincipalToDependent") is { } pd ? (string)Get(pd, "Name") : null,
                    });
                }
            }
        }

        /// <summary>An entity type's query filters: EF Core 10's declared ones (named or not), or the one filter before it.</summary>
        internal const string Unequal = @"^[\[""`]?(\w+)[\]""`]?\s*(?:<>|!=)\s*(N?'(?:[^']|'')*'|-?\d+)$";

        /// <summary>
        /// A filter's conjuncts [C] &lt;&gt; v, each as C's property and the value of its type that is stored as v: what
        /// the property's converter reads v as. A converter's two directions are taken to be each other's inverse, as
        /// EF takes them where it compares a column to a value: no value is stored as a v that it can't read.
        /// </summary>
        private static List<(string, string)> Excluded(string filter, Entity e, Dictionary<string, object> mapped)
        {
            var found = new List<(string, string)>();
            if (string.IsNullOrWhiteSpace(filter))
            {
                return found;
            }
            foreach (var conjunct in System.Text.RegularExpressions.Regex.Split(filter, @"\s+AND\s+", System.Text.RegularExpressions.RegexOptions.IgnoreCase))
            {
                var m = System.Text.RegularExpressions.Regex.Match(conjunct.Trim().Trim('(', ')').Trim(), Unequal);
                if (!m.Success || e.Properties.FirstOrDefault(p => p.Column == m.Groups[1].Value) is not Property column || !mapped.TryGetValue(column.Name, out var property))
                {
                    continue;
                }
                try
                {
                    if (StoredAs(property, m.Groups[2].Value) is string value)
                    {
                        found.Add((column.Name, value));
                    }
                }
                catch (Exception x) when (x is FormatException or InvalidCastException or OverflowException or ArgumentException or MissingMemberException)
                {
                    // (a literal not of the column's type: nothing known of it)
                }
            }
            return found;
        }

        /// <summary>The value of a property's type that the model stores as this SQL literal (see Index.Excluded); null: not one of those.</summary>
        private static string StoredAs(object property, string literal)
        {
            var clr = (Type)Get(property, "ClrType");
            var type = Nullable.GetUnderlyingType(clr) ?? clr;
            var converter = Call(property, "GetValueConverter");
            var provider = converter == null ? type : (Type)Get(converter, "ProviderClrType");
            provider = Nullable.GetUnderlyingType(provider) ?? provider;
            object stored;
            if (literal.EndsWith("'"))
            {
                var text = literal.Substring(literal.IndexOf('\'') + 1, literal.Length - literal.IndexOf('\'') - 2).Replace("''", "'");
                stored = provider == typeof(string) ? text : provider == typeof(Guid) ? Guid.Parse(text) : provider.IsEnum ? Enum.Parse(provider, text) : null;
            }
            else
            {
                long n = long.Parse(literal, System.Globalization.CultureInfo.InvariantCulture);
                stored = provider.IsEnum ? Enum.ToObject(provider, n) : provider == typeof(bool) ? n != 0 : provider.IsPrimitive ? Convert.ChangeType(n, provider) : null;
            }
            if (stored == null)
            {
                return null;
            }
            object value = stored;
            if (converter != null)
            {
                try
                {
                    value = ((Delegate)Get(converter, "ConvertFromProvider")).DynamicInvoke(stored);
                }
                catch (TargetInvocationException)
                {
                    return "none";
                }
            }
            return value switch
            {
                null => "null",
                Enum member => "number:" + Convert.ToInt64(member).ToString(System.Globalization.CultureInfo.InvariantCulture),
                _ when value.GetType() != type => null,
                _ when type.IsValueType && value.Equals(Activator.CreateInstance(type)) => "default",
                string { Length: 0 } => "string:",
                sbyte or byte or short or ushort or int or uint or long => "number:" + Convert.ToInt64(value).ToString(System.Globalization.CultureInfo.InvariantCulture),
                _ => null,
            };
        }

        private static List<System.Linq.Expressions.LambdaExpression> QueryFilters(object entityType)
        {
            var filters = new List<System.Linq.Expressions.LambdaExpression>();
            try
            {
                foreach (var f in Many(Call(entityType, "GetDeclaredQueryFilters")))
                {
                    var expression = Get(f, "Expression");
                    if (expression is System.Linq.Expressions.LambdaExpression e)
                    {
                        filters.Add(e);
                    }
                }
                if (filters.Count > 0)
                {
                    return filters;
                }
            }
            catch (Exception)
            {
            }
            try
            {
                if (Call(entityType, "GetQueryFilter") is System.Linq.Expressions.LambdaExpression one)
                {
                    filters.Add(one);
                }
            }
            catch (Exception)
            {
            }
            return filters;
        }

        /// <summary>The columns a filter's conjuncts say are false: !x.P, x.P == false, of a property or EF.Property(x, "P").</summary>
        private static IEnumerable<string> False(System.Linq.Expressions.Expression e)
        {
            switch (e)
            {
                case System.Linq.Expressions.BinaryExpression { NodeType: System.Linq.Expressions.ExpressionType.AndAlso } and:
                    return False(and.Left).Concat(False(and.Right));
                case System.Linq.Expressions.UnaryExpression { NodeType: System.Linq.Expressions.ExpressionType.Not } not when Column(not.Operand) is string c:
                    return new[] { c };
                case System.Linq.Expressions.BinaryExpression { NodeType: System.Linq.Expressions.ExpressionType.Equal, Right: System.Linq.Expressions.ConstantExpression { Value: false } } eq
                    when Column(eq.Left) is string c:
                    return new[] { c };
                default:
                    return Array.Empty<string>();
            }

            // (the row, as it is or converted: EF.Property takes an object)
            static bool Row(System.Linq.Expressions.Expression x) =>
                x is System.Linq.Expressions.ParameterExpression ||
                x is System.Linq.Expressions.UnaryExpression { NodeType: System.Linq.Expressions.ExpressionType.Convert or System.Linq.Expressions.ExpressionType.TypeAs, Operand: System.Linq.Expressions.ParameterExpression };

            static string Column(System.Linq.Expressions.Expression x) => x switch
            {
                System.Linq.Expressions.MemberExpression { Expression: { } of } m when Row(of) => m.Member.Name,
                System.Linq.Expressions.MethodCallExpression { Method.Name: "Property", Arguments: [var of, System.Linq.Expressions.ConstantExpression { Value: string name }] } when Row(of) => name,
                _ => null,
            };
        }

        private static List<string> Names(object properties) => Many(properties).Select(p => (string)Get(p, "Name")).ToList();

        private static IEnumerable<object> Many(object o) => o == null ? Enumerable.Empty<object>() : ((IEnumerable)o).Cast<object>().ToList();

        /// <summary>A property's value: the object's own, or of an interface it implements.</summary>
        private static object Get(object o, string name)
        {
            var t = o.GetType();
            PropertyInfo p = null;
            // (the most derived one of the name: a generic class's hides its base's)
            for (var c = t; c != null && p == null; c = c.BaseType)
            {
                p = c.GetProperties(BindingFlags.Public | BindingFlags.Instance | BindingFlags.DeclaredOnly).FirstOrDefault(x => x.Name == name && x.GetIndexParameters().Length == 0);
            }
            p ??= t.GetInterfaces().Select(i => i.GetProperty(name)).FirstOrDefault(x => x != null);
            return p == null ? throw new MissingMemberException(t.Name, name) : p.GetValue(o);
        }

        /// <summary>A method of no parameters: the object's own, or of an interface it implements.</summary>
        private static object Call(object o, string name)
        {
            var t = o.GetType();
            var m = t.GetMethods(BindingFlags.Public | BindingFlags.Instance).FirstOrDefault(x => x.Name == name && x.GetParameters().Length == 0 && !x.IsGenericMethodDefinition) ??
                    t.GetInterfaces().SelectMany(i => i.GetMethods()).FirstOrDefault(x => x.Name == name && x.GetParameters().Length == 0 && !x.IsGenericMethodDefinition);
            return m == null ? throw new MissingMemberException(t.Name, name) : m.Invoke(o, null);
        }

        /// <summary>An extension method of one parameter the target fits (null where there is none).</summary>
        private static object Extension(Assembly a, string type, string method, object target)
        {
            var m = a.GetType(type)?.GetMethods(BindingFlags.Public | BindingFlags.Static)
                .FirstOrDefault(x => x.Name == method && x.GetParameters() is { Length: 1 } ps && ps[0].ParameterType.IsInstanceOfType(target));
            return m?.Invoke(null, new[] { target });
        }
    }
}
