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
        public readonly List<ForeignKey> ForeignKeys = new List<ForeignKey>();
        /// <summary>The contexts read.</summary>
        public readonly List<string> Contexts = new List<string>();
        /// <summary>Why a context's model couldn't be read: the context and the reason.</summary>
        public readonly List<(string context, string why)> Failures = new List<(string, string)>();

        /// <summary>The models of the contexts given, of the compilation as emitted.</summary>
        public static EfRuntimeModel Read(Compilation compilation, IEnumerable<INamedTypeSymbol> contexts, IEnumerable<string> providersNamed)
        {
            var model = new EfRuntimeModel();
            var wanted = contexts.ToList();
            if (wanted.Count == 0)
            {
                return model;
            }
            // (a context that takes no options and has no OnConfiguring: in the copy emitted here, one that configures the
            // provider found; the program's own isn't changed)
            var hooked = false;
            var member = (Microsoft.CodeAnalysis.CSharp.Syntax.MemberDeclarationSyntax)Microsoft.CodeAnalysis.CSharp.SyntaxFactory.ParseMemberDeclaration(
                "protected override void OnConfiguring(global::Microsoft.EntityFrameworkCore.DbContextOptionsBuilder b) { base.OnConfiguring(b); if (!b.IsConfigured) global::__CsVerifyEf.Configure?.Invoke(b); }");
            var declarations = wanted.Where(c => !c.InstanceConstructors.Any(k => k.Parameters.Any(p => p.Type.Name == "DbContextOptions")) && !c.GetMembers("OnConfiguring").Any())
                .Select(c => c.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax()).OfType<Microsoft.CodeAnalysis.CSharp.Syntax.ClassDeclarationSyntax>().ToList();
            var original = compilation;
            foreach (var group in declarations.GroupBy(d => d.SyntaxTree))
            {
                var tree = group.Key;
                compilation = compilation.ReplaceSyntaxTree(tree, tree.WithRootAndOptions(tree.GetRoot().ReplaceNodes(group, (d, _) => d.AddMembers(member)), tree.Options));
                hooked = true;
            }
            if (hooked && compilation.SyntaxTrees.FirstOrDefault() is SyntaxTree first)
            {
                compilation = compilation.AddSyntaxTrees(first.WithRootAndOptions(
                    Microsoft.CodeAnalysis.CSharp.SyntaxFactory.ParseCompilationUnit("internal static class __CsVerifyEf { public static global::System.Action<object> Configure; }"), first.Options).WithFilePath("__CsVerifyEf.cs"));
                if (compilation.GetDiagnostics().Any(d => d.Severity == DiagnosticSeverity.Error))
                {
                    compilation = original;
                    hooked = false;
                }
            }
            var providers = providersNamed.ToList();
            var load = new Loader(compilation);
            try
            {
                Assembly program;
                try
                {
                    program = load.Program();
                }
                catch (Exception e)
                {
                    model.Failures.AddRange(wanted.Select(c => (EfModel.MetadataName(c), "the program couldn't be loaded: " + Inner(e).Message)));
                    return model;
                }
                if (hooked)
                {
                    program.GetType("__CsVerifyEf").GetField("Configure").SetValue(null, (Action<object>)(b => load.Shared.Provider(b, providers)));
                }
                foreach (var name in wanted.Select(EfModel.MetadataName))
                {
                    try
                    {
                        var type = program.GetType(name) ?? load.Find(name);
                        var context = Make(type ?? throw new InvalidOperationException("its type isn't found"), load, providers);
                        try
                        {
                            model.ReadModel(DesignTimeModel(context), load);
                            model.Contexts.Add(name);
                        }
                        finally
                        {
                            (context as IDisposable)?.Dispose();
                        }
                    }
                    catch (Exception e)
                    {
                        if (Environment.GetEnvironmentVariable("CSVERIFY_EF_MODEL_TRACE") != null)
                        {
                            Console.Error.WriteLine(Inner(e));
                        }
                        model.Failures.Add((name, Inner(e).Message));
                    }
                }
            }
            finally
            {
                load.Unload();
            }
            return model;
        }

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

            public static References For(IEnumerable<string> paths)
            {
                var all = paths.Select(Path.GetFullPath).Distinct().OrderBy(p => p, StringComparer.Ordinal).ToList();
                var key = string.Join("|", all.Select(p => p + "@" + File.GetLastWriteTimeUtc(p).Ticks));
                lock (Cache)
                {
                    return Cache.TryGetValue(key, out var found) ? found : Cache[key] = new References(all);
                }
            }

            private References(List<string> paths) : base("csverify-ef-references")
            {
                foreach (var path in paths)
                {
                    _paths.TryAdd(Path.GetFileNameWithoutExtension(path), path);
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

            public IEnumerable<Assembly> All()
            {
                foreach (var a in _paths.Keys.ToList())
                {
                    Assembly loaded = null;
                    try
                    {
                        loaded = LoadFromAssemblyName(new AssemblyName(a));
                    }
                    catch (Exception)
                    {
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
                foreach (var candidate in Implementations(path, name.Name))
                {
                    try
                    {
                        return LoadFromAssemblyPath(candidate);
                    }
                    catch (BadImageFormatException)
                    {
                        // (a reference assembly: its implementation, next)
                    }
                }
                return null;
            }

            /// <summary>The assembly, then where its implementation is if it is a reference assembly: a package's lib folder, a shared framework.</summary>
            private static IEnumerable<string> Implementations(string path, string name)
            {
                yield return path;
                var sep = Path.DirectorySeparatorChar;
                var inRef = path.LastIndexOf(sep + "ref" + sep, StringComparison.OrdinalIgnoreCase);
                if (inRef >= 0)
                {
                    var lib = path.Substring(0, inRef) + sep + "lib" + sep + path.Substring(inRef + 5);
                    if (File.Exists(lib))
                    {
                        yield return lib;
                    }
                }
                // (a framework's reference pack: the shared framework of the same name the runtime has)
                var shared = Path.GetDirectoryName(Path.GetDirectoryName(Path.GetDirectoryName(typeof(object).Assembly.Location)));
                if (shared != null && Directory.Exists(shared))
                {
                    foreach (var framework in Directory.GetDirectories(shared))
                    {
                        foreach (var version in Directory.GetDirectories(framework).OrderByDescending(v => v, StringComparer.Ordinal))
                        {
                            var file = Path.Combine(version, name + ".dll");
                            if (File.Exists(file))
                            {
                                yield return file;
                                break;
                            }
                        }
                    }
                }
            }

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
                        Type[] types;
                        try
                        {
                            types = a.GetExportedTypes();
                        }
                        catch (Exception)
                        {
                            continue;
                        }
                        foreach (var t in types.Where(t => t.IsAbstract && t.IsSealed && (t.Name.EndsWith("DbContextOptionsBuilderExtensions") || t.Name.EndsWith("DbContextOptionsExtensions"))))
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

            public Loader(Compilation compilation) : base("csverify-ef-model", isCollectible: true)
            {
                _compilation = compilation;
                var paths = new List<string>();
                Collect(compilation, paths);
                Shared = References.For(paths);
            }

            private void Collect(Compilation c, List<string> paths)
            {
                foreach (var r in c.References)
                {
                    if (r is PortableExecutableReference { FilePath: { } path } && File.Exists(path))
                    {
                        paths.Add(path);
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
                return _emitted[name] = LoadFromStream(image);
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
                catch (Exception)
                {
                    return null;
                }
            }
        }

        // ------------------------------------------------------------------ a context

        /// <summary>
        /// A context, as EF's design-time tools make one: by the program's IDesignTimeDbContextFactory for it; else by
        /// its constructor, given options of the provider the program references (which is never connected to) and
        /// nothing for what else it takes.
        /// </summary>
        private static object Make(Type context, Loader load, List<string> providersNamed)
        {
            var factory = context.Assembly.GetTypes().FirstOrDefault(t => !t.IsAbstract && t.GetInterfaces().Any(i =>
                i.IsGenericType && i.GetGenericTypeDefinition().FullName == "Microsoft.EntityFrameworkCore.Design.IDesignTimeDbContextFactory`1" && i.GetGenericArguments()[0] == context));
            if (factory != null)
            {
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
            var configured = load.Shared.Provider(builder, providersNamed);
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
            throw new InvalidOperationException(last?.Message ?? (configured ? "it has no constructor the verifier can call" : "no database provider is found among the program's references"));
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
                if (clr == null || clr.FullName == null || (bool)(Get(et, "HasSharedClrType") ?? false) || Call(et, "FindOwnership") != null || Entities.ContainsKey(clr.FullName))
                {
                    continue;
                }
                var e = new Entity { Type = clr.FullName };
                Entities[e.Type] = e;
                foreach (var p in Many(Call(et, "GetProperties")))
                {
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
                }
                foreach (var n in Many(Call(et, "GetNavigations")).Where(n => (bool)Get(n, "IsEagerLoaded")))
                {
                    e.AutoIncluded.Add((string)Get(n, "Name"));
                }
                for (var filtered = et; filtered != null; filtered = Get(filtered, "BaseType"))
                {
                    if (QueryFilter(filtered) is System.Linq.Expressions.LambdaExpression filter)
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

        private static object QueryFilter(object entityType)
        {
            try
            {
                return Call(entityType, "GetQueryFilter");
            }
            catch (Exception)
            {
                return null;
            }
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

            static string Column(System.Linq.Expressions.Expression x) => x switch
            {
                System.Linq.Expressions.MemberExpression { Expression: System.Linq.Expressions.ParameterExpression } m => m.Member.Name,
                System.Linq.Expressions.MethodCallExpression { Method.Name: "Property", Arguments: [System.Linq.Expressions.ParameterExpression, System.Linq.Expressions.ConstantExpression { Value: string name }] } => name,
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
