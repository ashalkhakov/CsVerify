namespace CsVerify.Verifier
{
    /// <summary>
    /// A relational EF provider of no database, as source: EfRuntimeModel compiles it against the EF Core the program
    /// references, where the program references no provider of its own (a library whose host picks the database). It
    /// has the services EF builds a model with (EF's relational conventions, a column type for each type every
    /// database has one for) and none that reach a database. EF7: the program's EF Core is 7 or later (JSON columns;
    /// conventions that ask for the update SQL generator).
    /// </summary>
    internal static class EfNeutralProvider
    {
        public const string Type = "__CsVerifyEfProvider";

        /// <summary>
        /// A stand-in's base (EfHostServices): compiled into the program's load context, since a proxy of one of the
        /// program's interfaces can't be made over a class of the verifier's.
        /// </summary>
        public const string StandIn = "__CsVerifyEfStandIn";

        public const string StandInSource = """
            public class __CsVerifyEfStandIn : System.Reflection.DispatchProxy
            {
                protected override object Invoke(System.Reflection.MethodInfo method, object[] args) =>
                    method == null || method.ReturnType == typeof(void) || !method.ReturnType.IsValueType ? null : System.Activator.CreateInstance(method.ReturnType);
            }
            """;

        public const string Source = """
            using System;
            using System.Collections.Generic;
            using Microsoft.EntityFrameworkCore;
            using Microsoft.EntityFrameworkCore.Diagnostics;
            using Microsoft.EntityFrameworkCore.Infrastructure;
            using Microsoft.EntityFrameworkCore.Metadata.Conventions.Infrastructure;
            using Microsoft.EntityFrameworkCore.Storage;
            using Microsoft.EntityFrameworkCore.Update;
            using Microsoft.Extensions.DependencyInjection;

            public static class __CsVerifyEfProvider
            {
                public static void Use(DbContextOptionsBuilder builder) =>
                    ((IDbContextOptionsBuilderInfrastructure)builder).AddOrUpdateExtension(new Extension());

                private sealed class Extension : RelationalOptionsExtension
                {
                    private DbContextOptionsExtensionInfo _info;

                    public Extension() { }

                    private Extension(Extension from) : base(from) { }

                    public override DbContextOptionsExtensionInfo Info => _info ??= new ExtensionInfo(this);

                    protected override RelationalOptionsExtension Clone() => new Extension(this);

                    public override void ApplyServices(IServiceCollection services) =>
                        new EntityFrameworkRelationalServicesBuilder(services)
                            .TryAdd<LoggingDefinitions, Logging>()
                            .TryAdd<IDatabaseProvider, DatabaseProvider<Extension>>()
                            .TryAdd<IRelationalTypeMappingSource, Mappings>()
                            .TryAdd<IProviderConventionSetBuilder, Conventions>()
                            .TryAdd<IRelationalConnection, Connection>()
                            .TryAdd<ISqlGenerationHelper, RelationalSqlGenerationHelper>()
                            .TryAdd<IModificationCommandBatchFactory, Batches>()
            #if EF7
                            .TryAdd<IUpdateSqlGenerator, Updates>()
            #endif
                            .TryAddCoreServices();

                    private sealed class ExtensionInfo : RelationalExtensionInfo
                    {
                        public ExtensionInfo(IDbContextOptionsExtension extension) : base(extension) { }

                        public override void PopulateDebugInfo(IDictionary<string, string> debugInfo) { }
                    }
                }

                private sealed class Logging : RelationalLoggingDefinitions { }

                private sealed class Conventions : RelationalConventionSetBuilder
                {
                    public Conventions(ProviderConventionSetBuilderDependencies dependencies, RelationalConventionSetBuilderDependencies relational) : base(dependencies, relational) { }
                }

                // (what EF's services ask for and a model is built without: there is no database)
                private sealed class Connection : RelationalConnection
                {
                    public Connection(RelationalConnectionDependencies dependencies) : base(dependencies) { }

                    protected override System.Data.Common.DbConnection CreateDbConnection() => throw new NotSupportedException("the verifier's provider has no database");
                }

                private sealed class Batches : IModificationCommandBatchFactory
                {
                    public ModificationCommandBatch Create() => throw new NotSupportedException("the verifier's provider has no database");
                }

            #if EF7
                private sealed class Updates : UpdateSqlGenerator
                {
                    public Updates(UpdateSqlGeneratorDependencies dependencies) : base(dependencies) { }
                }
            #endif

                // (a column for each type every database has one for; of another type, where the program names its column's type)
                private sealed class Mappings : RelationalTypeMappingSource
                {
                    private readonly Dictionary<Type, RelationalTypeMapping> _columns = new Dictionary<Type, RelationalTypeMapping>
                    {
                        [typeof(bool)] = new BoolTypeMapping("boolean"),
                        [typeof(byte)] = new ByteTypeMapping("tinyint"),
                        [typeof(sbyte)] = new SByteTypeMapping("tinyint"),
                        [typeof(short)] = new ShortTypeMapping("smallint"),
                        [typeof(ushort)] = new UShortTypeMapping("smallint"),
                        [typeof(int)] = new IntTypeMapping("integer"),
                        [typeof(uint)] = new UIntTypeMapping("integer"),
                        [typeof(long)] = new LongTypeMapping("bigint"),
                        [typeof(ulong)] = new ULongTypeMapping("bigint"),
                        [typeof(char)] = new CharTypeMapping("char"),
                        [typeof(float)] = new FloatTypeMapping("real"),
                        [typeof(double)] = new DoubleTypeMapping("double precision"),
                        [typeof(decimal)] = new DecimalTypeMapping("decimal"),
                        [typeof(string)] = new StringTypeMapping("text", System.Data.DbType.String),
                        [typeof(byte[])] = new ByteArrayTypeMapping("blob"),
                        [typeof(Guid)] = new GuidTypeMapping("uuid"),
                        [typeof(DateTime)] = new DateTimeTypeMapping("timestamp"),
                        [typeof(DateTimeOffset)] = new DateTimeOffsetTypeMapping("timestamp with time zone"),
                        [typeof(DateOnly)] = new DateOnlyTypeMapping("date"),
                        [typeof(TimeOnly)] = new TimeOnlyTypeMapping("time"),
                        [typeof(TimeSpan)] = new TimeSpanTypeMapping("interval"),
            #if EF7
                        [typeof(System.Text.Json.JsonElement)] = new Json("json"),
            #endif
                    };

                    public Mappings(TypeMappingSourceDependencies dependencies, RelationalTypeMappingSourceDependencies relational) : base(dependencies, relational) { }

                    protected override RelationalTypeMapping FindMapping(in RelationalTypeMappingInfo info)
                    {
                        var type = info.ClrType == null ? null : Nullable.GetUnderlyingType(info.ClrType) ?? info.ClrType;
                        return type == null ? null
                            : _columns.TryGetValue(type, out var column) ? column
                            : info.StoreTypeName != null && !type.IsEnum ? new Column(info.StoreTypeName, type) : null;
                    }
                }

                private sealed class Column : RelationalTypeMapping
                {
                    public Column(string storeType, Type type) : base(storeType, type) { }

                    private Column(RelationalTypeMappingParameters parameters) : base(parameters) { }

                    protected override RelationalTypeMapping Clone(RelationalTypeMappingParameters parameters) => new Column(parameters);
                }

            #if EF7
                private sealed class Json : JsonTypeMapping
                {
                    public Json(string storeType) : base(storeType, typeof(System.Text.Json.JsonElement), System.Data.DbType.String) { }

                    private Json(RelationalTypeMappingParameters parameters) : base(parameters) { }

                    protected override RelationalTypeMapping Clone(RelationalTypeMappingParameters parameters) => new Json(parameters);
                }
            #endif
            }
            """;
    }
}
