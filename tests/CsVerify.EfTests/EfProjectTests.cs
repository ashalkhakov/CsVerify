using System;
using System.IO;
using System.Linq;
using Xunit;
using static CsVerify.Tests.EfHarness;

namespace CsVerify.Tests
{
    /// <summary>A context of the program whose entities and configurations are referenced projects of their own.</summary>
    public class EfProjectTests
    {
        private const string Entities = @"namespace Domain
{
    public class Parcel
    {
        public long Id { get; set; }
        public string Code { get; set; } = """";
        public long Weight { get; set; }
    }
}";

        private const string Configurations = @"using Domain;
using Microsoft.EntityFrameworkCore.Metadata.Builders;
namespace Data
{
    public sealed class ParcelConfiguration : IEntityTypeConfiguration<Parcel>
    {
        public void Configure(EntityTypeBuilder<Parcel> b) { b.HasKey(p => p.Id); b.HasIndex(p => p.Code).IsUnique(); }
    }
}";

        private const string Program = @"using Domain;
public sealed class Shop : DbContext
{
    public Shop(DbContextOptions<Shop> options) : base(options) { }
    public DbSet<Parcel> Parcels { get; set; } = null!;
    protected override void OnModelCreating(ModelBuilder b) => b.ApplyConfigurationsFromAssembly(typeof(Data.ParcelConfiguration).Assembly);
}
public sealed class Parcels
{
    private readonly Shop _shop;
    public Parcels(Shop shop) { _shop = shop; }
    public IReadOnlyList<Parcel> All() => _shop.Set<Parcel>().ToList();
    public long WeightOf(string code)
    {
        var p = _shop.Parcels.AsNoTracking().SingleOrDefault(x => x.Code == code);
        return p == null ? 0 : p.Weight;
    }
    // (#118: not verified, and the rest as they would be without it)
    public static bool IsDuplicate(Exception e) => e.InnerException?.GetType().GetProperty(""Number"")?.GetValue(e.InnerException) is 2601 or 2627;
}";

        [Fact]
        public void AnIdentityUsersId_FromAReferencedProject_IsItsColumn()
        {
            // (#129's review: User : IdentityUser<long>, IRow in a domain project, IRow.Id the library's Id)
            var r = VerifyEfWithProjects(@"public sealed class Users
{
    private readonly Shop _shop;
    public Users(Shop shop) { _shop = shop; }
    public async Task<long?> IdOf(string name) =>
        await _shop.Set<User>().AsNoTracking().Where(u => u.UserName == name).Select(u => (long?)u.Id).FirstOrDefaultAsync();
    public async Task<List<long>> Ids() =>
        await _shop.Set<User>().AsNoTracking().Select(u => u.Id).ToListAsync();
}",
                new Project("Domain", @"using Microsoft.AspNetCore.Identity;
public interface IRow { long Id { get; set; } }
public class User : IdentityUser<long>, IRow { }", new string[0]),
                new Project("Data", @"using Microsoft.AspNetCore.Identity;
using Microsoft.AspNetCore.Identity.EntityFrameworkCore;
public sealed class Shop : IdentityDbContext<User, IdentityRole<long>, long>
{
    public Shop(DbContextOptions<Shop> o) : base(o) { }
}", new[] { "Domain" }));
            Assert.True(r.Errors("Ids").Length == 0, r.Explain("Ids"));
        }

        [Fact]
        public void AnEntityOfOneProject_ConfiguredInAnother_IsOneType()
        {
            // (#119: each type, field and procedure declared once)
            // (the program of more references than its projects: SQLite's provider, say)
            var r = VerifyEfWithProjects(Program, o => o.References.AddRange(EfReferences(sqlite: true).Except(o.References)),
                new Project("Domain", Entities, new string[0], Ef: false),
                new Project("Data", Configurations, new[] { "Domain" }));
            // (a project of fewer references than the program's, as the Spec library is compiled with, is not retargeted)
            Assert.Empty(r.Warnings);
            foreach (var m in new[] { "All", "WeightOf" })
            {
                Assert.True(r.Errors(m).Length == 0, r.Explain(m));
            }
            Assert.Contains(r["IsDuplicate"].Diagnostics, d => d.Id == "CSV1902" && d.Message.Contains("unboxing"));
        }

        [Fact]
        public void AContextOfAFrameworksTargetingPack_HasEfsModel()
        {
            // (PR #134's review: a project with <FrameworkReference Include="Microsoft.AspNetCore.App" /> gives the verifier
            // the targeting pack's reference assemblies, which can't be loaded; the shared framework's are, in their
            // place, and the context, derived from ASP.NET Core Identity's, gets EF's own model)
            var dotnet = Path.GetFullPath(Path.Combine(Path.GetDirectoryName(typeof(object).Assembly.Location), "..", "..", ".."));
            var packs = Path.Combine(dotnet, "packs", "Microsoft.AspNetCore.App.Ref");
            Assert.True(Directory.Exists(packs), "the SDK's ASP.NET Core targeting pack, at " + packs);
            var major = Environment.Version.Major.ToString();
            var version = Directory.GetDirectories(packs).Where(d => Path.GetFileName(d).Split('.')[0] == major).OrderBy(d => d, StringComparer.Ordinal).Last();
            var pack = Directory.EnumerateFiles(Directory.GetDirectories(Path.Combine(version, "ref")).Single(), "*.dll").ToList();
            var names = pack.Select(Path.GetFileNameWithoutExtension).ToHashSet(StringComparer.OrdinalIgnoreCase);
            var r = EfHarness.VerifyEf(@"using Microsoft.AspNetCore.Identity;
using Microsoft.AspNetCore.Identity.EntityFrameworkCore;
public sealed class Tag
{
    public long Id { get; set; }
    public string? Code { get; set; }
    public string Name { get; set; } = """";
}
public sealed class Db(DbContextOptions<Db> options) : IdentityDbContext<IdentityUser<long>, IdentityRole<long>, long>(options)
{
    protected override void OnModelCreating(ModelBuilder b)
    {
        base.OnModelCreating(b);
        b.Entity<Tag>().Property(t => t.Code).HasColumnName(""CodeId"");
        b.Entity<Tag>().HasIndex(t => t.Code).IsUnique().HasFilter(""[CodeId] IS NOT NULL"");
    }
}
public sealed class Store(Db db)
{
    public async Task<Tag?> ByCode(string code) => await db.Set<Tag>().Where(t => t.Code == code).SingleOrDefaultAsync();
    public async Task<Tag?> ByName(string name) => await db.Set<Tag>().Where(t => t.Name == name).SingleOrDefaultAsync();
    public async Task<IdentityUser<long>?> ById(long id) => await db.Users.Where(u => u.Id == id).SingleOrDefaultAsync();
    public async Task<IdentityUser<long>?> ByNormalizedName(string name) => await db.Users.Where(u => u.NormalizedUserName == name).SingleOrDefaultAsync();
    public async Task<IdentityUser<long>?> ByEmail(string email) => await db.Users.Where(u => u.Email == email).SingleOrDefaultAsync();
    public async Task<long> Rename(long id, string name)
    {
        var user = await db.Users.Where(u => u.Id == id).SingleOrDefaultAsync();
        if (user == null) return 0;
        user.UserName = name;
        await db.SaveChangesAsync();
        return user.Id;
    }
}", options =>
            {
                // (as a build has them: the framework's, in place of the packages' of the same names)
                options.References.RemoveAll(reference => names.Contains(Path.GetFileNameWithoutExtension(reference)));
                options.References.AddRange(pack);
            });
            Assert.DoesNotContain(r.Diagnostics, d => d.Id == "CSV1902");
            // (a library's own entity, Identity's IdentityUser<long> through db.Users: its key and its unique index, as
            // EF's model has them)
            foreach (var ok in new[] { "ByCode", "ById", "ByNormalizedName", "Rename" })
            {
                Assert.True(r.Errors("Store." + ok).Length == 0, ok + ": " + r.Explain("Store." + ok));
            }
            // (an email isn't unique by Identity's model)
            Assert.True(r.Errors("Store.ByEmail").SequenceEqual(new[] { "CSV1001" }), r.Explain("Store.ByEmail"));
            Assert.True(r.Errors("Store.ByName").SequenceEqual(new[] { "CSV1001" }), r.Explain("Store.ByName"));
        }

        // (a configuration the sources' reading doesn't follow: an index's filter that names a renamed column, a unique
        // index over a shadow foreign key. Verified only where EF's own model was built)
        private const string HostPicksTheDatabase = @"
public sealed class Tag
{
    public long Id { get; set; }
    public string? Code { get; set; }
    public string Name { get; set; } = """";
}
public sealed class Owner
{
    public long RowId { get; set; }
}
public sealed class Payment
{
    public long RowId { get; set; }
    public Owner? Holder { get; private set; }
    public Guid? IdempotencyKey { get; set; }
}
public sealed class Db : DbContext
{
    CONSTRUCTORS
    protected override void OnModelCreating(ModelBuilder b)
    {
        b.Entity<Tag>().Property(t => t.Code).HasColumnName(""CodeId"");
        b.Entity<Tag>().HasIndex(t => t.Code).IsUnique().HasFilter(""[CodeId] IS NOT NULL"");
        b.Entity<Owner>().HasKey(o => o.RowId);
        b.Entity<Payment>().HasKey(p => p.RowId);
        b.Entity<Payment>().HasOne(p => p.Holder).WithMany().HasForeignKey(""OwnerId"").IsRequired();
        b.Entity<Payment>().HasIndex(""OwnerId"", nameof(Payment.IdempotencyKey)).IsUnique();
    }
}
public sealed class Store(Db db)
{
    public async Task<Tag?> ByCode(string code) => await db.Set<Tag>().Where(t => t.Code == code).SingleOrDefaultAsync();
    public async Task<Tag?> ByName(string name) => await db.Set<Tag>().Where(t => t.Name == name).SingleOrDefaultAsync();
    public async Task<Payment?> ByKey(long owner, Guid key) =>
        await db.Set<Payment>().Where(p => EF.Property<long>(p, ""OwnerId"") == owner && p.IdempotencyKey == key).SingleOrDefaultAsync();
}";

        private const string OptionsConstructor = "public Db(DbContextOptions<Db> options) : base(options) { }";

        private const string FailingFactory = @"
public sealed class DbFactory : Microsoft.EntityFrameworkCore.Design.IDesignTimeDbContextFactory<Db>
{
    public Db CreateDbContext(string[] args) => throw new InvalidOperationException(""the connection string isn't configured"");
}";

        private static void AssertEfsModel(CsVerify.Verifier.VerificationResult r)
        {
            Assert.DoesNotContain(r.Diagnostics, d => d.Id == "CSV1902");
            Assert.True(r.Errors("Store.ByCode").Length == 0, r.Explain("Store.ByCode"));
            Assert.True(r.Errors("Store.ByKey").Length == 0, r.Explain("Store.ByKey"));
            Assert.True(r.Errors("Store.ByName").SequenceEqual(new[] { "CSV1001" }), r.Explain("Store.ByName"));
        }

        // (PR #134's review, the third: a library's project references EF Core and no provider, its host picks the
        // database; EF's model is built with the verifier's own provider, of no database. A context with the options'
        // constructor; with a parameterless one too; with only that one, and no OnConfiguring)
        [Theory]
        [InlineData(OptionsConstructor)]
        [InlineData("public Db() { } " + OptionsConstructor)]
        [InlineData("public Db() { }")]
        public void AContextWhoseProjectReferencesNoProvider_HasEfsModel(string constructors) =>
            AssertEfsModel(VerifyEfWithoutAProvider(HostPicksTheDatabase.Replace("CONSTRUCTORS", constructors)));

        // (a design-time factory that can't make the context here, one that reads a configuration: the context is made
        // by its constructor; with the provider the program references, or with the verifier's own)
        [Fact]
        public void AContextWhoseFactoryFails_IsMadeByItsConstructor()
        {
            var source = HostPicksTheDatabase.Replace("CONSTRUCTORS", OptionsConstructor) + FailingFactory;
            AssertEfsModel(VerifyEf(source));
            AssertEfsModel(VerifyEfWithoutAProvider(source));
        }
    }
}
