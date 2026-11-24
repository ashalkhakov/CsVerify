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
    }
}
