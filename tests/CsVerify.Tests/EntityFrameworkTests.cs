using System.Linq;
using Xunit;
using static CsVerify.Tests.Harness;

namespace CsVerify.Tests
{
    /// <summary>Entity Framework Core: queries, the change tracker, transactions, one operation at a time.</summary>
    public class EntityFrameworkTests
    {
        // A shop's database, written for these tests.
        private const string Model = @"
public sealed class Customer
{
    public int Id { get; set; }
    public string Email { get; set; } = """";
    public string Name { get; set; } = """";
    public List<Order> Orders { get; set; } = new List<Order>();
    public string Display => Name + "" <"" + Email + "">"";
}
public sealed class Order
{
    public int Id { get; set; }
    public int CustomerId { get; set; }
    public Customer? Customer { get; set; }
    public int Total { get; set; }
    public bool Shipped { get; set; }
    public bool IsDeleted { get; set; }
    [System.ComponentModel.DataAnnotations.ConcurrencyCheck] public System.DateTime Updated { get; set; }
}
public sealed class Shop : DbContext
{
    public DbSet<Customer> Customers => Set<Customer>();
    public DbSet<Order> Orders => Set<Order>();
    protected override void OnModelCreating(ModelBuilder b)
    {
        b.Entity<Customer>().HasIndex(c => c.Email).IsUnique();
        b.Entity<Order>().HasQueryFilter(o => !o.IsDeleted);
    }
}
";

        private static string[] Errors(string method, string source) => VerifyEf(Model + source).Errors(method);

        // ---- queries ----------------------------------------------------------------------------------------

        [Fact]
        public void Where_RowsPassThePredicate() => Assert.Empty(Errors("M",
            "public static class C { public static async Task M(Shop db) { var r = await db.Orders.AsNoTracking().Where(o => o.Total > 5).ToListAsync(); " +
            "Spec.Assert(Spec.Forall(0, r.Count, i => r[i].Total > 5)); } }"));

        [Fact]
        public void Where_SaysNothingElse() => Assert.NotEmpty(Errors("M",
            "public static class C { public static async Task M(Shop db) { var r = await db.Orders.AsNoTracking().Where(o => o.Total > 5).ToListAsync(); " +
            "Spec.Assert(Spec.Forall(0, r.Count, i => r[i].Total > 6)); } }"));

        [Fact]
        public void Sync_CountIsNotNegative() => Assert.Empty(Errors("M",
            "public static class C { public static int M(Shop db) { Spec.Ensures<int>(r => r >= 0); return db.Orders.Where(o => o.Total > 5).Count(); } }"));

        [Fact]
        public void QueryFilter_HidesDeletedRows() => Assert.Empty(Errors("M",
            "public static class C { public static async Task M(Shop db) { var r = await db.Orders.AsNoTracking().ToListAsync(); " +
            "Spec.Assert(Spec.Forall(0, r.Count, i => !r[i].IsDeleted)); } }"));

        [Fact]
        public void IgnoreQueryFilters_ShowsThem() => Assert.NotEmpty(Errors("M",
            "public static class C { public static async Task M(Shop db) { var r = await db.Orders.AsNoTracking().IgnoreQueryFilters().ToListAsync(); " +
            "Spec.Assert(Spec.Forall(0, r.Count, i => !r[i].IsDeleted)); } }"));

        [Fact]
        public void Single_ByKey_MatchesAtMostOne() => Assert.Empty(Errors("M",
            "public static class C { public static Customer? M(Shop db, int id) { return db.Customers.AsNoTracking().SingleOrDefault(c => c.Id == id); } }"));

        [Fact]
        public void Single_MayFindNone() => Assert.Equal(new[] { "CSV1001" }, Errors("M",
            "public static class C { public static Customer M(Shop db, int id) { return db.Customers.AsNoTracking().Single(c => c.Id == id); } }"));

        [Fact]
        public void Single_ByUniqueIndex_MatchesAtMostOne() => Assert.Empty(Errors("M",
            "public static class C { public static async Task<Customer?> M(Shop db, string email) { return await db.Customers.AsNoTracking().SingleOrDefaultAsync(c => c.Email == email); } }"));

        [Fact]
        public void Single_ByAnotherColumn_MayMatchMore() => Assert.Equal(new[] { "CSV1001" }, Errors("M",
            "public static class C { public static Customer? M(Shop db, string name) { return db.Customers.AsNoTracking().SingleOrDefault(c => c.Name == name); } }"));

        [Fact]
        public void Strings_AreComparedByTheDatabase() => Assert.NotEmpty(Errors("M",
            "public static class C { public static async Task M(Shop db, string email) { var c = await db.Customers.AsNoTracking().SingleOrDefaultAsync(c => c.Email == email); " +
            "if (c != null) Spec.Assert(c.Email == email); } }"));

        // ---- rows by their place: an order the database fixes (CSV1031) ----

        [Fact]
        public void First_WithoutOrder_IsReported() => Assert.Equal(new[] { "CSV1031" }, Errors("M",
            "public static class C { public static Order? M(Shop db) { return db.Orders.AsNoTracking().Where(o => o.Total > 0).FirstOrDefault(); } }"));

        [Fact]
        public void First_OrderedByAKey_IsDeterministic() => Assert.Empty(Errors("M",
            "public static class C { public static async Task<Order?> M(Shop db) { return await db.Orders.AsNoTracking().OrderBy(o => o.Total).ThenBy(o => o.Id).FirstOrDefaultAsync(); } }"));

        [Fact]
        public void First_OrderedByAColumn_IsReported() => Assert.Equal(new[] { "CSV1031" }, Errors("M",
            "public static class C { public static async Task<Order?> M(Shop db) { return await db.Orders.AsNoTracking().OrderBy(o => o.Total).FirstOrDefaultAsync(); } }"));

        [Fact]
        public void First_OfOneRow_NeedsNoOrder() => Assert.Empty(Errors("M",
            "public static class C { public static async Task<Customer?> M(Shop db, string email) { return await db.Customers.AsNoTracking().FirstOrDefaultAsync(c => c.Email == email); } }"));

        [Fact]
        public void Take_WithoutOrder_IsReported() => Assert.Equal(new[] { "CSV1031" }, Errors("M",
            "public static class C { public static async Task<List<Order>> M(Shop db) { return await db.Orders.AsNoTracking().Take(10).ToListAsync(); } }"));

        [Fact]
        public void Paging_ByKey_IsDeterministic() => Assert.Empty(Errors("M",
            "public static class C { public static async Task<List<Order>> M(Shop db, int page) { Spec.Requires(0 <= page && page < 1000); " +
            "return await db.Orders.AsNoTracking().OrderByDescending(o => o.Id).Skip(page * 10).Take(10).ToListAsync(); } }"));

        // ---- what EF translates (CSV1032) ----

        [Fact]
        public void Translate_ProgramMethodOnARow_IsReported() => Assert.Equal(new[] { "CSV1032" }, Errors("M",
            "public static class C { [Pure] static bool Big(Order o) => o.Total > 100; " +
            "public static async Task<int> M(Shop db) { return await db.Orders.CountAsync(o => Big(o)); } }"));

        [Fact]
        public void Translate_ProgramMethodOfCapturedValues_IsEvaluatedFirst() => Assert.Empty(Errors("M",
            "public static class C { [Pure] static int Limit(int x) => x * 2; " +
            "public static async Task<int> M(Shop db, int x) { Spec.Requires(0 <= x && x < 1000); return await db.Orders.CountAsync(o => o.Total > Limit(x)); } }"));

        [Fact]
        public void Translate_StringsAndLists_Translate() => Assert.Empty(Errors("M",
            "public static class C { public static async Task<int> M(Shop db, List<int> ids) { return await db.Customers.CountAsync(c => c.Name.StartsWith(\"A\") && ids.Contains(c.Id)); } }"));

        [Fact]
        public void Translate_ComputedProperty_IsReported() => Assert.Equal(new[] { "CSV1032" }, VerifyEf(Model +
            "public static class Extra { } public static class C { public static async Task<int> M(Shop db) { return await db.Customers.CountAsync(c => c.Display.Length > 3); } }" +
            "").Errors("M").Distinct().ToArray());

        // ---- navigations ----

        [Fact]
        public void Navigation_NotIncluded_IsNull() => Assert.Empty(Errors("M",
            "public static class C { public static async Task M(Shop db) { var r = await db.Orders.AsNoTracking().ToListAsync(); " +
            "Spec.Assert(Spec.Forall(0, r.Count, i => r[i].Customer == null)); } }"));

        [Fact]
        public void Navigation_Included_IsLoaded() => Assert.NotEmpty(Errors("M",
            "public static class C { public static async Task M(Shop db) { var r = await db.Orders.AsNoTracking().Include(o => o.Customer).ToListAsync(); " +
            "Spec.Assert(Spec.Forall(0, r.Count, i => r[i].Customer == null)); } }"));

        [Fact]
        public void Smoke_CompilesAndRuns() => Assert.NotNull(VerifyEf(Model +
            "public static class C { public static int M(Shop db) { return db.Orders.Where(o => o.Total > 0).Count(); } }").Methods);
    }
}
