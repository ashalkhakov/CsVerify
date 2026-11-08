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
    [System.ComponentModel.DataAnnotations.Timestamp] public byte[]? Version { get; set; }
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

        // ---- the change tracker (CSV1033) ----

        [Fact]
        public void Tracked_LoadChangeSave_Verifies() => Assert.Empty(Errors("M",
            "public static class C { public static async Task M(int id) { using var db = new Shop(); " +
            "var o = await db.Orders.FirstOrDefaultAsync(o => o.Id == id); if (o == null) return; o.Total = 5; await db.SaveChangesAsync(); } }"));

        [Fact]
        public void Attach_ToANewContext_Verifies() => Assert.Empty(Errors("M",
            "public static class C { public static void M() { using var db = new Shop(); db.Attach(new Order { Id = 1 }); } }"));

        [Fact]
        public void Attach_SameKeyTwice_IsReported() => Assert.Equal(new[] { "CSV1033" }, Errors("M",
            "public static class C { public static void M() { using var db = new Shop(); db.Attach(new Order { Id = 1 }); db.Attach(new Order { Id = 1 }); } }"));

        [Fact]
        public void Attach_ToAContextTrackingWhoKnowsWhat_IsReported() => Assert.Equal(new[] { "CSV1033" }, Errors("M",
            "public static class C { public static void M(Shop db) { db.Attach(new Order { Id = 1 }); } }"));

        [Fact]
        public void Add_WithAGeneratedKey_NeverClashes() => Assert.Empty(Errors("M",
            "public static class C { public static async Task M(Shop db) { db.Orders.Add(new Order { Total = 3 }); await db.SaveChangesAsync(); } }"));

        [Fact]
        public void Update_ALoadedGraph_IsReported() => Assert.Equal(new[] { "CSV1033" }, Errors("M",
            "public static class C { public static async Task M(int id) { using var db = new Shop(); " +
            "var o = await db.Orders.AsNoTracking().Include(x => x.Customer).FirstOrDefaultAsync(x => x.Id == id); if (o == null) return; " +
            "db.Update(o); await db.SaveChangesAsync(); } }"));

        [Fact]
        public void Update_ARowAlone_Verifies() => Assert.Empty(Errors("M",
            "public static class C { public static async Task M(int id) { using var db = new Shop(); " +
            "var o = await db.Orders.AsNoTracking().FirstOrDefaultAsync(x => x.Id == id); if (o == null) return; " +
            "db.Update(o); o.Total = 1; await db.SaveChangesAsync(); } }"));

        [Fact]
        public void AfterAFailedSave_TheContextIsDoneWith() => Assert.Equal(new[] { "CSV1033" }, Errors("M",
            "public static class C { public static async Task M(Shop db) { try { await db.SaveChangesAsync(); } catch (DbUpdateConcurrencyException) { await db.SaveChangesAsync(); } } }"));

        [Fact]
        public void ExecuteUpdate_ThenSavingAStaleCopy_IsReported() => Assert.Equal(new[] { "CSV1033" }, Errors("M",
            "public static class C { public static async Task M(int id) { using var db = new Shop(); " +
            "var o = await db.Orders.FirstOrDefaultAsync(x => x.Id == id); if (o == null) return; " +
            "await db.Orders.Where(x => x.Id == id).ExecuteUpdateAsync(s => s.SetProperty(x => x.Shipped, true)); o.Total = 2; await db.SaveChangesAsync(); } }"));

        [Fact]
        public void ExecuteUpdate_ThenReload_Verifies() => Assert.Empty(Errors("M",
            "public static class C { public static async Task M(int id) { using var db = new Shop(); " +
            "var o = await db.Orders.FirstOrDefaultAsync(x => x.Id == id); if (o == null) return; " +
            "await db.Orders.Where(x => x.Id == id).ExecuteUpdateAsync(s => s.SetProperty(x => x.Shipped, true)); await db.Entry(o).ReloadAsync(); o.Total = 2; await db.SaveChangesAsync(); } }"));

        // ---- concurrency tokens (CSV1034) ----

        [Fact]
        public void RowVersion_WrittenByTheProgram_IsReported() => Assert.Equal(new[] { "CSV1034" }, Errors("M",
            "public static class C { public static void M(Customer c) { c.Version = new byte[8]; } }"));

        [Fact]
        public void Token_ChangedBeforeUpdate_IsReported() => Assert.Equal(new[] { "CSV1034" }, Errors("M",
            "public static class C { public static async Task M(int id, System.DateTime now) { using var db = new Shop(); " +
            "var o = await db.Orders.AsNoTracking().FirstOrDefaultAsync(x => x.Id == id); if (o == null) return; " +
            "o.Updated = now; db.Update(o); await db.SaveChangesAsync(); } }"));

        [Fact]
        public void Token_ChangedAfterUpdate_Verifies() => Assert.Empty(Errors("M",
            "public static class C { public static async Task M(int id, System.DateTime now) { using var db = new Shop(); " +
            "var o = await db.Orders.AsNoTracking().FirstOrDefaultAsync(x => x.Id == id); if (o == null) return; " +
            "db.Update(o); o.Updated = now; await db.SaveChangesAsync(); } }"));

        // ---- transactions (CSV1035) ----

        [Fact]
        public void TwoSaves_OutsideATransaction_AreReported() => Assert.Equal(new[] { "CSV1035" }, Errors("M",
            "public static class C { public static async Task M() { using var db = new Shop(); db.Orders.Add(new Order()); await db.SaveChangesAsync(); " +
            "db.Orders.Add(new Order()); await db.SaveChangesAsync(); } }"));

        [Fact]
        public void TwoSaves_InOneTransaction_Verify() => Assert.Empty(Errors("M",
            "public static class C { public static async Task M() { using var db = new Shop(); await using var tx = await db.Database.BeginTransactionAsync(); " +
            "db.Orders.Add(new Order()); await db.SaveChangesAsync(); db.Orders.Add(new Order()); await db.SaveChangesAsync(); await tx.CommitAsync(); } }"));

        [Fact]
        public void BeginTransaction_WithOneOpen_IsReported() => Assert.Equal(new[] { "CSV1035" }, Errors("M",
            "public static class C { public static async Task M(Shop db) { await using var tx = await db.Database.BeginTransactionAsync(); await db.SaveChangesAsync(); await tx.CommitAsync(); } }"));

        [Fact]
        public void BeginTransaction_JoiningOneOpen_Verifies() => Assert.Empty(Errors("M",
            "public static class C { public static async Task M(Shop db) { " +
            "var own = db.Database.CurrentTransaction == null ? await db.Database.BeginTransactionAsync() : null; " +
            "await db.SaveChangesAsync(); if (own != null) { await own.CommitAsync(); await own.DisposeAsync(); } } }"));

        [Fact]
        public void Commit_WithChangesNotSaved_IsReported() => Assert.Equal(new[] { "CSV1035" }, Errors("M",
            "public static class C { public static async Task M() { using var db = new Shop(); await using var tx = await db.Database.BeginTransactionAsync(); " +
            "db.Orders.Add(new Order()); await tx.CommitAsync(); } }"));

        [Fact]
        public void Smoke_CompilesAndRuns() => Assert.NotNull(VerifyEf(Model +
            "public static class C { public static int M(Shop db) { return db.Orders.Where(o => o.Total > 0).Count(); } }").Methods);
    }
}
