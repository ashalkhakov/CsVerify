using System.Linq;
using Xunit;
using static CsVerify.Tests.EfHarness;

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
    public int? Rating { get; set; }
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

        private static string[] Errors(string method, string source, bool overflow = true) => VerifyEf(Model + source, overflow).Errors(method);

        private static void AssertNone(int which, string[] errors) => Assert.True(errors.Length == 0, $"case {which}: " + string.Join(", ", errors));

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
        public void First_GivesARowPassingItsPredicate() => Assert.Empty(Errors("M",
            "public static class C { public static async Task M(Shop db, int id) { var o = await db.Orders.AsNoTracking().FirstOrDefaultAsync(x => x.Id == id); " +
            "if (o != null) Spec.Assert(o.Id == id); var p = await db.Orders.AsNoTracking().OrderBy(x => x.Id).FirstOrDefaultAsync(x => !x.Shipped); if (p != null) Spec.Assert(!p.Shipped); } }"));

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
        public void First_OfAProjection_ByUniqueIndex_MatchesAtMostOne()
        {
            // (#110: Select gives one value per row, so a filter that keeps at most one row keeps at most one value)
            AssertNone(1, Errors("M",
                "public static class C { public static async Task<string?> M(Shop db, string email) => " +
                "await db.Customers.AsNoTracking().Where(c => c.Email == email).Select(c => c.Name).FirstOrDefaultAsync(); }"));
            AssertNone(2, Errors("M",
                "public static class C { public static async Task<int> M(Shop db, string email) => " +
                "await db.Customers.AsNoTracking().Where(c => c.Email == email).Select(c => c.Id).SingleOrDefaultAsync(); }"));
            AssertNone(3, Errors("M",
                "public static class C { public static async Task<int?> M(Shop db, string email) => " +
                "(await db.Customers.AsNoTracking().Where(c => c.Email == email).Select(c => new { c.Id }).FirstOrDefaultAsync())?.Id; }"));
            Assert.Equal(new[] { "CSV1031" }, Errors("M",
                "public static class C { public static async Task<string?> M(Shop db, string name) => " +
                "await db.Customers.AsNoTracking().Where(c => c.Name == name).Select(c => c.Email).FirstOrDefaultAsync(); }"));
        }

        private const string Identity = @"using Microsoft.AspNetCore.Identity;
using Microsoft.AspNetCore.Identity.EntityFrameworkCore;
public class AppUser : IdentityUser<long>
{
    public Guid ExternalId { get; set; }
}
public sealed class Users : IdentityDbContext<AppUser, IdentityRole<long>, long>
{
    protected override void OnModelCreating(ModelBuilder modelBuilder)
    {
        base.OnModelCreating(modelBuilder);
        modelBuilder.Entity<AppUser>().HasAlternateKey(u => u.ExternalId);
    }
}
";

        [Fact]
        public void AnIdentityUser_IsAnEntity_KeyedByItsId()
        {
            // (#113: what it inherits from Identity's IdentityUser<TKey> is read from its metadata; Users is its table)
            var r = VerifyEf(Identity + @"public static class Store
{
    public static async Task<AppUser?> ByKey(Users db, long id) => await db.Set<AppUser>().AsNoTracking().FirstOrDefaultAsync(u => u.Id == id);
    public static async Task<AppUser?> ByExternalId(Users db, Guid g) => await db.Users.AsNoTracking().FirstOrDefaultAsync(u => u.ExternalId == g);
    public static async Task<string?> NameOf(Users db, long id) => await db.Users.AsNoTracking().Where(u => u.Id == id).Select(u => u.UserName).FirstOrDefaultAsync();
    public static async Task<AppUser?> ByName(Users db, string name) => await db.Users.AsNoTracking().FirstOrDefaultAsync(u => u.Email == name);
}");
            foreach (var m in new[] { "ByKey", "ByExternalId", "NameOf" })
            {
                Assert.True(r.Errors(m).Length == 0, r.Explain(m));
            }
            Assert.Equal(new[] { "CSV1031" }, r.Errors("ByName"));
        }

        [Fact]
        public void AnIdentityUser_HasIdentitysIndexAndToken()
        {
            // (the Spec library's model of Identity's OnModelCreating: NormalizedUserName unique, ConcurrencyStamp a token)
            var r = VerifyEf(Identity + @"public static class Store
{
    public static async Task<AppUser?> ByName(Users db, string name) => await db.Users.AsNoTracking().FirstOrDefaultAsync(u => u.NormalizedUserName == name);
    public static async Task Stamp(long id)
    {
        using var db = new Users();
        var u = await db.Users.AsNoTracking().FirstOrDefaultAsync(x => x.Id == id);
        if (u == null) return;
        u.ConcurrencyStamp = ""new"";
        db.Update(u);
        await db.SaveChangesAsync();
    }
}");
            Assert.True(r.Errors("ByName").Length == 0, r.Explain("ByName"));
            Assert.Equal(new[] { "CSV1034" }, r.Errors("Stamp"));
        }

        [Fact]
        public void AnEntityALibrarysContextConfigures_WithoutAModel_IsReadNoFurther()
        {
            // (a library context's OnModelCreating, of no model of the Spec library's: its key and tokens unknown)
            var r = EfHarness.VerifyEfWithContextLibrary(@"namespace Lib
{
    public class Member { public long Id { get; set; } public string Name { get; set; } = """"; }
    public class Members<TMember> : DbContext where TMember : Member
    {
        public DbSet<TMember> All { get; set; } = null!;
        protected override void OnModelCreating(ModelBuilder modelBuilder) => modelBuilder.Entity<TMember>().HasKey(m => m.Name);
    }
}", @"public sealed class Mine : Lib.Member { }
public sealed class Club : Lib.Members<Mine> { }
public static class Store
{
    public static async Task<Mine?> ById(Club db, long id) => await db.All.AsNoTracking().FirstOrDefaultAsync(m => m.Id == id);
    public static async Task Attach(Mine m) { using var db = new Club(); db.Attach(m); await db.SaveChangesAsync(); }
}", sources: false);
            Assert.Equal(new[] { "CSV1031" }, r.Errors("ById"));
            Assert.Contains(r["Attach"].Diagnostics, d => d.Id == "CSV1902" && d.Message.Contains("a library's OnModelCreating configures it"));
        }

        [Fact]
        public void Single_ByAnotherColumn_MayMatchMore() => Assert.Equal(new[] { "CSV1001" }, Errors("M",
            "public static class C { public static Customer? M(Shop db, string name) { return db.Customers.AsNoTracking().SingleOrDefault(c => c.Name == name); } }"));

        [Fact]
        public void Strings_AreComparedByTheDatabase() => Assert.NotEmpty(Errors("M",
            "public static class C { public static async Task M(Shop db, string email) { var c = await db.Customers.AsNoTracking().SingleOrDefaultAsync(c => c.Email == email); " +
            "if (c != null) Spec.Assert(c.Email == email); } }"));

        private const string OnSqlite = "public static class Configure { public static void Sqlite(DbContextOptionsBuilder o) => o.UseSqlite(\"Data Source=shop.db\"); }\n";

        [Fact]
        public void Strings_OnSqlite_AreComparedExactly() => Assert.Empty(VerifyEf(Model + OnSqlite +
            "public static class C { public static async Task M(Shop db, string email) { var c = await db.Customers.AsNoTracking().SingleOrDefaultAsync(c => c.Email == email); " +
            "if (c != null) Spec.Assert(c.Email == email); } }", sqlite: true).Errors("M"));

        [Fact]
        public void Strings_OnSqlite_WithACollation_AreNot() => Assert.NotEmpty(VerifyEf(Model + OnSqlite +
            "public static class Collated { public static void Configure(ModelBuilder b) => b.UseCollation(\"NOCASE\"); }\n" +
            "public static class C { public static async Task M(Shop db, string email) { var c = await db.Customers.AsNoTracking().SingleOrDefaultAsync(c => c.Email == email); " +
            "if (c != null) Spec.Assert(c.Email == email); } }", sqlite: true).Errors("M"));

        // ---- joins ----

        [Fact]
        public void Join_OnAKey_MatchesEqualKeys() => Assert.Empty(Errors("M",
            "public static class C { public static async Task M(Shop db) { var r = await db.Orders.AsNoTracking().Join(db.Customers.AsNoTracking(), o => o.CustomerId, c => c.Id, " +
            "(o, c) => new { o.CustomerId, CustomerKey = c.Id, o.Total }).Where(x => x.Total > 5).ToListAsync(); " +
            "Spec.Assert(Spec.Forall(0, r.Count, i => r[i].CustomerId == r[i].CustomerKey && r[i].Total > 5)); } }"));

        [Fact]
        public void Join_InQuerySyntax_MatchesEqualKeys() => Assert.Empty(Errors("M",
            "public static class C { public static async Task M(Shop db) { var r = await (from o in db.Orders.AsNoTracking() join c in db.Customers.AsNoTracking() on o.CustomerId equals c.Id " +
            "where !o.Shipped select new { o.Shipped, o.CustomerId, CustomerKey = c.Id }).ToListAsync(); " +
            "Spec.Assert(Spec.Forall(0, r.Count, i => r[i].CustomerId == r[i].CustomerKey && !r[i].Shipped)); } }"));

        [Fact]
        public void Join_OnKeys_SingleMatchesAtMostOne() => Assert.Empty(Errors("M",
            "public static class C { public static async Task<int> M(Shop db, int id) { var row = await db.Orders.AsNoTracking().Where(o => o.Id == id)" +
            ".Join(db.Customers.AsNoTracking(), o => o.CustomerId, c => c.Id, (o, c) => new { Order = o, Customer = c }).SingleOrDefaultAsync(); " +
            "if (row != null) Spec.Assert(row.Customer.Id == row.Order.CustomerId && row.Order.Id == id); return 0; } }"));

        [Fact]
        public void Join_SaysNothingElse() => Assert.NotEmpty(Errors("M",
            "public static class C { public static async Task M(Shop db) { var r = await db.Orders.AsNoTracking().Join(db.Customers.AsNoTracking(), o => o.CustomerId, c => c.Id, " +
            "(o, c) => new { o.Total, CustomerKey = c.Id }).ToListAsync(); Spec.Assert(Spec.Forall(0, r.Count, i => r[i].Total == r[i].CustomerKey)); } }"));

        [Fact]
        public void Join_CountIsNotNegative() => Assert.Empty(Errors("M",
            "public static class C { public static int M(Shop db) { Spec.Ensures<int>(r => r >= 0); " +
            "return db.Orders.Join(db.Customers, o => o.CustomerId, c => c.Id, (o, c) => o.Total).Count(); } }"));

        [Fact]
        public void LeftJoin_MatchesEqualKeys_OrNone() => Assert.Empty(Errors("M",
            "public static class C { public static async Task M(Shop db) { var r = await db.Orders.AsNoTracking().LeftJoin(db.Customers.AsNoTracking(), o => o.CustomerId, c => c.Id, " +
            "(o, c) => new { o.CustomerId, Found = c != null, CustomerKey = c == null ? 0 : c.Id }).ToListAsync(); " +
            "Spec.Assert(Spec.Forall(0, r.Count, i => !r[i].Found || r[i].CustomerId == r[i].CustomerKey)); } }"));

        [Fact]
        public void RightJoin_IsNotRead() => Assert.NotEmpty(Errors("M", // (EF Core filters the left side after the join)
            "public static class C { public static async Task M(Shop db) { var r = await db.Orders.AsNoTracking().RightJoin(db.Customers.AsNoTracking(), o => o.CustomerId, c => c.Id, " +
            "(o, c) => new { OrderCustomer = o == null ? -1 : o.CustomerId, c.Id }).ToListAsync(); " +
            "Spec.Assert(Spec.Forall(0, r.Count, i => r[i].OrderCustomer == -1 || r[i].OrderCustomer == r[i].Id)); } }"));

        [Fact]
        public void LeftJoin_IsInNoOrder() => Assert.NotEmpty(Errors("M",
            "public static class C { public static async Task M(Shop db) { var r = await db.Orders.AsNoTracking().LeftJoin(db.Customers.AsNoTracking(), o => o.CustomerId, c => c.Id, " +
            "(o, c) => c != null).ToListAsync(); Spec.Assert(r.Count == 0 || r[0] || !r.Contains(true)); } }"));

        [Fact]
        public void Join_OnANullableKey_MatchesEqualValues() => Assert.Empty(Errors("M",
            "public static class C { public static async Task M(Shop db) { var r = await db.Orders.AsNoTracking().Join(db.Customers.AsNoTracking(), o => (int?)o.CustomerId, c => (int?)c.Id, " +
            "(o, c) => new { o.CustomerId, CustomerKey = c.Id }).ToListAsync(); Spec.Assert(Spec.Forall(0, r.Count, i => r[i].CustomerId == r[i].CustomerKey)); } }"));

        [Fact]
        public void Join_OnANullKey_MatchesNothing() => Assert.Empty(Errors("M",
            "public static class C { public static async Task M(Shop db) { var r = await db.Orders.AsNoTracking().Join(db.Customers.AsNoTracking(), o => o.Total > 5 ? (int?)o.CustomerId : null, c => (int?)c.Id, " +
            "(o, c) => o.Total).ToListAsync(); Spec.Assert(Spec.Forall(0, r.Count, i => r[i] > 5)); } }"));

        [Fact]
        public void Join_OnStrings_OnSqlite_MatchesEqualStrings() => Assert.Empty(VerifyEf(Model + OnSqlite +
            "public static class C { public static async Task M(Shop db) { var r = await db.Customers.AsNoTracking().Join(db.Customers.AsNoTracking(), a => a.Name, b => b.Email, " +
            "(a, b) => new { a.Name, b.Email }).ToListAsync(); Spec.Assert(Spec.Forall(0, r.Count, i => r[i].Name == r[i].Email)); } }", sqlite: true).Errors("M"));

        [Fact]
        public void Join_OnStrings_ComparesByCollation() => Assert.NotEmpty(Errors("M",
            "public static class C { public static async Task M(Shop db) { var r = await db.Customers.AsNoTracking().Join(db.Customers.AsNoTracking(), a => a.Name, b => b.Email, " +
            "(a, b) => new { a.Name, b.Email }).ToListAsync(); Spec.Assert(Spec.Forall(0, r.Count, i => r[i].Name == r[i].Email)); } }"));

        // ---- nulls ----

        private const string RelationalNulls =
            "public static class Options { public static void Relational<B, E>(Microsoft.EntityFrameworkCore.Infrastructure.RelationalDbContextOptionsBuilder<B, E> x) " +
            "where B : Microsoft.EntityFrameworkCore.Infrastructure.RelationalDbContextOptionsBuilder<B, E> where E : Microsoft.EntityFrameworkCore.Infrastructure.RelationalOptionsExtension, new() " +
            "=> x.UseRelationalNulls(); }\n";

        private const string EitherRating = "public static class C { public static bool M(Shop db) { Spec.Ensures<bool>(r => r); return db.Orders.All(o => o.Rating != 3 || o.Rating == 3); } }";

        [Fact]
        public void Nulls_ByDefault_CompareAsInCSharp() => Assert.Empty(Errors("M", EitherRating));

        [Fact]
        public void Nulls_Relational_AComparisonWithNullIsUnknown() => Assert.NotEmpty(Errors("M", RelationalNulls + EitherRating));

        [Fact]
        public void Nulls_Relational_WhatHasNoNullIsAsBefore() => Assert.Empty(Errors("M", RelationalNulls +
            "public static class C { public static async Task M(Shop db) { var r = await db.Orders.AsNoTracking().Where(o => o.Rating != 3 && o.Total > 5).ToListAsync(); " +
            "Spec.Assert(Spec.Forall(0, r.Count, i => r[i].Total > 5 && r[i].Rating != 3)); } }"));

        // (objects: a navigation that may be null compared with another is SQL's unknown there; with the literal null, IS NULL)
        private const string EitherCustomer = "public static class C { public static bool M(Shop db, Customer c) { Spec.Requires(c != null); Spec.Ensures<bool>(r => r); return db.Orders.All(o => o.Customer != c || o.Customer == c); } }";

        [Fact]
        public void Nulls_Relational_ObjectsComparedAreUnknownWhereNull() => Assert.Equal(new[] { "CSV1002" }, Errors("M", RelationalNulls + EitherCustomer));

        [Fact]
        public void Nulls_ByDefault_ObjectsCompareAsInCSharp() => Assert.Empty(Errors("M", EitherCustomer));

        [Fact]
        public void Nulls_Relational_IsNullIsExact() => Assert.Empty(Errors("M", RelationalNulls +
            "public static class C { public static bool M(Shop db) { Spec.Ensures<bool>(r => r); return db.Orders.All(o => o.Customer == null || o.Customer != null); } }"));

        // ---- what compares values: groups, Distinct, set operators ----

        [Fact]
        public void Contains_OnKeys_IsRead() => Assert.Empty(Errors("M",
            "public static class C { public static bool M(Shop db) { Spec.Ensures<bool>(r => !r); return db.Orders.Where(o => o.Total > 5).Select(o => o.Total).Contains(3); } }"));

        [Fact]
        public void Distinct_OnKeys_IsRead() => Assert.Empty(Errors("M",
            "public static class C { public static async Task M(Shop db) { var r = await db.Orders.Where(o => o.Total > 5).Select(o => o.Total).Distinct().ToListAsync(); " +
            "Spec.Assert(Spec.Forall(0, r.Count, i => r[i] > 5)); } }"));

        [Fact]
        public void Distinct_OnStrings_ComparesByCollation() => Assert.NotEmpty(Errors("M",
            "public static class C { public static async Task M(Shop db) { var r = await db.Customers.Where(c => c.Id > 5).Select(c => c.Name).Distinct().ToListAsync(); " +
            "Spec.Assert(Spec.Forall(0, r.Count, i => r[i] != null)); } }"));

        [Fact]
        public void GroupBy_OnKeys_GivesGroupsOfThatKey() => Assert.Empty(Errors("M",
            "public static class C { public static async Task M(Shop db) { var r = await db.Orders.AsNoTracking().GroupBy(o => o.CustomerId).Select(g => new { g.Key, N = g.Count() }).ToListAsync(); " +
            "Spec.Assert(Spec.Forall(0, r.Count, i => r[i].N > 0)); } }"));

        [Fact]
        public void GroupJoin_OnKeys_GivesTheMatches() => Assert.Empty(Errors("M",
            "public static class C { public static async Task M(Shop db) { var r = await db.Customers.AsNoTracking().GroupJoin(db.Orders, c => c.Id, o => o.CustomerId, (c, os) => new { c.Id, N = os.Count() }).ToListAsync(); " +
            "Spec.Assert(Spec.Forall(0, r.Count, i => r[i].N >= 0)); } }"));

        [Fact]
        public void Union_IsInNoOrder() => Assert.NotEmpty(Errors("M",
            "public static class C { public static async Task M(Shop db) { var r = await db.Orders.Select(o => o.Id).Union(db.Customers.Select(c => c.Id)).ToListAsync(); " +
            "var o0 = await db.Orders.Select(o => o.Id).ToListAsync(); Spec.Assert(r.Count == 0 || o0.Count == 0 || r[0] == o0[0]); } }"));

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
        public void Include_GivesTheRowTheForeignKeyNames() => Assert.Empty(Errors("M",
            "public static class C { public static async Task M(Shop db) { var r = await db.Orders.AsNoTracking().Include(o => o.Customer).ToListAsync(); " +
            "Spec.Assert(Spec.Forall(0, r.Count, i => r[i].Customer != null && r[i].Customer!.Id == r[i].CustomerId)); } }"));

        [Fact]
        public void Include_ACollection_HoldsTheRowsWithThisKey() => Assert.Empty(Errors("M",
            "public static class C { public static async Task M(Shop db) { var r = await db.Customers.AsNoTracking().Include(c => c.Orders).ToListAsync(); " +
            "Spec.Assert(Spec.Forall(0, r.Count, i => Spec.Forall(0, r[i].Orders.Count, j => r[i].Orders[j].CustomerId == r[i].Id && !r[i].Orders[j].IsDeleted))); } }"));

        [Fact]
        public void Collection_NotIncluded_IsAsItsInitializerMadeIt() => Assert.Empty(Errors("M",
            "public static class C { public static async Task M(Shop db) { var r = await db.Customers.AsNoTracking().ToListAsync(); " +
            "Spec.Assert(Spec.Forall(0, r.Count, i => r[i].Orders.Count == 0)); } }"));

        [Fact]
        public void NavigationFacts_LeaveTheRowsAsMany() => Assert.NotEmpty(Errors("M", // (they don't contradict each other: any number of rows)
            "public static class C { public static async Task M(Shop db) { var r = await db.Customers.AsNoTracking().Include(c => c.Orders).ToListAsync(); " +
            "var s = await db.Customers.AsNoTracking().ToListAsync(); var o = await db.Orders.AsNoTracking().Include(x => x.Customer).ToListAsync(); " +
            "Spec.Assert(r.Count <= 1 || s.Count <= 1 || o.Count <= 1); } }"));

        private const string People =
            "public sealed class Addr { public string City { get; set; } = \"\"; }\n" +
            "[Microsoft.EntityFrameworkCore.Owned] public sealed class Phone { public string Number { get; set; } = \"\"; }\n" +
            "public sealed class Person { public int Id { get; set; } public Addr Home { get; set; } = new Addr(); public Phone? Phone { get; set; } }\n" +
            "public sealed class People : DbContext { public DbSet<Person> All => Set<Person>(); protected override void OnModelCreating(ModelBuilder b) { b.Entity<Person>().OwnsOne(p => p.Home); } }\n";

        [Fact]
        public void Owned_IsLoadedWithItsOwner_NotSaidNull() => Assert.NotEmpty(Errors("M", People +
            "public static class C { public static async Task M(People db) { var r = await db.All.AsNoTracking().ToListAsync(); Spec.Assert(Spec.Forall(0, r.Count, i => r[i].Home == null)); } }"));

        [Fact]
        public void Owned_ByItsAttribute_NotSaidNull() => Assert.NotEmpty(Errors("M", People +
            "public static class C { public static async Task M(People db) { var r = await db.All.AsNoTracking().ToListAsync(); Spec.Assert(Spec.Forall(0, r.Count, i => r[i].Phone == null)); } }"));

        private const string Store =
            "public sealed class Prod { public int Id { get; set; } public string Name { get; set; } = \"\"; public List<Ord> Ords { get; set; } = new List<Ord>(); }\n" +
            "public sealed class Ln { public int Id { get; set; } public int OrdId { get; set; } public int ProdId { get; set; } public Prod? Prod { get; set; } }\n" +
            "public sealed class Ord { public int Id { get; set; } public int? FeaturedId { get; set; } public Prod? Featured { get; set; } public List<Ln> Lns { get; set; } = new List<Ln>(); }\n" +
            "public sealed class Store : DbContext { public DbSet<Ord> Ords => Set<Ord>(); public DbSet<Ln> Lns => Set<Ln>(); public DbSet<Prod> Prods => Set<Prod>(); }\n";

        [Fact]
        public void ThenInclude_LoadsTheNextLevel() => Assert.Empty(Errors("M", Store +
            "public static class C { public static async Task M(Store db) { var r = await db.Ords.AsNoTracking().Include(o => o.Lns).ThenInclude(l => l.Prod).ToListAsync(); " +
            "Spec.Assert(Spec.Forall(0, r.Count, i => Spec.Forall(0, r[i].Lns.Count, j => r[i].Lns[j].OrdId == r[i].Id && r[i].Lns[j].Prod != null && r[i].Lns[j].Prod!.Id == r[i].Lns[j].ProdId))); } }"));

        private const string Interfaces =
            "public sealed class Item { public int Id { get; set; } public int BagId { get; set; } public int ShelfId { get; set; } }\n" +
            "public sealed class Bag { public int Id { get; set; } public ICollection<Item> Items { get; set; } = new List<Item>(); }\n" +
            "public sealed class Shelf { public int Id { get; set; } public IList<Item> Items { get; set; } = null!; }\n" +
            "public sealed class Room : DbContext { public DbSet<Bag> Bags => Set<Bag>(); public DbSet<Shelf> Shelves => Set<Shelf>(); public DbSet<Item> Items => Set<Item>(); }\n";

        private const string Posts =
            "public sealed class Tag { public int Id { get; set; } public int PostId { get; set; } public bool Hidden { get; set; } }\n" +
            "public sealed class Post { public int Id { get; set; } public HashSet<Tag> Tags { get; set; } = new HashSet<Tag>(); }\n" +
            "public sealed class Blog : DbContext { public DbSet<Post> Posts => Set<Post>(); public DbSet<Tag> Tags => Set<Tag>(); " +
            "protected override void OnModelCreating(ModelBuilder b) { b.Entity<Tag>().HasQueryFilter(t => !t.Hidden); } }\n";

        [Fact]
        public void Include_AHashSet_HoldsTheRowsWithThisKey() => Assert.Empty(Errors("M", Posts +
            "public static class C { public static async Task M(Blog db) { var r = await db.Posts.AsNoTracking().Include(p => p.Tags).ToListAsync(); " +
            "if (r.Count == 0) return; var p = r[0]; foreach (var t in p.Tags) Spec.Assert(t.PostId == p.Id && !t.Hidden); } }"));

        [Fact]
        public void Collection_AHashSetNotIncluded_IsEmpty() => Assert.Empty(Errors("M", Posts +
            "public static class C { public static async Task M(Blog db) { var r = await db.Posts.AsNoTracking().ToListAsync(); Spec.Assert(Spec.Forall(0, r.Count, i => r[i].Tags.Count == 0)); } }"));

        [Fact]
        public void Include_AHashSet_SaysNothingElse() => Assert.NotEmpty(Errors("M", Posts +
            "public static class C { public static async Task M(Blog db) { var r = await db.Posts.AsNoTracking().Include(p => p.Tags).ToListAsync(); " +
            "if (r.Count == 0) return; var p = r[0]; foreach (var t in p.Tags) Spec.Assert(t.Id == p.Id); } }"));

        private const string Notes =
            "public sealed class Note { public int Id { get; set; } public int TagId { get; set; } }\n" +
            "public sealed class Tag { public int Id { get; set; } public int PostId { get; set; } public HashSet<Note> Notes { get; set; } = new HashSet<Note>(); }\n" +
            "public sealed class Post { public int Id { get; set; } public HashSet<Tag> Tags { get; set; } = new HashSet<Tag>(); }\n" +
            "public sealed class Blog : DbContext { public DbSet<Post> Posts => Set<Post>(); public DbSet<Tag> Tags => Set<Tag>(); public DbSet<Note> Notes => Set<Note>(); }\n";

        // (a set under a set: each note is its own tag's, not one the inner set's variable stands for)
        [Fact]
        public void ThenInclude_AHashSetUnderAHashSet_HoldsTheRowsWithItsParentsKey() => Assert.Empty(Errors("M", Notes +
            "public static class C { public static async Task M(Blog db) { var r = await db.Posts.AsNoTracking().Include(p => p.Tags).ThenInclude(t => t.Notes).ToListAsync(); " +
            "if (r.Count == 0) return; var p = r[0]; foreach (var t in p.Tags) { foreach (var n in t.Notes) Spec.Assert(n.TagId == t.Id); } } }"));

        [Fact]
        public void Include_AnIList_HoldsTheRowsWithThisKey() => Assert.Empty(Errors("M", Interfaces +
            "public static class C { public static async Task M(Room db) { var r = await db.Shelves.AsNoTracking().Include(b => b.Items).ToListAsync(); " +
            "if (r.Count == 0) return; var s = r[0]; var items = s.Items; if (items.Count == 0) return; var it = items[0]; Spec.Assert(it.ShelfId == s.Id); } }"));

        [Fact]
        public void Collection_AnICollectionNotIncluded_IsEmpty() => Assert.Empty(Errors("M", Interfaces +
            "public static class C { public static async Task M(Room db) { var r = await db.Bags.AsNoTracking().ToListAsync(); Spec.Assert(Spec.Forall(0, r.Count, i => r[i].Items.Count == 0)); } }"));

        [Fact]
        public void ThenInclude_Tracked_ACollectionBelow_HoldsTheRowsWithItsKey() => Assert.Empty(Errors("M", Store +
            "public static class C { public static void M() { using var db = new Store(); var r = db.Ords.Include(o => o.Featured).ThenInclude(p => p!.Ords).ToList(); " +
            "Spec.Assert(r.Count == 0 || r[0].Featured == null || r[0].Featured!.Ords.Count == 0 || r[0].Featured!.Ords[0].FeaturedId == r[0].Featured!.Id); } }"));

        [Fact]
        public void Navigation_ToATypeAPathLoads_IsNotSaidNull() => Assert.NotEmpty(Errors("M", Store +
            "public static class C { public static async Task M(Store db) { var r = await db.Ords.AsNoTracking().Include(o => o.Lns).ThenInclude(l => l.Prod).ToListAsync(); " +
            "Spec.Assert(Spec.Forall(0, r.Count, i => r[i].Featured == null)); } }"));

        [Fact]
        public void Navigation_ToATypeNoPathLoads_IsNull() => Assert.Empty(Errors("M", Store +
            "public static class C { public static async Task M(Store db) { var r = await db.Ords.AsNoTracking().Include(o => o.Lns).ToListAsync(); " +
            "Spec.Assert(Spec.Forall(0, r.Count, i => r[i].Featured == null)); } }"));

        [Fact]
        public void Include_Tracked_IsTheRowTheForeignKeyNames() => Assert.Empty(Errors("M",
            "public static class C { public static async Task M() { using var db = new Shop(); var r = await db.Orders.Include(o => o.Customer).ToListAsync(); " +
            "Spec.Assert(Spec.Forall(0, r.Count, i => r[i].Customer == null || r[i].Customer!.Id == r[i].CustomerId)); } }"));

        [Fact]
        public void ThenInclude_Tracked_OnANewContext_LoadsTheNextLevel() => Assert.Empty(Errors("M", Store +
            "public static class C { public static void M() { using var db = new Store(); var r = db.Ords.Include(o => o.Lns).ThenInclude(l => l.Prod).ToList(); " +
            "Spec.Assert(Spec.Forall(0, r.Count, i => Spec.Forall(0, r[i].Lns.Count, j => r[i].Lns[j].OrdId == r[i].Id && r[i].Lns[j].Prod != null && r[i].Lns[j].Prod!.Id == r[i].Lns[j].ProdId))); } }"));

        [Fact]
        public void ThenInclude_Tracked_AfterTheContextTrackedSome_SaysNothing() => Assert.NotEmpty(Errors("M", Store +
            "public static class C { public static async Task M() { using var db = new Store(); var p = await db.Prods.ToListAsync(); var r = await db.Ords.Include(o => o.Lns).ThenInclude(l => l.Prod).ToListAsync(); " +
            "Spec.Assert(Spec.Forall(0, r.Count, i => Spec.Forall(0, r[i].Lns.Count, j => r[i].Lns[j].OrdId == r[i].Id && r[i].Lns[j].Prod != null && r[i].Lns[j].Prod!.Id == r[i].Lns[j].ProdId))); } }"));

        [Fact]
        public void Include_Tracked_WhatItLoadsIsTrackedAfter() => Assert.NotEmpty(Errors("M", Store +
            "public static class C { public static async Task M() { using var db = new Store(); var os = await db.Ords.Include(o => o.Lns).ToListAsync(); " +
            "var r = await db.Lns.Where(l => l.ProdId > 5).ToListAsync(); Spec.Assert(Spec.Forall(0, r.Count, i => r[i].ProdId > 5)); } }"));

        [Fact]
        public void Include_Tracked_InAContextPassedIn_SaysNothing() => Assert.NotEmpty(Errors("M",
            "public static class C { public static async Task M(Shop db) { var r = await db.Orders.Include(o => o.Customer).ToListAsync(); " +
            "Spec.Assert(Spec.Forall(0, r.Count, i => r[i].Customer == null || r[i].Customer!.Id == r[i].CustomerId)); } }"));

        [Fact]
        public void Include_ByName_SaysNothing() => Assert.NotEmpty(Errors("M",
            "public static class C { public static async Task M(Shop db) { var r = await db.Orders.AsNoTracking().Include(\"Customer\").ToListAsync(); " +
            "Spec.Assert(Spec.Forall(0, r.Count, i => r[i].Customer == null)); } }"));

        [Fact]
        public void IdentityResolution_SaysNothingOfNavigations() => Assert.NotEmpty(Errors("M",
            "public static class C { public static async Task M(Shop db) { var r = await db.Orders.AsNoTrackingWithIdentityResolution().ToListAsync(); " +
            "Spec.Assert(Spec.Forall(0, r.Count, i => r[i].Customer == null)); } }"));

        [Fact]
        public void Include_ACycleWithoutTracking_IsReported() => Assert.Equal(new[] { "CSV1032" }, Errors("M",
            "public static class C { public static async Task<int> M(Shop db) { var r = await db.Orders.AsNoTracking().Include(o => o.Customer).ThenInclude(c => c!.Orders).ToListAsync(); return r.Count; } }"));

        [Fact]
        public void Include_ACycleTracked_IsNot() => Assert.Empty(Errors("M",
            "public static class C { public static async Task<int> M(Shop db) { var r = await db.Orders.Include(o => o.Customer).ThenInclude(c => c!.Orders).ToListAsync(); return r.Count; } }"));

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
        public void Token_EachOfTwo_IsFollowed() => Assert.Equal(new[] { "CSV1034" }, Errors("M",
            "public sealed class Doc { public int Id { get; set; } [System.ComponentModel.DataAnnotations.ConcurrencyCheck] public int A { get; set; } " +
            "[System.ComponentModel.DataAnnotations.ConcurrencyCheck] public int B { get; set; } }\n" +
            "public sealed class Docs : DbContext { public DbSet<Doc> All => Set<Doc>(); }\n" +
            "public static class C { public static async Task M(int id) { using var db = new Docs(); var d = await db.All.AsNoTracking().FirstOrDefaultAsync(x => x.Id == id); if (d == null) return; " +
            "d.B = 5; db.Update(d); await db.SaveChangesAsync(); } }"));

        [Fact]
        public void Token_ChangedAfterUpdate_Verifies() => Assert.Empty(Errors("M",
            "public static class C { public static async Task M(int id, System.DateTime now) { using var db = new Shop(); " +
            "var o = await db.Orders.AsNoTracking().FirstOrDefaultAsync(x => x.Id == id); if (o == null) return; " +
            "db.Update(o); o.Updated = now; await db.SaveChangesAsync(); } }"));

        [Fact]
        public void Token_AwaitBetweenReadAndUpdate_Verifies() => Assert.Empty(Errors("M",
            "public static class C { public static async Task M(int id, System.DateTime now) { using var db = new Shop(); " +
            "var o = await db.Orders.AsNoTracking().FirstOrDefaultAsync(x => x.Id == id); if (o == null) return; " +
            "await using var tx = await db.Database.BeginTransactionAsync(); db.Update(o); o.Updated = now; await db.SaveChangesAsync(); await tx.CommitAsync(); } }"));

        [Fact]
        public void Token_AwaitAfterTheEntityWentOut_IsReported() => Assert.Contains("CSV1034", Errors("M",
            "public static class C { public static Order? Last; public static async Task M(int id) { using var db = new Shop(); " +
            "var o = await db.Orders.AsNoTracking().FirstOrDefaultAsync(x => x.Id == id); if (o == null) return; Last = o; " +
            "await using var tx = await db.Database.BeginTransactionAsync(); db.Update(o); await db.SaveChangesAsync(); await tx.CommitAsync(); } }"));

        [Fact]
        public void Unshared_ColumnsKeptAcrossAwait() => Assert.Empty(Errors("M",
            "public static class C { public static async Task M(int id) { using var db = new Shop(); " +
            "var o = await db.Orders.AsNoTracking().FirstOrDefaultAsync(x => x.Id == id); if (o == null) return; var t = o.Total; " +
            "await db.Customers.CountAsync(); Spec.Assert(o.Total == t); } }"));

        [Fact]
        public void Unshared_LetOut_ColumnsForgottenAcrossAwait() => Assert.NotEmpty(Errors("M",
            "public static class C { public static void Keep(Order o) { } public static async Task M(int id) { using var db = new Shop(); " +
            "var o = await db.Orders.AsNoTracking().FirstOrDefaultAsync(x => x.Id == id); if (o == null) return; var t = o.Total; Keep(o); " +
            "await db.Customers.CountAsync(); Spec.Assert(o.Total == t); } }"));

        [Fact]
        public void RowVersion_SetByTheDatabaseOnSave() => Assert.NotEmpty(Errors("M",
            "public static class C { public static async Task M(int id) { using var db = new Shop(); " +
            "var c = await db.Customers.AsNoTracking().FirstOrDefaultAsync(x => x.Id == id); if (c == null) return; var v = c.Version; " +
            "db.Entry(c).State = EntityState.Modified; await db.SaveChangesAsync(); Spec.Assert(c.Version == v); } }"));

        // ---- Find ----

        private const string Lines =
            "public sealed class Line { public int OrderId { get; set; } public int No { get; set; } public int Qty { get; set; } }\n" +
            "public sealed class LineShop : DbContext { public DbSet<Line> Lines => Set<Line>(); " +
            "protected override void OnModelCreating(ModelBuilder b) { b.Entity<Line>().HasKey(l => new { l.OrderId, l.No }); } }\n";

        [Fact]
        public void Find_ByAKey_GivesItsRow() => Assert.Empty(Errors("M",
            "public static class C { public static void M(Shop db, int id) { var o = db.Orders.Find(id); if (o != null) Spec.Assert(o.Id == id); } }"));

        [Fact]
        public void Find_ByACompositeKey_InTheKeysOrder() => Assert.Empty(Errors("M", Lines +
            "public static class C { public static void M(LineShop db, int order, int no) { var l = db.Lines.Find(order, no); if (l != null) Spec.Assert(l.OrderId == order && l.No == no); } }"));

        [Fact]
        public void Find_ByACompositeKey_NotInAnotherOrder() => Assert.NotEmpty(Errors("M", Lines +
            "public static class C { public static void M(LineShop db, int order, int no) { var l = db.Lines.Find(no, order); if (l != null) Spec.Assert(l.OrderId == order); } }"));

        // ---- inheritance ----

        private const string Zoo =
            "public abstract class Animal { public int Id { get; set; } public string Name { get; set; } = \"\"; public bool Gone { get; set; } }\n" +
            "public sealed class Dog : Animal { public int Barks { get; set; } }\n" +
            "public sealed class Cat : Animal { public int Lives { get; set; } }\n" +
            "public sealed class ZooDb : DbContext { public DbSet<Animal> Animals => Set<Animal>(); " +
            "protected override void OnModelCreating(ModelBuilder b) { b.Entity<Dog>(); b.Entity<Cat>(); b.Entity<Animal>().HasQueryFilter(a => !a.Gone).HasIndex(a => a.Name).IsUnique(); } }\n";

        [Fact]
        public void Inheritance_ADerivedType_HasItsRootsKey() => Assert.Empty(Errors("M", Zoo +
            "public static class C { public static void M(ZooDb db, int id) { var d = db.Set<Dog>().Find(id); if (d != null) Spec.Assert(d.Id == id); } }"));

        [Fact]
        public void Inheritance_ADerivedType_HasItsRootsFilter() => Assert.Empty(Errors("M", Zoo +
            "public static class C { public static async Task M(ZooDb db) { var r = await db.Set<Dog>().AsNoTracking().ToListAsync(); Spec.Assert(Spec.Forall(0, r.Count, i => !r[i].Gone)); } }"));

        [Fact]
        public void Inheritance_ADerivedType_HasItsRootsUniqueIndex() => Assert.Empty(Errors("M", Zoo +
            "public static class C { public static Dog? M(ZooDb db, string name) { return db.Set<Dog>().AsNoTracking().SingleOrDefault(d => d.Name == name); } }"));

        [Fact]
        public void Inheritance_ADerivedType_OnAnotherColumn_MayMatchMore() => Assert.Equal(new[] { "CSV1001" }, Errors("M", Zoo +
            "public static class C { public static Dog? M(ZooDb db, int barks) { return db.Set<Dog>().AsNoTracking().SingleOrDefault(d => d.Barks == barks); } }"));

        // ---- across calls ----

        private const string Helpers =
            "public static class H { public static async Task TrySave(Shop db) { try { await db.SaveChangesAsync(); } catch (DbUpdateException) { } } " +
            "public static async Task Save(Shop db) { await db.SaveChangesAsync(); } " +
            "public static async Task ShipAll(Shop db) { await db.Orders.ExecuteUpdateAsync(s => s.SetProperty(o => o.Shipped, true)); } }\n";

        [Fact]
        public void Calls_ACalleeThatSwallowsAFailedSave_LeavesTheContextBroken() => Assert.Equal(new[] { "CSV1033" }, Errors("M", Helpers +
            "public static class C { public static async Task M() { using var db = new Shop(); db.Orders.Add(new Order()); await H.TrySave(db); db.Orders.Add(new Order()); } }"));

        [Fact]
        public void Calls_ACalleeThatSaves_LeavesTheContextUsable() => Assert.Empty(Errors("M", Helpers +
            "public static class C { public static async Task M() { using var db = new Shop(); db.Orders.Add(new Order()); await H.Save(db); db.Orders.Add(new Order()); } }"));

        [Fact]
        public void Calls_ACalleesSave_AndTheCallers_AreTwoOutsideATransaction() => Assert.Equal(new[] { "CSV1035" }, Errors("M", Helpers +
            "public static class C { public static async Task M() { using var db = new Shop(); db.Orders.Add(new Order()); await H.Save(db); db.Orders.Add(new Order()); await db.SaveChangesAsync(); } }"));

        [Fact]
        public void Calls_ACalleesBulkUpdate_MakesTrackedRowsStale() => Assert.Equal(new[] { "CSV1033" }, Errors("M", Helpers +
            "public static class C { public static async Task M(int id) { using var db = new Shop(); var o = await db.Orders.FirstOrDefaultAsync(x => x.Id == id); if (o == null) return; " +
            "await H.ShipAll(db); o.Total = 1; await db.SaveChangesAsync(); } }"));

        // ---- compiled queries ----

        private const string Compiled =
            "public static class Q { public static readonly Func<Shop, int, IEnumerable<Order>> Large = EF.CompileQuery((Shop db, int above) => db.Orders.AsNoTracking().Where(o => o.Total > above)); " +
            "public static readonly Func<Shop, int, Order?> ById = EF.CompileQuery((Shop db, int id) => db.Orders.AsNoTracking().FirstOrDefault(o => o.Id == id)); " +
            "public static readonly Func<Shop, Order?> AnyOne = EF.CompileQuery((Shop db) => db.Orders.AsNoTracking().FirstOrDefault()); }\n";

        [Fact]
        public void CompiledQuery_OfAValue_IsTheQueryItsLambdaWrites() => Assert.Empty(Errors("M", Compiled +
            "public static class C { public static void M(Shop db, int id) { var o = Q.ById(db, id); if (o != null) Spec.Assert(o.Id == id); } }"));

        [Fact]
        public void CompiledQuery_OfAValue_IsCheckedAsItsQuery() => Assert.Contains("CSV1031", Errors("M", Compiled +
            "public static class C { public static Order? M(Shop db) => Q.AnyOne(db); }"));

        [Fact]
        public void CompiledQuery_OfASequence_IsALibraryCall() => Assert.NotEmpty(Errors("M", Compiled +
            "public static class C { public static void M(Shop db) { var r = Q.Large(db, 5).ToList(); Spec.Assert(Spec.Forall(0, r.Count, i => r[i].Total > 5)); } }"));

        // ---- the local view ----

        [Fact]
        public void Local_OfANewContext_IsEmpty() => Assert.Empty(Errors("M",
            "public static class C { public static void M() { using var db = new Shop(); var n = db.Orders.Local.Count; var any = db.Orders.Local.Any(); Spec.Assert(n == 0 && !any); } }"));

        [Fact]
        public void Local_HasWhatIsAdded() => Assert.Empty(Errors("M",
            "public static class C { public static void M() { using var db = new Shop(); db.Orders.Add(new Order { Total = 3 }); " +
            "var any = db.Orders.Local.Any(x => x.Total == 3); var all = db.Orders.Local.All(x => x.Total == 3); Spec.Assert(any && all); } }"));

        [Fact]
        public void Local_NotWhatIsRemoved() => Assert.Empty(Errors("M",
            "public static class C { public static void M() { using var db = new Shop(); var o = new Order { Total = 3 }; db.Orders.Add(o); db.Orders.Remove(o); " +
            "var n = db.Orders.Local.Count; Spec.Assert(n == 0); } }"));

        [Fact]
        public void Local_OfTwoAdded_IsNotOne() => Assert.NotEmpty(Errors("M",
            "public static class C { public static void M() { using var db = new Shop(); db.Orders.Add(new Order { Total = 3 }); db.Orders.Add(new Order { Total = 4 }); " +
            "var n = db.Orders.Local.Count; Spec.Assert(n <= 1); } }"));

        [Fact]
        public void Local_OfAContextPassedIn_IsUnknown() => Assert.NotEmpty(Errors("M",
            "public static class C { public static void M(Shop db) { var n = db.Orders.Local.Count; Spec.Assert(n == 0); } }"));

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

        // ---- one operation at a time on a context (CSV1036) ----

        [Fact]
        public void TwoQueriesAtOnce_AreReported() => Assert.Equal(new[] { "CSV1036", "CSV1036" }, Errors("M",
            "public static class C { public static async Task M(Shop db) { var a = db.Orders.ToListAsync(); var b = db.Customers.ToListAsync(); await Task.WhenAll(a, b); } }"));

        [Fact]
        public void QueriesOneAfterAnother_Verify() => Assert.Empty(Errors("M",
            "public static class C { public static async Task<int> M(Shop db) { var a = await db.Orders.AsNoTracking().CountAsync(); var b = await db.Customers.CountAsync().ConfigureAwait(false); return a + b; } }", overflow: false));

        [Fact]
        public void ReturningTheTask_LeavesItToTheCaller() => Assert.Empty(Errors("M",
            "public static class C { public static Task<int> M(Shop db) { return db.SaveChangesAsync(); } }"));

        [Fact]
        public void AContextInTaskRun_IsReported() => Assert.Equal(new[] { "CSV1036" }, Errors("M",
            "public static class C { public static async Task M(Shop db) { await Task.Run(() => db.Orders.Count()); } }"));

        [Fact]
        public void AContextMadeInTaskRun_Verifies() => Assert.Empty(Errors("M",
            "public static class C { public static async Task M(IDbContextFactory<Shop> factory) { await Task.Run(() => { using var db = factory.CreateDbContext(); return db.Orders.Count(); }); } }"));

        // (a call EF translates, in a database lambda: the database's function of its arguments)
        [Fact]
        public void ATranslatedCallInAQuery_Verifies() => Assert.Empty(Errors("M",
            "public static class C { public static int M(Shop db) { return db.Customers.Where(c => c.Name.ToUpper() == \"A\").Count(); } }"));

        [Fact]
        public void GroupsAndGroupJoins_OnTheDatabase_Verify() => Assert.Empty(Errors("M",
            "public static class C { public static int M(Shop db) { return db.Orders.GroupBy(o => o.CustomerId).Select(g => g.Count()).Count() + " +
            "db.Customers.GroupJoin(db.Orders, c => c.Id, o => o.CustomerId, (c, os) => new { c.Id, N = os.Count() }).Count(); } }", overflow: false));

        [Fact]
        public void AContextOfAPrimaryConstructor_IsTranslated()
        {
            // (#83: the captured context in a query that isn't awaited, and in Add)
            var r = VerifyEf(@"public class Payee { public long Id { get; set; } public string Name { get; set; } = """"; }
public sealed class Db(DbContextOptions<Db> options) : DbContext(options)
{
    protected override void OnModelCreating(ModelBuilder modelBuilder) => modelBuilder.Entity<Payee>();
}
public sealed class Store(Db db)
{
    public async Task<Payee?> FindPayee(long id) => await db.Set<Payee>().AsNoTracking().SingleOrDefaultAsync(p => p.Id == id);
    public Task<Payee?> ByName(string name) => db.Set<Payee>().AsNoTracking().FirstOrDefaultAsync(p => p.Name == name);
    public async Task Add(string name)
    {
        db.Set<Payee>().Add(new Payee { Name = name });
        await db.SaveChangesAsync();
    }
}");
            Assert.True(r.Errors("FindPayee").Length == 0, r.Explain("FindPayee"));
            Assert.True(r.Errors("Add").Length == 0, r.Explain("Add"));
            // (a query's task returned by a method that isn't async: the caller's to await, as ReturningTheTask_LeavesItToTheCaller)
            Assert.True(r.Errors("ByName").Length == 0, r.Explain("ByName"));
        }

        [Fact]
        public void ABaseOfAReferenceAssembly_HasItsAutoPropertiesAsColumns()
        {
            // (#129's review: a targeting pack's assembly, IdentityUser's under the ASP.NET Core framework reference, has no
            // backing fields; its auto-properties' accessors are the compiler's, and they are columns. One with code isn't)
            var r = VerifyEfWithLibrary(@"namespace Lib
{
    public class Row<TKey>
    {
        public virtual TKey Id { get; set; } = default!;
        public virtual string? UserName { get; set; }
        public string Display => UserName + ""!"";
    }
}", @"using Lib;
public class User : Row<long> { }
public sealed class Db(DbContextOptions<Db> options) : DbContext(options)
{
    public DbSet<User> Users => Set<User>();
}
public sealed class Users(Db db)
{
    public async Task<List<long>> Ids() => await db.Users.AsNoTracking().Select(u => u.Id).ToListAsync();
    public async Task<List<string?>> Names() => await db.Users.AsNoTracking().Select(u => u.UserName).ToListAsync();
    public async Task<List<string>> Displays() => await db.Users.AsNoTracking().Select(u => u.Display).ToListAsync();
}", referenceAssembly: true);
            foreach (var ok in new[] { "Ids", "Names" })
            {
                Assert.True(r.Errors("Users." + ok).Length == 0, ok + ": " + r.Explain("Users." + ok));
            }
            Assert.NotEmpty(r.Errors("Users.Displays"));
        }

        [Fact]
        public void EntitiesOfAReferencedAssembly_AndConfigurationsOfAGenericBase_AreRead()
        {
            // (#82: the entities in a domain assembly; a configuration from a generic base whose key is named by the
            // derived class's lambda, a string computed from it)
            var r = VerifyEfWithLibrary(@"namespace EfLib
{
    public class Payee
    {
        public long Id { get; set; }
        public string Name { get; set; } = """";
        public string Display => Name + ""!"";
    }
    public class Transfer
    {
        internal long RowId { get; private set; }
        public string Reference { get; set; } = """";
    }
}", @"using System.Linq.Expressions;
using EfLib;
using Microsoft.EntityFrameworkCore.Metadata.Builders;
public sealed class Db(DbContextOptions<Db> options) : DbContext(options)
{
    protected override void OnModelCreating(ModelBuilder modelBuilder)
    {
        modelBuilder.Entity<Payee>();
    }
}
public abstract class KeyedConfiguration<T> : IEntityTypeConfiguration<T> where T : class
{
    protected abstract Expression<Func<T, long>> Key { get; }
    public void Configure(EntityTypeBuilder<T> builder)
    {
        builder.Property(Key).HasColumnName(""Id"");
        builder.HasKey(((MemberExpression)Key.Body).Member.Name);
    }
}
public sealed class TransferConfiguration : KeyedConfiguration<Transfer>
{
    protected override Expression<Func<Transfer, long>> Key => x => x.RowId;
}
public sealed class Store(Db db)
{
    public async Task<Payee?> FindPayee(long id) =>
        await db.Set<Payee>().AsNoTracking().SingleOrDefaultAsync(p => p.Id == id);
    public async Task<Transfer?> Find(long row) =>
        await db.Set<Transfer>().AsNoTracking().SingleOrDefaultAsync(t => t.RowId == row);
    public async Task<string> Named(long id)
    {
        var p = await db.Set<Payee>().AsNoTracking().SingleOrDefaultAsync(p => p.Id == id);
        if (p == null) return """";
        Spec.Assert(p.Id == id);
        return p.Name;
    }
    public async Task<int> ByDisplay(string d) => await db.Set<Payee>().CountAsync(p => p.Display == d);
    public async Task AddTransfer(string reference)
    {
        db.Set<Transfer>().Add(new Transfer { Reference = reference });
        await db.SaveChangesAsync();
    }
}");
            foreach (var ok in new[] { "FindPayee", "Find", "Named", "AddTransfer" })
            {
                Assert.True(r.Errors(ok).Length == 0, r.Explain(ok));
            }
            // (a computed property of a referenced entity isn't a column)
            Assert.Equal(new[] { "CSV1032" }, r.Errors("ByDisplay"));
        }

        [Fact]
        public void AContextOfAReferencedProject_IsReadFromItsSources()
        {
            // (#102: the context and its configuration in one project, the queries in another)
            var r = EfHarness.VerifyEfWithContextLibrary(@"
namespace Lib;
public class Payee { public long Id { get; set; } public string Name { get; set; } = """"; }
public sealed class Db(DbContextOptions<Db> options) : DbContext(options)
{
    protected override void OnModelCreating(ModelBuilder modelBuilder) { modelBuilder.Entity<Payee>().HasIndex(p => p.Name).IsUnique(); }
}", @"
using Lib;
public sealed class Store(Db db)
{
    public async Task<Payee?> ByName(string name) => await db.Set<Payee>().FirstOrDefaultAsync(p => p.Name == name);
    public async Task<Payee?> After(long id) => await db.Set<Payee>().FirstOrDefaultAsync(p => p.Id > id);
    public async Task<string> Named(long id)
    {
        var p = await db.Set<Payee>().AsNoTracking().SingleOrDefaultAsync(p => p.Id == id);
        return p == null ? """" : p.Name;
    }
}");
            Assert.True(r.Errors("ByName").Length == 0, r.Explain("ByName"));
            Assert.True(r.Errors("Named").Length == 0, r.Explain("Named"));
            Assert.Equal(new[] { "CSV1031" }, r.Errors("After"));
            Assert.DoesNotContain(r.Diagnostics, d => d.Id is "CSV1900" or "CSV1902");
        }

        [Fact]
        public void AnAwait_KeepsOnlyTheColumnsTheMethodReaches()
        {
            // (#90: a method of one entity awaits and keeps that entity's columns only, not the whole model's)
            var boogie = System.IO.Path.Combine(System.IO.Path.GetTempPath(), "csverify-await-" + System.Guid.NewGuid().ToString("N") + ".bpl");
            var options = Options();
            options.BoogieOut = boogie;
            var r = CsVerify.Verifier.Engine.VerifySources(new[] { ("Test.cs", "using System; using CsVerify; using System.Linq; using System.Threading.Tasks; using Microsoft.EntityFrameworkCore;\n" + @"
public sealed class Payee { public long Id { get; set; } public string Name { get; set; } = """"; }
public sealed class Ledger { public long Id { get; set; } public int Total { get; set; } }
public sealed class Db(DbContextOptions<Db> options) : DbContext(options)
{
    protected override void OnModelCreating(ModelBuilder b) { b.Entity<Payee>(); b.Entity<Ledger>(); }
}
public sealed class Store(Db db)
{
    public async Task<Payee?> Find(long id) => await db.Set<Payee>().AsNoTracking().SingleOrDefaultAsync(p => p.Id == id);
}") }, options);
            try
            {
                Assert.True(r.Errors("Find").Length == 0, r.Explain("Find"));
                var text = System.IO.File.ReadAllText(boogie);
                var find = text.Substring(text.IndexOf("procedure Store.Find"));
                find = find.Substring(0, find.IndexOf("\n}\n"));
                var awaited = System.Text.RegularExpressions.Regex.Match(find, @"call (\$await\$\d+)\(").Groups[1].Value;
                Assert.NotEqual("", awaited);
                var declaration = text.Substring(text.IndexOf("procedure " + awaited + "("));
                declaration = declaration.Substring(0, declaration.IndexOf("\nprocedure "));
                Assert.Contains("$F.Payee.Name", declaration);
                Assert.DoesNotContain("$F.Ledger.Total", declaration);
                // (its body keeps no column of the other entity across the await)
                Assert.DoesNotContain("$F.Ledger.Total", find.Substring(find.IndexOf("{")));
            }
            finally { try { System.IO.File.Delete(boogie); } catch (System.IO.IOException) { } }
        }

        [Fact]
        public void TranslatedLambdas_Converters_AndSingle_AreReadAsEfRunsThem()
        {
            // (#93: a query's lambdas are SQL, where a null member is a null, not a throw; a converter isn't given null;
            // SingleAsync gives its row or throws; a readonly array field's initializer says its length)
            var r = VerifyEfWithLibrary(@"namespace Lib
{
    using System;
    public sealed record MemberId(Guid Value);
    public sealed record ProviderRef(string Value)
    {
        public static ProviderRef? ParseOptional(string? value) => string.IsNullOrEmpty(value) ? null : new ProviderRef(value);
    }
    public class Card
    {
        public long Id { get; set; }
        public string Provider { get; set; } = """";
    }
    public class Member
    {
        public Member(MemberId id) => Id = id;
        private Member() { Id = new MemberId(Guid.Empty); }
        public long RowId { get; private set; }
        public MemberId Id { get; }
        public string? Email { get; set; }
        public Card? Card { get; set; }
        public long? CardId { get; set; }
        public DateTime? StartedAt { get; set; }
        public ProviderRef? Portfolio { get; set; }
        public void Touch(DateTime at) => StartedAt = at;
    }
}", @"using Lib;
public sealed class Db(DbContextOptions<Db> options) : DbContext(options)
{
    protected override void OnModelCreating(ModelBuilder modelBuilder)
    {
        modelBuilder.Entity<Card>();
        modelBuilder.Entity<Member>(b =>
        {
            b.HasKey(m => m.RowId);
            b.Property(m => m.Id).HasColumnName(""ExternalId"").HasConversion(id => id.Value, value => new MemberId(value));
            b.HasAlternateKey(m => m.Id);
            b.HasOne(m => m.Card).WithMany().HasForeignKey(m => m.CardId);
            b.Property(m => m.Portfolio).HasConversion(reference => reference!.Value, value => ProviderRef.ParseOptional(value)!);
        });
    }
}
public sealed record HeldCard(long CardId, long MemberRow);
public sealed class Store(Db db)
{
    private readonly char[] digits = ""0123456789"".ToCharArray();
    public async Task<HeldCard?> Held(string provider) =>
        await db.Set<Member>().AsNoTracking()
            .Where(m => m.Card!.Provider == provider)
            .Select(m => new HeldCard(m.Card!.Id, m.RowId))
            .FirstOrDefaultAsync();
    public async Task<List<DateTime>> Started(DateTime before) =>
        await db.Set<Member>().AsNoTracking()
            .Where(m => m.StartedAt != null && m.StartedAt <= before)
            .Select(m => m.StartedAt!.Value)
            .ToListAsync();
    public async Task<Member?> ById(Guid id) =>
        await db.Set<Member>().AsNoTracking().SingleOrDefaultAsync(m => m.Id == new MemberId(id));
    public async Task Touch(long row, DateTime at)
    {
        var member = await db.Set<Member>().SingleAsync(m => m.RowId == row);
        member.Touch(at);
    }
    public async Task<long> Read(long row)
    {
        var member = await db.Set<Member>().AsNoTracking().SingleOrDefaultAsync(m => m.RowId == row) ?? throw new InvalidOperationException($""no member {row}"");
        return member.RowId;
    }
    public void AddCard(Card card) => db.Set<Card>().Add(card);
    public void AddNewCard(Card card)
    {
        Spec.Requires(card.Id == 0);
        db.Set<Card>().Add(card);
    }
    public string Code(int length) =>
        string.Concat(Enumerable.Range(1, length).Select(_ => digits[System.Security.Cryptography.RandomNumberGenerator.GetInt32(digits.Length)]));
    public async Task<Member?> ByEmail(string email) =>
        await db.Set<Member>().AsNoTracking().FirstOrDefaultAsync(m => m.Email!.Equals(email));
}");
            // (the converter's lambdas: EF gives them no null)
            Assert.DoesNotContain(r.Methods.Where(m => m.Name == "Db.OnModelCreating.<lambda:14>").SelectMany(m => m.Diagnostics), d => d.IsError);
            foreach (var ok in new[] { "ByEmail", "Read", "AddNewCard" })
            {
                Assert.True(r.Errors(ok).Length == 0, r.Explain(ok));
            }
            // (and these report nothing but what isn't verified yet: a list's task, LINQ's Select)
            foreach (var ok in new[] { "Started", "ById", "Code" })
            {
                Assert.True(r.Errors(ok).All(id => id == "CSV1902"), r.Explain(ok));
            }
            // (#129: a projection's record, a data value, is read: First of a filter no index makes unique, in no order)
            Assert.Equal(new[] { "CSV1031" }, r.Errors("Held"));
            // (no lambda of a query is verified as C#; Code's, LINQ to Objects', is, and knows digits' length)
            Assert.Equal(new[] { "Store.Code.<lambda:51>" }, r.Methods.Where(m => m.Name.StartsWith("Store.") && m.Name.Contains("<lambda:")).Select(m => m.Name));
            Assert.True(r.Errors("Store.Code.<lambda:51>").Length == 0, r.Explain("Store.Code.<lambda:51>"));
            // (SingleAsync's row isn't null; that there is one is still its precondition. Add of an entity passed in may
            // meet a tracked one with its key, unless the caller says it is new: a store-generated key's default)
            Assert.Equal(new[] { "CSV1001" }, r.Errors("Touch"));
            Assert.Equal(new[] { "CSV1033" }, r.Errors("AddCard"));
        }

        [Fact]
        public void QueriesFromALocal_QuerySyntax_AndMembersOfTuplesAndAnonymousTypes_AreNotNull()
        {
            // (#96: a query is SQL whatever local holds it, and in query syntax too; a lambda returning a tuple's or an
            // anonymous type's non-nullable member returns no null)
            var r = VerifyEfWithLibrary(@"namespace Lib
{
    using System;
    public sealed record MemberId(Guid Value);
    public class Card
    {
        public long Id { get; set; }
        public string Provider { get; set; } = """";
    }
    public class Member
    {
        public Member(MemberId id) => Id = id;
        private Member() { Id = new MemberId(Guid.Empty); }
        public long RowId { get; private set; }
        public MemberId Id { get; }
        public Card? Card { get; set; }
        public long? CardId { get; set; }
    }
}", @"using Lib;
public sealed class Db(DbContextOptions<Db> options) : DbContext(options)
{
    protected override void OnModelCreating(ModelBuilder modelBuilder)
    {
        modelBuilder.Entity<Card>();
        modelBuilder.Entity<Member>(b =>
        {
            b.HasKey(m => m.RowId);
            b.Property(m => m.Id).HasColumnName(""ExternalId"").HasConversion(id => id.Value, value => new MemberId(value));
            b.HasOne(m => m.Card).WithMany().HasForeignKey(m => m.CardId);
        });
    }
}
public sealed record HeldCard(long CardId, long MemberRow);
public sealed class Store(Db db)
{
    public async Task<HeldCard?> Held(string provider, bool includeDeleted)
    {
        var members = includeDeleted ? db.Set<Member>().IgnoreQueryFilters() : db.Set<Member>();
        return await members.AsNoTracking()
            .Where(m => m.Card!.Provider == provider)
            .Select(m => new HeldCard(m.Card!.Id, m.RowId))
            .FirstOrDefaultAsync();
    }
    public static async Task<HeldCard?> From(IQueryable<Member> members, string provider) =>
        await members.Where(m => m.Card!.Provider == provider).Select(m => new HeldCard(m.Card!.Id, m.RowId)).FirstOrDefaultAsync();
    public async Task<List<long>> CardsOf(string provider) =>
        await (
                from member in db.Set<Member>().AsNoTracking()
                join card in db.Set<Card>() on member.Card!.Id equals card.Id
                where card.Provider == provider
                select card.Id)
            .ToListAsync();
    public static Dictionary<long, MemberId> ById(IEnumerable<(long Row, MemberId Id)> members) =>
        members.ToDictionary(m => m.Row, m => m.Id);
    public async Task<List<Member>> WithCards()
    {
        var rows = await db.Set<Member>().Select(m => new { Member = m, Provider = m.Card!.Provider }).ToListAsync();
        return rows.Select(r => r.Member).ToList();
    }
}");
            // (an IQueryable parameter may be a list's AsQueryable(), where a null member throws: its lambdas are C#)
            Assert.Equal(new[] { "CSV1013", "CSV1013" }, r.Methods.Where(m => m.Name == "Store.From.<lambda:28>").SelectMany(m => m.Diagnostics).Where(d => d.IsError).Select(d => d.Id));
            foreach (var ok in new[] { "Held", "From", "CardsOf", "ById", "WithCards" })
            {
                Assert.True(r.Errors(ok).All(id => id == "CSV1902"), r.Explain(ok));
            }
            // (no lambda of a query is verified as C#, in query syntax either; LINQ to Objects' are, and return no null)
            var lambdas = r.Methods.Where(m => m.Name.StartsWith("Store.") && m.Name.Contains("<lambda:")).ToList();
            Assert.Equal(new[] { "Store.ById.<lambda:37>", "Store.ById.<lambda:37>", "Store.From.<lambda:28>", "Store.From.<lambda:28>", "Store.WithCards.<lambda:41>" },
                lambdas.Select(m => m.Name).OrderBy(n => n, System.StringComparer.Ordinal));
            Assert.DoesNotContain(lambdas.Where(m => m.Name != "Store.From.<lambda:28>").SelectMany(m => m.Diagnostics), d => d.IsError);
        }

        [Fact]
        public void ATrackedQueryByKey_MatchesTheRowsTheDatabaseDoes_AndAKeyIsNotChanged()
        {
            // (a tracked entity's key, or alternate key, is its row's: EF throws where one changes. So a tracked filter by
            // key matches the rows the database does, whatever the context tracked; one by another column may not)
            var r = VerifyEf(@"public sealed class Member
{
    public long RowId { get; set; }
    public Guid Code { get; set; }
    public int Badge { get; set; }
    public string Name { get; set; } = """";
}
public sealed class Db(DbContextOptions<Db> options) : DbContext(options)
{
    protected override void OnModelCreating(ModelBuilder b)
    {
        b.Entity<Member>().HasKey(m => m.RowId);
        b.Entity<Member>().HasAlternateKey(m => m.Code);
        b.Entity<Member>().HasIndex(m => m.Badge).IsUnique();
    }
}
public static class C
{
    public static async Task<string> ByKey(Db db, long row) =>
        (await db.Set<Member>().SingleOrDefaultAsync(m => m.RowId == row) ?? throw new InvalidOperationException()).Name;
    public static async Task<string> ByCode(Db db, Guid code) =>
        (await db.Set<Member>().SingleOrDefaultAsync(m => m.Code == code) ?? throw new InvalidOperationException()).Name;
    public static async Task<string> WhereByKey(Db db, long row) =>
        (await db.Set<Member>().Where(m => m.RowId == row).SingleOrDefaultAsync() ?? throw new InvalidOperationException()).Name;
    public static async Task<string> ByBadge(Db db, int badge) =>
        (await db.Set<Member>().SingleOrDefaultAsync(m => m.Badge == badge) ?? throw new InvalidOperationException()).Name;
    public static async Task<string> ByName(Db db, string name) =>
        (await db.Set<Member>().SingleOrDefaultAsync(m => m.Name == name) ?? throw new InvalidOperationException()).Name;
    public static async Task Rekey(Db db, long row)
    {
        var m = await db.Set<Member>().FirstOrDefaultAsync(x => x.RowId == row) ?? throw new InvalidOperationException();
        m.Code = Guid.NewGuid();
    }
    public static void Added(Db db)
    {
        var m = new Member { Code = Guid.NewGuid() };
        db.Set<Member>().Add(m);
        m.Code = Guid.NewGuid();
    }
}");
            // (#125: a unique index's column may differ from its row's in a tracked entity, but not how many rows match)
            foreach (var ok in new[] { "ByKey", "ByCode", "WhereByKey", "ByBadge", "Added" })
            {
                Assert.True(r.Errors(ok).Length == 0, r.Explain(ok));
            }
            // (a column no index makes unique; a tracked entity's key mustn't change)
            Assert.Equal(new[] { "CSV1001" }, r.Errors("ByName"));
            Assert.Equal(new[] { "CSV1033" }, r.Errors("Rekey"));
        }

        [Fact]
        public void ATrackedQueryOnAUniqueIndex_MatchesOneRowAtMost()
        {
            // (#125: the database's rows are distinct by key and by each unique index; tracking changes which instance a
            // row is, not how many there are. A filter fixing one, whatever else it adds, keeps one row at most)
            var r = VerifyEf(@"public sealed class Item
{
    public long Id { get; set; }
    public Guid ExternalId { get; set; }
    public DateTime CreatedAt { get; set; }
    public Guid? Other { get; set; }
}
public sealed class Db(DbContextOptions<Db> options) : DbContext(options)
{
    protected override void OnModelCreating(ModelBuilder b)
    {
        b.Entity<Item>().HasIndex(x => x.ExternalId).IsUnique();
        b.Entity<Item>().HasIndex(x => x.Other).IsUnique();
    }
}
public sealed class Store(Db db)
{
    public async Task<Item?> UntrackedQuery(Guid id) =>
        await db.Set<Item>().AsNoTracking().Where(t => t.ExternalId == id).SingleOrDefaultAsync();
    public async Task<Item?> TrackedByKey(long id) =>
        await db.Set<Item>().Where(t => t.Id == id).SingleOrDefaultAsync();
    public async Task<Item?> TrackedQuery(Guid id) =>
        await db.Set<Item>().Where(t => t.ExternalId == id).SingleOrDefaultAsync();
    public async Task<Item?> TrackedList(Guid id) =>
        (await db.Set<Item>().Where(t => t.ExternalId == id).ToListAsync()).SingleOrDefault();
    public async Task<Item?> TrackedByKeyAndColumn(long id, DateTime at) =>
        await db.Set<Item>().SingleOrDefaultAsync(t => t.Id == id && t.CreatedAt == at);
    public async Task<Item?> TrackedOrdered(Guid id) =>
        await db.Set<Item>().Where(t => t.CreatedAt > DateTime.MinValue).OrderBy(t => t.Id).Where(t => id == t.ExternalId).SingleOrDefaultAsync();
    public async Task<Item?> ByColumn(DateTime at) =>
        await db.Set<Item>().SingleOrDefaultAsync(t => t.CreatedAt == at);
    public async Task<Item?> EitherIndex(Guid id, long key) =>
        await db.Set<Item>().SingleOrDefaultAsync(t => t.ExternalId == id || t.Id == key);
    public async Task<Item?> NullableIndex(Guid? other) =>
        await db.Set<Item>().SingleOrDefaultAsync(t => t.Other == other);
}");
            foreach (var ok in new[] { "UntrackedQuery", "TrackedByKey", "TrackedQuery", "TrackedList", "TrackedByKeyAndColumn", "TrackedOrdered" })
            {
                Assert.True(r.Errors("Store." + ok).Length == 0, r.Explain("Store." + ok));
            }
            // (a column no index makes unique; either of two; a nullable one, where null matches every null)
            foreach (var bad in new[] { "ByColumn", "EitherIndex", "NullableIndex" })
            {
                Assert.True(r.Errors("Store." + bad).SequenceEqual(new[] { "CSV1001" }), bad + ": " + r.Explain("Store." + bad));
            }
        }

        [Fact]
        public void AQueryHelper_IsTranslated_AndReadAtItsCall()
        {
            // (#126: a helper taking a query is translated, its query rows nothing is known of; a private one returning one
            // expression is read where it is awaited, on the query passed in)
            var r = VerifyEf(@"public sealed class Tag
{
    public long Id { get; set; }
    public long ItemId { get; set; }
}
public sealed class Item
{
    public long Id { get; set; }
    public Guid ExternalId { get; set; }
    public DateTime CreatedAt { get; set; }
    public List<Tag> Tags { get; set; } = new List<Tag>();
}
public sealed class Db(DbContextOptions<Db> options) : DbContext(options)
{
    protected override void OnModelCreating(ModelBuilder b) => b.Entity<Item>().HasIndex(x => x.ExternalId).IsUnique();
}
public sealed class Store(Db db)
{
    public async Task<Item?> Inline(Guid id) =>
        (await db.Set<Item>().AsNoTracking().Where(t => t.ExternalId == id).OrderBy(t => t.CreatedAt).ThenBy(t => t.Id).ToListAsync()).SingleOrDefault();
    public async Task<Item?> ThroughHelper(Guid id) =>
        (await Load(db.Set<Item>().AsNoTracking().Where(t => t.ExternalId == id))).SingleOrDefault();
    public async Task<Item?> ThroughIncluding(Guid id) =>
        (await LoadWithTags(db.Set<Item>().Where(t => t.ExternalId == id))).SingleOrDefault();
    public async Task<Item?> ThroughTaking(Guid id, int n) =>
        (await LoadSome(db.Set<Item>().Where(t => t.ExternalId == id), n)).SingleOrDefault();
    public async Task<Item?> ByColumn(DateTime at) =>
        (await Load(db.Set<Item>().Where(t => t.CreatedAt == at))).SingleOrDefault();
    public async Task<Item?> ThroughPublic(Guid id) =>
        (await LoadPublic(db.Set<Item>().Where(t => t.ExternalId == id))).SingleOrDefault();
    private static async Task<IReadOnlyList<Item>> Load(IQueryable<Item> query) =>
        await query.OrderBy(t => t.CreatedAt).ThenBy(t => t.Id).ToListAsync();
    private static async Task<IReadOnlyList<Item>> LoadWithTags(IQueryable<Item> query) =>
        await query.Include(t => t.Tags).OrderBy(t => t.Id).ToListAsync();
    private async Task<List<Item>> LoadSome(IQueryable<Item> query, int n)
    {
        return await query.OrderBy(t => t.Id).Take(n).ToListAsync();
    }
    public static async Task<IReadOnlyList<Item>> LoadPublic(IQueryable<Item> query) =>
        await query.OrderBy(t => t.Id).ToListAsync();
}");
            foreach (var ok in new[] { "Inline", "ThroughHelper", "ThroughIncluding", "ThroughTaking", "Load", "LoadWithTags", "LoadSome", "LoadPublic" })
            {
                Assert.True(r.Errors("Store." + ok).Length == 0, ok + ": " + r.Explain("Store." + ok));
            }
            // (a column no index makes unique; a public helper is read by its contract, which says nothing of its rows)
            foreach (var bad in new[] { "ByColumn", "ThroughPublic" })
            {
                Assert.True(r.Errors("Store." + bad).SequenceEqual(new[] { "CSV1001" }), bad + ": " + r.Explain("Store." + bad));
            }
        }

        [Fact]
        public void AColumnWrittenOnlyWhenMade_IsKeptAcrossAnAwait()
        {
            // (#127: no code writes a private setter's column outside its constructors, nor an init one's after; an await
            // leaves it as it was, entities let out or not. A public setter's, or one a method assigns, may change)
            var r = VerifyEf(@"public sealed class Report
{
    public Report(string eventId) => EventId = eventId;
    public long RowId { get; private set; }
    public string EventId { get; private set; }
    public int Tries { get; private set; }
    public int Seen { get; set; }
    public Guid Batch { get; init; }
    public void Retry() => Tries++;
}
public sealed class Db(DbContextOptions<Db> options) : DbContext(options)
{
    protected override void OnModelCreating(ModelBuilder b) => b.Entity<Report>().HasKey(x => x.RowId);
}
public sealed class Store(Db db)
{
    public void AddNow(Report report)
    {
        Spec.Requires(report.RowId == 0);
        db.Set<Report>().Add(report);
    }
    public async Task<bool> AddOnceAsync(Report report)
    {
        Spec.Requires(report.RowId == 0);
        if (await db.Set<Report>().AsNoTracking().AnyAsync(r => r.EventId == report.EventId))
        {
            return false;
        }
        db.Set<Report>().Add(report);
        return true;
    }
    public async Task KeptInit(Report report, Guid b)
    {
        Spec.Requires(report.Batch == b && report.RowId == 0);
        db.Set<Report>().Add(report);
        await Task.Yield();
        Spec.Assert(report.Batch == b);
    }
    public async Task Tried(Report report)
    {
        Spec.Requires(report.Tries == 0 && report.RowId == 0);
        db.Set<Report>().Add(report);
        await Task.Yield();
        Spec.Assert(report.Tries == 0);
    }
    public async Task Public(Report report)
    {
        Spec.Requires(report.Seen == 0 && report.RowId == 0);
        db.Set<Report>().Add(report);
        await Task.Yield();
        Spec.Assert(report.Seen == 0);
    }
}");
            foreach (var ok in new[] { "AddNow", "AddOnceAsync", "KeptInit" })
            {
                Assert.True(r.Errors("Store." + ok).Length == 0, ok + ": " + r.Explain("Store." + ok));
            }
            foreach (var bad in new[] { "Tried", "Public" })
            {
                Assert.True(r.Errors("Store." + bad).SequenceEqual(new[] { "CSV1004" }), bad + ": " + r.Explain("Store." + bad));
            }
        }

        [Fact]
        public void EachRowATrackedQueryListed_IsTheTrackedInstance()
        {
            // (#128: a tracked query's rows are distinct instances, each the one its context tracks; removing one changes
            // only its own state, so each still tracked where the loop reaches it)
            var r = VerifyEf(@"public sealed class Item
{
    public long Id { get; set; }
    public Guid ExternalId { get; set; }
}
public sealed class Db(DbContextOptions<Db> options) : DbContext(options)
{
    protected override void OnModelCreating(ModelBuilder b) => b.Entity<Item>();
}
public sealed class Store(Db db)
{
    public async Task RemoveOne(long id)
    {
        if (await db.Set<Item>().FirstOrDefaultAsync(t => t.Id == id) is { } item)
        {
            db.Remove(item);
        }
    }
    public async Task RemoveFound(Guid id)
    {
        foreach (var item in await db.Set<Item>().Where(t => t.ExternalId == id).ToListAsync())
        {
            db.Remove(item);
        }
        await db.SaveChangesAsync();
    }
    public async Task UpdateFound(Guid id)
    {
        foreach (var item in await db.Set<Item>().Where(t => t.ExternalId == id).ToListAsync())
        {
            db.Update(item);
        }
    }
    public async Task RemoveUntracked(Guid id)
    {
        foreach (var item in await db.Set<Item>().AsNoTracking().Where(t => t.ExternalId == id).ToListAsync())
        {
            db.Remove(item);
        }
    }
    public async Task AttachCopies(Guid id)
    {
        foreach (var item in await db.Set<Item>().Where(t => t.ExternalId == id).ToListAsync())
        {
            db.Attach(new Item { Id = item.Id });
        }
    }
}");
            foreach (var ok in new[] { "RemoveOne", "RemoveFound", "UpdateFound" })
            {
                Assert.True(r.Errors("Store." + ok).Length == 0, ok + ": " + r.Explain("Store." + ok));
            }
            // (rows read without tracking are new objects, which the context may track others of; a new one with a tracked
            // row's key)
            foreach (var bad in new[] { "RemoveUntracked", "AttachCopies" })
            {
                Assert.True(r.Errors("Store." + bad).Contains("CSV1033"), bad + ": " + r.Explain("Store." + bad));
            }
        }

        [Fact]
        public void ARepositorysShapes_SourceHelpersGuardsAndListsPassedOn()
        {
            // (#129's review: a private source helper's query is read where it's used; ThrowIfNull changes nothing; a private
            // method a tracked list is passed to says what it needs of its rows, and Remove of a tracked dependent leaves the
            // other rows' tracking as it was)
            var r = VerifyEf(@"public sealed class Owner { public long Id { get; set; } }
public sealed class Item
{
    public long Id { get; set; }
    public Guid ExternalId { get; set; }
    public DateTime CreatedAt { get; set; }
    public long? OwnerId { get; set; }
    public Owner? Owner { get; set; }
}
public sealed class Report
{
    public Report(string eventId) => EventId = eventId;
    internal long RowId { get; private set; }
    public string EventId { get; private set; }
}
public sealed class Db(DbContextOptions<Db> options) : DbContext(options)
{
    protected override void OnModelCreating(ModelBuilder b)
    {
        b.Entity<Owner>();
        b.Entity<Item>().HasIndex(x => x.ExternalId).IsUnique();
        b.Entity<Report>().HasKey(x => x.RowId);
    }
}
public sealed class Store(Db db)
{
    public async Task<Item?> FromSourceHelper(Guid id) =>
        (await Load(Items().Where(t => t.ExternalId == id))).SingleOrDefault();
    public async Task<Item?> FromSourceByColumn(DateTime at) =>
        (await Load(Items().Where(t => t.CreatedAt == at))).SingleOrDefault();
    private IQueryable<Item> Items() => db.Set<Item>().Include(t => t.Owner);
    private async Task<IReadOnlyList<Item>> Load(IQueryable<Item> query) =>
        await query.OrderBy(t => t.CreatedAt).ThenBy(t => t.Id).ToListAsync();
    public async Task<bool> Guarded(Item item, Report report)
    {
        Spec.Requires(report.RowId == 0);
        ArgumentNullException.ThrowIfNull(item);
        ArgumentNullException.ThrowIfNull(report);
        if (await db.Set<Report>().AsNoTracking().AnyAsync(r => r.EventId == report.EventId))
        {
            return false;
        }
        db.Set<Report>().Add(report);
        return true;
    }
    public async Task RemoveFound(Guid id) =>
        await Remove(await db.Set<Item>().Where(t => t.ExternalId == id).ToListAsync());
    public void RemoveGiven(List<Item> items)
    {
        foreach (var item in items)
        {
            db.Remove(item);
        }
    }
    private async Task Remove(List<Item> items)
    {
        foreach (var item in items)
        {
            db.Remove(item);
        }
        await db.SaveChangesAsync();
    }
    public async Task RemoveUntracked(Guid id) =>
        await Detach(await db.Set<Item>().AsNoTracking().Where(t => t.ExternalId == id).ToListAsync());
    public async Task RemoveTracked(Guid id) =>
        await Detach(await db.Set<Item>().Where(t => t.ExternalId == id).ToListAsync());
    private async Task Detach(List<Item> items)
    {
        foreach (var item in items)
        {
            db.Remove(item);
        }
        await db.SaveChangesAsync();
    }
}");
            foreach (var ok in new[] { "FromSourceHelper", "Items", "Guarded", "RemoveFound", "Remove" })
            {
                Assert.True(r.Errors("Store." + ok).Length == 0, ok + ": " + r.Explain("Store." + ok));
            }
            // (a column no index makes unique; a list of rows not known tracked; one a call passes rows read without tracking)
            Assert.True(r.Errors("Store.FromSourceByColumn").SequenceEqual(new[] { "CSV1001" }), r.Explain("Store.FromSourceByColumn"));
            Assert.True(r.Errors("Store.RemoveGiven").SequenceEqual(new[] { "CSV1033" }), r.Explain("Store.RemoveGiven"));
            Assert.True(r.Errors("Store.Detach").SequenceEqual(new[] { "CSV1033" }), r.Explain("Store.Detach"));
        }

        [Fact]
        public void KeysByName_ConvertedAndStringColumns_AndListsPassedWithOthers()
        {
            // (#129's review: an alternate key named by a string; a unique column of a converted record struct, or of
            // strings, keeps one row at most, as the database keeps it unique; a tracked list passed with a flag)
            var r = VerifyEf(@"public sealed class Account
{
    public long Id { get; set; }
    public Guid ExternalId { get; set; }
}
public readonly record struct OwnerId(Guid Value);
public sealed class Owner { public long RowId { get; set; } }
public sealed class Holder
{
    public long RowId { get; set; }
    public OwnerId Id { get; set; }
    public Owner? Owner { get; set; }
}
public sealed class Purchase
{
    public long Id { get; set; }
    public string Reference { get; set; } = """";
    public string Note { get; set; } = """";
    public string? Code { get; set; }
}
public sealed class Code
{
    public long Id { get; set; }
    public Guid ExternalId { get; set; }
    public bool IsDeleted { get; set; }
}
public sealed class Db(DbContextOptions<Db> options) : DbContext(options)
{
    protected override void OnModelCreating(ModelBuilder b)
    {
        b.Entity<Owner>().HasKey(x => x.RowId);
        b.Entity<Account>().HasAlternateKey(""ExternalId"");
        b.Entity<Holder>().HasKey(x => x.RowId);
        b.Entity<Holder>().Property(x => x.Id).HasConversion(id => id.Value, value => new OwnerId(value));
        b.Entity<Holder>().HasAlternateKey(x => x.Id);
        b.Entity<Purchase>().HasIndex(x => x.Reference).IsUnique();
        b.Entity<Purchase>().HasIndex(""Code"").IsUnique();
        b.Entity<Code>();
    }
}
public sealed class Store(Db db)
{
    public async Task<long?> ByNamedAlternateKey(Guid id) =>
        await db.Set<Account>().AsNoTracking().Where(a => a.ExternalId == id).Select(a => (long?)a.Id).SingleOrDefaultAsync();
    public async Task<long?> ByConvertedAlternateKey(Guid id)
    {
        var holder = new OwnerId(id);
        return await db.Set<Holder>().AsNoTracking().Where(h => h.Id == holder && h.Owner != null).Select(h => (long?)h.Owner!.RowId).FirstOrDefaultAsync();
    }
    public async Task<Purchase?> ByReference(string reference) =>
        await db.Set<Purchase>().SingleOrDefaultAsync(t => t.Reference == reference);
    public async Task<Purchase?> ByNote(string note) =>
        await db.Set<Purchase>().SingleOrDefaultAsync(t => t.Note == note);
    public async Task<Purchase?> ByCode(string code) =>
        await db.Set<Purchase>().SingleOrDefaultAsync(t => t.Code == code);
    public async Task<Purchase?> ByNullableCode(string? code) =>
        await db.Set<Purchase>().SingleOrDefaultAsync(t => t.Code == code);
    public async Task DeleteAsync(Guid id, bool permanent) =>
        await Delete(await db.Set<Code>().Where(c => c.ExternalId == id).ToListAsync(), permanent);
    private async Task Delete(List<Code> codes, bool permanent)
    {
        foreach (var code in codes)
        {
            if (permanent)
            {
                db.Remove(code);
            }
            else
            {
                code.IsDeleted = true;
            }
        }
        await db.SaveChangesAsync();
    }
}");
            // (a nullable column compared to a value not null: its null rows don't match, #130)
            foreach (var ok in new[] { "ByNamedAlternateKey", "ByConvertedAlternateKey", "ByReference", "ByCode", "DeleteAsync", "Delete" })
            {
                Assert.True(r.Errors("Store." + ok).Length == 0, ok + ": " + r.Explain("Store." + ok));
            }
            // (a string column no index makes unique; a nullable one compared to a value that may be null, which matches every null)
            foreach (var bad in new[] { "ByNote", "ByNullableCode" })
            {
                Assert.True(r.Errors("Store." + bad).SequenceEqual(new[] { "CSV1001" }), bad + ": " + r.Explain("Store." + bad));
            }
        }

        [Fact]
        public void AnIncludeCycle_IsANavigationThenItsInverse()
        {
            // (#129's review: EF refuses, without tracking, a path that follows a navigation and then its inverse; a
            // navigation back to its own type with none, or one whose inverse isn't on the path, it runs)
            var r = VerifyEf(@"public sealed class Posting
{
    public long Id { get; set; }
    public long? OffsetPostingId { get; set; }
    public Posting? OffsetPosting { get; set; }
    public long? ParentPostingId { get; set; }
    public Posting? ParentPosting { get; set; }
    public List<Posting> ChildPostings { get; set; } = [];
}
public sealed class Db(DbContextOptions<Db> options) : DbContext(options)
{
    protected override void OnModelCreating(ModelBuilder b)
    {
        b.Entity<Posting>().HasOne(x => x.ParentPosting).WithMany(x => x.ChildPostings).HasForeignKey(x => x.ParentPostingId).IsRequired(false);
        b.Entity<Posting>().HasOne(x => x.OffsetPosting).WithMany().HasForeignKey(x => x.OffsetPostingId);
    }
}
public sealed class Store(Db db)
{
    public async Task<List<Posting>> WithOffset() =>
        await db.Set<Posting>().AsNoTracking().Include(p => p.OffsetPosting).ToListAsync();
    public async Task<List<Posting>> WithParent() =>
        await db.Set<Posting>().AsNoTracking().Include(p => p.ParentPosting).ToListAsync();
    public async Task<List<Posting>> OffsetOfOffset() =>
        await db.Set<Posting>().AsNoTracking().Include(p => p.OffsetPosting).ThenInclude(p => p!.OffsetPosting).ToListAsync();
    public async Task<List<Posting>> Cycle() =>
        await db.Set<Posting>().AsNoTracking().Include(p => p.ParentPosting).ThenInclude(p => p!.ChildPostings).ToListAsync();
    public async Task<List<Posting>> TrackedCycle() =>
        await db.Set<Posting>().Include(p => p.ParentPosting).ThenInclude(p => p!.ChildPostings).ToListAsync();
}");
            foreach (var ok in new[] { "WithOffset", "WithParent", "OffsetOfOffset", "TrackedCycle" })
            {
                Assert.DoesNotContain("CSV1032", r.Errors("Store." + ok));
            }
            Assert.Contains("CSV1032", r.Errors("Store.Cycle"));
        }

        [Fact]
        public void AHelpersShapes_VirtualNavigationsInitializersContainsRecordsIncludesAndRequiredColumns()
        {
            // (#129's review: a virtual navigation nothing overrides; a projection into an initializer of auto-properties, or
            // a record's data value; Contains of a captured list; a tracked Include by a shadow key; a required column of
            // an entity without nullable annotations, unique)
            var r = VerifyEf(@"public sealed class Profile
{
    public long RowId { get; private set; }
}

public sealed class Customer
{
    public long RowId { get; private set; }

    public Profile? Profile { get; private set; }
}
public class User
{
    public long Id { get; set; }

    public Guid ExternalId { get; set; }

    public virtual Customer Customer { get; set; } = null!;
}
public class Member
{
    public long Id { get; set; }

    public Guid ExternalId { get; set; }

    public Customer Customer { get; set; } = null!;
}

public sealed class ProfileOfMember
{
    public required Profile Profile { get; init; }

    public required long MemberId { get; init; }
}

public sealed record HeldProfile(long Row, Profile Profile);

public sealed class Account
{
    public long RowId { get; private set; }

    public Profile? Client { get; set; }
}
#nullable disable
public sealed class Purchase
{
    public long Id { get; set; }

    public string Reference { get; set; }
    public string Label { get; set; }
}
#nullable enable
public sealed class Note
{
    public long Id { get; set; }

    public string Reference { get; set; } = """";
}

public sealed class Db(DbContextOptions<Db> options) : DbContext(options)
{
    protected override void OnModelCreating(ModelBuilder b)
    {
        b.Entity<Profile>().HasKey(x => x.RowId);
        b.Entity<Customer>().HasKey(x => x.RowId);
        b.Entity<Customer>().HasOne(c => c.Profile).WithOne().HasForeignKey<Profile>(""CustomerId"");
        b.Entity<User>().HasKey(x => x.Id);
        b.Entity<User>().HasAlternateKey(x => x.ExternalId);
        b.Entity<User>().HasOne(u => u.Customer).WithOne().HasForeignKey<Customer>(""UserId"");
        b.Entity<Member>().HasKey(x => x.Id);
        b.Entity<Member>().HasAlternateKey(x => x.ExternalId);
        b.Entity<Member>().HasOne(u => u.Customer).WithOne().HasForeignKey<Customer>(""MemberId"");
        b.Entity<Account>().HasKey(x => x.RowId);
        b.Entity<Account>().HasOne(x => x.Client).WithMany().HasForeignKey(""ClientId"");
        b.Entity<Purchase>().HasKey(x => x.Id);
        b.Entity<Purchase>().HasIndex(x => x.Reference).IsUnique();
        b.Entity<Purchase>().Property(x => x.Reference).HasMaxLength(128).IsRequired();
        b.Entity<Purchase>().Property(x => x.Label).IsRequired();
        b.Entity<Note>().HasKey(x => x.Id);
        b.Entity<Note>().HasIndex(x => x.Reference).IsUnique();
    }
}

public sealed class Store(Db db)
{
    public async Task<Profile?> ProfileOfUser(Guid user) =>
        await db.Set<User>().AsNoTracking().Where(u => u.ExternalId == user).Select(u => u.Customer.Profile).SingleOrDefaultAsync();
    public async Task<Profile?> ProfileOfMember(Guid member) =>
        await db.Set<Member>().AsNoTracking().Where(u => u.ExternalId == member).Select(u => u.Customer.Profile).SingleOrDefaultAsync();
    public async Task<ProfileOfMember?> Initialized(Guid member) =>
        await db.Set<Member>().AsNoTracking()
            .Where(u => u.ExternalId == member && u.Customer.Profile != null)
            .Select(u => new ProfileOfMember { Profile = u.Customer.Profile!, MemberId = u.Id })
            .SingleOrDefaultAsync();
    public async Task<long?> Anonymous(Guid member) =>
        (await db.Set<Member>().AsNoTracking()
            .Where(u => u.ExternalId == member && u.Customer.Profile != null)
            .Select(u => new { Profile = u.Customer.Profile!, MemberId = u.Id })
            .SingleOrDefaultAsync())?.MemberId;
    public async Task<List<Profile>> Filtered(IReadOnlyList<long> rows) =>
        await db.Set<Profile>().AsNoTracking().Where(p => rows.Contains(p.RowId)).ToListAsync();
    public async Task<List<Profile>> FilteredOne(long row) =>
        await db.Set<Profile>().AsNoTracking().Where(p => p.RowId == row).ToListAsync();
    public async Task<List<HeldProfile>> Listed(long row) =>
        (await db.Set<Profile>().AsNoTracking().Where(p => p.RowId == row).ToListAsync())
            .Select(p => new HeldProfile(p.RowId, p))
            .ToList();
    public async Task<Dictionary<long, Profile>> Keyed(long row) =>
        (await db.Set<Profile>().AsNoTracking().Where(p => p.RowId == row).ToListAsync())
            .ToDictionary(p => p.RowId);
    public async Task<List<Account>> Tracked(long row) =>
        await db.Set<Account>().Include(a => a.Client).Where(a => a.RowId == row).ToListAsync();
    public async Task<List<Account>> Untracked(long row) =>
        await db.Set<Account>().AsNoTracking().Include(a => a.Client).Where(a => a.RowId == row).ToListAsync();
    public async Task<Purchase?> PurchaseOf(string reference) =>
        await db.Set<Purchase>().SingleOrDefaultAsync(t => t.Reference == reference);
    public async Task<Note?> NoteOf(string reference) =>
        await db.Set<Note>().SingleOrDefaultAsync(t => t.Reference == reference);
    public async Task<Purchase?> PurchaseByLabel(string label) =>
        await db.Set<Purchase>().SingleOrDefaultAsync(t => t.Label == label);
    public async Task<ProfileOfMember?> InitializedById(long id) =>
        await db.Set<Member>().AsNoTracking()
            .Where(u => u.Id > id && u.Customer.Profile != null)
            .Select(u => new ProfileOfMember { Profile = u.Customer.Profile!, MemberId = u.Id })
            .SingleOrDefaultAsync();
}");
            foreach (var ok in new[] { "ProfileOfUser", "ProfileOfMember", "Initialized", "Anonymous", "Filtered", "FilteredOne", "Listed", "Keyed", "Tracked", "Untracked", "PurchaseOf", "NoteOf" })
            {
                Assert.True(r.Errors("Store." + ok).Length == 0, ok + ": " + r.Explain("Store." + ok));
            }
            // (a required column no index makes unique; a projection of a filter that fixes no key)
            foreach (var bad in new[] { "PurchaseByLabel", "InitializedById" })
            {
                Assert.True(r.Errors("Store." + bad).SequenceEqual(new[] { "CSV1001" }), bad + ": " + r.Explain("Store." + bad));
            }
        }

        [Fact]
        public void AListBuiltOfAQuerysRows_HasNoMoreThanItsRows()
        {
            // (#129's review: a list a loop builds, Add by Add, of a query's rows has at most as many as the rows times the
            // Adds of a round, inline or in a helper read at its call)
            var r = VerifyEf(@"public sealed class Account
{
    public long RowId { get; private set; }
    public bool Open { get; set; }
    public int Rank { get; set; }
}
public sealed record Held(long Row, Account Account);
public sealed class Db(DbContextOptions<Db> options) : DbContext(options)
{
    protected override void OnModelCreating(ModelBuilder b) => b.Entity<Account>().HasKey(x => x.RowId);
}
public sealed class Store(Db db)
{
    public async Task<Account?> FindListed(long row) =>
        (await Listed(db.Set<Account>().Where(a => a.RowId == row))).SingleOrDefault();
    public async Task<Held?> FindAll(long row) =>
        (await HeldAll(db.Set<Account>().Where(a => a.RowId == row))).SingleOrDefault();
    public async Task<Held?> FindSome(long row) =>
        (await HeldSome(db.Set<Account>().Where(a => a.RowId == row))).SingleOrDefault();
    public async Task<Held?> FindInline(long row)
    {
        var accounts = await db.Set<Account>().Where(a => a.RowId == row).ToListAsync();
        var held = new List<Held>();
        foreach (var account in accounts)
        {
            held.Add(new Held(account.RowId, account));
        }
        return held.SingleOrDefault();
    }
    public async Task<Held?> FindTwice(long row)
    {
        var accounts = await db.Set<Account>().Where(a => a.RowId == row).ToListAsync();
        var held = new List<Held>();
        foreach (var account in accounts)
        {
            held.Add(new Held(account.RowId, account));
            held.Add(new Held(account.RowId, account));
        }
        return held.SingleOrDefault();
    }
    public async Task<Held?> FindByRank(int rank) =>
        (await HeldAll(db.Set<Account>().Where(a => a.Rank == rank))).SingleOrDefault();
    private static async Task<IReadOnlyList<Account>> Listed(IQueryable<Account> query) =>
        await query.OrderBy(a => a.RowId).ToListAsync();
    private static async Task<IReadOnlyList<Held>> HeldAll(IQueryable<Account> query)
    {
        var accounts = await query.OrderBy(a => a.RowId).ToListAsync();
        var held = new List<Held>();
        foreach (var account in accounts)
        {
            held.Add(new Held(account.RowId, account));
        }
        return held;
    }
    private static async Task<IReadOnlyList<Held>> HeldSome(IQueryable<Account> query)
    {
        var accounts = await query.OrderBy(a => a.RowId).ToListAsync();
        var held = new List<Held>();
        foreach (var account in accounts)
        {
            if (account.Open)
            {
                held.Add(new Held(account.RowId, account));
            }
        }
        return held;
    }
}");
            foreach (var ok in new[] { "FindListed", "FindAll", "FindSome", "FindInline", "HeldAll", "HeldSome" })
            {
                Assert.True(r.Errors("Store." + ok).Length == 0, ok + ": " + r.Explain("Store." + ok));
            }
            // (two a row; a column no index makes unique)
            foreach (var bad in new[] { "FindTwice", "FindByRank" })
            {
                Assert.True(r.Errors("Store." + bad).SequenceEqual(new[] { "CSV1001" }), bad + ": " + r.Explain("Store." + bad));
            }
            Assert.DoesNotContain(r.Warnings, w => w.Contains("'Current'"));
        }

        [Fact]
        public void QueryFilters_OfShadowColumnsAndBaseConfigurations()
        {
            // (#129's review: EF.Property(x, name) is the column of the name, a shadow one's a value of the row not known;
            // a filter's lambda isn't run as C#; a filter the kernel doesn't read says nothing, the query still read)
            var r = VerifyEf(@"public abstract class Base
{
    public long Id { get; set; }
    public bool IsDeleted { get; set; }
}
public sealed class Item : Base { public Guid ExternalId { get; set; } }
public sealed class Other
{
    public long Id { get; set; }
    public Guid ExternalId { get; set; }
    public int Rank { get; set; }
}
public abstract class BaseConfiguration<T> : IEntityTypeConfiguration<T> where T : Base
{
    public virtual void Configure(Microsoft.EntityFrameworkCore.Metadata.Builders.EntityTypeBuilder<T> builder) => builder.HasQueryFilter(x => x.IsDeleted == false);
}
public sealed class ItemConfiguration : BaseConfiguration<Item>
{
    public override void Configure(Microsoft.EntityFrameworkCore.Metadata.Builders.EntityTypeBuilder<Item> builder)
    {
        base.Configure(builder);
        builder.HasIndex(x => x.ExternalId).IsUnique();
    }
}
public sealed class Db(DbContextOptions<Db> options) : DbContext(options)
{
    protected override void OnModelCreating(ModelBuilder b)
    {
        new ItemConfiguration().Configure(b.Entity<Item>());
        b.Entity<Other>().Property<bool>(""IsDeleted"");
        b.Entity<Other>().HasQueryFilter(x => !EF.Property<bool>(x, ""IsDeleted"") && EF.Property<int>(x, ""Rank"") > 0);
        b.Entity<Other>().HasIndex(x => x.ExternalId).IsUnique();
    }
}
public sealed class Store(Db db)
{
    public async Task<Item?> GenericFilter(Guid id) =>
        await db.Set<Item>().Where(t => t.ExternalId == id).SingleOrDefaultAsync();
    public async Task<Other?> ShadowFilter(Guid id) =>
        await db.Set<Other>().Where(t => t.ExternalId == id).SingleOrDefaultAsync();
    public async Task<List<Other>> Ranked() =>
        await db.Set<Other>().AsNoTracking().ToListAsync();
    public async Task<List<Other>> Shadowed() =>
        await db.Set<Other>().AsNoTracking().IgnoreQueryFilters().Where(t => EF.Property<bool>(t, ""IsDeleted"")).ToListAsync();
}");
            foreach (var ok in new[] { "GenericFilter", "ShadowFilter", "Ranked", "Shadowed" })
            {
                Assert.True(r.Errors("Store." + ok).Length == 0, ok + ": " + r.Explain("Store." + ok));
            }
            Assert.DoesNotContain(r.Methods, m => m.Name.Contains("<lambda") && m.Name.Contains("Configure") || m.Name.Contains("OnModelCreating.<lambda"));
        }

        [Fact]
        public void AQueryHelperOfStatements_IsReadAtItsCall()
        {
            // (#129's review: a private helper of declarations, ifs that return, loops that set fields, awaits and a return is
            // read where it's awaited; a correlated subquery in a projection is a value of its row; LoadAsync tracks what it
            // reads; a list ToListAsync made keeps its rows across an await)
            var r = VerifyEf(@"public sealed class Owner { public long Id { get; set; } }
public sealed class Item
{
    public long Id { get; set; }
    public Guid ExternalId { get; set; }
    public DateTime CreatedAt { get; set; }
    public long? OwnerId { get; set; }
    public Owner? Owner { get; set; }
    public string? Note { get; set; }
}
public sealed class Db(DbContextOptions<Db> options) : DbContext(options)
{
    protected override void OnModelCreating(ModelBuilder b)
    {
        b.Entity<Owner>();
        b.Entity<Item>().HasIndex(x => x.ExternalId).IsUnique();
    }
}
public sealed class Store(Db db)
{
    public async Task<Item?> ThroughLongHelper(Guid id) =>
        (await LoadMore(db.Set<Item>().Where(t => t.ExternalId == id))).SingleOrDefault();
    public async Task<Item?> ThroughProjection(Guid id) =>
        (await WithNotes(db.Set<Item>().Where(t => t.ExternalId == id))).SingleOrDefault();
    public async Task<Item?> LongByColumn(DateTime at) =>
        (await LoadMore(db.Set<Item>().Where(t => t.CreatedAt == at))).SingleOrDefault();
    public async Task<Item?> NotEveryWay(Guid id) =>
        (await Halfway(db.Set<Item>().Where(t => t.ExternalId == id))).SingleOrDefault();
    public async Task LoadedThenAttached(long id)
    {
        await db.Set<Owner>().Where(o => o.Id == id).LoadAsync();
        db.Attach(new Owner { Id = id });
    }
    private async Task<IReadOnlyList<Item>> LoadMore(IQueryable<Item> query)
    {
        var items = await query.Include(t => t.Owner).OrderBy(t => t.CreatedAt).ThenBy(t => t.Id).ToListAsync();
        if (items.Count == 0)
        {
            return items;
        }
        var owners = items.Where(t => t.OwnerId != null).Select(t => t.OwnerId!.Value).Distinct().ToList();
        await db.Set<Owner>().Where(o => owners.Contains(o.Id)).LoadAsync();
        return items;
    }
    private async Task<IReadOnlyList<Item>> WithNotes(IQueryable<Item> query)
    {
        var rows = await query.Select(t => new { Item = t, Owner = db.Set<Owner>().Where(o => o.Id == t.OwnerId).Select(o => o.Id).FirstOrDefault() }).ToListAsync();
        foreach (var row in rows)
        {
            row.Item.Note = row.Owner.ToString();
        }
        return rows.Select(r => r.Item).ToList();
    }
    private async Task<List<Item>> Halfway(IQueryable<Item> query)
    {
        var items = await query.ToListAsync();
        if (items.Count > 0)
        {
            items.Add(items[0]);
        }
        return items;
    }
}");
            foreach (var ok in new[] { "ThroughLongHelper", "ThroughProjection", "LoadMore", "WithNotes", "Halfway" })
            {
                Assert.True(r.Errors("Store." + ok).Length == 0, ok + ": " + r.Explain("Store." + ok));
            }
            // (a column no index makes unique; a helper that adds a row; a row LoadAsync tracked, met again)
            Assert.True(r.Errors("Store.LongByColumn").SequenceEqual(new[] { "CSV1001" }), r.Explain("Store.LongByColumn"));
            Assert.True(r.Errors("Store.NotEveryWay").SequenceEqual(new[] { "CSV1001" }), r.Explain("Store.NotEveryWay"));
            Assert.True(r.Errors("Store.LoadedThenAttached").SequenceEqual(new[] { "CSV1033" }), r.Explain("Store.LoadedThenAttached"));
        }

        [Fact]
        public void AKeyAGenericBaseConfigurationSets_IsTheEntitysKey_AndAColumnOnlyWrittenIsDeclared()
        {
            // (#100: HasKey(c => c.Id) over T : IHasId names the entity's Id, which implements IHasId.Id; Provider is
            // only written)
            var r = VerifyEfWithLibrary(@"namespace Lib
{
    public interface IHasId { long Id { get; set; } }
    public class Card : IHasId
    {
        public long Id { get; set; }
        public string Provider { get; set; } = """";
    }
    public class Wallet
    {
        public long Id { get; set; }
        public string Provider { get; set; } = """";
    }
}", @"using Lib;
using Microsoft.EntityFrameworkCore.Metadata.Builders;
public sealed class Db(DbContextOptions<Db> options) : DbContext(options)
{
    protected override void OnModelCreating(ModelBuilder modelBuilder)
    {
        modelBuilder.ApplyConfiguration(new CardConfiguration());
        modelBuilder.Entity<Wallet>(b => b.HasKey(w => w.Id));
    }
}
public abstract class BaseConfiguration<T> : IEntityTypeConfiguration<T> where T : class, IHasId
{
    public virtual void Configure(EntityTypeBuilder<T> builder) => builder.HasKey(c => c.Id);
}
public sealed class CardConfiguration : BaseConfiguration<Card> { }
public sealed class Store(Db db)
{
    public long AddCard(string provider)
    {
        var card = new Card { Provider = provider };
        db.Set<Card>().Add(card);
        return card.Id;
    }
    public long AddWallet(string provider)
    {
        var wallet = new Wallet { Provider = provider };
        db.Set<Wallet>().Add(wallet);
        return wallet.Id;
    }
    public void AddGiven(Card card)
    {
        Spec.Requires(card.Id == 0);
        db.Set<Card>().Add(card);
    }
}");
            foreach (var ok in new[] { "AddCard", "AddWallet", "AddGiven" })
            {
                Assert.True(r.Errors(ok).Length == 0, r.Explain(ok));
            }
        }

        [Fact]
        public void AGetOnlyPropertyTheConfigurationNames_IsAColumn()
        {
            // (#93: EF maps a property without a setter where Property(...) names it)
            var r = VerifyEf(@"public sealed class Account
{
    public Account(string code) { Code = code; }
    private Account() { Code = """"; }
    public long Id { get; set; }
    public string Code { get; }
}
public sealed class Db(DbContextOptions<Db> options) : DbContext(options)
{
    protected override void OnModelCreating(ModelBuilder b) { b.Entity<Account>().Property(a => a.Code).HasColumnName(""AccountCode""); }
}
public static class C { public static async Task<int> M(Db db, string code) => await db.Set<Account>().AsNoTracking().CountAsync(a => a.Code == code); }");
            Assert.True(r.Errors("M").Length == 0, r.Explain("M"));
        }

        [Fact]
        public void AUniqueFilter_ThroughOneToOneNavigations()
        {
            // #130: a one-to-one's foreign key is unique, so a row a one-to-one end of it leads to fixes it too
            var r = VerifyEf(@"public sealed class Invoice
{
    public long Id { get; set; }
    public Guid ExternalId { get; set; }
    public string Note { get; set; } = """";
}
public sealed class Payment
{
    public long Id { get; set; }
    public Guid ExternalId { get; set; }
    public Invoice? Invoice { get; set; }
    public decimal Amount { get; set; }
}
public sealed class Line
{
    public long Id { get; set; }
    public Invoice? Invoice { get; set; }
}
public sealed class Account
{
    public long Id { get; set; }
    public Member Member { get; set; } = null!;
}
public sealed class Member
{
    public long Id { get; set; }
    public Badge? Badge { get; set; }
}
public sealed class Badge
{
    public long Id { get; set; }
    public string? Code { get; set; }
    public string Serial { get; set; } = """";
    public bool Revoked { get; set; }
}
public sealed class Ledger
{
    public long RowId { get; set; }
    public Guid ExternalId { get; set; }
}
public sealed class Entry
{
    public long Id { get; set; }
    public Guid ExternalId { get; set; }
    public Ledger? Ledger { get; set; }
}
public sealed class Db(DbContextOptions<Db> options) : DbContext(options)
{
    protected override void OnModelCreating(ModelBuilder b)
    {
        b.Entity<Invoice>().HasAlternateKey(x => x.ExternalId);
        b.Entity<Payment>().HasAlternateKey(x => x.ExternalId);
        b.Entity<Payment>().HasOne(x => x.Invoice).WithOne().HasForeignKey<Payment>(""InvoiceId"");
        b.Entity<Line>().HasOne(x => x.Invoice).WithMany();
        b.Entity<Account>();
        b.Entity<Ledger>().HasKey(x => x.RowId);
        b.Entity<Entry>().HasOne(x => x.Ledger).WithOne().HasForeignKey<Entry>(""LedgerRowId"");
        b.Entity<Member>().HasOne<Account>().WithOne(a => a.Member).HasForeignKey<Member>(""AccountId"");
        b.Entity<Badge>().HasOne<Member>().WithOne(m => m.Badge).HasForeignKey<Badge>(""MemberId"");
        b.Entity<Badge>().HasIndex(x => x.Code).IsUnique().HasFilter(""[Code] IS NOT NULL"");
        b.Entity<Badge>().HasIndex(x => x.Serial).IsUnique().HasFilter(""[Revoked] = 0"");
    }
}
public sealed record Paid(Guid Payment, decimal Amount);
public sealed record InvoicePaid(Guid Invoice, Guid Payment);
public sealed class Store(Db db)
{
    public async Task<Paid?> PaymentOf(Guid invoice) =>
        (await db.Set<Payment>().AsNoTracking()
            .Where(p => p.Invoice!.ExternalId == invoice)
            .Select(p => new { p.ExternalId, p.Amount })
            .ToListAsync())
        .Select(p => new Paid(p.ExternalId, p.Amount))
        .SingleOrDefault();
    public async Task<List<InvoicePaid>> PaymentsOfInvoices() =>
        (await db.Set<Invoice>().AsNoTracking()
            .Select(i => new
            {
                i.ExternalId,
                Payment = db.Set<Payment>().Where(p => p.Invoice!.Id == i.Id).Select(p => p.ExternalId).SingleOrDefault(),
            })
            .ToListAsync())
        .Select(r => new InvoicePaid(r.ExternalId, r.Payment))
        .ToList();
    public async Task<IReadOnlyList<Ledger>> OpenLedgers() => await WithEntries(db.Set<Ledger>());
    private async Task<IReadOnlyList<Ledger>> WithEntries(IQueryable<Ledger> query)
    {
        var rows = await query
            .Select(l => new
            {
                Ledger = l,
                Entry = db.Set<Entry>().Where(e => e.Ledger!.RowId == l.RowId).Select(e => (Guid?)e.ExternalId).SingleOrDefault(),
            })
            .ToListAsync();
        foreach (var row in rows)
        {
            row.Ledger.ExternalId = row.Entry ?? row.Ledger.ExternalId;
        }
        return rows.Select(r => r.Ledger).ToList();
    }
    public async Task<Account?> AccountOfBadge(string code) =>
        await db.Set<Account>().Where(a => a.Member.Badge!.Code == code).SingleOrDefaultAsync();
    public async Task<Payment?> PaymentOfAmount(decimal amount) =>
        await db.Set<Payment>().Where(p => p.Amount == amount).SingleOrDefaultAsync();
    public async Task<Payment?> PaymentOfNote(string note) =>
        await db.Set<Payment>().Where(p => p.Invoice!.Note == note).SingleOrDefaultAsync();
    public async Task<Line?> LineOf(Guid invoice) =>
        await db.Set<Line>().Where(l => l.Invoice!.ExternalId == invoice).SingleOrDefaultAsync();
    public async Task<Badge?> BadgeOfSerial(string serial) =>
        await db.Set<Badge>().Where(b => b.Serial == serial).SingleOrDefaultAsync();
    public async Task<Badge?> BadgeOfCode(string? code) =>
        await db.Set<Badge>().Where(b => b.Code == code).SingleOrDefaultAsync();
}");
            foreach (var ok in new[] { "PaymentOf", "PaymentsOfInvoices", "OpenLedgers", "WithEntries", "AccountOfBadge" })
            {
                Assert.True(r.Errors("Store." + ok).Length == 0, ok + ": " + r.Explain("Store." + ok));
            }
            // (a column no index makes unique; a navigation of a one-to-many; an index unique only where a filter of
            // another column holds; a value that may be null, which matches each row whose column is)
            foreach (var bad in new[] { "PaymentOfAmount", "PaymentOfNote", "LineOf", "BadgeOfSerial", "BadgeOfCode" })
            {
                Assert.True(r.Errors("Store." + bad).SequenceEqual(new[] { "CSV1001" }), bad + ": " + r.Explain("Store." + bad));
            }
        }

        [Fact]
        public void AnOrderByTheKey_IsKeptAcrossASelect()
        {
            // #130: a Select maps the rows one to one, in their order
            var r = VerifyEf(@"public sealed class Charge
{
    public long Id { get; set; }
    public long AccountId { get; set; }
    public DateTime? Collected { get; set; }
}
public sealed class Db(DbContextOptions<Db> options) : DbContext(options)
{
    protected override void OnModelCreating(ModelBuilder b) => b.Entity<Charge>();
}
public sealed class Store(Db db)
{
    public async Task<DateTime?> LastCollected(long account) =>
        (await db.Set<Charge>().AsNoTracking()
            .Where(c => c.AccountId == account)
            .OrderByDescending(c => c.Id)
            .Select(c => new { c.Collected })
            .FirstOrDefaultAsync())?.Collected;
    public async Task<DateTime?> LastCollectedMember(long account) =>
        await db.Set<Charge>().AsNoTracking()
            .Where(c => c.AccountId == account)
            .OrderByDescending(c => c.Id)
            .Select(c => c.Collected)
            .FirstOrDefaultAsync();
    public async Task<DateTime?> LastCollectedByDate(long account) =>
        (await db.Set<Charge>().AsNoTracking()
            .Where(c => c.AccountId == account)
            .OrderByDescending(c => c.Collected)
            .Select(c => new { c.Collected })
            .FirstOrDefaultAsync())?.Collected;
    public async Task<DateTime?> OrderedAfter(long account) =>
        await db.Set<Charge>().AsNoTracking()
            .Where(c => c.AccountId == account)
            .Select(c => new { c.Id, c.Collected })
            .OrderByDescending(c => c.Id)
            .Select(c => c.Collected)
            .FirstOrDefaultAsync();
}");
            foreach (var ok in new[] { "LastCollected", "LastCollectedMember" })
            {
                Assert.True(r.Errors("Store." + ok).Length == 0, ok + ": " + r.Explain("Store." + ok));
            }
            // (a column that isn't unique; a key of a projection, which isn't the entity's)
            foreach (var bad in new[] { "LastCollectedByDate", "OrderedAfter" })
            {
                Assert.True(r.Errors("Store." + bad).SequenceEqual(new[] { "CSV1031" }), bad + ": " + r.Explain("Store." + bad));
            }
        }

        [Fact]
        public void AddAsyncOfANewRow_IsAsAdd()
        {
            // #130: the row made before the await is no one else's while it runs
            var r = VerifyEf(@"public sealed class Charge
{
    public long Id { get; set; }
    public long AccountId { get; set; }
}
public sealed class Db(DbContextOptions<Db> options) : DbContext(options)
{
    protected override void OnModelCreating(ModelBuilder b) => b.Entity<Charge>();
}
public sealed class Store(Db db)
{
    public void AddCharge()
    {
        db.Set<Charge>().Add(new Charge { AccountId = 1 });
        db.SaveChanges();
    }
    public async Task AddChargeAsync()
    {
        await db.Set<Charge>().AddAsync(new Charge { AccountId = 1 });
        await db.SaveChangesAsync();
    }
    public async Task AddKeyedAsync(long id)
    {
        await db.Set<Charge>().AddAsync(new Charge { Id = id, AccountId = 1 });
        await db.SaveChangesAsync();
    }
}");
            foreach (var ok in new[] { "AddCharge", "AddChargeAsync" })
            {
                Assert.True(r.Errors("Store." + ok).Length == 0, ok + ": " + r.Explain("Store." + ok));
            }
            // (a key given: another the context tracks may have it)
            Assert.True(r.Errors("Store.AddKeyedAsync").SequenceEqual(new[] { "CSV1033" }), r.Explain("Store.AddKeyedAsync"));
        }

        [Fact]
        public void AnEntrysValues_AreRead()
        {
            // #130: Entry(o).Property(x => x.P).CurrentValue is o.P; OriginalValue, a value of its type; neither writes anything
            var r = VerifyEf(@"public sealed class Invoice
{
    public long Id { get; set; }
    public Guid ExternalId { get; set; }
    public string Note { get; set; } = """";
}
public sealed class Db(DbContextOptions<Db> options) : DbContext(options)
{
    protected override void OnModelCreating(ModelBuilder b) => b.Entity<Invoice>().HasAlternateKey(x => x.ExternalId);
}
public sealed record Held(Invoice Invoice, string OriginalNote);
public sealed class Store(Db db)
{
    public async Task<Held?> HeldInvoice(Guid invoice) =>
        (await HeldAsync(db.Set<Invoice>().Where(i => i.ExternalId == invoice))).SingleOrDefault();
    private async Task<List<Held>> HeldAsync(IQueryable<Invoice> query)
    {
        var held = new List<Held>();
        foreach (var invoice in await query.OrderBy(i => i.Id).ToListAsync())
        {
            held.Add(new Held(invoice, db.Entry(invoice).Property(i => i.Note).OriginalValue));
        }
        return held;
    }
    public void Current(Invoice invoice)
    {
        var note = db.Entry(invoice).Property(i => i.Note).CurrentValue;
        Spec.Assert(note == invoice.Note);
    }
    public void Original(Invoice invoice)
    {
        var note = db.Entry(invoice).Property(i => i.Note).OriginalValue;
        Spec.Assert(note == invoice.Note);
    }
    public void SetCurrent(Invoice invoice)
    {
        db.Entry(invoice).Property(i => i.Note).CurrentValue = ""x"";
    }
}");
            foreach (var ok in new[] { "HeldInvoice", "HeldAsync", "Current" })
            {
                Assert.True(r.Errors("Store." + ok).Length == 0, ok + ": " + r.Explain("Store." + ok));
            }
            // (the original value isn't the current one; a write of one isn't translated)
            Assert.NotEmpty(r.Errors("Store.Original"));
            Assert.Contains(r["Store.SetCurrent"].Diagnostics, d => d.Id == "CSV1902");
        }

        [Fact]
        public void Smoke_CompilesAndRuns() => Assert.NotNull(VerifyEf(Model +
            "public static class C { public static int M(Shop db) { return db.Orders.Where(o => o.Total > 0).Count(); } }").Methods);
    }
}
