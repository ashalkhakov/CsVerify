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
        public void Smoke_CompilesAndRuns() => Assert.NotNull(VerifyEf(Model +
            "public static class C { public static int M(Shop db) { return db.Orders.Where(o => o.Total > 0).Count(); } }").Methods);
    }
}
