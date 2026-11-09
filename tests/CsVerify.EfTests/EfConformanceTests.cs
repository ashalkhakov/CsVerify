using System;
using System.Collections.Generic;
using System.ComponentModel.DataAnnotations;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Data.Sqlite;
using Microsoft.EntityFrameworkCore;
using Testcontainers.MsSql;
using Xunit;

namespace CsVerify.Tests
{
    /// <summary>
    /// What the verifier's model of Entity Framework Core says (MethodVerifier.EntityFramework, .EfTracker), checked
    /// against EF itself: each rule the model reports or relies on, shown to be EF's behaviour, on SQLite and on SQL
    /// Server. Where the two differ (collation, arithmetic, asynchronous commands), each test says what each does; the
    /// model claims only what holds of both.
    /// </summary>
    public abstract class EfConformanceTests : IDisposable
    {
        public sealed class Customer
        {
            public int Id { get; set; }
            public string Email { get; set; } = "";
            public string Name { get; set; } = "";
            public List<Order> Orders { get; set; } = new List<Order>();
            public string Display => Name + " <" + Email + ">";
        }

        public sealed class Order
        {
            public int Id { get; set; }
            public int CustomerId { get; set; }
            public Customer? Customer { get; set; }
            public int Total { get; set; }
            public bool IsDeleted { get; set; }
            public int? Rating { get; set; }
            [ConcurrencyCheck] public int Updated { get; set; }
        }

        public sealed class Shop : DbContext
        {
            private readonly Action<DbContextOptionsBuilder> _configure;
            public Shop(Action<DbContextOptionsBuilder> configure) { _configure = configure; }
            public DbSet<Customer> Customers => Set<Customer>();
            public DbSet<Order> Orders => Set<Order>();
            protected override void OnConfiguring(DbContextOptionsBuilder o) => _configure(o);
            protected override void OnModelCreating(ModelBuilder b)
            {
                b.Entity<Customer>().HasIndex(c => c.Email).IsUnique();
                b.Entity<Order>().HasQueryFilter(o => !o.IsDeleted);
            }
        }

        /// <summary>How a context of this provider connects (to a database of this test's own).</summary>
        protected abstract void Configure(DbContextOptionsBuilder o);

        /// <summary>The same, with SQL's null semantics (UseRelationalNulls).</summary>
        protected abstract void ConfigureRelationalNulls(DbContextOptionsBuilder o);

        /// <summary>Does the provider's default collation ignore case and trailing spaces (SQL Server's does)?</summary>
        protected abstract bool CaseInsensitive { get; }

        /// <summary>Does it run commands asynchronously (so two can overlap)? SQLite's run synchronously.</summary>
        protected abstract bool TrulyAsync { get; }

        protected EfConformanceTests() { }

        /// <summary>The database made and filled (called by each provider's constructor).</summary>
        protected void Seed()
        {
            using var db = New();
            db.Database.EnsureDeleted();
            db.Database.EnsureCreated();
            var ann = new Customer { Email = "ann@example.com", Name = "Ann" };
            var bob = new Customer { Email = "bob@example.com", Name = "Bob" };
            db.Customers.AddRange(ann, bob, new Customer { Email = "ann2@example.com", Name = "Ann" });
            db.Orders.AddRange(new Order { Customer = ann, Total = 10, Rating = 3 }, new Order { Customer = ann, Total = 50, Rating = 5 },
                               new Order { Customer = bob, Total = 70 }, new Order { Customer = bob, Total = 90, IsDeleted = true });
            db.SaveChanges();
        }

        public virtual void Dispose() { }

        protected Shop New() => new Shop(Configure);

        // ---- queries ----

        [Fact]
        public void Rows_PassTheirPredicateAndTheQueryFilter()
        {
            using var db = New();
            var rows = db.Orders.AsNoTracking().Where(o => o.Total > 20).ToList();
            Assert.All(rows, o => Assert.True(o.Total > 20 && !o.IsDeleted));
            Assert.Contains(db.Orders.AsNoTracking().IgnoreQueryFilters().ToList(), o => o.IsDeleted);
        }

        [Fact]
        public void Navigations_AreNullUnlessIncluded()
        {
            using var db = New();
            Assert.All(db.Orders.AsNoTracking().ToList(), o => Assert.Null(o.Customer));
            Assert.All(db.Orders.AsNoTracking().Include(o => o.Customer).ToList(), o => Assert.NotNull(o.Customer));
        }

        [Fact]
        public void Include_LoadsTheRowTheForeignKeyNames()
        {
            using var db = New();
            Assert.All(db.Orders.AsNoTracking().Include(o => o.Customer).ToList(), o => Assert.True(o.Customer != null && o.Customer.Id == o.CustomerId));
            Assert.All(db.Orders.Include(o => o.Customer).ToList(), o => Assert.True(o.Customer != null && o.Customer.Id == o.CustomerId));
        }

        [Fact]
        public void Include_ACollection_LoadsTheRowsWithThisKey_ThroughTheQueryFilter()
        {
            using var db = New();
            var customers = db.Customers.AsNoTracking().Include(c => c.Orders).ToList();
            Assert.All(customers, c => Assert.All(c.Orders, o => Assert.True(o.CustomerId == c.Id && !o.IsDeleted)));
            Assert.Contains(customers, c => c.Orders.Count == 2);
        }

        [Fact]
        public void Collections_NotIncluded_AreAsTheInitializerMadeThem()
        {
            using var db = New();
            Assert.All(db.Customers.AsNoTracking().ToList(), c => Assert.Empty(c.Orders));
        }

        [Fact]
        public void ThenInclude_LoadsTheNextLevel()
        {
            using var db = New();
            Assert.All(db.Orders.Include(o => o.Customer).ThenInclude(c => c!.Orders).ToList(),
                o => Assert.All(o.Customer!.Orders, p => Assert.True(p.CustomerId == o.CustomerId && !p.IsDeleted)));
        }

        [Fact]
        public void Include_ACycleWithoutTracking_Throws()
        {
            using var db = New();
            Assert.Throws<InvalidOperationException>(() => db.Orders.AsNoTracking().Include(o => o.Customer).ThenInclude(c => c!.Orders).ToList());
            db.Orders.AsNoTrackingWithIdentityResolution().Include(o => o.Customer).ThenInclude(c => c!.Orders).ToList();
        }

        [Fact]
        public void Single_OnTwoMatchingRows_Throws()
        {
            using var db = New();
            Assert.Throws<InvalidOperationException>(() => db.Customers.AsNoTracking().SingleOrDefault(c => c.Name == "Ann"));
            Assert.NotNull(db.Customers.AsNoTracking().SingleOrDefault(c => c.Email == "ann@example.com"));
        }

        [Fact]
        public void UniqueIndex_RefusesASecondRow()
        {
            using var db = New();
            db.Customers.Add(new Customer { Email = "ann@example.com", Name = "Another" });
            Assert.Throws<DbUpdateException>(() => db.SaveChanges());
        }

        [Fact]
        public void Translation_AProgramMethodOfARow_Throws()
        {
            using var db = New();
            Assert.Throws<InvalidOperationException>(() => db.Orders.Count(o => Big(o)));
            Assert.Throws<InvalidOperationException>(() => db.Customers.Count(c => c.Display.Length > 3));
        }

        private static bool Big(Order o) => o.Total > 40;

        [Fact]
        public void Translation_WhatTheModelAccepts_Translates()
        {
            using var db = New();
            var ids = new List<int> { 1, 2 };
            int limit = Limit(10);
            Assert.True(db.Customers.Count(c => c.Name.StartsWith("A") && ids.Contains(c.Id)) >= 0);
            Assert.True(db.Customers.Count(c => c.Name.ToUpper() == "ANN" || c.Email.Contains("@") || c.Name.Length > 2) >= 0);
            Assert.True(db.Orders.Count(o => Math.Abs(o.Total - limit) > 3 && o.Total > Limit(1)) >= 0);
        }

        private static int Limit(int x) => x * 2;

        // ---- the change tracker ----

        [Fact]
        public void TrackingQuery_GivesTheTrackedInstance_WithItsValues()
        {
            using var db = New();
            var first = db.Orders.Single(o => o.Total == 10);
            first.Total = 11; // (in memory only)
            var again = db.Orders.Single(o => o.Id == first.Id);
            Assert.Same(first, again);
            Assert.Equal(11, again.Total);
            // so a tracking query's rows needn't pass its predicate: a tracked one keeps its own values
            Assert.Contains(db.Orders.Where(o => o.Total == 10).ToList(), o => o.Total == 11);
        }

        [Fact]
        public void Local_IsWhatTheContextTracks_ButWhatItDeletes()
        {
            using var db = New();
            Assert.Empty(db.Orders.Local);
            db.Orders.AsNoTracking().ToList();
            Assert.Empty(db.Orders.Local); // (rows read without tracking aren't tracked)
            var read = db.Orders.OrderBy(o => o.Id).ToList();
            var added = new Order { CustomerId = read[0].CustomerId, Total = 1 };
            db.Orders.Add(added);
            read[1].Total = 7;
            db.Orders.Remove(read[2]);
            Assert.Equal(new[] { read[0], read[1], added }.OrderBy(o => o.Total), db.Orders.Local.OrderBy(o => o.Total));
            Assert.Equal(EntityState.Modified, db.Entry(read[1]).State);
        }

        [Fact]
        public void Attach_ASecondInstanceOfARow_Throws()
        {
            using var db = New();
            db.Attach(new Order { Id = 1 });
            Assert.Throws<InvalidOperationException>(() => db.Attach(new Order { Id = 1 }));
        }

        [Fact]
        public void Attach_WithAKeyNotSet_Adds()
        {
            using var db = New();
            Assert.Equal(EntityState.Added, db.Attach(new Order { Total = 1 }).State);
        }

        [Fact]
        public void Update_TakesTheGraph()
        {
            using var db = New();
            var order = db.Orders.AsNoTracking().Include(o => o.Customer).First(o => o.Total == 10);
            db.Update(order);
            Assert.Equal(EntityState.Modified, db.Entry(order.Customer!).State);
        }

        [Fact]
        public void Token_ChangedBeforeUpdate_FailsTheSave()
        {
            using (var db = New())
            {
                var order = db.Orders.AsNoTracking().First(o => o.Total == 50);
                order.Updated = 7;
                db.Update(order);
                Assert.Throws<DbUpdateConcurrencyException>(() => db.SaveChanges());
            }
            using (var db = New())
            {
                var order = db.Orders.AsNoTracking().First(o => o.Total == 50);
                db.Update(order);
                order.Updated = 7;
                db.SaveChanges();
            }
        }

        [Fact]
        public void ExecuteUpdate_LeavesTrackedCopiesAsTheyWere()
        {
            using var db = New();
            var order = db.Orders.Single(o => o.Total == 70);
            db.Orders.Where(o => o.Id == order.Id).ExecuteUpdate(s => s.SetProperty(o => o.Total, 0));
            Assert.Equal(70, order.Total);
            db.Entry(order).Reload();
            Assert.Equal(0, order.Total);
        }

        // ---- transactions ----

        [Fact]
        public void BeginTransaction_WithOneOpen_Throws()
        {
            using var db = New();
            using var tx = db.Database.BeginTransaction();
            Assert.Throws<InvalidOperationException>(() => db.Database.BeginTransaction());
            Assert.NotNull(db.Database.CurrentTransaction);
        }

        [Fact]
        public void Rollback_LeavesTheTrackerAsIfSaved()
        {
            using var db = New();
            var tx = db.Database.BeginTransaction();
            var added = new Customer { Email = "new@example.com", Name = "New" };
            db.Customers.Add(added);
            db.SaveChanges();
            tx.Rollback();
            Assert.Equal(EntityState.Unchanged, db.Entry(added).State); // (the tracker says saved)
            using var other = New();
            Assert.False(other.Customers.Any(c => c.Email == "new@example.com")); // (the database says not)
        }

        [Fact]
        public void Commit_BeforeSaving_LeavesTheChangesOut()
        {
            using (var db = New())
            {
                using var tx = db.Database.BeginTransaction();
                db.Customers.Add(new Customer { Email = "late@example.com", Name = "Late" });
                tx.Commit();
            }
            using var other = New();
            Assert.False(other.Customers.Any(c => c.Email == "late@example.com"));
        }
        // ---- where SQLite and SQL Server differ ----

        // ---- joins: on a key the database and .NET compare alike, the pairs LINQ to Objects gives, in some order ----

        private static List<string> Sorted<T>(IEnumerable<T> rows) => rows.Select(r => r?.ToString() ?? "null").OrderBy(s => s, StringComparer.Ordinal).ToList();

        [Fact]
        public void Join_GivesThePairsWithEqualKeys()
        {
            using var db = New();
            var orders = db.Orders.AsNoTracking().ToList();
            var customers = db.Customers.AsNoTracking().ToList();
            Assert.Equal(Sorted(orders.Join(customers, o => o.CustomerId, c => c.Id, (o, c) => (o.Id, c.Id))),
                         Sorted(db.Orders.Join(db.Customers, o => o.CustomerId, c => c.Id, (o, c) => new { O = o.Id, C = c.Id }).ToList().Select(x => (x.O, x.C))));
        }

        [Fact]
        public void LeftJoin_AddsTheRowsThatMatchNone()
        {
            using var db = New();
            var orders = db.Orders.AsNoTracking().ToList();
            var customers = db.Customers.AsNoTracking().ToList();
            var left = db.Customers.LeftJoin(db.Orders, c => c.Id, o => o.CustomerId, (c, o) => new { C = c.Id, O = o == null ? -1 : o.Id }).ToList();
            Assert.Equal(Sorted(customers.LeftJoin(orders, c => c.Id, o => o.CustomerId, (c, o) => (c.Id, o == null ? -1 : o.Id))), Sorted(left.Select(x => (x.C, x.O))));
            Assert.Contains(left, x => x.O == -1); // (Ann's second account has no orders)
        }

        [Fact]
        public void RightJoin_FiltersTheLeftSideAfterTheJoin()
        {
            // EF Core applies the left side's query filter to the joined rows (WHERE NOT o.IsDeleted), which drops the
            // right side's rows that match none: the model doesn't read a RightJoin on a database
            using var db = New();
            var right = db.Orders.RightJoin(db.Customers, o => o.CustomerId, c => c.Id, (o, c) => new { O = o == null ? -1 : o.Id, C = c.Id }).ToList();
            Assert.DoesNotContain(right, x => x.O == -1);
            var unfiltered = db.Orders.IgnoreQueryFilters().RightJoin(db.Customers, o => o.CustomerId, c => c.Id, (o, c) => new { O = o == null ? -1 : o.Id, C = c.Id }).ToList();
            Assert.Contains(unfiltered, x => x.O == -1);
        }

        [Fact]
        public void Join_OnANullKey_MatchesNothing()
        {
            // as in LINQ to Objects, whose definition says so; the model reads only joins on keys that can't be null
            using var db = New();
            var orders = db.Orders.AsNoTracking().ToList();
            Assert.Equal(0, orders.Join(orders, a => (int?)null, b => (int?)null, (a, b) => a.Id).Count());
            Assert.Equal(0, db.Orders.Join(db.Orders, a => a.Total > 1000 ? a.Id : (int?)null, b => b.Total > 1000 ? b.Id : (int?)null, (a, b) => a.Id).Count());
        }

        // ---- nulls: by default, comparisons of nullable columns mean what they do in C#; with UseRelationalNulls, SQL's ----

        private static readonly System.Linq.Expressions.Expression<Func<Order, bool>>[] NullablePredicates =
        {
            o => o.Rating != 3, o => o.Rating == 3, o => !(o.Rating == 3), o => o.Rating > 3, o => !(o.Rating > 3), o => o.Rating <= 3,
            o => !(o.Rating > 3) && o.Total > 0, o => o.Rating == null || o.Rating < 4, o => !(o.Rating < 4 || o.Total > 60),
        };

        [Fact]
        public void Nulls_ByDefault_CompareAsInCSharp()
        {
            using var db = New();
            var orders = db.Orders.AsNoTracking().ToList();
            foreach (var p in NullablePredicates)
                Assert.True(orders.Count(p.Compile()) == db.Orders.Count(p), p.ToString());
        }

        [Fact]
        public void Nulls_Relational_DropRowsWhereAComparisonIsUnknown()
        {
            using var db = new Shop(ConfigureRelationalNulls);
            var orders = db.Orders.AsNoTracking().ToList();
            Assert.Equal(3, orders.Count(o => o.Rating != 3 || o.Rating == 3));
            Assert.Equal(2, db.Orders.Count(o => o.Rating != 3 || o.Rating == 3)); // (the order without a rating in neither)
            Assert.Equal(1, db.Orders.Count(o => !(o.Rating == 3))); // (EF takes the NOT into the comparison: Rating <> 3)
            // (other comparisons, and against null, stay C#'s: EF compensates for them)
            Assert.Equal(orders.Count(o => !(o.Rating > 3)), db.Orders.Count(o => !(o.Rating > 3)));
            Assert.Equal(orders.Count(o => o.Rating == null), db.Orders.Count(o => o.Rating == null));
        }

        [Fact]
        public void Collation_EqualStringsMatch_AndCaseMayNot()
        {
            using var db = New();
            Assert.Equal(1, db.Customers.Count(c => c.Email == "ann@example.com"));
            // the model: only that the database's equality is an equivalence equal strings satisfy
            Assert.Equal(CaseInsensitive ? 1 : 0, db.Customers.Count(c => c.Email == "ANN@EXAMPLE.COM"));
            Assert.Equal(CaseInsensitive ? 1 : 0, db.Customers.Count(c => c.Email == "ann@example.com  "));
        }

        [Fact]
        public void Collation_AUniqueIndexComparesAsTheDatabaseDoes()
        {
            using var db = New();
            db.Customers.Add(new Customer { Email = "ANN@example.com", Name = "Loud" });
            if (CaseInsensitive) Assert.Throws<DbUpdateException>(() => db.SaveChanges());
            else db.SaveChanges();
        }

        [Fact]
        public void Arithmetic_OverflowInAQuery()
        {
            using var db = New();
            // SQL Server fails the query; SQLite goes on in floating point: the model says nothing of either
            // (a query may throw; what it gives passes its predicate)
            Func<int> big = () => db.Orders.Count(o => o.Total * 100000000 > 0);
            if (CaseInsensitive) Assert.ThrowsAny<Exception>(() => big());
            else Assert.Equal(3, big());
        }

        [Fact]
        public async Task TwoOperationsAtOnce_Throw()
        {
            using var db = New();
            var first = db.Orders.ToListAsync();
            if (!TrulyAsync) { await first; return; } // (SQLite's has finished before the next starts)
            await Assert.ThrowsAsync<InvalidOperationException>(() => db.Customers.ToListAsync());
            await first;
        }
    }

    /// <summary>On SQLite, in memory.</summary>
    public sealed class SqliteConformanceTests : EfConformanceTests
    {
        private readonly SqliteConnection _connection = new SqliteConnection("DataSource=:memory:");
        public SqliteConformanceTests() { _connection.Open(); Seed(); }
        protected override void Configure(DbContextOptionsBuilder o) => o.UseSqlite(_connection);
        protected override void ConfigureRelationalNulls(DbContextOptionsBuilder o) => o.UseSqlite(_connection, x => x.UseRelationalNulls());
        protected override bool CaseInsensitive => false;
        protected override bool TrulyAsync => false;
        public override void Dispose() => _connection.Dispose();
    }

    /// <summary>
    /// SQL Server in a container, started once for these tests (Testcontainers: Docker must be running); or the server
    /// CSVERIFY_SQLSERVER names, a connection string without a database (LocalDB: "Server=(localdb)\MSSQLLocalDB").
    /// </summary>
    public sealed class SqlServerFixture : IAsyncLifetime
    {
        private MsSqlContainer? _container;
        public string Server { get; private set; } = "";

        public async Task InitializeAsync()
        {
            var given = Environment.GetEnvironmentVariable("CSVERIFY_SQLSERVER");
            if (!string.IsNullOrEmpty(given)) { Server = given; return; }
            _container = new MsSqlBuilder().WithImage("mcr.microsoft.com/mssql/server:2022-latest").Build();
            await _container.StartAsync();
            Server = _container.GetConnectionString();
        }

        public async Task DisposeAsync()
        {
            if (_container != null) await _container.DisposeAsync();
        }
    }

    /// <summary>On SQL Server: a database for each test, dropped after it.</summary>
    public sealed class SqlServerConformanceTests : EfConformanceTests, IClassFixture<SqlServerFixture>
    {
        private readonly string _connection;

        public SqlServerConformanceTests(SqlServerFixture server)
        {
            var b = new Microsoft.Data.SqlClient.SqlConnectionStringBuilder(server.Server) { InitialCatalog = "csverify_" + Guid.NewGuid().ToString("N"), TrustServerCertificate = true };
            _connection = b.ConnectionString;
            Seed();
        }

        protected override void Configure(DbContextOptionsBuilder o) => o.UseSqlServer(_connection);
        protected override void ConfigureRelationalNulls(DbContextOptionsBuilder o) => o.UseSqlServer(_connection, x => x.UseRelationalNulls());
        protected override bool CaseInsensitive => true;
        protected override bool TrulyAsync => true;

        public override void Dispose()
        {
            using var db = New();
            db.Database.EnsureDeleted();
        }
    }
}
