// Written for this repository, to show Entity Framework Core used as it should be: queries in an order the database
// fixes, read without tracking when only read, a row changed by loading it tracked, a disconnected update checked
// against the concurrency token it was read with, two saves in one transaction (joined if one is open), a bulk update
// reloaded before saving, and every operation on a context awaited where it starts.
using System;
using System.Collections.Generic;
using System.ComponentModel.DataAnnotations;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using CsVerify;
using Microsoft.EntityFrameworkCore;

namespace EfShopSample
{
    public sealed class Customer
    {
        public int Id { get; set; }
        public string Email { get; set; } = "";
        public string Name { get; set; } = "";
        public List<Order> Orders { get; set; } = new List<Order>();
    }

    public sealed class Order
    {
        public int Id { get; set; }
        public int CustomerId { get; set; }
        public Customer? Customer { get; set; }
        public int Total { get; set; }
        public bool Shipped { get; set; }
        public bool IsDeleted { get; set; }
        public DateTime Placed { get; set; }
        [ConcurrencyCheck] public DateTime Updated { get; set; }
    }

    public sealed class AuditEntry
    {
        public int Id { get; set; }
        public int OrderId { get; set; }
        public string What { get; set; } = "";
    }

    public sealed class ShopContext : DbContext
    {
        public ShopContext(DbContextOptions<ShopContext> options) : base(options) { }

        // (read by tasks that run alongside each other, each on a context of its own)
        [RunsConcurrently] public DbSet<Customer> Customers => Set<Customer>();
        [RunsConcurrently] public DbSet<Order> Orders => Set<Order>();
        public DbSet<AuditEntry> Audit => Set<AuditEntry>();

        protected override void OnModelCreating(ModelBuilder b)
        {
            b.Entity<Customer>().HasIndex(c => c.Email).IsUnique();
            b.Entity<Order>().HasQueryFilter(o => !o.IsDeleted);
        }
    }

    public static class Orders
    {
        /// <summary>A customer by their email, which a unique index makes one at most.</summary>
        public static async Task<Customer?> ByEmail(ShopContext db, string email, CancellationToken ct) =>
            await db.Customers.AsNoTracking().SingleOrDefaultAsync(c => c.Email == email, ct);

        /// <summary>A page of the newest orders: ordered by a key last, so every page is the same each time.</summary>
        public static async Task<List<Order>> Newest(ShopContext db, int page, CancellationToken ct)
        {
            Spec.Requires(0 <= page && page < 100000);
            return await db.Orders.AsNoTracking()
                .OrderByDescending(o => o.Placed).ThenByDescending(o => o.Id)
                .Skip(page * 20).Take(20).ToListAsync(ct);
        }

        /// <summary>Unshipped orders above a total, deleted ones never among them.</summary>
        public static async Task<List<Order>> Large(ShopContext db, int above, CancellationToken ct)
        {
            Spec.Ensures<List<Order>>(r => Spec.Forall(0, r.Count, i => r[i].Total > above && !r[i].Shipped && !r[i].IsDeleted));
            return await db.Orders.AsNoTracking().Where(o => o.Total > above && !o.Shipped).ToListAsync(ct);
        }

        /// <summary>Ships an order: loaded tracked, changed, saved; the change tracker writes what changed.</summary>
        public static async Task<bool> Ship(IDbContextFactory<ShopContext> factory, int id, DateTime now, CancellationToken ct)
        {
            await using var db = await factory.CreateDbContextAsync(ct);
            var order = await db.Orders.FirstOrDefaultAsync(o => o.Id == id, ct);
            if (order == null) return false;
            order.Shipped = true;
            order.Updated = now;
            await db.SaveChangesAsync(ct);
            return true;
        }

        /// <summary>
        /// A disconnected update: the order read without tracking is marked modified in a new context, then changed, so
        /// EF checks the row against the token it was read with. Two saves (the order, then its audit entry, which
        /// needs nothing of the first) are in one transaction: both or neither.
        /// </summary>
        public static async Task<bool> Reprice(IDbContextFactory<ShopContext> factory, int id, int total, DateTime now, CancellationToken ct)
        {
            await using var db = await factory.CreateDbContextAsync(ct);
            await using var tx = await db.Database.BeginTransactionAsync(ct);
            var order = await db.Orders.AsNoTracking().FirstOrDefaultAsync(o => o.Id == id, ct);
            if (order == null) return false;
            db.Entry(order).State = EntityState.Modified;
            order.Total = total;
            order.Updated = now;
            await db.SaveChangesAsync(ct);
            db.Audit.Add(new AuditEntry { OrderId = id, What = "repriced" });
            await db.SaveChangesAsync(ct);
            await tx.CommitAsync(ct);
            return true;
        }

        /// <summary>Saves inside the caller's transaction when there is one, or its own.</summary>
        public static async Task Record(ShopContext db, int orderId, string what, CancellationToken ct)
        {
            var own = db.Database.CurrentTransaction == null ? await db.Database.BeginTransactionAsync(ct) : null;
            db.Audit.Add(new AuditEntry { OrderId = orderId, What = what });
            await db.SaveChangesAsync(ct);
            if (own != null)
            {
                await own.CommitAsync(ct);
                await own.DisposeAsync();
            }
        }

        /// <summary>A bulk update, then the tracked order reloaded before it is changed and saved.</summary>
        public static async Task ShipAll(IDbContextFactory<ShopContext> factory, int customerId, int keep, CancellationToken ct)
        {
            await using var db = await factory.CreateDbContextAsync(ct);
            var first = await db.Orders.FirstOrDefaultAsync(o => o.Id == keep, ct);
            await db.Orders.Where(o => o.CustomerId == customerId).ExecuteUpdateAsync(s => s.SetProperty(o => o.Shipped, true), ct);
            if (first == null) return;
            await db.Entry(first).ReloadAsync(ct);
            first.Shipped = false;
            await db.SaveChangesAsync(ct);
        }

        /// <summary>Counts in two contexts at once: each task makes its own.</summary>
        public static async Task<long> CountBoth(IDbContextFactory<ShopContext> factory, CancellationToken ct)
        {
            var a = Task.Run(async () => { await using var db = await factory.CreateDbContextAsync(ct); return await db.Orders.CountAsync(ct); });
            var b = Task.Run(async () => { await using var db = await factory.CreateDbContextAsync(ct); return await db.Customers.CountAsync(ct); });
            await Task.WhenAll(a, b);
            return (long)a.Result + b.Result;
        }
    }
}
