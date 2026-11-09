// Written for this repository: Entity Framework Core misused, one planted bug in each method.
using System;
using System.Collections.Generic;
using System.ComponentModel.DataAnnotations;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using CsVerify;
using Microsoft.EntityFrameworkCore;

namespace EfStoreBugs
{
    public sealed class Product
    {
        public int Id { get; set; }
        public string Sku { get; set; } = "";
        public string Name { get; set; } = "";
        public int Stock { get; set; }
        public Category? Category { get; set; }
        [Timestamp] public byte[]? Version { get; set; }
        public string Label => Sku + " " + Name;
    }

    public sealed class Category
    {
        public int Id { get; set; }
        public string Title { get; set; } = "";
    }

    public sealed class StoreContext : DbContext
    {
        public DbSet<Product> Products => Set<Product>();
        public DbSet<Category> Categories => Set<Category>();
        protected override void OnModelCreating(ModelBuilder b) => b.Entity<Product>().HasIndex(p => p.Sku).IsUnique();
    }

    public static class StoreBugs
    {
        /// <summary>The first in no order: which product comes back is up to the database.</summary>
        public static async Task<Product?> AnyLowStock(StoreContext db) => await db.Products.AsNoTracking().FirstOrDefaultAsync(p => p.Stock < 5);

        /// <summary>By name, which nothing makes unique: two matching rows make SingleOrDefault throw.</summary>
        public static async Task<Product?> ByName(StoreContext db, string name) => await db.Products.AsNoTracking().SingleOrDefaultAsync(p => p.Name == name);

        [Pure] private static bool Scarce(Product p) => p.Stock < 3;

        /// <summary>A method of the program in a query: EF can't send it to the database, and throws.</summary>
        public static async Task<int> CountScarce(StoreContext db) => await db.Products.CountAsync(p => Scarce(p));

        /// <summary>A property computed in C#, not a column: EF can't translate it.</summary>
        public static async Task<int> CountLabelled(StoreContext db) => await db.Products.CountAsync(p => p.Label.Length > 10);

        /// <summary>Update of a product loaded with its category: the category's row is rewritten too.</summary>
        public static async Task Restock(int id, int stock)
        {
            using var db = new StoreContext();
            var p = await db.Products.AsNoTracking().Include(x => x.Category).FirstOrDefaultAsync(x => x.Id == id);
            if (p == null) return;
            p.Stock = stock;
            db.Update(p);
            await db.SaveChangesAsync();
        }

        /// <summary>Two instances of one row attached to one context: EF throws.</summary>
        public static void AttachTwice(int id)
        {
            using var db = new StoreContext();
            db.Attach(new Product { Id = id });
            db.Attach(new Product { Id = id });
        }

        /// <summary>Saves again after a failed save: what the context tracks no longer matches the database.</summary>
        public static async Task Retry(StoreContext db)
        {
            try { await db.SaveChangesAsync(); }
            catch (DbUpdateConcurrencyException) { await db.SaveChangesAsync(); }
        }

        /// <summary>A bulk update, then a stale tracked copy saved over it.</summary>
        public static async Task Zero(int id)
        {
            using var db = new StoreContext();
            var p = await db.Products.FirstOrDefaultAsync(x => x.Id == id);
            if (p == null) return;
            await db.Products.Where(x => x.Id == id).ExecuteUpdateAsync(s => s.SetProperty(x => x.Stock, 0));
            p.Name = p.Name + "*";
            await db.SaveChangesAsync();
        }

        /// <summary>Writes a row version, which the database sets.</summary>
        public static void Bump(Product p) { p.Version = new byte[8]; }

        /// <summary>Two saves without a transaction: if the second fails, the first stays.</summary>
        public static async Task Split(int id)
        {
            using var db = new StoreContext();
            db.Products.Add(new Product { Sku = "a" });
            await db.SaveChangesAsync();
            db.Categories.Add(new Category { Title = "b" });
            await db.SaveChangesAsync();
        }

        /// <summary>A transaction begun on a context that may have one open: EF throws.</summary>
        public static async Task Nested(StoreContext db)
        {
            await using var tx = await db.Database.BeginTransactionAsync();
            await db.SaveChangesAsync();
            await tx.CommitAsync();
        }

        /// <summary>Two queries at once on one context: EF throws.</summary>
        public static async Task Both(StoreContext db)
        {
            var a = db.Products.ToListAsync();
            var b = db.Categories.ToListAsync();
            await Task.WhenAll(a, b);
        }

        /// <summary>A context used from Task.Run, alongside its caller.</summary>
        public static async Task<int> Background(StoreContext db) => await Task.Run(() => db.Products.Count());
    }
}
