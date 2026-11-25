using Microsoft.EntityFrameworkCore;

namespace EfCoreOnly;

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

public sealed class Db(DbContextOptions<Db> options) : DbContext(options)
{
    protected override void OnModelCreating(ModelBuilder b)
    {
        b.Entity<Owner>().HasKey(o => o.RowId);
        b.Entity<Payment>().HasKey(p => p.RowId);
        b.Entity<Payment>().HasOne(p => p.Holder).WithMany().HasForeignKey("OwnerId").IsRequired();
        b.Entity<Payment>().HasIndex("OwnerId", nameof(Payment.IdempotencyKey)).IsUnique();
    }
}

public sealed class Store(Db db)
{
    // one row at most: (OwnerId, IdempotencyKey) is unique, OwnerId the shadow foreign key, as EF's model has it
    public async Task<Payment?> ByKey(long owner, Guid key) =>
        await db.Set<Payment>().Where(p => EF.Property<long>(p, "OwnerId") == owner && p.IdempotencyKey == key).SingleOrDefaultAsync();
}
