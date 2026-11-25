using System.Linq.Expressions;
using Microsoft.EntityFrameworkCore;
using Microsoft.EntityFrameworkCore.Metadata.Builders;

namespace EfAspNet;

public readonly record struct OwnerId(Guid Value);

public readonly record struct PaymentId
{
    public PaymentId(Guid value)
    {
        if (value == Guid.Empty)
        {
            throw new ArgumentException("empty", nameof(value));
        }

        Value = value;
    }

    public Guid Value { get; }
}

public sealed class Owner
{
    public long RowId { get; set; }

    public OwnerId Id { get; set; }
}

public sealed class Receipt
{
    public long RowId { get; set; }

    public string? Number { get; set; }
}

public sealed class Payment
{
    public long RowId { get; set; }

    public PaymentId ExternalId { get; set; }

    public Owner? Holder { get; private set; }

    public long? ReceiptRowId { get; set; }

    public Receipt? Receipt { get; private set; }

    public Guid? IdempotencyKey { get; set; }
}

public sealed class Order
{
    public long RowId { get; set; }

    public Guid? PlatformOrder { get; set; }

    public Payment? Payment { get; set; }
}

/// <summary>As before: the key named by an expression, a Guid ExternalId when the class has none, an alternate key on it, a soft-delete filter.</summary>
public abstract class RowConfiguration<T> : IEntityTypeConfiguration<T>
    where T : class
{
    protected abstract Expression<Func<T, long>> Key { get; }

    public virtual void Configure(EntityTypeBuilder<T> builder)
    {
        builder.Property(Key).HasColumnName("Id");
        builder.HasKey(((MemberExpression)Key.Body).Member.Name);
        if (typeof(T).GetProperty("ExternalId") is null)
        {
            builder.Property<Guid>("ExternalId");
        }

        builder.HasAlternateKey("ExternalId");
        builder.Property<bool>("IsDeleted");
        builder.HasQueryFilter(x => !EF.Property<bool>(x, "IsDeleted"));
    }
}

internal sealed class OwnerConfiguration : IEntityTypeConfiguration<Owner>
{
    public void Configure(EntityTypeBuilder<Owner> builder)
    {
        builder.HasKey(o => o.RowId);
        builder.Property(o => o.Id).HasColumnName("ExternalId").HasConversion(id => id.Value, v => new OwnerId(v));
        builder.HasAlternateKey(o => o.Id);
    }
}

internal sealed class ReceiptConfiguration : RowConfiguration<Receipt>
{
    protected override Expression<Func<Receipt, long>> Key => x => x.RowId;

    public override void Configure(EntityTypeBuilder<Receipt> builder)
    {
        base.Configure(builder);
        builder.HasIndex(r => r.Number).IsUnique().HasFilter("[Number] IS NOT NULL");
    }
}

internal sealed class PaymentConfiguration : RowConfiguration<Payment>
{
    private const string Owner = "OwnerId";

    protected override Expression<Func<Payment, long>> Key => x => x.RowId;

    public override void Configure(EntityTypeBuilder<Payment> builder)
    {
        builder.Property(x => x.ExternalId).HasConversion(id => id.Value, v => new PaymentId(v));
        base.Configure(builder);
        builder.HasOne(x => x.Holder).WithMany().HasForeignKey(Owner).IsRequired();
        builder.Property(x => x.ReceiptRowId).HasColumnName("ReceiptId");
        builder.HasOne(x => x.Receipt).WithMany().HasForeignKey(x => x.ReceiptRowId);
        builder.HasIndex(Owner, nameof(Payment.IdempotencyKey)).IsUnique().HasFilter("[IdempotencyKey] IS NOT NULL AND [IsDeleted] = 0");
        builder.HasIndex(x => x.ReceiptRowId).IsUnique().HasFilter("[ReceiptId] IS NOT NULL");
    }
}

internal sealed class OrderConfiguration : RowConfiguration<Order>
{
    protected override Expression<Func<Order, long>> Key => x => x.RowId;

    public override void Configure(EntityTypeBuilder<Order> builder)
    {
        base.Configure(builder);
        builder.HasOne(x => x.Payment).WithOne().HasForeignKey<Order>("PaymentId");
    }
}

public sealed class Db(DbContextOptions<Db> options) : Microsoft.AspNetCore.Identity.EntityFrameworkCore.IdentityDbContext<Microsoft.AspNetCore.Identity.IdentityUser<long>, Microsoft.AspNetCore.Identity.IdentityRole<long>, long>(options)
{
    protected override void OnModelCreating(ModelBuilder b)
    {
        base.OnModelCreating(b);
        b.ApplyConfigurationsFromAssembly(typeof(Db).Assembly);
    }
}
