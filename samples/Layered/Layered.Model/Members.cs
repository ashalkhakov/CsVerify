using Microsoft.EntityFrameworkCore;
using Microsoft.EntityFrameworkCore.Metadata.Builders;

namespace Layered.Model;

// entities configured here, applied by the context in Layered.Data (#109): Member has a DbSet property, Guest none
public class Member
{
    public long Id { get; set; }

    public string Email { get; set; } = "";
}

public class Guest
{
    public long Id { get; set; }

    public string Email { get; set; } = "";
}

public sealed class MemberConfiguration : IEntityTypeConfiguration<Member>
{
    public void Configure(EntityTypeBuilder<Member> builder) => builder.HasIndex(m => m.Email).IsUnique();
}

public sealed class GuestConfiguration : IEntityTypeConfiguration<Guest>
{
    public void Configure(EntityTypeBuilder<Guest> builder) => builder.HasIndex(g => g.Email).IsUnique();
}
