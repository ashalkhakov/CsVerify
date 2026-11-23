using Layered.Model;
using Microsoft.AspNetCore.Identity;
using Microsoft.AspNetCore.Identity.EntityFrameworkCore;
using Microsoft.EntityFrameworkCore;

namespace Layered.Data;

// the context, in a project of its own (#102), Identity's (#113); it applies Layered.Model's configurations (#109)
public sealed class Db(DbContextOptions<Db> options) : IdentityDbContext<AppUser, IdentityRole<long>, long>(options)
{
    public DbSet<Member> Members { get; set; } = null!;

    protected override void OnModelCreating(ModelBuilder modelBuilder)
    {
        base.OnModelCreating(modelBuilder);
        modelBuilder.ApplyConfigurationsFromAssembly(typeof(MemberConfiguration).Assembly);
        modelBuilder.Entity<AppUser>().HasAlternateKey(u => u.ExternalId);
    }
}
