using Layered.Model;
using Microsoft.EntityFrameworkCore;

namespace Layered.Data;

// the context, in a project of its own (#102); it applies Layered.Model's configurations (#109)
public sealed class Db(DbContextOptions<Db> options) : DbContext(options)
{
    public DbSet<Member> Members { get; set; } = null!;

    protected override void OnModelCreating(ModelBuilder modelBuilder) =>
        modelBuilder.ApplyConfigurationsFromAssembly(typeof(MemberConfiguration).Assembly);
}
