#nullable enable
namespace CsVerify.Ef.Identity
{
    using System;
    using Microsoft.AspNetCore.Identity;
    using Microsoft.AspNetCore.Identity.EntityFrameworkCore;
    using Microsoft.EntityFrameworkCore;

    /// <summary>
    /// ASP.NET Core Identity's model of its users, as IdentityUserContext's OnModelCreating configures it: their keys,
    /// unique indexes and concurrency tokens. Compiled in only for programs that reference Identity's EF Core stores.
    /// Passkeys are mapped by Identity's schema version (IdentityOptions.Stores), which the program sets at run time:
    /// not here, so a passkey entity of the program's is one the verifier reads nothing of.
    /// </summary>
    [ModelOf(typeof(IdentityUserContext<,,,,,>))]
    internal static class UserContextModel<TUser, TKey, TUserClaim, TUserLogin, TUserToken, TUserPasskey>
        where TUser : IdentityUser<TKey>
        where TKey : IEquatable<TKey>
        where TUserClaim : IdentityUserClaim<TKey>
        where TUserLogin : IdentityUserLogin<TKey>
        where TUserToken : IdentityUserToken<TKey>
        where TUserPasskey : IdentityUserPasskey<TKey>
    {
        public static void OnModelCreating(ModelBuilder builder)
        {
            builder.Entity<TUser>(b =>
            {
                b.HasKey(u => u.Id);
                b.HasIndex(u => u.NormalizedUserName).HasDatabaseName("UserNameIndex").IsUnique();
                b.Property(u => u.ConcurrencyStamp).IsConcurrencyToken();
            });
            builder.Entity<TUserClaim>(b => b.HasKey(uc => uc.Id));
            builder.Entity<TUserLogin>(b => b.HasKey(l => new { l.LoginProvider, l.ProviderKey }));
            builder.Entity<TUserToken>(b => b.HasKey(t => new { t.UserId, t.LoginProvider, t.Name }));
        }
    }

    /// <summary>Identity's model of its roles, as IdentityDbContext's OnModelCreating configures it (after its users').</summary>
    [ModelOf(typeof(IdentityDbContext<,,,,,,,,>))]
    internal static class DbContextModel<TUser, TRole, TKey, TUserClaim, TUserRole, TUserLogin, TRoleClaim, TUserToken, TUserPasskey>
        where TUser : IdentityUser<TKey>
        where TRole : IdentityRole<TKey>
        where TKey : IEquatable<TKey>
        where TUserClaim : IdentityUserClaim<TKey>
        where TUserRole : IdentityUserRole<TKey>
        where TUserLogin : IdentityUserLogin<TKey>
        where TRoleClaim : IdentityRoleClaim<TKey>
        where TUserToken : IdentityUserToken<TKey>
        where TUserPasskey : IdentityUserPasskey<TKey>
    {
        public static void OnModelCreating(ModelBuilder builder)
        {
            builder.Entity<TRole>(b =>
            {
                b.HasKey(r => r.Id);
                b.HasIndex(r => r.NormalizedName).HasDatabaseName("RoleNameIndex").IsUnique();
                b.Property(r => r.ConcurrencyStamp).IsConcurrencyToken();
            });
            builder.Entity<TRoleClaim>(b => b.HasKey(rc => rc.Id));
            builder.Entity<TUserRole>(b => b.HasKey(r => new { r.UserId, r.RoleId }));
        }
    }
}
