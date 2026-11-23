using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using CsVerify.Verifier;
using Microsoft.AspNetCore.Identity;
using Microsoft.AspNetCore.Identity.EntityFrameworkCore;
using Microsoft.EntityFrameworkCore;
using Xunit;

namespace CsVerify.Tests
{
    /// <summary>
    /// The Spec library's model of ASP.NET Core Identity (CsVerify.Ef.Identity, a [ModelOf] for each of its contexts that
    /// configures a model) compared with the model EF builds of an IdentityDbContext: each entity's key, its unique
    /// sets (unique indexes, alternate keys) and its concurrency tokens, the same. Each of Identity's types is a class
    /// of the program's here, so that each is an entity the verifier reads.
    /// </summary>
    public class IdentityModelTests
    {
        public sealed class AppUser : IdentityUser<long> { }
        public sealed class AppRole : IdentityRole<long> { }
        public sealed class AppUserClaim : IdentityUserClaim<long> { }
        public sealed class AppUserRole : IdentityUserRole<long> { }
        public sealed class AppUserLogin : IdentityUserLogin<long> { }
        public sealed class AppRoleClaim : IdentityRoleClaim<long> { }
        public sealed class AppUserToken : IdentityUserToken<long> { }

        public sealed class Users : IdentityDbContext<AppUser, AppRole, long, AppUserClaim, AppUserRole, AppUserLogin, AppRoleClaim, AppUserToken>
        {
            public Users(DbContextOptions<Users> options) : base(options) { }
        }

        private const string Program = @"using System;
using Microsoft.AspNetCore.Identity;
using Microsoft.AspNetCore.Identity.EntityFrameworkCore;
using Microsoft.EntityFrameworkCore;
public sealed class AppUser : IdentityUser<long> { }
public sealed class AppRole : IdentityRole<long> { }
public sealed class AppUserClaim : IdentityUserClaim<long> { }
public sealed class AppUserRole : IdentityUserRole<long> { }
public sealed class AppUserLogin : IdentityUserLogin<long> { }
public sealed class AppRoleClaim : IdentityRoleClaim<long> { }
public sealed class AppUserToken : IdentityUserToken<long> { }
public sealed class Users : IdentityDbContext<AppUser, AppRole, long, AppUserClaim, AppUserRole, AppUserLogin, AppRoleClaim, AppUserToken>
{
    public Users(DbContextOptions<Users> options) : base(options) { }
}";

        private static string Names(IEnumerable<string> names) => string.Join(",", names.OrderBy(n => n, StringComparer.Ordinal));

        private static string Sets(IEnumerable<IEnumerable<string>> sets) => string.Join(" ", sets.Select(Names).OrderBy(n => n, StringComparer.Ordinal));

        [Fact]
        public void TheSpecLibrarysModel_IsTheOneEfBuilds()
        {
            using var db = new Users(new DbContextOptionsBuilder<Users>().UseSqlite("Data Source=:memory:").Options);
            var ef = db.Model;
            var model = Engine.EfModelOf(new[] { ("Identity.cs", Program) }, EfHarness.Options());
            Assert.NotNull(model);
            var types = new[] { typeof(AppUser), typeof(AppRole), typeof(AppUserClaim), typeof(AppUserRole), typeof(AppUserLogin), typeof(AppRoleClaim), typeof(AppUserToken) };
            Assert.Equal(types.Length, ef.GetEntityTypes().Count());
            foreach (var type in types)
            {
                var et = ef.FindEntityType(type)!;
                var e = model.Entities.SingleOrDefault(x => x.Type.Name == type.Name);
                Assert.True(e != null, type.Name + " isn't an entity of the verifier's model");
                Assert.False(e.Unread, type.Name + " is configured by a library context the Spec library has no model of");
                Assert.Equal(Names(et.FindPrimaryKey()!.Properties.Select(p => p.Name)), Names(e.Key.Select(p => p.Name)));
                var unique = et.GetIndexes().Where(i => i.IsUnique).Select(i => i.Properties.Select(p => p.Name))
                    .Concat(et.GetKeys().Where(k => !k.IsPrimaryKey()).Select(k => k.Properties.Select(p => p.Name)));
                Assert.True(Sets(unique) == Sets(e.Unique.Select(u => u.Select(p => p.Name))), $"{type.Name}'s unique sets: EF's {Sets(unique)}, the verifier's {Sets(e.Unique.Select(u => u.Select(p => p.Name)))}");
                Assert.True(Names(et.GetProperties().Where(p => p.IsConcurrencyToken).Select(p => p.Name)) == Names(e.Tokens.Select(p => p.Name)),
                    $"{type.Name}'s concurrency tokens: EF's {Names(et.GetProperties().Where(p => p.IsConcurrencyToken).Select(p => p.Name))}, the verifier's {Names(e.Tokens.Select(p => p.Name))}");
            }
        }
    }
}
