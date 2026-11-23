using Layered.Data;
using Layered.Model;
using Microsoft.EntityFrameworkCore;

namespace Layered.App;

// a referenced project's Identity user, by its key and by its alternate key, through Identity's Users (#113)
public sealed class Users(Db db)
{
    public async Task<AppUser?> ByKey(long id) => await db.Set<AppUser>().AsNoTracking().FirstOrDefaultAsync(u => u.Id == id);

    public async Task<AppUser?> ByExternalId(Guid g) => await db.Users.AsNoTracking().FirstOrDefaultAsync(u => u.ExternalId == g);

    public async Task<string?> NameOf(long id) => await db.Users.AsNoTracking().Where(u => u.Id == id).Select(u => u.UserName).FirstOrDefaultAsync();
}
