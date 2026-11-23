using Layered.Data;
using Layered.Model;
using Microsoft.EntityFrameworkCore;

namespace Layered.App;

// queries of a referenced project's context (#102), by a unique index its configuration declares (#109)
public sealed class Members(Db db)
{
    public async Task<Member?> MemberByEmail(string email) => await db.Set<Member>().FirstOrDefaultAsync(m => m.Email == email);

    public async Task<Member?> MemberByEmailThroughItsSet(string email) => await db.Members.FirstOrDefaultAsync(m => m.Email == email);

    public async Task<Guest?> GuestByEmail(string email) => await db.Set<Guest>().FirstOrDefaultAsync(g => g.Email == email);

    // (one column, by a unique index: at most one value, #110)
    public async Task<long> IdByEmail(string email) => await db.Members.AsNoTracking().Where(m => m.Email == email).Select(m => m.Id).SingleOrDefaultAsync();
}
