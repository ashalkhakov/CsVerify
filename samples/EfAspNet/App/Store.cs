global using Microsoft.EntityFrameworkCore;

namespace EfAspNet;

public sealed class Store(Db db)
{
    public async Task<Payment?> ByReceipt(string number) =>
        await db.Set<Payment>().Where(p => p.Receipt!.Number == number).SingleOrDefaultAsync();

    public async Task<Payment?> ByIdempotencyKey(OwnerId owner, Guid key) =>
        await db.Set<Payment>().Where(p => p.Holder!.Id == owner && p.IdempotencyKey == key).SingleOrDefaultAsync();

    public async Task<Payment?> ById(PaymentId id) =>
        await db.Set<Payment>().Where(p => p.ExternalId == id).SingleOrDefaultAsync();

    // (Identity's own user class, an entity of the context's model as it is: its normalized name has a unique index)
    public async Task<Microsoft.AspNetCore.Identity.IdentityUser<long>?> UserByName(string normalizedName) =>
        await db.Users.Where(u => u.NormalizedUserName == normalizedName).SingleOrDefaultAsync();
}
