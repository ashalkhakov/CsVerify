using Microsoft.AspNetCore.Identity;

namespace Layered.Model;

// the application's user, of ASP.NET Core Identity (#113): its key Identity's Id, its ExternalId an alternate key
public class AppUser : IdentityUser<long>
{
    public Guid ExternalId { get; set; }
}
