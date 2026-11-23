using Layered.Model;

namespace Layered.App;

// a referenced project's record struct (#111)
public static class Parcels
{
    public static int Plain(ParcelId id, int x) => x + 0;

    public static Guid ValueOf(ParcelId id) => id.Value;

    public static ParcelId Make(Guid g) => new ParcelId(g);

    public static bool Same(Guid g) => Make(g) == new ParcelId(g);
}
