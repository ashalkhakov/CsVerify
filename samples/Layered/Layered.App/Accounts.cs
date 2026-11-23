using Layered.Model;

namespace Layered.App;

// an internal member of Layered.Model, which grants it to Layered.App: verified also when Model isn't built with it (#116)
public static class Accounts
{
    public static long RowOf(Account a) => a.RowId;
}
