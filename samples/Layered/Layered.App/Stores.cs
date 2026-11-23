using CsVerify;
using Layered.Model;
using Microsoft.Extensions.DependencyInjection;

namespace Layered.App;

// an implementation of a referenced project's interface gets its contract class's preconditions (#114)
public sealed class Store : IStore
{
    public int Take(int amount)
    {
        Spec.Assert(amount > 0);
        return amount;
    }
}

// a call through it: its precondition checked here
public static class Takes
{
    public static int One(IStore store) => store.Take(1);
}

// a class implementing a referenced project's interfaces (#106)
public sealed class Repository : IRepository, ICounter
{
    public int Plain(int x) => x + 0;

    public int Next(int x) => 0;
}

// a library interface, stored (#107)
public sealed class Scoped
{
    private readonly IServiceScopeFactory scopes;

    public Scoped(IServiceScopeFactory scopes) => this.scopes = scopes;

    public int Plain(int x) => x + 0;
}
