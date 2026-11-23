using CsVerify;

namespace Layered.Model;

// an interface with its contract class beside it (#114)
public interface IStore
{
    int Take(int amount);
}

[ContractClassFor(typeof(IStore))]
internal abstract class StoreContract : IStore
{
    public int Take(int amount)
    {
        Spec.Requires(amount > 0);
        return 0;
    }
}

// a marker for registration by assembly scanning, and an interface without a contract (#106)
public interface IRepository
{
}

public interface ICounter
{
    int Next(int x);
}
