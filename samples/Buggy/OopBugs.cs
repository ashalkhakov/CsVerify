using CsVerify;

namespace Samples.Buggy
{
    public abstract class Purse
    {
        [Pure] public abstract int Cash { get; }
        public abstract void Add(int amount);
        public abstract bool TrySpend(int amount);
    }

    [ContractClassFor(typeof(Purse))]
    internal abstract class PurseContract : Purse
    {
        public override int Cash { get { Spec.Reads(ObjSet.Of(this)); return 0; } }

        public override void Add(int amount)
        {
            Spec.Requires(amount >= 0);
            Spec.Modifies(ObjSet.Of(this));
            Spec.Ensures(Cash == Spec.Old(Cash) + amount);
        }

        public override bool TrySpend(int amount)
        {
            Spec.Requires(amount >= 0);
            Spec.Modifies(ObjSet.Of(this));
            Spec.Ensures((bool ok) => ok ? Cash == Spec.Old(Cash) - amount : Cash == Spec.Old(Cash));
            return false;
        }
    }

    public class PlainPurse : Purse
    {
        protected int Funds;
        public PlainPurse(int initial) { Spec.Requires(initial >= 0); Funds = initial; }
        [Pure] public sealed override int Cash => Funds;

        public override void Add(int amount) { Spec.Modifies(ObjSet.Of(this)); Funds = checked(Funds + amount); }

        public override bool TrySpend(int amount)
        {
            Spec.Modifies(ObjSet.Of(this));
            if (amount > Funds) return false;
            Funds -= amount;
            return true;
        }
    }

    // BUG: requires more than Purse promises its callers (CSV1018)
    public sealed class PickyPurse : PlainPurse
    {
        public PickyPurse() : base(0) { }

        public override bool TrySpend(int amount)
        {
            Spec.Requires(amount > 10);
            Spec.Modifies(ObjSet.Of(this));
            return false;
        }
    }

    // BUG: forgets the deposit, breaking the postcondition it inherits (CSV1002)
    public sealed class LyingPurse : PlainPurse
    {
        public LyingPurse() : base(0) { }
        public override void Add(int amount) { Spec.Modifies(ObjSet.Of(this)); }
    }

    // BUG: also credits another wallet, outside the frame it inherits (CSV1017)
    public sealed class LeakyPurse : PlainPurse
    {
        public PlainPurse? Twin;
        public LeakyPurse() : base(0) { }

        public override void Add(int amount)
        {
            Spec.Modifies(ObjSet.Of(this));
            Funds = checked(Funds + amount);
            if (Twin != null) Twin.Add(amount);
        }
    }

    // BUG: passes a negative balance to its base constructor (CSV1001)
    public sealed class Overdrawn : PlainPurse
    {
        public Overdrawn() : base(-5) { }
    }

    public sealed class Tile
    {
        public readonly int Side;
        [Invariant, Pure] public bool Valid() => Side > 0;

        // BUG: an empty tile breaks the invariant the constructor must establish (CSV1015)
        public Tile(int side) { Side = side; }
    }

    public sealed class Registered
    {
        public readonly int Id;
        [Invariant, Pure] public bool Valid() => Id > 0;

        // BUG: hands out this before Id is set (CSV1015)
        public Registered(int id)
        {
            Spec.Requires(id > 0);
            Registry.Remember(this);
            Id = id;
        }
    }

    public static class Registry
    {
        public static void Remember(Registered r) { }

        // BUG: a pure function that casts without knowing the object is a PlainPurse (CSV1011)
        [Pure]
        public static int FundsOf(Purse w) => ((PlainPurse)w).Cash;
    }
}
