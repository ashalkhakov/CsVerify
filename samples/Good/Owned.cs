using CsVerify;

namespace Samples
{
    /// <summary>
    /// A mutable object owned ATS-style: only code holding its linear view Own&lt;Account&gt; may change it, and its
    /// invariant (never overdrawn) travels with the view.
    /// </summary>
    [Owned]
    public sealed class Account
    {
        public int Balance;

        [Invariant, Pure] public bool Valid() => Balance >= 0;

        public Account(int initial)
        {
            Spec.Requires(initial >= 0);
            Spec.Ensures(Balance == initial);
            Balance = initial;
        }

        public void Deposit(int amount)
        {
            Spec.Requires(amount >= 0);
            Spec.Ensures(Balance == Spec.Old(Balance) + amount);
            Balance += amount;
        }

        public void Withdraw(int amount)
        {
            Spec.Requires(0 <= amount && amount <= Balance);
            Spec.Ensures(Balance == Spec.Old(Balance) - amount);
            Balance -= amount;
        }
    }

    /// <summary>Code the verifier knows nothing about: it cannot touch an account whose view it does not get.</summary>
    public interface IAudit { void Record(int amount); }

    public sealed class NullAudit : IAudit { public void Record(int amount) { } }

    public static class Bank
    {
        /// <summary>
        /// ATS's <c>(pf | p)</c>: each object travels with its view, tied by the precondition. Both views in hand at
        /// once means two different accounts, so no aliasing case is needed.
        /// </summary>
        public static void Transfer(Account from, ref Own<Account> fromView, Account to, ref Own<Account> toView, int amount)
        {
            Spec.Requires(fromView.Obj.Value == from && toView.Obj.Value == to);
            Spec.Requires(0 <= amount && amount <= from.Balance);
            Spec.Ensures(from.Balance == Spec.Old(from.Balance) - amount && to.Balance == Spec.Old(to.Balance) + amount);
            from.Withdraw(amount);
            to.Deposit(amount);
        }

        public static int Demo(IAudit audit)
        {
            Spec.Ensures((int r) => r == 30 + 20);
            var a = Own.New(new Account(50), out var va);
            var b = Own.New(new Account(0), out var vb);
            Transfer(a, ref va, b, ref vb, 20);
            audit.Record(20); // unknown code in between: the balances are still known
            int result = a.Balance + b.Balance;
            Own.Drop(va);
            Own.Drop(vb);
            return result;
        }
    }
}
