// Written for this repository, to show deadlock freedom by lock levels: transfers between accounts lock both, ordered
// by id; a ledger taken inside them has a higher level; an async log is a semaphore above both; and a callback run
// under a lock says it takes none.
using System.Threading;
using System.Threading.Tasks;
using CsVerify;

namespace Samples.Good.Levels
{
    /// <summary>What a transfer reports to, under the accounts' locks: it must take no lock, or it could close a cycle.</summary>
    [TakesNoLocks]
    public delegate void Notify(int from, int to, int amount);

    /// <summary>It accepts any transfer.</summary>
    [ContractClassFor(typeof(Notify))]
    internal abstract class NotifyContract
    {
        public void Invoke(int from, int to, int amount) { }
    }

    public sealed class Ledger
    {
        [LockLevel(2)] private readonly object _lock = new object();
        [GuardedBy(nameof(_lock))] private int _entries;

        public void Record()
        {
            lock (_lock) { if (_entries < int.MaxValue) _entries++; }
        }
    }

    public sealed class Account
    {
        public readonly int Id;
        [LockLevel(1, OrderedBy = nameof(Id))] public readonly object Lock = new object();
        [GuardedBy(nameof(Lock))] public int Balance;

        public Account(int id) { Id = id; }
    }

    public static class Bank
    {
        /// <summary>Both accounts' locks, the one with the lower id first; then the ledger's, which is above both.</summary>
        public static void Transfer(Account from, Account to, int amount, Ledger ledger, Notify notify)
        {
            Spec.Requires(from.Id != to.Id && 0 <= amount && amount <= 1000);
            if (from.Id < to.Id)
            {
                lock (from.Lock)
                {
                    lock (to.Lock)
                    {
                        if (from.Balance < amount || to.Balance > int.MaxValue - amount) return;
                        from.Balance -= amount;
                        to.Balance += amount;
                        ledger.Record();
                        notify(from.Id, to.Id, amount);
                    }
                }
            }
            else
            {
                lock (to.Lock)
                {
                    lock (from.Lock)
                    {
                        if (from.Balance < amount || to.Balance > int.MaxValue - amount) return;
                        from.Balance -= amount;
                        to.Balance += amount;
                        ledger.Record();
                        notify(from.Id, to.Id, amount);
                    }
                }
            }
        }
    }

    /// <summary>An async log, held across awaits: it's above every lock, so it may be taken inside any of them, and takes none itself.</summary>
    public sealed class AuditLog
    {
        [LockLevel(3)] private readonly SemaphoreSlim _gate = new SemaphoreSlim(1, 1);
        [GuardedBy(nameof(_gate))] private int _written;

        public async Task WriteAsync(CancellationToken ct)
        {
            await _gate.WaitAsync(ct);
            try
            {
                await Task.Delay(1, ct);
                if (_written < int.MaxValue) _written++;
            }
            finally { _gate.Release(); }
        }
    }
}
