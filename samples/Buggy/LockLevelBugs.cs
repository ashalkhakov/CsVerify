// Written for this repository: deadlocks that lock levels rule out, each planted once.
using System;
using System.Threading;
using System.Threading.Tasks;
using CsVerify;

namespace Samples.Buggy.Levels
{
    public sealed class Account
    {
        public readonly int Id;
        [LockLevel(1, OrderedBy = nameof(Id))] public readonly object Lock = new object();
        [GuardedBy(nameof(Lock))] public int Balance;

        public Account(int id) { Id = id; }
    }

    public sealed class LevelBugs
    {
        [LockLevel(1)] private readonly object _low = new object();
        [LockLevel(2)] private readonly object _high = new object();
        private readonly object _other = new object();

        /// <summary>Locks the two accounts in the order given: two opposite transfers can each hold one and wait for the other.</summary>
        public static void Transfer(Account from, Account to)
        {
            lock (from.Lock) lock (to.Lock) { }
        }

        private void TakeLow() { lock (_low) { } }

        /// <summary>Takes the lower lock through a call, while holding the higher one.</summary>
        public void LowUnderHigh()
        {
            lock (_high) { TakeLow(); }
        }

        /// <summary>Calls a delegate under a lock: it could take any lock.</summary>
        public void Callback(Action notify)
        {
            Spec.Requires(Spec.Pre(notify));
            lock (_low) { notify(); }
        }

        /// <summary>Waits for a task it was given while holding a lock: the task may need it.</summary>
        public void WaitUnder(Task t)
        {
            lock (_low) { t.Wait(); }
        }

        /// <summary>Waits on one lock while holding another: whoever would pulse it may need that one first.</summary>
        public void WaitHolding()
        {
            lock (_low) lock (_high) { Monitor.Wait(_high); }
        }

        [RunsConcurrently]
        private static async Task<int> Fetch()
        {
            await Task.Delay(1);
            return 1;
        }

        /// <summary>
        /// Blocks on async code that comes back to its context: on a UI thread it waits for itself. (Reading Result before
        /// awaiting is reported too.)
        /// </summary>
        public static async Task<int> Blocking()
        {
            var t = Fetch();
            int x = t.Result;
            await t;
            return x;
        }
    }
}
