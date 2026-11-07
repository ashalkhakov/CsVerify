// Written for this repository, to show work split between tasks and threads, and a lock class around a semaphore.
using System;
using System.Threading;
using System.Threading.Tasks;
using CsVerify;

namespace ParallelWorkSample
{
    public static class Parts
    {
        /// <summary>Copies a part of one array to another. It only reads what it copies, so any number can share it.</summary>
        [RunsConcurrently]
        public static void CopyPart(int[] from, int[] to, int lo, int hi)
        {
            Spec.Requires(from.Length == to.Length && 0 <= lo && lo <= hi && hi <= to.Length);
            Spec.Requires(Spec.AccRead(from, lo, hi) && Spec.Acc(to, lo, hi));
            Spec.Ensures(Spec.AccRead(from, lo, hi) && Spec.Acc(to, lo, hi));
            Spec.Ensures(Spec.Forall(lo, hi, i => to[i] == from[i]));
            for (int k = lo; k < hi; k++)
            {
                Spec.Invariant(lo <= k && k <= hi && Spec.AccRead(from, lo, hi) && Spec.Acc(to, lo, hi));
                Spec.Invariant(Spec.Forall(lo, k, i => to[i] == from[i]));
                to[k] = from[k];
            }
        }

        [RunsConcurrently]
        public static async Task CopyPartAsync(int[] from, int[] to, int lo, int hi)
        {
            Spec.Requires(from.Length == to.Length && 0 <= lo && lo <= hi && hi <= to.Length);
            Spec.Requires(Spec.AccRead(from, lo, hi) && Spec.Acc(to, lo, hi));
            Spec.Ensures(Spec.AccRead(from, lo, hi) && Spec.Acc(to, lo, hi));
            Spec.Ensures(Spec.Forall(lo, hi, i => to[i] == from[i]));
            await Task.Yield();
            CopyPart(from, to, lo, hi);
        }

        /// <summary>Two tasks, each with its part of the target: they can't touch each other's, and together they do all of it.</summary>
        public static async Task CopyWithTasks(int[] from, int[] to)
        {
            Spec.Requires(from.Length == to.Length && from != to && Spec.AccRead(from) && Spec.Acc(to));
            Spec.Ensures(Spec.AccRead(from) && Spec.Acc(to));
            Spec.Ensures(Spec.Forall(0, to.Length, i => to[i] == from[i]));
            int mid = to.Length / 2;
            await Task.WhenAll(CopyPartAsync(from, to, 0, mid), CopyPartAsync(from, to, mid, to.Length));
        }

        /// <summary>The same with Task.Run: the delegate is just the call, proved here.</summary>
        public static async Task CopyWithRun(int[] from, int[] to)
        {
            Spec.Requires(from.Length == to.Length && from != to && Spec.AccRead(from) && Spec.Acc(to));
            Spec.Ensures(Spec.AccRead(from) && Spec.Acc(to));
            Spec.Ensures(Spec.Forall(0, to.Length, i => to[i] == from[i]));
            int mid = to.Length / 2;
            var left = Task.Run(() => CopyPart(from, to, 0, mid));
            var right = Task.Run(() => CopyPart(from, to, mid, to.Length));
            await left;
            await right;
        }

        /// <summary>And with threads.</summary>
        public static void CopyWithThreads(int[] from, int[] to)
        {
            Spec.Requires(from.Length == to.Length && from != to && Spec.AccRead(from) && Spec.Acc(to));
            Spec.Ensures(Spec.AccRead(from) && Spec.Acc(to));
            Spec.Ensures(Spec.Forall(0, to.Length, i => to[i] == from[i]));
            int mid = to.Length / 2;
            var left = new Thread(() => CopyPart(from, to, 0, mid));
            var right = new Thread(() => CopyPart(from, to, mid, to.Length));
            left.Start();
            right.Start();
            left.Join();
            right.Join();
        }
    }

    /// <summary>A lock that can be held across an await, as it's often written.</summary>
    public sealed class AsyncLock
    {
        private readonly SemaphoreSlim _gate = new SemaphoreSlim(1, 1);

        [Acquires]
        public async Task<Releaser> LockAsync(CancellationToken ct)
        {
            await _gate.WaitAsync(ct);
            return new Releaser(_gate);
        }

        public sealed class Releaser : IDisposable
        {
            private readonly SemaphoreSlim _held;
            public Releaser(SemaphoreSlim held) { _held = held; }
            public void Dispose() { _held.Release(); }
        }
    }

    public sealed class Balance
    {
        private readonly AsyncLock _lock = new AsyncLock();
        [GuardedBy(nameof(_lock))] private long _cents;

        public Balance() { _cents = 0; }

        [LockInvariant(nameof(_lock)), Pure]
        private bool NotNegative() => _cents >= 0;

        /// <summary>Held across the await: what it read is still so when it writes.</summary>
        public async Task<bool> TryWithdraw(long cents, CancellationToken ct)
        {
            Spec.Requires(cents >= 0);
            using (await _lock.LockAsync(ct))
            {
                if (_cents < cents) return false;
                await Task.Delay(1, ct);
                _cents = _cents - cents;
                return true;
            }
        }
    }
}
