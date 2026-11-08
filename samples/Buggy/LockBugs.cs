// Written for this repository: shared state under locks and semaphores, and tasks, each with one planted bug.
using System;
using System.Threading;
using System.Threading.Tasks;
using CsVerify;

namespace Samples.Buggy.Locks
{
    public sealed class Tally
    {
        private readonly object _lock = new object();
        [GuardedBy(nameof(_lock))] private int _count;
        [LockInvariant(nameof(_lock)), Pure] private bool Valid() => _count >= 0;

        public Tally() { _count = 0; }

        /// <summary>Reads the count without the lock: another thread may be writing it.</summary>
        public int Peek() => _count;

        /// <summary>Takes one off with no check, so the count can go below zero while the lock is free.</summary>
        public void Undo()
        {
            lock (_lock) { _count = _count - 1; }
        }
    }

    public sealed class Gate
    {
        private readonly SemaphoreSlim _gate = new SemaphoreSlim(1, 1);
        [GuardedBy(nameof(_gate))] private int _n;

        /// <summary>Takes the semaphore while holding it: it isn't reentrant, so this waits forever.</summary>
        public async Task Twice()
        {
            await _gate.WaitAsync();
            try
            {
                await _gate.WaitAsync();
                try { _n = 2; }
                finally { _gate.Release(); }
            }
            finally { _gate.Release(); }
        }

        [GuardedBy(nameof(_gate))] private string? _cached;

        /// <summary>Awaits a delegate while holding the semaphore: it could take any lock, this one included.</summary>
        public async Task<string> GetOrCompute(Func<Task<string>> compute)
        {
            Spec.Requires(Spec.Pre(compute));
            await _gate.WaitAsync();
            try
            {
                if (_cached != null) return _cached;
                var result = await compute();
                _cached = result;
                return result;
            }
            finally { _gate.Release(); }
        }

        /// <summary>No try/finally: if the work throws, the semaphore is never released.</summary>
        public async Task Unreleased()
        {
            await _gate.WaitAsync();
            _n = 1;
            _gate.Release();
        }
    }

    public sealed class Jobs
    {
        private int _done;

        [RunsConcurrently]
        private static async Task<int> Work()
        {
            await Task.Delay(1).ConfigureAwait(false);
            return 1;
        }

        /// <summary>Awaits the task on one path only: on the other, its failure is lost.</summary>
        public static async Task Lost(bool wait)
        {
            var t = Work();
            if (wait) await t;
        }

        /// <summary>Reads the result before awaiting: it blocks.</summary>
        public static async Task<int> Early()
        {
            var t = Work();
            int x = t.Result;
            await t;
            return x;
        }

        /// <summary>Runs alongside other code and writes a field with no lock.</summary>
        [RunsConcurrently]
        public void Finish() { _done = 1; }
    }
}
