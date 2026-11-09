// Written for these tests: code that waits on a monitor, to check under Coyote that every wait ends (CsVerify proves
// no deadlock between locks, not that a waiter is woken). It is compiled in a checked build, which reports each wait.
using System.Threading;
using CsVerify;

namespace CsVerify.CoyoteTests.Waits
{
    /// <summary>One item at a time, from those who put to those who take: each waits, in a loop, until it can go on.</summary>
    public sealed class Mailbox
    {
        private readonly object _lock = new object();
        [GuardedBy(nameof(_lock))] private int _count;
        [GuardedBy(nameof(_lock))] private int _item;

        [LockInvariant(nameof(_lock)), Pure]
        private bool Valid() => _count == 0 || _count == 1;

        public void Put(int x)
        {
            lock (_lock)
            {
                while (_count == 1) Monitor.Wait(_lock);
                _item = x;
                _count = 1;
                Monitor.PulseAll(_lock);
            }
        }

        public int Take()
        {
            lock (_lock)
            {
                while (_count == 0) Monitor.Wait(_lock);
                _count = 0;
                Monitor.PulseAll(_lock);
                return _item;
            }
        }
    }

    /// <summary>
    /// A latch with a lost wakeup: <see cref="Await"/> looks at the flag without the lock, so Open can set it and pulse
    /// between that look and the wait, and nothing wakes the waiter again.
    /// </summary>
    public sealed class Latch
    {
        private readonly object _lock = new object();
        private volatile bool _open;

        public void Open()
        {
            lock (_lock)
            {
                _open = true;
                Monitor.PulseAll(_lock);
            }
        }

        public void Await()
        {
            if (_open) return;
            lock (_lock) { Monitor.Wait(_lock); }
        }
    }
}
