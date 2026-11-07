// Classes shared between threads: what a lock guards is used only under it, and what holds while it is free is proved
// on leaving it. So these have no races on the fields they guard, whichever threads call them.
using System;
using CsVerify;

namespace Samples.Good
{
    /// <summary>A counter: the smallest thing that loses updates without its lock.</summary>
    public sealed class SharedCounter
    {
        private readonly object _lock = new object();
        public SharedCounter() { }
        [GuardedBy(nameof(_lock))] private int _count;

        [LockInvariant(nameof(_lock)), Pure]
        private bool Valid() => 0 <= _count;

        public void Increment()
        {
            lock (_lock)
            {
                if (_count < int.MaxValue) _count++;
            }
        }

        public int Read()
        {
            Spec.Ensures<int>(r => r >= 0);
            lock (_lock) { return _count; }
        }
    }

    /// <summary>A bank: the money in an account never goes below zero, and a transfer moves what it takes.</summary>
    public sealed class SharedAccount
    {
        private readonly object _lock = new object();
        public SharedAccount() { }
        [GuardedBy(nameof(_lock))] private int _balance;

        [LockInvariant(nameof(_lock)), Pure]
        private bool Valid() => 0 <= _balance && _balance <= 1000000000;

        public void Deposit(int amount)
        {
            Spec.Requires(0 <= amount && amount <= 1000000);
            lock (_lock)
            {
                if (_balance <= 1000000000 - amount) _balance += amount;
            }
        }

        /// <summary>True when the money was there.</summary>
        public bool Withdraw(int amount)
        {
            Spec.Requires(0 <= amount);
            lock (_lock)
            {
                if (_balance < amount) return false;
                _balance -= amount;
                return true;
            }
        }

        public int Balance()
        {
            Spec.Ensures<int>(r => 0 <= r && r <= 1000000000);
            lock (_lock) { return _balance; }
        }

        /// <summary>Locks one account at a time: another thread may see the money in neither, but it is never in both.</summary>
        public static bool Transfer(SharedAccount from, SharedAccount to, int amount)
        {
            Spec.Requires(0 <= amount && amount <= 1000000);
            if (!from.Withdraw(amount)) return false;
            to.Deposit(amount);
            return true;
        }
    }

    /// <summary>A stack with a fixed capacity: its count and its array must agree, under one lock.</summary>
    public sealed class SharedStack
    {
        private const int Capacity = 16;
        private readonly object _lock = new object();
        private readonly int[] _items = new int[Capacity];
        [GuardedBy(nameof(_lock))] private int _count;

        public SharedStack() { }

        [LockInvariant(nameof(_lock)), Pure]
        private bool Valid() => 0 <= _count && _count <= Capacity && _items.Length == Capacity;

        public bool Push(int value)
        {
            lock (_lock)
            {
                if (_count == Capacity) return false;
                _items[_count] = value;
                _count++;
                return true;
            }
        }

        /// <summary>The top, or null when there's nothing there.</summary>
        public int? Pop()
        {
            lock (_lock)
            {
                if (_count == 0) return null;
                _count--;
                return _items[_count];
            }
        }
    }

    /// <summary>Built on first use, once: a reader takes the lock too, so it can't see it half made.</summary>
    public sealed class LazyTable
    {
        private readonly object _lock = new object();
        public LazyTable() { }
        [GuardedBy(nameof(_lock))] private int[]? _table;

        [LockInvariant(nameof(_lock)), Pure]
        private bool Valid() => _table == null || _table.Length == 8;

        public int Get(int index)
        {
            Spec.Requires(0 <= index && index < 8);
            lock (_lock)
            {
                if (_table == null) _table = new int[8];
                return _table[index];
            }
        }
    }

    /// <summary>Statistics: three fields that must agree, restored before the lock is left, even when a value is refused.</summary>
    public sealed class SharedStatistics
    {
        private readonly object _lock = new object();
        public SharedStatistics() { }
        [GuardedBy(nameof(_lock))] private int _count;
        [GuardedBy(nameof(_lock))] private int _min;
        [GuardedBy(nameof(_lock))] private int _max;

        [LockInvariant(nameof(_lock)), Pure]
        private bool Valid() => 0 <= _count && (_count == 0 || _min <= _max);

        public void Add(int value)
        {
            lock (_lock)
            {
                if (_count == int.MaxValue) return;
                if (_count == 0)
                {
                    _min = value;
                    _max = value;
                }
                else
                {
                    if (value < _min) _min = value;
                    if (value > _max) _max = value;
                }
                _count++;
            }
        }

        /// <summary>The spread between the largest and the smallest, or 0 before there are any.</summary>
        public long Range()
        {
            Spec.Ensures<long>(r => r >= 0);
            lock (_lock)
            {
                if (_count == 0) return 0;
                return (long)_max - _min;
            }
        }
    }
}
