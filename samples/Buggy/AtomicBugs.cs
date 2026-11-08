// Written for this repository: lock-free code with atomic fields, each method with one planted bug.
using System.Threading;
using CsVerify;

namespace Samples.Buggy.Atomic
{
    public sealed class Counter
    {
        [Atomic(Step = nameof(Grows))] private volatile int _hits;
        [Atomic(Step = nameof(Grows64))] private long _total;
        [Pure] private static bool Grows(int old, int now) => old <= now;
        [Pure] private static bool Grows64(long old, long now) => old <= now;

        /// <summary>Read, then a plain write: another thread's increment in between is lost, and the count may go down.</summary>
        public void LostUpdate()
        {
            int seen = _hits;
            if (seen < int.MaxValue) _hits = seen + 1;
        }

        /// <summary>Interlocked.Increment wraps at int.MaxValue, so the count can go down.</summary>
        public void Wraps() { Interlocked.Increment(ref _hits); }

        /// <summary>Takes two reads to be equal, though another thread may step in between.</summary>
        public void TwoReads()
        {
            int a = _hits;
            int b = _hits;
            Spec.Assert(a == b);
        }

        /// <summary>A plain read of a long that isn't volatile: it may be torn or reordered.</summary>
        public long Torn() => _total;
    }

    public sealed class Ticket
    {
        [Atomic(Step = nameof(Next))] private volatile int _number;

        /// <summary>A step of exactly one: two steps in a row aren't one, so what other threads do between two reads isn't one step.</summary>
        [Pure] private static bool Next(int old, int now) => (long)now == (long)old + 1;
    }
}
