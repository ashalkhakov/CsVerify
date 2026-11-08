// Written for this repository, to show lock-free code proved over every interleaving: a counter that only grows, a
// high-water mark, a gate that once closed stays closed, a configuration published once, and a generation number that
// wraps. Each field says the step every thread's change keeps; reads see the others' steps, writes are proved steps.
using System.Threading;
using System.Threading.Tasks;
using CsVerify;

namespace Samples.Good.Atomic
{
    [RunsConcurrently]
    public sealed class Config
    {
        public readonly int Size;
        public Config(int size) { Size = size; }
    }

    [RunsConcurrently]
    public sealed class Stats
    {
        [Atomic(Step = nameof(Grows))] private volatile int _hits;
        [Atomic(Step = nameof(Grows))] private volatile int _peak;
        [Atomic(Step = nameof(StaysClosed))] private volatile bool _closed;
        [Atomic(Step = nameof(SetOnce))] private volatile Config? _config;
        [Atomic] private long _generation;

        [Pure] private static bool Grows(int old, int now) => old <= now;
        [Pure] private static bool StaysClosed(bool old, bool now) => !old || now;
        [Pure] private static bool SetOnce(Config? old, Config? now) => old == null || old == now;

        /// <summary>One more hit, unless the count is at its top: read, then a compare-and-swap that fails if another got in first.</summary>
        public void Hit()
        {
            Spec.Ensures(Spec.Old(_hits) <= _hits);
            while (true)
            {
                int seen = _hits;
                if (seen == int.MaxValue) return;
                if (Interlocked.CompareExchange(ref _hits, seen + 1, seen) == seen) return;
            }
        }

        /// <summary>The peak is at least v afterwards, whoever else raised it meanwhile.</summary>
        public void Observe(int v)
        {
            Spec.Ensures(v <= _peak);
            while (true)
            {
                int peak = _peak;
                if (v <= peak) return;
                if (Interlocked.CompareExchange(ref _peak, v, peak) == peak) return;
            }
        }

        public int Hits()
        {
            Spec.Ensures<int>(r => Spec.Old(_hits) <= r && r <= _hits);
            return _hits;
        }

        public void Close()
        {
            Spec.Ensures(_closed);
            _closed = true;
        }

        /// <summary>False once closed, for good: a gate that was seen closed is closed at every later look.</summary>
        public bool Open()
        {
            Spec.Ensures<bool>(r => r == !_closed);
            return !_closed;
        }

        /// <summary>The one configuration: the first to publish it wins, and every caller gets that same object.</summary>
        public Config Configuration(int size)
        {
            Spec.Ensures<Config>(r => r != null && r == _config);
            var seen = _config;
            if (seen != null) return seen;
            var made = new Config(size);
            var winner = Interlocked.CompareExchange(ref _config, made, null);
            return winner ?? made;
        }

        /// <summary>A number for each round, which wraps as Interlocked does: any change is a step.</summary>
        public long NextGeneration() => Interlocked.Increment(ref _generation);

        public static async Task Use(Stats s)
        {
            var worker = Task.Run(() => { s.Hit(); s.Observe(10); });
            int before = s.Hits();
            s.Hit();
            s.Observe(3);
            await worker;
            int after = s.Hits();
            Spec.Assert(before <= after);

            var a = s.Configuration(4);
            var b = s.Configuration(8);
            Spec.Assert(a == b);

            s.Close();
            bool open = s.Open();
            Spec.Assert(!open);
        }
    }
}
