#nullable enable
using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Linq;
using System.Threading;
using System.Threading.Channels;
using System.Threading.Tasks;
using CsVerify;

// A small async service, written for this repository to try the async support on: it isn't taken from a real program.
// It has no contracts, but for one loop invariant: this is what the verifier says of code as it is usually written.
// In a first version it found that OrderWorker never disposed its CancellationTokenSource, and that negative cents
// overflowed the sum of a customer's total. It proves there are no null dereferences, overflows or unguarded uses of
// what a semaphore guards. It doesn't prove the cache gives back what was put in: nothing here says it should.
namespace AsyncServiceSample
{
    public sealed record Order(int Id, string Customer, int Cents);

    [RunsConcurrently]
    public interface IOrderStore
    {
        Task<Order?> FindAsync(int id, CancellationToken ct);
        Task SaveAsync(Order order, CancellationToken ct);
    }

    /// <summary>An in-memory cache, with a semaphore held across the load so one id is loaded once.</summary>
    [RunsConcurrently]
    public sealed class OrderCache
    {
        private readonly SemaphoreSlim _gate = new SemaphoreSlim(1, 1);
        private readonly Dictionary<int, Order> _orders = new Dictionary<int, Order>();
        private readonly IOrderStore _store;
        [GuardedBy(nameof(_gate))] private int _hits;
        [GuardedBy(nameof(_gate))] private int _misses;

        public OrderCache(IOrderStore store) { _store = store; }

        public async Task<Order?> GetAsync(int id, CancellationToken ct)
        {
            await _gate.WaitAsync(ct);
            try
            {
                if (_orders.TryGetValue(id, out var cached))
                {
                    _hits = _hits < int.MaxValue ? _hits + 1 : _hits;
                    return cached;
                }
                _misses = _misses < int.MaxValue ? _misses + 1 : _misses;
                var loaded = await _store.FindAsync(id, ct);
                if (loaded != null) _orders[id] = loaded;
                return loaded;
            }
            finally { _gate.Release(); }
        }

        public async Task PutAsync(Order order, CancellationToken ct)
        {
            await _store.SaveAsync(order, ct);
            await _gate.WaitAsync(ct);
            try { _orders[order.Id] = order; }
            finally { _gate.Release(); }
        }

        public async Task<int> HitsAsync()
        {
            await _gate.WaitAsync();
            try { return _hits; }
            finally { _gate.Release(); }
        }
    }

    /// <summary>At most a few calls at once: a semaphore that counts, so it guards nothing.</summary>
    public sealed class Throttle : IDisposable
    {
        private readonly SemaphoreSlim _slots;

        public Throttle(int slots)
        {
            if (slots <= 0) throw new ArgumentOutOfRangeException(nameof(slots));
            _slots = new SemaphoreSlim(slots);
        }

        public async Task<T> RunAsync<T>(Func<CancellationToken, Task<T>> work, CancellationToken ct)
        {
            await _slots.WaitAsync(ct);
            try { return await work(ct); }
            finally { _slots.Release(); }
        }

        public void Dispose() => _slots.Dispose();
    }

    /// <summary>A worker that takes orders off a channel until it is told to stop.</summary>
    public sealed class OrderWorker : IDisposable
    {
        private readonly Channel<Order> _queue = Channel.CreateBounded<Order>(100);
        private readonly OrderCache _cache;
        private readonly ConcurrentDictionary<string, int> _totals = new ConcurrentDictionary<string, int>();
        private readonly CancellationTokenSource _stop = new CancellationTokenSource();
        private readonly object _startLock = new object();
        [GuardedBy(nameof(_startLock))] private Task? _running;

        public OrderWorker(OrderCache cache) { _cache = cache; }

        public void Start()
        {
            var running = Task.Run(() => LoopAsync(_stop.Token));
            lock (_startLock) { _running = running; }
        }

        public ValueTask EnqueueAsync(Order order, CancellationToken ct) => _queue.Writer.WriteAsync(order, ct);

        public async Task StopAsync()
        {
            _queue.Writer.Complete();
            _stop.Cancel();
            Task? running;
            lock (_startLock) { running = _running; }
            if (running != null)
            {
                try { await running; }
                catch (OperationCanceledException) { }
            }
        }

        [RunsConcurrently]
        private async Task LoopAsync(CancellationToken ct)
        {
            await foreach (var order in _queue.Reader.ReadAllAsync(ct))
            {
                ct.ThrowIfCancellationRequested();
                await _cache.PutAsync(order, ct);
                // (negative cents would overflow the test below: orders are checked here, as nothing says they can't be)
                if (order.Cents < 0) continue;
                _totals.AddOrUpdate(order.Customer, order.Cents, (_, old) => Add(old, order.Cents));
            }
        }

        [RunsConcurrently]
        private static int Add(int total, int cents)
        {
            if (cents < 0 || total > int.MaxValue - cents) return total;
            return total + cents;
        }

        public int TotalFor(string customer) => _totals.TryGetValue(customer, out var total) ? total : 0;

        public void Dispose() => _stop.Dispose();
    }

    public static class Fetching
    {
        /// <summary>Several at once, with a timeout, keeping those that were found.</summary>
        public static async Task<List<Order>> FetchAllAsync(OrderCache cache, int[] ids, TimeSpan timeout, CancellationToken ct)
        {
            using var limit = CancellationTokenSource.CreateLinkedTokenSource(ct);
            limit.CancelAfter(timeout);
            var tasks = ids.Select(id => cache.GetAsync(id, limit.Token)).ToArray();
            var found = new List<Order>();
            foreach (var order in await Task.WhenAll(tasks))
                if (order != null) found.Add(order);
            return found;
        }

        /// <summary>Two at once: one result from each.</summary>
        public static async Task<int> TotalOfTwoAsync(OrderCache cache, int a, int b, CancellationToken ct)
        {
            var first = cache.GetAsync(a, ct);
            var second = cache.GetAsync(b, ct);
            await Task.WhenAll(first, second);
            var x = first.Result;
            var y = second.Result;
            int cents = 0;
            if (x != null && x.Cents >= 0 && x.Cents < 1000000) cents = x.Cents;
            if (y != null && y.Cents >= 0 && y.Cents < 1000000) cents = cents + y.Cents;
            return cents;
        }

        /// <summary>Tries again a few times, waiting longer each time, unless it was cancelled.</summary>
        public static async Task<Order?> WithRetryAsync(IOrderStore store, int id, CancellationToken ct)
        {
            int delay = 100;
            for (int attempt = 0; attempt < 3; attempt++)
            {
                Spec.Invariant(0 < delay && delay <= 20000);
                try { return await store.FindAsync(id, ct); }
                catch (TimeoutException) when (attempt < 2)
                {
                    await Task.Delay(delay, ct);
                    if (delay <= 10000) delay = delay * 2;
                }
            }
            return null;
        }
    }
}
