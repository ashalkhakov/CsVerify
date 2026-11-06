using System.Linq;
using Xunit;

namespace CsVerify.Tests
{
    /// <summary>Concurrent collections and channels: what they give is not null, and nothing about what they hold can be relied on.</summary>
    public class ConcurrentCollectionTests
    {
        private static string[] Errors(string m) =>
            Harness.Verify("using CsVerify; using System; using System.Linq; using System.Collections.Generic; using System.Collections.Concurrent; using System.Threading; using System.Threading.Channels; using System.Threading.Tasks; " +
                           "public class Item { public int V; } public sealed record Order(int Id, string C); public static class C { " + m + " }").Errors("M");

        [Theory]
        [InlineData("static int M(ConcurrentDictionary<string, Item> d, string k) { if (d.TryGetValue(k, out var v)) return v.V; return 0; }")]
        [InlineData("static int M(ConcurrentDictionary<string, Item> d, string k) { var v = d.GetOrAdd(k, _ => new Item()); return v.V; }")]
        [InlineData("static int M(ConcurrentDictionary<string, Item> d, string k) { var v = d.AddOrUpdate(k, new Item(), (_, o) => o); return v.V; }")]
        [InlineData("static int M(ConcurrentDictionary<string, Item> d, string k) { if (d.TryRemove(k, out var v)) return v.V; return 0; }")]
        [InlineData("static int M(ConcurrentQueue<Item> q) { if (q.TryDequeue(out var v)) return v.V; return 0; }")]
        [InlineData("static int M(ConcurrentStack<Item> q) { if (q.TryPop(out var v)) return v.V; return 0; }")]
        [InlineData("static int M(ConcurrentBag<Item> q) { if (q.TryTake(out var v)) return v.V; return 0; }")]
        [InlineData("static async Task<int> M(ChannelReader<Item> r, CancellationToken ct) { var v = await r.ReadAsync(ct); return v.V; }")]
        [InlineData("static int M(ChannelReader<Item> r) { if (r.TryRead(out var v)) return v.V; return 0; }")]
        [InlineData("static async Task M(ChannelWriter<Item> w, CancellationToken ct) { await w.WriteAsync(new Item(), ct); w.Complete(); }")]
        [InlineData("static Channel<Item> M() { return Channel.CreateBounded<Item>(10); }")]
        // await foreach
        [InlineData("static async Task M(ChannelReader<Item> r, CancellationToken ct) { await foreach (var v in r.ReadAllAsync(ct)) { var x = v.V; } }")]
        [InlineData("static async Task M(ChannelReader<Item> r) { await foreach (var v in r.ReadAllAsync().ConfigureAwait(false)) { var x = v.V; } }")]
        [InlineData("static async Task M(ChannelReader<Item> r) { await foreach (var v in r.ReadAllAsync()) { if (v.V == 0) break; } }")]
        [InlineData("static async Task<int> M(ChannelReader<Item> r) { int n = 0; await foreach (var v in r.ReadAllAsync()) { Spec.Invariant(n >= 0); if (n < 1000) n = n + 1; } Spec.Assert(n >= 0); return n; }")]
        [InlineData("static async Task M(ChannelReader<int?> r) { int k = 3; await foreach (var v in r.ReadAllAsync()) { Spec.Invariant(k == 3); } Spec.Assert(k == 3); }")]
        // value types and records
        [InlineData("static bool M(ConcurrentDictionary<int, Item> d, int k) { return d.TryGetValue(k, out var v); }")]
        [InlineData("static int M(ChannelReader<Order> r) { if (r.TryRead(out var v) && v != null) return v.Id; return 0; }")]
        [InlineData("static async Task<int> M(ChannelReader<Order?> r) { var v = await r.ReadAsync(); return v != null ? v.Id : 0; }")]
        [InlineData("static string[] M(string[] ids) { using var s = new CancellationTokenSource(); return ids.Select(i => s.Token.ToString()).ToArray(); }")]
        public void Proved(string m) => Assert.Empty(Errors(m));

        [Theory]
        // a value is only there if it says so
        [InlineData("CSV1013", "static int M(ConcurrentDictionary<string, Item> d, string k) { d.TryGetValue(k, out var v); return v.V; }")]
        [InlineData("CSV1013", "static int M(ConcurrentQueue<Item> q) { q.TryDequeue(out var v); return v.V; }")]
        [InlineData("CSV1013", "static int M(ChannelReader<Item> r) { r.TryRead(out var v); return v.V; }")]
        [InlineData("CSV1013", "static async Task<int> M(ChannelReader<Item?> r) { var v = await r.ReadAsync(); return v.V; }")]
        [InlineData("CSV1013", "static int M(ConcurrentDictionary<string, Item?> d, string k) { var v = d.GetOrAdd(k, _ => null); return v.V; }")]
        [InlineData("CSV1013", "static async Task M(ChannelReader<Item?> r) { await foreach (var v in r.ReadAllAsync()) { var x = v.V; } }")]
        [InlineData("CSV1013", "static async Task M(ChannelReader<Item?> r) { await foreach (var v in r.ReadAllAsync().ConfigureAwait(false)) { var x = v.V; } }")]
        // a library's T? isn't its T
        [InlineData("CSV1013", "static int M(List<Item> l) { return l.FindLast(x => x.V == 0).V; }")]
        [InlineData("CSV1013", "static int M(List<Item> l) { return l.Find(x => x.V == 0).V; }")]
        // no null keys: they throw
        [InlineData("CSV1014", "static void M(ConcurrentDictionary<string, Item> d, string? k) { d.TryAdd(k!, new Item()); }")]
        // nothing about what they hold stays
        [InlineData("CSV1004", "static void M(ConcurrentDictionary<string, int> d, string k) { var a = d.ContainsKey(k); var b = d.ContainsKey(k); Spec.Assert(a == b); }")]
        [InlineData("CSV1004", "static void M(ConcurrentDictionary<string, int> d, string k) { var a = d.Count; var b = d.Count; Spec.Assert(a == b); }")]
        [InlineData("CSV1004", "static void M(ConcurrentDictionary<string, int> d, string k) { d[k] = 1; var a = d[k]; Spec.Assert(a == 1); }")]
        [InlineData("CSV1004", "static void M(ConcurrentDictionary<string, int> d, string k) { d.TryAdd(k, 1); var a = d.ContainsKey(k); Spec.Assert(a); }")]
        [InlineData("CSV1004", "static void M(ConcurrentQueue<int> q) { q.Enqueue(1); var e = q.IsEmpty; Spec.Assert(!e); }")]
        [InlineData("CSV1004", "static void M(ConcurrentQueue<int> q) { q.Enqueue(1); var ok = q.TryDequeue(out var x); Spec.Assert(ok); }")]
        // await foreach: others run at each round, and it may not go round at all
        [InlineData("CSV1004", "static async Task M(ChannelReader<int> r, Item c) { c.V = 1; await foreach (var v in r.ReadAllAsync()) { Spec.Assert(c.V == 1); } }")]
        [InlineData("CSV1004", "static async Task M(ChannelReader<int> r, Item c) { c.V = 1; await foreach (var v in r.ReadAllAsync()) { } Spec.Assert(c.V == 1); }")]
        [InlineData("CSV1004", "static async Task M(ChannelReader<int> r) { int n = 0; await foreach (var v in r.ReadAllAsync()) { n = 1; } Spec.Assert(n == 1); }")]
        // it may throw, at each round
        [InlineData("CSV1004", "static async Task M(ChannelReader<int> r) { int n = 0; try { await foreach (var v in r.ReadAllAsync()) { } n = 1; } catch (OperationCanceledException) { Spec.Assert(n == 1); } }")]
        public void Reported(string id, string m) => Assert.Contains(id, Errors(m));

        // a new collection of records runs nothing of theirs
        [Fact]
        public void NewCollectionOfRecords_KeepsFieldsJustSet() => Assert.DoesNotContain(Harness.Verify("using System.Collections.Generic; public sealed record Order(int Id, string C); " +
            "public sealed class H { private readonly object _a = new object(); private readonly Dictionary<int, Order> _o = new Dictionary<int, Order>(); public H(string s) { } }").Diagnostics, d => d.Id == "CSV1014");

        private static bool LambdaNullAlarm(string m) =>
            Harness.Verify("using CsVerify; using System; using System.Linq; using System.Collections.Generic; using System.Collections.Concurrent; public sealed record Order(int Id, string C); public static class C { " + m + " }")
                .Diagnostics.Any(d => d.Id == "CSV1013");

        // what's captured keeps what the compiler knows of it, if it has only the one value
        [Fact]
        public void Captured_OneValue() => Assert.False(LambdaNullAlarm(
            "static void M(ConcurrentDictionary<string, int> d, List<Order> os) { foreach (var o in os) { d.AddOrUpdate(\"k\", 1, (_, old) => o.Id); } }"));

        [Fact]
        public void Captured_GivenAnotherValue() => Assert.True(LambdaNullAlarm(
            "static int M() { string? s = \"a\"; Func<int> f = () => s.Length; s = null; return f(); }"));
    }
}
