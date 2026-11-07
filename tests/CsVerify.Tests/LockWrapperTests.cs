using System.Linq;
using Xunit;

namespace CsVerify.Tests
{
    /// <summary>[Acquires] and [Releases]: helpers and lock classes that wrap a SemaphoreSlim of count 1 hold what it guards like the semaphore itself.</summary>
    public class LockWrapperTests
    {
        private const string Lock = "using CsVerify; using System; using System.Threading; using System.Threading.Tasks; " +
            "public sealed class AsyncLock { private readonly SemaphoreSlim _s = new SemaphoreSlim(1, 1); " +
            "[Acquires] public async Task<Releaser> LockAsync(CancellationToken ct = default) { await _s.WaitAsync(ct); return new Releaser(_s); } " +
            "[Acquires] public Releaser Lock() { _s.Wait(); return new Releaser(_s); } " +
            "public sealed class Releaser : IDisposable { private readonly SemaphoreSlim _r; public Releaser(SemaphoreSlim r) { _r = r; } public void Dispose() { _r.Release(); } } } " +
            "public static class Ext { [Acquires] public static async Task<Gone> TakeAsync(this SemaphoreSlim s) { await s.WaitAsync(); return new Gone(s); } " +
            "public sealed class Gone : IDisposable { private readonly SemaphoreSlim _r; public Gone(SemaphoreSlim r) { _r = r; } public void Dispose() { _r.Release(); } } } ";

        private static string[] Ids(string cls) => Harness.Verify(Lock + cls).Diagnostics.Where(d => d.IsError).Select(d => d.Id).ToArray();
        private static string[] All(string cls) => Harness.Verify(Lock + cls).Diagnostics.Where(d => d.IsError).Select(d => d.Id + " " + d.Message).ToArray();

        private const string Guarded = "public class C { private readonly AsyncLock _l = new AsyncLock(); [GuardedBy(nameof(_l))] private int _n; ";
        private const string Inferred = "public class C { private readonly AsyncLock _l = new AsyncLock(); private int _n; ";
        private const string OnSemaphore = "public class C { private readonly SemaphoreSlim _g = new SemaphoreSlim(1, 1); [GuardedBy(nameof(_g))] private int _n; ";
        private const string Helpers = "public class C { private readonly SemaphoreSlim _g = new SemaphoreSlim(1, 1); [GuardedBy(nameof(_g))] private int _n; " +
            "[Acquires(nameof(_g))] private async Task EnterAsync() { await _g.WaitAsync(); } [Releases(nameof(_g))] private void Exit() { _g.Release(); } ";

        [Theory]
        [InlineData(Guarded + "public async Task M() { using (await _l.LockAsync()) { _n = 1; await Task.Yield(); Spec.Assert(_n == 1); } } }")]
        [InlineData(Guarded + "public async Task M() { using (await _l.LockAsync().ConfigureAwait(false)) { _n = 1; } } }")]
        [InlineData(Guarded + "public async Task M(CancellationToken ct) { using (await _l.LockAsync(ct)) { _n = 1; } } }")]
        [InlineData(Guarded + "public async Task M() { using var held = await _l.LockAsync(); _n = 1; await Task.Yield(); Spec.Assert(_n == 1); } }")]
        [InlineData(Guarded + "public async Task M() { using (var held = await _l.LockAsync()) { _n = 1; } } }")]
        [InlineData(Guarded + "public void M() { using (_l.Lock()) { _n = 1; } } }")]
        [InlineData(Inferred + "public async Task M() { using (await _l.LockAsync()) { _n = 1; } } public async Task<int> N() { using (await _l.LockAsync()) { return _n; } } }")]
        [InlineData(OnSemaphore + "public async Task M() { using (await _g.TakeAsync()) { _n = 1; await Task.Yield(); Spec.Assert(_n == 1); } } }")]
        [InlineData(Helpers + "public async Task M() { await EnterAsync(); try { _n = 1; await Task.Yield(); Spec.Assert(_n == 1); } finally { Exit(); } } }")]
        // its invariant holds, once it is taken, and is restored
        [InlineData(Guarded + "[LockInvariant(nameof(_l)), Pure] private bool Ok() => _n >= 0; public C() { _n = 0; } public async Task M() { using (await _l.LockAsync()) { Spec.Assert(_n >= 0); if (_n < 100) _n = _n + 1; } } }")]
        public void Proved(string cls) => Assert.Empty(All(cls));

        [Theory]
        // outside it, after it, or before it
        [InlineData("CSV1023", Guarded + "public async Task M() { using (await _l.LockAsync()) { } _n = 1; } }")]
        [InlineData("CSV1023", Guarded + "public async Task M() { _n = 1; using var held = await _l.LockAsync(); } }")]
        [InlineData("CSV1023", Guarded + "public void M() { _n = 1; } }")]
        [InlineData("CSV1023", Helpers + "public async Task M() { await EnterAsync(); try { } finally { Exit(); } _n = 1; } }")]
        // in another form: kept, handed on, used, or not given back in a finally
        [InlineData("CSV1023", Guarded + "public async Task M() { var r = await _l.LockAsync(); _n = 1; r.Dispose(); } }")]
        [InlineData("CSV1023", Guarded + "public async Task M() { using var r = await _l.LockAsync(); r.Dispose(); _n = 1; } }")]
        [InlineData("CSV1023", Guarded + "public async Task M() { await _l.LockAsync(); _n = 1; } }")]
        [InlineData("CSV1023", Helpers + "public async Task M() { await EnterAsync(); _n = 1; Exit(); } }")]
        [InlineData("CSV1023", Helpers + "public void M() { Exit(); } }")]
        [InlineData("CSV1023", Guarded + "public AsyncLock M() { return _l; } }")]
        // on another object
        [InlineData("CSV1023", Guarded + "public async Task M(C o) { using (await _l.LockAsync()) { o._n = 1; } } }")]
        // inside a lambda: who knows when it runs
        [InlineData("CSV1023", Guarded + "public async Task M() { using (await _l.LockAsync()) { Action a = () => { _n = 1; }; } } }")]
        // two of them
        [InlineData("CSV1025", Guarded + "public async Task M() { using (await _l.LockAsync()) { using (await _l.LockAsync()) { } } } }")]
        [InlineData("CSV1025", Guarded + "private async Task N() { using (await _l.LockAsync()) { _n = 1; } } public async Task M() { using (await _l.LockAsync()) { await N(); } } }")]
        [InlineData("CSV1025", Helpers + "public async Task M() { await EnterAsync(); try { await EnterAsync(); try { } finally { Exit(); } } finally { Exit(); } } }")]
        // its invariant at the end of the using, and on the way out by an exception
        [InlineData("CSV1024", Guarded + "[LockInvariant(nameof(_l)), Pure] private bool Ok() => _n >= 0; public C() { _n = 0; } public async Task M() { using (await _l.LockAsync()) { _n = -1; } } }")]
        [InlineData("CSV1024", Guarded + "[LockInvariant(nameof(_l)), Pure] private bool Ok() => _n >= 0; public C() { _n = 0; } public async Task M() { using (await _l.LockAsync()) { _n = -1; await Task.Yield(); _n = 0; } } }")]
        public void Reported(string id, string cls) => Assert.Contains(id, Ids(cls));

        [Theory]
        // the shape of what's claimed
        [InlineData("public class D { [Acquires] public Task<AsyncLock.Releaser> LockAsync() { return null!; } private readonly D _d = new D(); private int _n; }")]
        [InlineData("public class W { private readonly SemaphoreSlim _s = new SemaphoreSlim(5); [Acquires] public async Task<Back> LockAsync() { await _s.WaitAsync(); return new Back(); } public sealed class Back : IDisposable { public void Dispose() { } } } public class C { private readonly W _l = new W(); [GuardedBy(nameof(_l))] private int _n; public async Task M() { using (await _l.LockAsync()) { _n = 1; } } }")]
        [InlineData("public class W { private readonly SemaphoreSlim _s = new SemaphoreSlim(1, 1); [Acquires] public async Task<Back> LockAsync() { await _s.WaitAsync(); return new Back(); } public sealed class Back : IDisposable { public void Dispose() { } } } public class C { private readonly W _l = new W(); [GuardedBy(nameof(_l))] private int _n; public async Task M() { using (await _l.LockAsync()) { _n = 1; } } }")]
        [InlineData("public class C { private readonly SemaphoreSlim _g = new SemaphoreSlim(1, 1); [GuardedBy(nameof(_g))] private int _n; [Releases(nameof(_g))] private void Exit() { } public void M() { _g.Wait(); try { _n = 1; } finally { Exit(); } } }")]
        public void ShapeIsLookedAt(string cls) => Assert.Contains("CSV1023", Ids(cls.Contains("private int _n; }") ? cls.Replace("private int _n; }", "[GuardedBy(nameof(_d))] private int _n; }") : cls));

        // a library's lock, by a stub
        [Fact]
        public void ALibrarysLock() => Assert.Empty(Harness.Verify("using CsVerify; using System; using System.IO; using System.Threading.Tasks; " +
            "[ContractsFor(typeof(StringWriter))] public static class LockStub { [Acquires] public static Task FlushAsync(StringWriter @this) => throw null!; [Releases] public static void Close(StringWriter @this) { } } " +
            "public class C { private readonly StringWriter _l = new StringWriter(); [GuardedBy(nameof(_l))] private int _n; public async Task M() { await _l.FlushAsync(); try { _n = 1; await Task.Yield(); Spec.Assert(_n == 1); } finally { _l.Close(); } } }")
            .Diagnostics.Where(d => d.IsError).Select(d => d.Id + " " + d.Message));
    }
}
