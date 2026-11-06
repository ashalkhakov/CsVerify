using System.Linq;
using Xunit;

namespace CsVerify.Tests
{
    /// <summary>Cancellation: a token's state changes behind its back, and what is cancelled comes out as an exception.</summary>
    public class CancellationTests
    {
        private static string[] Errors(string m) =>
            Harness.Verify("using CsVerify; using System; using System.Threading; using System.Threading.Tasks; public class Cell { public int V; } public class Gate { " + m + " }").Errors("M");

        private static string[] ErrorsAndWarnings(string m) =>
            Harness.Verify("using CsVerify; using System; using System.Threading; using System.Threading.Tasks; public class Cell { public int V; } public class Gate { " + m + " }").Diagnostics.Select(d => d.Id).ToArray();

        [Theory]
        [InlineData("static async Task M(CancellationToken ct) { while (!ct.IsCancellationRequested) { await Task.Delay(1, ct); } }")]
        [InlineData("static void M(Cell c, CancellationToken ct) { c.V = 1; try { ct.ThrowIfCancellationRequested(); c.V = 2; } catch (OperationCanceledException) { c.V = 2; } Spec.Assert(c.V == 2); }")]
        [InlineData("static async Task M(CancellationToken ct) { int x = 1; try { await Task.Delay(1, ct); x = 2; } catch (OperationCanceledException) { Spec.Assert(x == 1); } }")]
        // a postcondition is of a normal return: cancelled, there is no result to speak of
        [InlineData("static async Task<int> Pos(CancellationToken ct) { Spec.Ensures<int>(r => r > 0); await Task.Delay(1, ct); return 1; } static async Task M(CancellationToken ct) { var r = await Pos(ct); Spec.Assert(r > 0); }")]
        [InlineData("static void M(CancellationToken ct) { var a = ct.CanBeCanceled; var b = ct.CanBeCanceled; Spec.Assert(a == b); }")]
        public void Proved(string m) => Assert.Empty(Errors(m));

        [Theory]
        // it may change at any moment, between two reads as much as across an await
        [InlineData("CSV1004", "static void M(CancellationToken ct) { var a = ct.IsCancellationRequested; var b = ct.IsCancellationRequested; Spec.Assert(a == b); }")]
        [InlineData("CSV1004", "static async Task M(CancellationToken ct) { var a = ct.IsCancellationRequested; await Task.Yield(); var b = ct.IsCancellationRequested; Spec.Assert(a == b); }")]
        [InlineData("CSV1004", "static async Task M(ValueTask t) { var a = t.IsCompleted; await Task.Yield(); var b = t.IsCompleted; Spec.Assert(a == b); }")]
        [InlineData("CSV1004", "static void M(CancellationToken ct) { if (ct.IsCancellationRequested) return; var b = ct.IsCancellationRequested; Spec.Assert(!b); }")]
        [InlineData("CSV1004", "static void M(CancellationToken ct) { ct.ThrowIfCancellationRequested(); var b = ct.IsCancellationRequested; Spec.Assert(!b); }")]
        // specifications can't speak of it
        [InlineData("CSV1901", "static void M(CancellationToken ct) { if (!ct.IsCancellationRequested) Spec.Assert(!ct.IsCancellationRequested); }")]
        // being cancelled comes out as an exception, at any of these
        [InlineData("CSV1004", "static void M(Cell c, CancellationToken ct) { c.V = 1; try { ct.ThrowIfCancellationRequested(); c.V = 2; } catch (OperationCanceledException) { Spec.Assert(c.V == 2); } }")]
        [InlineData("CSV1004", "static void M(Cell c, CancellationToken ct) { c.V = 1; try { ct.ThrowIfCancellationRequested(); c.V = 2; } catch (OperationCanceledException) { } Spec.Assert(c.V == 2); }")]
        [InlineData("CSV1004", "static async Task M(CancellationToken ct) { int x = 1; try { await Task.Delay(1, ct); x = 2; } catch (OperationCanceledException) { Spec.Assert(x == 2); } }")]
        [InlineData("CSV1004", "static async Task Work(CancellationToken ct) { await Task.Delay(1, ct); } static async Task M(CancellationToken ct) { int x = 1; try { await Work(ct); x = 2; } catch (OperationCanceledException) { Spec.Assert(x == 2); } }")]
        // so what a semaphore's or a lock's invariant needs must hold where it is cancelled
        [InlineData("CSV1024", "private readonly SemaphoreSlim _gate = new SemaphoreSlim(1, 1); [GuardedBy(nameof(_gate))] private int _n; [LockInvariant(nameof(_gate))] [Pure] private bool Inv() => _n >= 0; public Gate() { _n = 0; } " +
                               "public async Task M(CancellationToken ct) { await _gate.WaitAsync(ct); try { _n = -1; await Task.Delay(1, ct); _n = 1; } finally { _gate.Release(); } }")]
        public void Reported(string id, string m) => Assert.Contains(id, Errors(m));

        [Fact]
        public void ArraySegment_SeesWritesToItsArray() => Assert.Contains("CSV1004", Errors(
            "static void M(int[] a) { Spec.Requires(a.Length > 0); var s = new ArraySegment<int>(a); var x = s[0]; a[0] = 1; var y = s[0]; Spec.Assert(x == y); }"));

        [Fact]
        public void ReadingAToken_IsNotWarnedOf() =>
            Assert.DoesNotContain("CSV1900", ErrorsAndWarnings("static bool M(CancellationToken ct) { return ct.IsCancellationRequested; }"));

        [Fact]
        public void ReleasedOnCancellation_InvariantRestored() => Assert.Empty(Errors(
            "private readonly SemaphoreSlim _gate = new SemaphoreSlim(1, 1); [GuardedBy(nameof(_gate))] private int _n; [LockInvariant(nameof(_gate))] [Pure] private bool Inv() => _n >= 0; public Gate() { _n = 0; } " +
            "public async Task M(CancellationToken ct) { await _gate.WaitAsync(ct); try { _n = -1; await Task.Delay(1, ct); } finally { _n = 0; _gate.Release(); } }"));
    }
}
