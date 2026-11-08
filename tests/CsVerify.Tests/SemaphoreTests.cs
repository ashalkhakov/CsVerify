using System.Linq;
using Xunit;

namespace CsVerify.Tests
{
    /// <summary>A SemaphoreSlim of count 1 as a lock: held across an await, where a lock statement can't be.</summary>
    public class SemaphoreTests
    {
        private const string Usings = "using CsVerify; using System; using System.Threading; using System.Threading.Tasks; ";

        private static string[] Errors(string members, string gate = "private readonly SemaphoreSlim _gate = new SemaphoreSlim(1, 1);") =>
            Harness.Verify(Usings + "public class C { " + gate + " [GuardedBy(nameof(_gate))] private int _n; " + members + " }").Errors("M");

        [Theory]
        [InlineData("public async Task M() { await _gate.WaitAsync(); try { _n = 1; } finally { _gate.Release(); } }")]
        [InlineData("public async Task M() { await _gate.WaitAsync().ConfigureAwait(false); try { _n = 1; } finally { _gate.Release(); } }")]
        [InlineData("public async Task M(CancellationToken ct) { await _gate.WaitAsync(ct); try { _n = 1; } finally { _gate.Release(); } }")]
        [InlineData("public void M() { _gate.Wait(); try { _n = 1; } finally { _gate.Release(); } }")]
        // what it guards stays across an await: nobody else can have it
        [InlineData("public async Task M() { await _gate.WaitAsync(); try { _n = 1; await Task.Yield(); Spec.Assert(_n == 1); } finally { _gate.Release(); } }")]
        [InlineData("public async Task M() { await _gate.WaitAsync(); try { _n = 1; await Task.Delay(1); _n = _n + 1; Spec.Assert(_n == 2); } finally { _gate.Release(); } }")]
        // before the release, the finally still has it; so does a catch
        [InlineData("public async Task M() { await _gate.WaitAsync(); try { _n = 1; } finally { _n = 0; _gate.Release(); } }")]
        [InlineData("public async Task M() { await _gate.WaitAsync(); try { _n = 1; } catch (InvalidOperationException) { _n = 0; } finally { _gate.Release(); } }")]
        // a method whose caller holds it
        [InlineData("[GuardedBy(nameof(_gate))] private async Task Bump() { Spec.Requires(_n < 100); Spec.Ensures(_n == Spec.Old(_n) + 1); await Task.Yield(); _n = _n + 1; } " +
                    "public async Task M() { await _gate.WaitAsync(); try { _n = 0; await Bump(); Spec.Assert(_n == 1); } finally { _gate.Release(); } }")]
        [InlineData("[GuardedBy(nameof(_gate))] private async Task M() { _n = 1; await Task.Yield(); Spec.Assert(_n == 1); }")]
        // another object's
        [InlineData("public async Task M(C o) { await o._gate.WaitAsync(); try { o._n = 1; await Task.Yield(); Spec.Assert(o._n == 1); } finally { o._gate.Release(); } }")]
        // taken one after another
        [InlineData("public async Task M() { await _gate.WaitAsync(); try { _n = 1; } finally { _gate.Release(); } await _gate.WaitAsync(); try { _n = 2; } finally { _gate.Release(); } }")]
        public void Proved(string members) => Assert.Empty(Errors(members));

        [Theory]
        // outside it
        [InlineData("CSV1023", "public int M() { return _n; }")]
        [InlineData("CSV1023", "public async Task M() { _n = 1; await _gate.WaitAsync(); try { } finally { _gate.Release(); } }")]
        [InlineData("CSV1023", "public async Task M() { await _gate.WaitAsync(); try { } finally { _gate.Release(); } _n = 1; }")]
        [InlineData("CSV1023", "public async Task M() { await _gate.WaitAsync(); try { } finally { _gate.Release(); _n = 0; } }")]
        [InlineData("CSV1023", "public async Task M() { await _gate.WaitAsync(); try { Action a = () => _n = 1; a(); } finally { _gate.Release(); } }")]
        // another object's isn't this one's
        [InlineData("CSV1023", "public async Task M(C o) { await o._gate.WaitAsync(); try { _n = 1; } finally { o._gate.Release(); } }")]
        [InlineData("CSV1023", "public async Task M(C o, C p) { await o._gate.WaitAsync(); try { o._n = 1; } finally { p._gate.Release(); } }")]
        [InlineData("CSV1023", "public async Task M(C o, C p) { await o._gate.WaitAsync(); try { o = p; o._n = 1; } finally { o._gate.Release(); } }")]
        // not the form
        [InlineData("CSV1023", "public async Task M() { await _gate.WaitAsync(); _n = 1; _gate.Release(); }")]
        [InlineData("CSV1023", "public async Task M() { await _gate.WaitAsync(); await Task.Yield(); try { _n = 1; } finally { _gate.Release(); } }")]
        [InlineData("CSV1023", "public async Task M() { try { await _gate.WaitAsync(); _n = 1; } finally { _gate.Release(); } }")]
        [InlineData("CSV1023", "public async Task M() { await _gate.WaitAsync(); try { _n = 1; _gate.Release(); } finally { _gate.Release(); } }")]
        [InlineData("CSV1023", "public async Task M(bool b) { await _gate.WaitAsync(); try { _n = 1; } finally { if (b) _gate.Release(); } }")]
        [InlineData("CSV1023", "public async Task M() { await _gate.WaitAsync(); try { _n = 1; } finally { _gate.Release(); _gate.Release(); } }")]
        [InlineData("CSV1023", "public void M() { _gate.Release(); }")]
        // a wait that may not have got it
        [InlineData("CSV1023", "public async Task M() { await _gate.WaitAsync(10); try { _n = 1; } finally { _gate.Release(); } }")]
        [InlineData("CSV1023", "public void M() { _gate.Wait(10); try { _n = 1; } finally { _gate.Release(); } }")]
        // handed to someone who could release it
        [InlineData("CSV1023", "public SemaphoreSlim M() { return _gate; }")]
        [InlineData("CSV1023", "static void Use(SemaphoreSlim s) { } public void M() { Use(_gate); }")]
        // it would run alongside the holder
        [InlineData("CSV1023", "[GuardedBy(nameof(_gate))] private async Task Bump() { await Task.Yield(); _n = 1; } " +
                               "public async Task M() { await _gate.WaitAsync(); try { var t = Bump(); _n = 2; await t; } finally { _gate.Release(); } }")]
        // others have had it since
        [InlineData("CSV1004", "public async Task M() { await _gate.WaitAsync(); try { _n = 1; } finally { _gate.Release(); } await _gate.WaitAsync(); try { Spec.Assert(_n == 1); } finally { _gate.Release(); } }")]
        [InlineData("CSV1004", "public async Task M() { await _gate.WaitAsync(); try { Spec.Assert(_n == 0); } finally { _gate.Release(); } }")]
        [InlineData("CSV1004", "public void M() { _gate.Wait(); try { _n = 1; } finally { _gate.Release(); } _gate.Wait(); try { Spec.Assert(_n == 1); } finally { _gate.Release(); } }")]
        // the one taken and the one given back are different objects', even if what it uses is the latter's
        [InlineData("CSV1023", "public async Task M(C o, C p) { await o._gate.WaitAsync(); try { p._n = 1; } finally { p._gate.Release(); } }")]
        // holding this one's says nothing of another's
        [InlineData("CSV1004", "public async Task M(C o) { await o._gate.WaitAsync(); try { await _gate.WaitAsync(); try { o._n = 1; _n = 2; await Task.Yield(); Spec.Assert(_n == 2); Spec.Assert(o._n == 1); Spec.Assert(o == this); } finally { _gate.Release(); } } finally { o._gate.Release(); } }")]
        // taken twice: it would wait for itself
        [InlineData("CSV1025", "public async Task M() { await _gate.WaitAsync(); try { await _gate.WaitAsync(); try { _n = 1; } finally { _gate.Release(); } } finally { _gate.Release(); } }")]
        [InlineData("CSV1025", "private async Task Set() { await _gate.WaitAsync(); try { _n = 1; } finally { _gate.Release(); } } " +
                               "public async Task M() { await _gate.WaitAsync(); try { await Set(); } finally { _gate.Release(); } }")]
        [InlineData("CSV1025", "private async Task Set() { await _gate.WaitAsync(); try { _n = 1; } finally { _gate.Release(); } } private async Task Via() { await Set(); } " +
                               "public async Task M() { await _gate.WaitAsync(); try { await Via(); } finally { _gate.Release(); } }")]
        [InlineData("CSV1025", "private async Task Set() { await _gate.WaitAsync(); try { _n = 1; } finally { _gate.Release(); } } " +
                               "[GuardedBy(nameof(_gate))] private async Task M() { await Set(); }")]
        public void Reported(string id, string members) => Assert.Contains(id, Errors(members));

        [Fact]
        public void Taking_AnotherObjectsIsNotTakingItTwice_ButIsInNoOrder()
        {
            // (not a wait for itself; still, two objects' semaphores taken in no fixed order could deadlock)
            var r = Harness.Verify(Usings + "public class C { private readonly SemaphoreSlim _gate = new SemaphoreSlim(1, 1); [GuardedBy(nameof(_gate))] private int _n; " +
                "private async Task Set() { await _gate.WaitAsync(); try { _n = 1; } finally { _gate.Release(); } } " +
                "public async Task M(C o) { await _gate.WaitAsync(); try { await o.Set(); } finally { _gate.Release(); } } }");
            Assert.DoesNotContain(r.Diagnostics, d => d.Message.Contains("wait for itself"));
            Assert.Contains(r.Diagnostics, d => d.Id == "CSV1025" && d.Message.Contains("another object"));
        }

        [Theory]
        [InlineData("private readonly SemaphoreSlim _gate = new SemaphoreSlim(2);")]
        [InlineData("private readonly SemaphoreSlim _gate = new SemaphoreSlim(1, 2);")]
        [InlineData("private readonly SemaphoreSlim _gate = new SemaphoreSlim(0, 1);")]
        public void CountOtherThanOne_IsNotALock(string gate) => Assert.Contains("CSV1023", Errors(
            "public async Task M() { await _gate.WaitAsync(); try { _n = 1; } finally { _gate.Release(); } }", gate));

        [Fact]
        public void NotReadonly_IsNotALock() => Assert.Contains("CSV1023", Errors(
            "public async Task M() { await _gate.WaitAsync(); try { _n = 1; } finally { _gate.Release(); } }", "private SemaphoreSlim _gate = new SemaphoreSlim(1, 1);"));

        [Fact]
        public void MadeInTheConstructor() => Assert.Empty(Errors(
            "public C() { _gate = new SemaphoreSlim(1, 1); } public async Task M() { await _gate.WaitAsync(); try { _n = 1; await Task.Yield(); Spec.Assert(_n == 1); } finally { _gate.Release(); } }",
            "private readonly SemaphoreSlim _gate;"));

        [Fact]
        public void Static_StaysAcrossAnAwait() => Assert.Empty(Harness.Verify(Usings + "public static class C { private static readonly SemaphoreSlim _gate = new SemaphoreSlim(1, 1); [GuardedBy(nameof(_gate))] private static int _n; " +
            "public static async Task M() { await _gate.WaitAsync(); try { _n = 1; await Task.Yield(); Spec.Assert(_n == 1); } finally { _gate.Release(); } } }").Errors("M"));

        private const string Invariant = "using CsVerify; using System.Threading; using System.Threading.Tasks; public class C { private readonly SemaphoreSlim _gate = new SemaphoreSlim(1, 1); " +
            "[GuardedBy(nameof(_gate))] private int _n; [LockInvariant(nameof(_gate))] [Pure] private bool Inv() => _n >= 0; public C() { _n = 0; } ";

        [Fact]
        public void Invariant_IsGivenWhenTaken() => Assert.Empty(Harness.Verify(Invariant +
            "public async Task<int> M() { Spec.Ensures<int>(r => r >= 0); await _gate.WaitAsync(); try { return _n; } finally { _gate.Release(); } } }").Errors("M"));

        [Fact]
        public void Invariant_MustHoldWhenReleased() => Assert.Contains("CSV1024", Harness.Verify(Invariant +
            "public async Task M() { await _gate.WaitAsync(); try { _n = -1; } finally { _gate.Release(); } } }").Errors("M"));

        [Fact]
        public void Invariant_NeedNotHoldAcrossAnAwait() => Assert.Empty(Harness.Verify(Invariant +
            "public async Task M() { await _gate.WaitAsync(); try { _n = -1; await Task.Yield(); } finally { _n = 1; _gate.Release(); } } }").Errors("M"));

        // (an await may throw, and then the finally gives it back as it is)
        // (a call can't enter it again without waiting for itself, so it needn't hold there either)
        [Fact]
        public void Invariant_NeedNotHoldAcrossACall() => Assert.Empty(Harness.Verify(Invariant +
            "private static void Other() { } [GuardedBy(nameof(_gate))] private void M() { _n = -1; Other(); _n = 1; } }").Errors("M"));

        [Fact]
        public void Invariant_MustHoldIfAnAwaitThrows() => Assert.Contains("CSV1024", Harness.Verify(Invariant +
            "public async Task M() { await _gate.WaitAsync(); try { _n = -1; await Task.Yield(); _n = 1; } finally { _gate.Release(); } } }").Errors("M"));

        [Fact]
        public void Guard_IsNotInferredFromWrites_ButAnUnlockedUseIsReported()
        {
            const string Program = Usings + "public class C { private readonly SemaphoreSlim _gate = new SemaphoreSlim(1, 1); private int _n; " +
                "public async Task Set() { await _gate.WaitAsync(); try { _n = 1; await Task.Yield(); Spec.Assert(_n == 1); } finally { _gate.Release(); } } " +
                "public int M() { return _n; } }";
            var r = Harness.Verify(Program);
            // (only [GuardedBy] keeps it across the await)
            Assert.Contains("CSV1004", r.Errors("Set"));
            Assert.Contains("CSV1023", r.Errors("M"));
            Assert.Empty(Harness.Verify(Program.Replace("private int _n;", "[GuardedBy(nameof(_gate))] private int _n;")).Errors("Set"));
        }

        [Fact]
        public void Guard_IsNotInferredFromACountingSemaphore()
        {
            var r = Harness.Verify(Usings + "public class C { private readonly SemaphoreSlim _gate = new SemaphoreSlim(4); private int _n; " +
                "public async Task Set() { await _gate.WaitAsync(); try { _n = 1; } finally { _gate.Release(); } } public int M() { return _n; } }");
            Assert.DoesNotContain("CSV1023", r.Errors("M"));
        }

        [Fact]
        public void CountingSemaphore_DoesNotKeepStateAcrossAnAwait() => Assert.Contains("CSV1004", Harness.Verify(
            Usings + "public class C { private readonly SemaphoreSlim _gate = new SemaphoreSlim(4); private int _n; " +
            "public async Task M() { await _gate.WaitAsync(); try { _n = 1; await Task.Yield(); Spec.Assert(_n == 1); } finally { _gate.Release(); } } }").Errors("M"));
    }
}
