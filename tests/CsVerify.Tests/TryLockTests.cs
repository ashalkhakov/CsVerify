using System.Linq;
using Xunit;

namespace CsVerify.Tests
{
    /// <summary>A flag taken by Interlocked as a try-lock, in its form: it guards state as a lock does, and never deadlocks.</summary>
    public class TryLockTests
    {
        private const string Usings = "using CsVerify; using System; using System.Threading; using System.Threading.Tasks; ";

        // an instance flag guarding a count, with an invariant
        private const string Flag =
            "int _busy; [GuardedBy(nameof(_busy))] int _n; [LockInvariant(nameof(_busy)), Pure] bool Valid() => _n >= 0; public C() { _n = 0; } ";
        private const string BoolFlag =
            "bool _taken; [GuardedBy(nameof(_taken))] int _m; ";

        private static string[] Errors(string members) =>
            Harness.Verify(Usings + "public class C { " + members + " }").Errors("M");

        private static string Explain(string members) =>
            Harness.Verify(Usings + "public class C { " + members + " }").Explain("M");

        private static string[] AllErrors(string source) =>
            Harness.Verify(Usings + source).Diagnostics.Where(d => d.IsError).Select(d => d.Id).ToArray();

        [Theory]
        // the forms: taken when the if runs, or the if leaving when it fails and the try after
        [InlineData(Flag + "bool M() { if (Interlocked.Exchange(ref _busy, 1) == 0) { try { if (_n < int.MaxValue) _n = _n + 1; } finally { Volatile.Write(ref _busy, 0); } return true; } return false; }")]
        [InlineData(Flag + "bool M() { if (0 == Interlocked.CompareExchange(ref _busy, 1, 0)) { try { if (_n < int.MaxValue) _n++; } finally { Interlocked.Exchange(ref _busy, 0); } return true; } else return false; }")]
        [InlineData(Flag + "bool M() { if (Interlocked.Exchange(ref _busy, 1) != 0) return false; try { if (_n < int.MaxValue) _n++; } finally { Volatile.Write(ref _busy, 0); } return true; }")]
        [InlineData(Flag + "bool M() { if (Interlocked.Exchange(ref _busy, 1) == 1) { return false; } try { _n = 5; } finally { Volatile.Write(ref _busy, 0); } return true; }")]
        [InlineData(BoolFlag + "bool M() { if (!Interlocked.Exchange(ref _taken, true)) { try { _m = 1; } finally { Volatile.Write(ref _taken, false); } return true; } return false; }")]
        [InlineData(BoolFlag + "void M() { if (Interlocked.Exchange(ref _taken, true)) return; try { _m = 2; } finally { Volatile.Write(ref _taken, false); } }")]
        // while held, nothing else changes what it guards; on taking, its invariant is known
        [InlineData(Flag + "void M() { if (Interlocked.Exchange(ref _busy, 1) == 0) { try { int a = _n; Thread.Sleep(1); Spec.Assert(a == _n && a >= 0); } finally { Volatile.Write(ref _busy, 0); } } }")]
        // taken again by its holder, it's refused
        [InlineData(Flag + "void M() { if (Interlocked.Exchange(ref _busy, 1) == 0) { try { if (Interlocked.Exchange(ref _busy, 1) == 0) { try { Spec.Assert(false); } finally { Volatile.Write(ref _busy, 0); } } } finally { Volatile.Write(ref _busy, 0); } } }")]
        // another object's flag
        [InlineData(Flag + "static void M(C c) { if (Interlocked.Exchange(ref c._busy, 1) == 0) { try { c._n = 0; } finally { Volatile.Write(ref c._busy, 0); } } }")]
        // concurrent code
        [InlineData(Flag + "[RunsConcurrently] void M() { if (Interlocked.Exchange(ref _busy, 1) != 0) return; try { _n = 1; } finally { Volatile.Write(ref _busy, 0); } }")]
        // it never waits: no order with other locks, either way
        [InlineData(Flag + "[LockLevel(1)] readonly object _l = new object(); void M() { lock (_l) { if (Interlocked.Exchange(ref _busy, 1) == 0) { try { _n = 1; lock (_l) { } } finally { Volatile.Write(ref _busy, 0); } } } }")]
        [InlineData(Flag + "readonly object _l = new object(); void M() { if (Interlocked.Exchange(ref _busy, 1) == 0) { try { lock (_l) { _n = 1; } } finally { Volatile.Write(ref _busy, 0); } } }")]
        public void Proved(string members) => Assert.True(Errors(members).Length == 0, Explain(members));

        [Theory]
        // what it guards, outside it
        [InlineData("CSV1023", Flag + "void M() { _n = 1; }")]
        [InlineData("CSV1023", Flag + "void M() { if (Interlocked.Exchange(ref _busy, 1) == 0) { try { } finally { Volatile.Write(ref _busy, 0); } } else { _n = 1; } }")]
        [InlineData("CSV1023", Flag + "void M() { if (Interlocked.Exchange(ref _busy, 1) == 0) { try { } finally { Volatile.Write(ref _busy, 0); _n = 1; } } }")]
        // the invariant broken where it's given back
        [InlineData("CSV1024", Flag + "void M() { if (Interlocked.Exchange(ref _busy, 1) == 0) { try { _n = -1; } finally { Volatile.Write(ref _busy, 0); } } }")]
        // out of its form: no finally (as in the Interlocked documentation's example), given back elsewhere, read, written
        [InlineData("CSV1023", Flag + "bool M() { if (Interlocked.Exchange(ref _busy, 1) == 0) { _n = 1; Interlocked.Exchange(ref _busy, 0); return true; } return false; }")]
        [InlineData("CSV1023", Flag + "void M() { Volatile.Write(ref _busy, 0); }")]
        [InlineData("CSV1023", Flag + "bool M() { return _busy == 0; }")]
        [InlineData("CSV1023", Flag + "void M() { _busy = 1; }")]
        [InlineData("CSV1023", Flag + "void M() { if (Interlocked.Exchange(ref _busy, 1) == 0) { int x = 0; try { } finally { Volatile.Write(ref _busy, 0); } } }")]
        public void Reported(string id, string members) => Assert.True(Errors(members).Contains(id), Explain(members));

        [Fact]
        public void A_Flag_IsNotAlsoAtomic() =>
            Assert.Contains("CSV1030", AllErrors("public class C { [Atomic] volatile int _busy; [GuardedBy(nameof(_busy))] int _n; void M() { } }"));

        [Fact]
        public void A_StaticConstructor_HasItsStaticsToItself() =>
            Assert.Empty(AllErrors("public static class C { static int _busy; [GuardedBy(nameof(_busy))] static int _n; [LockInvariant(nameof(_busy)), Pure] static bool Valid() => _n >= 0; static C() { _n = 0; } " +
                                   "static void M() { if (Interlocked.Exchange(ref _busy, 1) == 0) { try { if (_n < int.MaxValue) _n++; } finally { Volatile.Write(ref _busy, 0); } } } }"));
    }
}
