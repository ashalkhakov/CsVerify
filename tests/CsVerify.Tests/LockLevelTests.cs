using System.Linq;
using Xunit;

namespace CsVerify.Tests
{
    /// <summary>Deadlock freedom by lock levels: while a lock is held, only higher locks are taken, by the code, its calls, and the tasks it waits for.</summary>
    public class LockLevelTests
    {
        private const string Usings = "using CsVerify; using System; using System.Threading; using System.Threading.Tasks; ";
        private const string Order = "CSV1025";

        private const string Two = "[LockLevel(1)] readonly object _a = new object(); [LockLevel(2)] readonly object _b = new object(); ";
        private const string Unleveled = "readonly object _a = new object(); readonly object _b = new object(); ";
        private const string Gates = "[LockLevel(1)] readonly SemaphoreSlim _g = new SemaphoreSlim(1, 1); [LockLevel(2)] readonly object _b = new object(); [LockLevel(0)] readonly object _z = new object(); ";

        private static string[] Errors(string members) =>
            Harness.Verify(Usings + "public class C { " + members + " }").Errors("M");

        private static string[] AllErrors(string source) =>
            Harness.Verify(Usings + source).Diagnostics.Where(d => d.IsError).Select(d => d.Id).ToArray();

        [Theory]
        // increasing order
        [InlineData(Two + "void M() { lock (_a) { lock (_b) { } } }")]
        // one at a time needs no level
        [InlineData(Unleveled + "void M() { lock (_a) { } lock (_b) { } }")]
        // the same lock again: a lock is reentrant
        [InlineData(Unleveled + "void M() { lock (_a) { lock (_a) { } } }")]
        // through calls
        [InlineData(Two + "void B() { lock (_b) { } } void M() { lock (_a) { B(); } }")]
        [InlineData(Two + "void B() { lock (_b) { } } void Mid() { B(); } void M() { lock (_a) { Mid(); } }")]
        [InlineData(Two + "int P { get { lock (_b) { return 1; } } } int M() { lock (_a) { return P; } }")]
        [InlineData(Two + "void A() { lock (_a) { } } void M() { lock (_a) { A(); } }")]
        // calls that take nothing
        [InlineData(Two + "int F(int x) => x + 1; int M() { lock (_b) { return F(1); } }")]
        [InlineData(Two + "int M() { lock (_b) { return Math.Abs(-1); } }")]
        // a lambda that a library call runs at once
        [InlineData(Two + "void M(System.Collections.Generic.List<int> l) { lock (_a) { l.ForEach(x => { lock (_b) { } }); } }")]
        // a delegate type said to take none
        [InlineData("[LockLevel(1)] readonly object _a = new object(); void M(Quiet q) { lock (_a) { q(); } } } [TakesNoLocks] public delegate void Quiet(); class D {")]
        // a method said to take none, which doesn't
        [InlineData(Two + "[TakesNoLocks] int F(int x) => x; int M() { lock (_a) { return F(1); } }")]
        public void Proved(string members) => Assert.DoesNotContain(Order, Errors(members));

        [Theory]
        // decreasing, equal, or not given
        [InlineData(Two + "void M() { lock (_b) { lock (_a) { } } }")]
        [InlineData("[LockLevel(1)] readonly object _a = new object(); [LockLevel(1)] readonly object _b = new object(); void M() { lock (_a) { lock (_b) { } } }")]
        [InlineData(Unleveled + "void M() { lock (_a) { lock (_b) { } } }")]
        [InlineData("[LockLevel(1)] readonly object _a = new object(); readonly object _b = new object(); void M() { lock (_a) { lock (_b) { } } }")]
        // a lock that isn't a field
        [InlineData(Two + "void M(object o) { lock (_a) { lock (o) { } } }")]
        // through calls, however deep
        [InlineData(Two + "void A() { lock (_a) { } } void M() { lock (_b) { A(); } }")]
        [InlineData(Two + "void A() { lock (_a) { } } void Mid() { A(); } void M() { lock (_b) { Mid(); } }")]
        [InlineData(Two + "int P { get { lock (_a) { return 1; } } } int M() { lock (_b) { return P; } }")]
        [InlineData(Two + "void A() { lock (_a) { } } void M(System.Collections.Generic.List<int> l) { lock (_b) { l.ForEach(x => A()); } }")]
        // a delegate could take any lock
        [InlineData(Two + "void M(Action f) { lock (_a) { f(); } }")]
        [InlineData(Two + "void M(Action<int> f, System.Collections.Generic.List<int> l) { lock (_a) { l.ForEach(f); } }")]
        // the same field of another object, in no order
        [InlineData(Two + "void M(C o) { lock (_a) { lock (o._a) { } } }")]
        [InlineData(Two + "void A() { lock (_a) { } } void M(C o) { lock (_a) { o.A(); } }")]
        public void Reported(string members) => Assert.Contains(Order, Errors(members));

        [Fact]
        public void Virtual_EveryOverrideCounts() => Assert.Contains(Order, AllErrors(
            "public class C { [LockLevel(1)] protected readonly object _a = new object(); [LockLevel(2)] protected readonly object _b = new object(); public virtual void V() { } public void M() { lock (_b) { V(); } } } " +
            "public class D : C { public override void V() { lock (_a) { } } }"));

        [Fact]
        public void Interface_EveryImplementationCounts() => Assert.Contains(Order, AllErrors(
            "public interface I { void V(); } public class D : I { public static readonly object L = new object(); public void V() { lock (L) { } } } " +
            "public class C { [LockLevel(1)] readonly object _a = new object(); public void M(I i) { lock (_a) { i.V(); } } }"));

        [Fact]
        public void Interface_SaidToTakeNone_IsTrusted_AndChecked()
        {
            const string Source = "[TakesNoLocks] public interface I { void V(); } public class D : I { [LockLevel(5)] public static readonly object L = new object(); public void V() { BODY } } " +
                                  "public class C { [LockLevel(1)] readonly object _a = new object(); public void M(I i) { lock (_a) { i.V(); } } }";
            Assert.Empty(AllErrors(Source.Replace("BODY", "")));
            Assert.Contains(Order, AllErrors(Source.Replace("BODY", "lock (L) { }")));
        }

        [Fact]
        public void SaidToTakeNone_ButDoes_IsReported() => Assert.Contains(Order, Harness.Verify(Usings +
            "public class C { [LockLevel(1)] readonly object _a = new object(); [TakesNoLocks] public void M() { lock (_a) { } } }").Errors("M"));

        [Fact]
        public void DelegateSaidToTakeNone_ALambdaThatDoes_IsReported() => Assert.Contains(Order, AllErrors(
            "[TakesNoLocks] public delegate void Quiet(); public class C { [LockLevel(1)] readonly object _a = new object(); public Quiet M() { return () => { lock (_a) { } }; } }"));

        // ---- two locks of one field, ordered by an id

        private const string Account = "public class Account { public readonly int Id; [LockLevel(1, OrderedBy = nameof(Id))] public readonly object Lock = new object(); [GuardedBy(nameof(Lock))] public int Balance; public Account(int id) { Id = id; } } ";

        [Fact]
        public void OrderedBy_TakenInOrderOfId_IsProved() => Assert.Empty(AllErrors(Account +
            "public static class Bank { public static void Transfer(Account from, Account to) { Spec.Requires(from.Id != to.Id); " +
            "if (from.Id < to.Id) { lock (from.Lock) { lock (to.Lock) { from.Balance = 0; to.Balance = 1; } } } " +
            "else { lock (to.Lock) { lock (from.Lock) { from.Balance = 0; to.Balance = 1; } } } } }"));

        [Fact]
        public void OrderedBy_GivenOrder_IsProved() => Assert.Empty(AllErrors(Account +
            "public static class Bank { public static void Both(Account a, Account b) { Spec.Requires(a.Id < b.Id); lock (a.Lock) { lock (b.Lock) { a.Balance = 0; b.Balance = 0; } } } }"));

        [Fact]
        public void OrderedBy_NotKnownToIncrease_IsReported() => Assert.Contains(Order, AllErrors(Account +
            "public static class Bank { public static void Both(Account a, Account b) { Spec.Requires(a != b); lock (a.Lock) { lock (b.Lock) { } } } }"));

        // ---- semaphores, across awaits

        [Theory]
        [InlineData(Gates + "async Task M() { await _g.WaitAsync(); try { lock (_b) { } } finally { _g.Release(); } }")]
        [InlineData(Gates + "void B() { lock (_b) { } } async Task M() { await _g.WaitAsync(); try { await Task.Yield(); B(); } finally { _g.Release(); } }")]
        // waiting for a task that takes only higher locks
        [InlineData(Gates + "async Task B() { await Task.Yield(); lock (_b) { } } async Task M() { var t = B(); await _g.WaitAsync(); try { await t; } finally { _g.Release(); } }")]
        [InlineData(Gates + "async Task M() { await _g.WaitAsync(); try { await Task.Delay(1); } finally { _g.Release(); } }")]
        public void Gates_Proved(string members) => Assert.DoesNotContain(Order, Errors(members));

        [Theory]
        [InlineData(Gates + "async Task M() { await _g.WaitAsync(); try { lock (_z) { } } finally { _g.Release(); } }")]
        [InlineData(Gates + "void Z() { lock (_z) { } } async Task M() { await _g.WaitAsync(); try { await Task.Yield(); Z(); } finally { _g.Release(); } }")]
        // waiting for a task that may need the semaphore held, or a lower lock
        [InlineData(Gates + "async Task Z() { await Task.Yield(); lock (_z) { } } async Task M() { var t = Z(); await _g.WaitAsync(); try { await t; } finally { _g.Release(); } }")]
        [InlineData(Gates + "async Task G() { await _g.WaitAsync(); try { } finally { _g.Release(); } } void M() { var t = G(); lock (_b) { t.Wait(); } }")]
        [InlineData(Gates + "void M() { var t = Task.Run(() => { lock (_z) { } }); lock (_b) { t.Wait(); } }")]
        // waiting for a task it was given, under a lock
        [InlineData(Gates + "void M(Task t) { lock (_b) { t.Wait(); } }")]
        [InlineData(Gates + "int M(Task<int> t) { lock (_b) { return t.Result; } }")]
        [InlineData(Gates + "async Task M(Task t) { await _g.WaitAsync(); try { await t; } finally { _g.Release(); } }")]
        public void Gates_Reported(string members) => Assert.Contains(Order, Errors(members));
    }
}
