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
    
        // ---- locks on objects: levels by class

        private const string Classes = "[LockLevel(1)] public class A { public void M(B b) { BODY } } [LockLevel(2)] public class B { } ";

        [Theory]
        [InlineData("lock (this) { lock (b) { } }")]
        [InlineData("var held = b; lock (this) { lock (held) { } }")]
        public void ByClass_Proved(string body) => Assert.DoesNotContain(Order, AllErrors(Classes.Replace("BODY", body)));

        [Theory]
        [InlineData("lock (b) { lock (this) { } }")]
        [InlineData("lock (this) { lock ((object)b) { } }")]
        [InlineData("lock (this) { lock (typeof(A)) { } }")]
        public void ByClass_Reported(string body) => Assert.Contains(Order, AllErrors(Classes.Replace("BODY", body)));

        [Fact]
        public void ALocalThatHoldsALockField_IsThatLock() => Assert.DoesNotContain(Order, Errors(Two + "void M() { var l = _a; lock (l) { lock (_b) { } } }"));

        [Theory]
        // one object, two levels
        [InlineData("[LockLevel(1)] public class P { } [LockLevel(2)] public class Q : P { }")]
        [InlineData("[LockLevel(1)] public class P { } public class C { [LockLevel(2)] readonly P _p = new P(); }")]
        [InlineData("public class C { [LockLevel(1)] readonly object _a = new object(); [LockLevel(2)] readonly object _b; public C() { _b = _a; } }")]
        [InlineData("public class C { [LockLevel(1)] object _a = new object(); }")]
        public void Misdeclared_IsReported(string source) => Assert.Contains(Order, AllErrors(source + " public class Z { public void Use() { } }"));

        // ---- the same field of two objects, through calls, ordered by id

        private const string Accounts = Account + "public static class Bank { static void Credit(Account a) { lock (a.Lock) { a.Balance = 1; } } BODY } ";

        [Theory]
        [InlineData("public static void M(Account x, Account y) { Spec.Requires(x.Id < y.Id); lock (x.Lock) { Credit(y); } }")]
        [InlineData("public static void M(Account x, Account y) { Spec.Requires(x.Id < y.Id); lock (x.Lock) { y.Add(); } }")]
        [InlineData("static void Mid(Account a) { Credit(a); } public static void M(Account x, Account y) { Spec.Requires(x.Id < y.Id); lock (x.Lock) { Mid(y); } }")]
        // the same object again: a lock is reentrant
        [InlineData("public static void M(Account x) { lock (x.Lock) { Credit(x); } }")]
        public void ThroughCalls_Proved(string body) => Assert.Empty(AllErrors(Accounts.Replace("BODY", body).Replace("public Account(int id)", "public void Add() { lock (Lock) { Balance = 2; } } public Account(int id)")));

        [Theory]
        [InlineData("public static void M(Account x, Account y) { Spec.Requires(x != y); lock (x.Lock) { Credit(y); } }")]
        [InlineData("public static void M(Account x, Account y) { Spec.Requires(y.Id < x.Id); lock (x.Lock) { y.Add(); } }")]
        [InlineData("static void Mid(Account a) { Credit(a); } public static void M(Account x, Account y) { lock (x.Lock) { Mid(y); } }")]
        public void ThroughCalls_Reported(string body) => Assert.Contains(Order, AllErrors(Accounts.Replace("BODY", body).Replace("public Account(int id)", "public void Add() { lock (Lock) { Balance = 2; } } public Account(int id)")));

        [Fact]
        public void ByClass_OrderedById() => Assert.Empty(AllErrors(
            "[LockLevel(1, OrderedBy = nameof(Id))] public class Node { public readonly int Id; public Node(int id) { Id = id; } } " +
            "public static class G { public static void Both(Node a, Node b) { Spec.Requires(a.Id < b.Id); lock (a) { lock (b) { } } } }"));

        [Fact]
        public void ByClass_OrderedById_Reversed_IsReported() => Assert.Contains(Order, AllErrors(
            "[LockLevel(1, OrderedBy = nameof(Id))] public class Node { public readonly int Id; public Node(int id) { Id = id; } } " +
            "public static class G { public static void Both(Node a, Node b) { Spec.Requires(b.Id < a.Id); lock (a) { lock (b) { } } } }"));

        // ---- what a library calls back, and calls with no call written

        private const string Key = "public sealed class Key { [LockLevel(LEVEL)] static readonly object L = new object(); public override bool Equals(object o) { lock (L) { return false; } } public override int GetHashCode() => 0; } ";

        [Theory]
        [InlineData("1", false)]
        [InlineData("3", true)]
        public void Callbacks_EqualsADictionaryCalls(string level, bool fine)
        {
            var errors = AllErrors(Key.Replace("LEVEL", level) +
                "public class C { [LockLevel(2)] readonly object _b = new object(); public bool M(System.Collections.Generic.Dictionary<Key, int> d, Key k) { lock (_b) { return d.ContainsKey(k); } } }");
            if (fine) Assert.DoesNotContain(Order, errors); else Assert.Contains(Order, errors);
        }

        [Fact]
        public void Callbacks_AComparerTheCollectionWasMadeWith() => Assert.Contains(Order, AllErrors(
            "public sealed class Cmp : System.Collections.Generic.IEqualityComparer<string> { [LockLevel(1)] static readonly object L = new object(); " +
            "public bool Equals(string a, string b) { lock (L) { return a == b; } } public int GetHashCode(string s) => 0; } " +
            "public class C { [LockLevel(2)] readonly object _b = new object(); public bool M(System.Collections.Generic.Dictionary<string, int> d) { lock (_b) { return d.ContainsKey(\"x\"); } } }"));

        [Theory]
        [InlineData("public static V operator +(V a, V b) { lock (L) { return a; } } ", "var c = v + v;")]
        [InlineData("public System.Collections.Generic.IEnumerator<int> GetEnumerator() { lock (L) { yield return 1; } } ", "foreach (var x in v) { }")]
        [InlineData("public void Dispose() { lock (L) { } } ", "using (v) { }")]
        public void ImplicitCalls_Count(string member, string use) => Assert.Contains(Order, AllErrors(
            "public sealed class V : IDisposable { [LockLevel(1)] static readonly object L = new object(); " + member + (member.Contains("Dispose") ? "" : "public void Dispose() { } ") + "} " +
            "public class C { [LockLevel(2)] readonly object _b = new object(); public void M(V v) { lock (_b) { " + use + " } } }"));

        // ---- Monitor.Wait and Pulse, and other waits

        private const string Monitor = "[LockLevel(1)] readonly object _l = new object(); [LockLevel(2)] readonly object _m = new object(); [GuardedBy(nameof(_l))] int _n; ";

        [Theory]
        [InlineData("void M() { lock (_l) { while (_n <= 0) Monitor.Wait(_l); _n = _n - 1; } }")]
        [InlineData("void M() { lock (_l) { _n = 1; Monitor.PulseAll(_l); } }")]
        public void Monitor_Proved(string m) => Assert.Empty(Errors(Monitor + m));

        [Theory]
        [InlineData("CSV1023", "void M() { Monitor.Wait(_l); }")]
        [InlineData("CSV1023", "void M() { lock (_m) { Monitor.Pulse(_l); } }")]
        [InlineData("CSV1025", "void M() { lock (_l) { lock (_m) { Monitor.Wait(_l); } } }")]
        // what it guards may change while it waits
        [InlineData("CSV1004", "void M() { lock (_l) { _n = 1; Monitor.Wait(_l); Spec.Assert(_n == 1); } }")]
        // a method that waits, called while another lock is held
        [InlineData("CSV1025", "void W() { lock (_l) { Monitor.Wait(_l); } } void M() { lock (_m) { W(); } }")]
        public void Monitor_Reported(string id, string m) => Assert.Contains(id, Errors(Monitor + m));

        [Fact]
        public void Monitor_InvariantMustHoldAtWait() => Assert.Contains("CSV1024", AllErrors(
            "public class C { readonly object _l = new object(); [GuardedBy(nameof(_l))] int _n; [LockInvariant(nameof(_l)), Pure] bool Valid() => _n >= 0; public C() { } " +
            "public void M() { lock (_l) { _n = -1; Monitor.Wait(_l); _n = 0; } } }"));

        [Theory]
        [InlineData("void M(ManualResetEventSlim e) { lock (_b) { e.Wait(); } }")]
        [InlineData("void M(CountdownEvent e) { lock (_b) { e.Wait(); } }")]
        [InlineData("readonly SemaphoreSlim _many = new SemaphoreSlim(4); void M() { lock (_b) { _many.Wait(); } }")]
        public void OtherWaits_UnderALock_AreReported(string m) => Assert.Contains(Order, Errors(Two + m));

        [Fact]
        public void OtherWaits_OutsideLocks_AreFine() => Assert.DoesNotContain(Order, Errors(Two + "void M(ManualResetEventSlim e) { e.Wait(); lock (_b) { } }"));

        // ---- blocking on async code that comes back to its context

        [Theory]
        [InlineData("async Task F() { await Task.Delay(1); } void M() { F().Wait(); }")]
        [InlineData("async Task<int> F() { await Task.Delay(1); return 1; } int M() { return F().Result; }")]
        [InlineData("async Task F() { await Task.Yield(); } void M() { var t = F(); t.GetAwaiter().GetResult(); }")]
        // (awaited only on one path: not finished on the other)
        [InlineData("async Task<int> F() { await Task.Delay(1); return 1; } async Task<int> M(bool b) { var t = F(); if (b) await t; return t.Result; }")]
        [InlineData("async Task G() { await Task.Delay(1); } async Task F() { await G().ConfigureAwait(false); } void M() { F().Wait(); }")]
        public void Context_Reported(string m) => Assert.Contains(Order, Errors(m));

        [Theory]
        [InlineData("async Task F() { await Task.Delay(1).ConfigureAwait(false); } void M() { F().Wait(); }")]
        [InlineData("async Task F() { await Task.Delay(1); } void M() { Task.Run(() => F().Wait()).Wait(); }")]
        [InlineData("async Task F() { await Task.Delay(1); } async Task M() { await F(); }")]
        // (already finished: its Result doesn't wait)
        [InlineData("async Task<int> F() { await Task.Delay(1); return 1; } async Task<int> M() { var t = F(); await t; return t.Result; }")]
        [InlineData("async Task<int> F() { await Task.Delay(1); return 1; } async Task<int> M() { var t = F(); var u = F(); await Task.WhenAll(t, u); return t.Result + u.Result; }")]
        public void Context_Fine(string m) => Assert.DoesNotContain(Order, Errors(m));

        // ---- other lock primitives, in their form

        private const string Prims = Two + "[LockLevel(3)] readonly ReaderWriterLockSlim _rw = new ReaderWriterLockSlim(); [LockLevel(0)] readonly Mutex _mx = new Mutex(); [GuardedBy(nameof(_a))] int _n; ";

        [Theory]
        [InlineData("void M() { Monitor.Enter(_a); try { lock (_b) { } } finally { Monitor.Exit(_a); } }")]
        [InlineData("void M() { bool taken = false; try { Monitor.Enter(_a, ref taken); lock (_b) { } } finally { if (taken) Monitor.Exit(_a); } }")]
        [InlineData("void M() { lock (_b) { _rw.EnterWriteLock(); try { } finally { _rw.ExitWriteLock(); } } }")]
        [InlineData("void M() { _mx.WaitOne(); try { lock (_a) { } } finally { _mx.ReleaseMutex(); } }")]
        // what Monitor.Enter's form guards
        [InlineData("void M() { Monitor.Enter(_a); try { _n = 1; } finally { Monitor.Exit(_a); } }")]
        public void Primitives_Proved(string m) => Assert.Empty(Errors(Prims + m));

        [Theory]
        [InlineData("CSV1025", "void M() { Monitor.Enter(_b); try { lock (_a) { } } finally { Monitor.Exit(_b); } }")]
        [InlineData("CSV1025", "void M() { _rw.EnterReadLock(); try { lock (_a) { } } finally { _rw.ExitReadLock(); } }")]
        [InlineData("CSV1025", "void M() { lock (_a) { _mx.WaitOne(); try { } finally { _mx.ReleaseMutex(); } } }")]
        // out of the form: where it's held can't be told
        [InlineData("CSV1025", "void M() { Monitor.Enter(_a); lock (_b) { } Monitor.Exit(_a); }")]
        [InlineData("CSV1025", "void M() { _rw.EnterWriteLock(); _rw.ExitWriteLock(); }")]
        // guarded state outside the form
        [InlineData("CSV1023", "void M() { Monitor.Enter(_a); try { } finally { Monitor.Exit(_a); } _n = 1; }")]
        public void Primitives_Reported(string id, string m) => Assert.Contains(id, Errors(Prims + m));

        [Fact]
        public void Primitives_MonitorInvariantAtExit() => Assert.Contains("CSV1024", AllErrors(
            "public class C { readonly object _l = new object(); [GuardedBy(nameof(_l))] int _n; [LockInvariant(nameof(_l)), Pure] bool Valid() => _n >= 0; public C() { } " +
            "public void M() { Monitor.Enter(_l); try { _n = -1; } finally { Monitor.Exit(_l); } } }"));
}
}
