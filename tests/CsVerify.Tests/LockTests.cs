using System.Linq;
using Xunit;

namespace CsVerify.Tests
{
    /// <summary>What locks guard, and what they promise: races reported, and the facts a lock gives and takes away.</summary>
    public class LockTests
    {
        private const string Race = "CSV1023", Invariant = "CSV1024", Rejected = "CSV1004";

        private const string Guarded = "readonly object _l = new object(); [GuardedBy(nameof(_l))] int _b; [GuardedBy(nameof(_l))] void Helper() { _b = 2; } ";
        private const string Valid = "public C() { } readonly object _l = new object(); [GuardedBy(nameof(_l))] int _b; [LockInvariant(nameof(_l)), Pure] bool Valid() => _b >= 0; void Other() { } ";

        private static string[] Errors(string members) =>
            Harness.Verify("using CsVerify; using System; public class C { " + members + " }").Errors("M");

        // ---- a field written under a lock is guarded by it, with no specifications

        private const string Inferred = "readonly object _l = new object(); int _b; public void Set(int a) { lock (_l) { _b = a; } } ";

        [Theory]
        [InlineData("public void M() { _b = 0; }")]
        [InlineData("public int M() { return _b; }")]
        [InlineData("public void M() { _b++; }")]
        [InlineData("public void M() { this._b = 0; }")]
        [InlineData("public void M(C o) { o._b = 0; }")]
        [InlineData("public void M(int a) { lock (_l) { Action g = () => { _b = a; }; g(); } }")]
        public void Inferred_AUseWithoutTheLock_IsReported(string m) => Assert.Contains(Race, Errors(Inferred + m));

        [Theory]
        [InlineData("public int M() { lock (_l) { return _b; } }")]
        [InlineData("public void M() { lock (_l) { _b = 1; lock (_l) { _b = 2; } } }")]
        [InlineData("public void M(C o) { lock (o._l) { o._b = 1; } }")]
        public void Inferred_AUseUnderTheLock_IsFine(string m) => Assert.Empty(Errors(Inferred + m));

        [Fact]
        public void Inferred_AConstructorHasTheObjectToItself() => Assert.Empty(Harness.Verify(
            "public class C { readonly object _l = new object(); int _b; public C() { _b = 1; } public void Set() { lock (_l) { _b = 2; } } }").Errors("C..ctor"));

        [Fact]
        public void Inferred_ANewObjectsInitializer_IsNotShared() => Assert.Empty(Errors(Inferred + "public int V; public static C M() { return new C { _b = 1 }; }"));

        [Fact]
        public void Inferred_TwoLocks_SayNothing() => Assert.Empty(Errors(
            "readonly object _a = new object(), _c = new object(); int _x; void A() { lock (_a) { _x = 1; } } void B() { lock (_c) { _x = 2; } } void M() { _x = 3; }"));

        [Fact]
        public void Inferred_ReadOnlyUnderALock_SaysNothing() => Assert.Empty(Errors(
            "readonly object _l = new object(); int _x; int A() { lock (_l) { return _x; } } void M() { _x = 3; }"));

        [Fact]
        public void Inferred_VolatileIsLeftAlone() => Assert.Empty(Errors(
            "readonly object _l = new object(); volatile int _x; void A() { lock (_l) { _x = 1; } } int M() { return _x; }"));

        [Fact]
        public void Inferred_AChangingLockObject_SaysNothing() => Assert.Empty(Errors(
            "object _l = new object(); int _x; void A() { lock (_l) { _x = 1; } } int M() { return _x; }"));

        [Fact]
        public void Inferred_Static() => Assert.Contains(Race, Errors(
            "static readonly object L = new object(); static int s; static void A() { lock (L) { s = 1; } } static void M() { s = 2; }"));

        // (only [GuardedBy] is used in proofs: entering the lock forgets nothing of an unmarked field, so concurrent code must say so)
        [Fact]
        public void Inferred_IsNotAGuard() => Assert.Empty(Errors(Inferred + "public void M() { lock (_l) { _b = 1; } lock (_l) { Spec.Assert(_b == 1); } }"));

        [Fact]
        public void Inferred_IsNotAGuardForConcurrentCode() => Assert.Contains("CSV1027", Errors(Inferred + "[RunsConcurrently] public void M() { lock (_l) { _b = 1; } }"));

        // ---- [GuardedBy]

        [Theory]
        [InlineData("void M() { _b = 1; }")]
        [InlineData("void M() { Helper(); }")]
        [InlineData("void M() { Spec.Assert(_b >= 0 || _b < 0); }")]
        [InlineData("void M() { System.Threading.Interlocked.Increment(ref _b); }")]
        [InlineData("static void M(C a, C b) { lock (a._l) { b._b = 1; } }")]
        [InlineData("static void M(C a, C b) { lock (a._l) { a = b; a._b = 1; } }")]
        [InlineData("void M() { lock (_l) { Action g = () => { Helper(); }; g(); } }")]
        [InlineData("void M() { lock (_l) { void L() { _b = 1; } L(); } }")]
        public void GuardedBy_WithoutTheLock_IsReported(string m) => Assert.Contains(Race, Errors(Guarded + m));

        [Theory]
        [InlineData("void M() { lock (_l) { _b = 1; } }")]
        [InlineData("void M() { lock (_l) { Helper(); } }")]
        [InlineData("[GuardedBy(nameof(_l))] void M() { _b = 1; Helper(); }")]
        [InlineData("static void M(C a) { lock (a._l) { a._b = 1; } }")]
        public void GuardedBy_WithTheLock_IsFine(string m) => Assert.Empty(Errors(Guarded + m));

        [Fact]
        public void GuardedBy_ALockThatIsNotReadonly_IsReported() => Assert.Contains(Race, Errors(
            "object _l = new object(); [GuardedBy(nameof(_l))] int _b; void M() { lock (_l) { _b = 1; } }"));

        [Theory]
        [InlineData("ref int M() { lock (_l) { return ref _b; } }")]
        [InlineData("void M() { lock (_l) { ref int r = ref _b; r = 1; } }")]
        public void GuardedBy_ARefOutlivesTheLock_IsReported(string m) => Assert.Contains(Race, Errors(Guarded + m));

        // (a ref to a heap field isn't supported at all, but it isn't this rule that says so)
        [Fact]
        public void GuardedBy_ARefArgumentUnderTheLock_IsNoRace() => Assert.DoesNotContain(Race, Errors(Guarded +
            "static void G(ref int v) { v = 1; } void M() { lock (_l) { G(ref _b); } }"));

        [Theory]
        [InlineData("static void M(C a, C b) { lock (a._l) { (a, b) = (b, a); a._b = 1; } }")]
        [InlineData("static void Sw(ref C x, C y) { x = y; } static void M(C a, C b) { lock (a._l) { Sw(ref a, b); a._b = 1; } }")]
        public void GuardedBy_TheReceiverChangingUnderTheLock_IsReported(string m) => Assert.Contains(Race, Errors(Guarded + m));

        [Fact]
        public void GuardedBy_APropertysBodyCounts() => Assert.Contains(Race,
            Harness.Verify("public class C { readonly object _l = new object(); [CsVerify.GuardedBy(nameof(_l))] int _b; public int P => _b; }").Errors("C.get_P"));

        // ---- what a lock gives and takes away

        [Fact]
        public void Lock_OthersMayHaveWrittenBetweenTwoEntries() => Assert.Equal(new[] { Rejected }, Errors(Guarded +
            "void M(int a) { lock (_l) { _b = a; } lock (_l) { Spec.Assert(_b == a); } }"));

        [Fact]
        public void Lock_WhileHeld_NothingChanges() => Assert.Empty(Errors(Guarded +
            "void M(int a) { lock (_l) { _b = a; Spec.Assert(_b == a); lock (_l) { Spec.Assert(_b == a); } } }"));

        [Fact]
        public void Lock_ALockOnAnotherLockKeepsNothingElseOut() => Assert.Empty(Errors(
            "[LockLevel(1)] readonly object _l = new object(); [LockLevel(2)] readonly object _o = new object(); [GuardedBy(nameof(_l))] int _b; void M(int a) { lock (_l) { _b = a; lock (_o) { } Spec.Assert(_b == a); } }"));

        // ---- lock invariants

        [Theory]
        [InlineData("void M(int a) { Spec.Requires(a >= 0); lock (_l) { _b = a; } }")]
        [InlineData("int M() { Spec.Ensures<int>(r => r >= 0); lock (_l) { return _b; } }")]
        [InlineData("void M() { lock (_l) { _b = -1; _b = 1; } }")]
        [InlineData("void M() { lock (_l) { _b = 1; Other(); } }")]
        [InlineData("[GuardedBy(nameof(_l))] void F() { Spec.Ensures(_b == 1); Spec.EnsuresOnThrow<Exception>(_b >= 0); _b = 1; } void M() { lock (_l) { _b = 1; F(); } }")]
        public void Invariant_Kept_IsFine(string m) => Assert.Empty(Errors(Valid + m));

        [Theory]
        [InlineData("void M() { lock (_l) { _b = -1; } }")]
        [InlineData("void M(int a) { lock (_l) { _b = a; } }")]
        [InlineData("void M() { lock (_l) { _b = -1; Other(); _b = 1; } }")]
        [InlineData("void M(bool c) { lock (_l) { _b = -1; if (c) throw new InvalidOperationException(); _b = 1; } }")]
        [InlineData("[GuardedBy(nameof(_l))] void F() { Spec.Ensures(_b == 1); _b = 1; } void M() { lock (_l) { F(); } }")]
        public void Invariant_Broken_IsReported(string m) => Assert.Contains(Invariant, Errors(Valid + m));

        /// <summary>The call itself is what is reported, not just the release if it throws.</summary>
        [Fact]
        public void Invariant_AtACallThatMayReenter_IsReportedThere()
        {
            var r = Harness.Verify("using CsVerify; using System; public class C { " + Valid + "void M() { lock (_l) { _b = -1; Other(); _b = 1; } } }");
            Assert.Contains(r.Diagnostics, d => d.Id == Invariant && d.Message.Contains("may enter the lock again"));
        }

        [Fact]
        public void Invariant_ReadWithoutTheLock_IsReported() => Assert.Contains(Race, Errors(Valid + "void M() { Spec.Assert(Valid() || !Valid()); }"));

        [Fact]
        public void Invariant_ReadUnderTheLock_IsFine() => Assert.Empty(Errors(Valid + "void M() { lock (_l) { Spec.Assert(Valid()); } }"));

        [Fact]
        public void Invariant_BrokenInAGuardedMethod_AtACallThatMayReenter_IsReported() => Assert.Contains(Invariant, Errors(Valid +
            "[GuardedBy(nameof(_l))] void M() { _b = -1; Other(); _b = 1; }"));

        [Fact]
        public void Invariant_BrokenInAGuardedMethod_AtAnotherGuardedCall_IsFine() => Assert.Empty(Errors(Valid +
            "[GuardedBy(nameof(_l))] void F() { } [GuardedBy(nameof(_l))] void M() { _b = -1; F(); _b = 1; }"));

        // ---- the samples, run on real threads: what was proved of them, under contention

        private static void OnThreads(int threads, System.Action<int> work)
        {
            var failures = new System.Collections.Concurrent.ConcurrentQueue<System.Exception>();
            var running = Enumerable.Range(0, threads).Select(n => new System.Threading.Thread(() =>
            {
                try { work(n); } catch (System.Exception e) { failures.Enqueue(e); }
            })).ToList();
            running.ForEach(t => t.Start());
            running.ForEach(t => t.Join());
            Assert.Empty(failures);
        }

        [Fact]
        public void SharedCounter_LosesNoUpdates()
        {
            var counter = new Samples.Good.SharedCounter();
            OnThreads(8, _ => { for (int i = 0; i < 20000; i++) counter.Increment(); });
            Assert.Equal(160000, counter.Read());
        }

        [Fact]
        public void SharedAccount_TransfersKeepTheMoney_AndNoBalanceGoesNegative()
        {
            var accounts = Enumerable.Range(0, 4).Select(_ => new Samples.Good.SharedAccount()).ToArray();
            foreach (var a in accounts) a.Deposit(1000);
            OnThreads(8, n =>
            {
                var r = new System.Random(n);
                for (int i = 0; i < 20000; i++)
                {
                    Samples.Good.SharedAccount.Transfer(accounts[r.Next(4)], accounts[r.Next(4)], r.Next(100));
                    Assert.True(accounts[r.Next(4)].Balance() >= 0);
                }
            });
            Assert.Equal(4000, accounts.Sum(a => a.Balance()));
        }

        [Fact]
        public void SharedStack_NeitherLosesNorInventsItems()
        {
            var stack = new Samples.Good.SharedStack();
            var pushed = new long[8];
            var popped = new long[8];
            OnThreads(8, n =>
            {
                var r = new System.Random(n);
                for (int i = 0; i < 50000; i++)
                    if (r.Next(2) == 0) { int v = r.Next(1000); if (stack.Push(v)) pushed[n] += v; }
                    else if (stack.Pop() is int got) popped[n] += got;
            });
            while (stack.Pop() is int left) popped[0] += left;
            Assert.Equal(pushed.Sum(), popped.Sum());
        }

        [Fact]
        public void LazyTable_IsBuiltOnce_ForEveryone()
        {
            var table = new Samples.Good.LazyTable();
            OnThreads(8, n => { for (int i = 0; i < 20000; i++) Assert.Equal(0, table.Get(i % 8)); });
        }

        [Fact]
        public void SharedStatistics_RangeIsNeverNegative()
        {
            var stats = new Samples.Good.SharedStatistics();
            OnThreads(8, n =>
            {
                var r = new System.Random(n);
                for (int i = 0; i < 20000; i++) { stats.Add(r.Next(-1000, 1000)); Assert.True(stats.Range() >= 0); }
            });
            Assert.True(stats.Range() <= 2000);
        }

        [Fact]
        public void Table_EveryMealIsCounted_AndNoOneDeadlocks()
        {
            var table = new Samples.Good.Table(5);
            var done = OnThreadsWithin(5, 60000, seat => { for (int i = 0; i < 5000; i++) table.Dine(seat); });
            Assert.True(done, "the philosophers deadlocked");
            for (int seat = 0; seat < 5; seat++) Assert.Equal(5000, table.Meals(seat));
        }

        private static bool OnThreadsWithin(int threads, int ms, System.Action<int> work)
        {
            var running = Enumerable.Range(0, threads).Select(n => new System.Threading.Thread(() => work(n)) { IsBackground = true }).ToList();
            running.ForEach(t => t.Start());
            var clock = System.Diagnostics.Stopwatch.StartNew();
            return running.All(t => t.Join(System.Math.Max(0, ms - (int)clock.ElapsedMilliseconds)));
        }

        // ---- lock order

        private const string Forks = "readonly object[] _f = { new object(), new object(), new object() }; ";

        [Theory]
        [InlineData("void M() { lock (_f[0]) { lock (_f[1]) { } } }")]
        [InlineData("void M(int i, int j) { Spec.Requires(0 <= i && i < j && j < _f.Length && _f[i] != null && _f[j] != null); lock (_f[i]) { lock (_f[j]) { } } }")]
        public void LockOrder_Increasing_IsFine(string m) => Assert.DoesNotContain("CSV1025", Errors(Forks + m));

        [Theory]
        [InlineData("void M() { lock (_f[1]) { lock (_f[0]) { } } }")]
        [InlineData("void M(int i, int j) { Spec.Requires(0 <= i && i < _f.Length && 0 <= j && j < _f.Length && i != j); lock (_f[i]) { lock (_f[j]) { } } }")]
        [InlineData("void M(int i) { Spec.Requires(0 <= i && i < _f.Length); lock (_f[i]) { lock (_f[(i + 1) % _f.Length]) { } } }")]
        [InlineData("void M(int i, int j) { Spec.Requires(0 <= i && i < j && j < _f.Length); lock (_f[i]) { i = j + 1; lock (_f[j]) { } } }")]
        [InlineData("void M(int i, int j) { Spec.Requires(0 <= j && j < i && i < _f.Length); lock (_f[i]) { i = j - 1; lock (_f[j]) { } } }")]
        public void LockOrder_NotKnownToIncrease_IsReported(string m) => Assert.Contains("CSV1025", Errors(Forks + m));

        // ---- what makes it true to begin with

        private static string[] AllErrors(string source) => Harness.Verify("using CsVerify; using System; " + source).Diagnostics.Where(d => d.IsError).Select(d => d.Id).ToArray();

        private const string Field = "readonly object _l = new object(); [GuardedBy(nameof(_l))] int _b; [LockInvariant(nameof(_l)), Pure] bool Valid() => _b >= 0; ";

        [Fact]
        public void Invariant_AConstructorBreakingIt_IsReported() => Assert.Contains(Invariant, AllErrors("public class C { " + Field + "public C() { _b = -5; } }"));

        [Fact]
        public void Invariant_AConstructorSettingIt_IsFine() => Assert.Empty(AllErrors("public class C { " + Field + "public C(int a) { Spec.Requires(a >= 0); _b = a; } }"));

        [Fact]
        public void Invariant_AnArgumentThatMightBreakIt_IsReported() => Assert.Contains(Invariant, AllErrors("public class C { " + Field + "public C(int a) { _b = a; } }"));

        [Fact]
        public void Invariant_NoConstructorToProveItOf_IsReported() => Assert.Contains(Invariant, AllErrors("public class C { " + Field + " }"));

        [Fact]
        public void Invariant_AFieldInitializerBreakingIt_IsReported() => Assert.Contains(Invariant, AllErrors(
            "public class C { readonly object _l = new object(); [GuardedBy(nameof(_l))] int _b = -5; [LockInvariant(nameof(_l)), Pure] bool Valid() => _b >= 0; public C() { } }"));

        [Fact]
        public void Invariant_ADefaultValueBreakingIt_IsReported() => Assert.Contains(Invariant, AllErrors(
            "public class C { readonly object _l = new object(); [GuardedBy(nameof(_l))] int _b; [LockInvariant(nameof(_l)), Pure] bool Valid() => _b > 0; public C() { } }"));

        [Fact]
        public void Invariant_ACheatingConstructorCannotProveFalseLater() => Assert.Contains(Invariant, AllErrors(
            "public class C { " + Field + "public C() { _b = -5; } public void M() { lock (_l) { Spec.Assert(_b >= 0); } } }"));

        [Fact]
        public void Invariant_Static() => Assert.Contains(Invariant, AllErrors(
            "public class C { static readonly object _l = new object(); [GuardedBy(nameof(_l))] static int _b; [LockInvariant(nameof(_l)), Pure] static bool Valid() => _b > 0; static C() { } }"));

        [Fact]
        public void Invariant_IsNotKnownWithoutTheLockTaken() => Assert.Contains(Rejected, Errors(Valid +
            "[GuardedBy(nameof(_l))] void M() { Spec.Assert(_b >= 0); }"));
    }
}
