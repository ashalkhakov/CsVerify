// What CsVerify proves of the concurrent code in samples/Good, checked at run time over many schedules: a schedule
// that breaks one of these would mean the verifier's model of threads, locks or atomic fields is unsound.
using System;
using System.Linq;
using System.Reflection;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Coyote.Specifications;
using Xunit;
using static CsVerify.CoyoteTests.Coyote;

namespace CsVerify.CoyoteTests
{
    public class GoodSampleTests
    {
        private static void Check(bool ok, string what, params object[] args) => Specification.Assert(ok, what, args);

        // ---- Locks.cs: guarded fields and lock invariants ----

        [Fact]
        public void Counter_CountsEveryIncrement() => Holds(async () =>
        {
            var c = new Samples.Good.SharedCounter();
            await All(Task.Run(c.Increment), Task.Run(c.Increment), Task.Run(() => Check(c.Read() >= 0, "Read < 0")));
            Check(c.Read() == 2, "count {0}", c.Read());
        });

        [Fact]
        public void Accounts_KeepTheMoney() => Holds(async () =>
        {
            var a = new Samples.Good.SharedAccount();
            var b = new Samples.Good.SharedAccount();
            a.Deposit(100);
            b.Deposit(100);
            await All(Task.Run(() => Samples.Good.SharedAccount.Transfer(a, b, 70)),
                      Task.Run(() => Samples.Good.SharedAccount.Transfer(b, a, 50)),
                      Task.Run(() => Samples.Good.SharedAccount.Transfer(a, b, 60)),
                      Task.Run(() => { int x = a.Balance(); Check(0 <= x && x <= 1000000000, "balance {0}", x); }));
            Check(a.Balance() + b.Balance() == 200, "money made or lost: {0}", a.Balance() + b.Balance());
        });

        [Fact]
        public void Stack_GivesBackWhatWasPushed() => Holds(async () =>
        {
            var s = new Samples.Good.SharedStack();
            int? x = null, y = null;
            await All(Task.Run(() => s.Push(1)), Task.Run(() => s.Push(2)), Task.Run(() => x = s.Pop()), Task.Run(() => y = s.Pop()));
            var got = new[] { x, y, s.Pop(), s.Pop() }.Where(v => v != null).Select(v => v!.Value).OrderBy(v => v).ToArray();
            Check(got.SequenceEqual(new[] { 1, 2 }), "pushed 1 and 2, popped {0}", string.Join(",", got));
        });

        [Fact]
        public void LazyTable_IsBuiltWhole() => Holds(async () =>
        {
            var t = new Samples.Good.LazyTable();
            await All(Task.Run(() => t.Get(1)), Task.Run(() => t.Get(7)));
            Check(Get<int[]>(t, "_table").Length == 8, "table");
        });

        [Fact]
        public void Statistics_RangeIsNeverNegative() => Holds(async () =>
        {
            var s = new Samples.Good.SharedStatistics();
            long seen = 0;
            await All(Task.Run(() => s.Add(5)), Task.Run(() => s.Add(-3)), Task.Run(() => seen = s.Range()));
            Check(seen >= 0, "range {0}", seen);
            Check(s.Range() == 8, "range {0}", s.Range());
        });

        // ---- AtomicFields.cs: lock-free steps ----

        [Fact]
        public void Atomic_HitsOnlyGrow() => Holds(async () =>
        {
            var s = new Samples.Good.Atomic.Stats();
            await All(Task.Run(s.Hit), Task.Run(s.Hit), Task.Run(() => { int a = s.Hits(); int b = s.Hits(); Check(a <= b, "hits went down"); }));
            Check(s.Hits() == 2, "hits {0}", s.Hits());
        });

        [Fact]
        public void Atomic_PeakIsAtLeastWhatWasObserved() => Holds(async () =>
        {
            var s = new Samples.Good.Atomic.Stats();
            await All(Task.Run(() => { s.Observe(7); Check(Get<int>(s, "_peak") >= 7, "peak below 7"); }),
                      Task.Run(() => { s.Observe(3); Check(Get<int>(s, "_peak") >= 3, "peak below 3"); }),
                      Task.Run(() => s.Observe(5)));
            Check(Get<int>(s, "_peak") == 7, "peak {0}", Get<int>(s, "_peak"));
        });

        [Fact]
        public void Atomic_ConfigurationIsPublishedOnce() => Holds(async () =>
        {
            var s = new Samples.Good.Atomic.Stats();
            Samples.Good.Atomic.Config? a = null, b = null;
            await All(Task.Run(() => a = s.Configuration(4)), Task.Run(() => b = s.Configuration(8)));
            Check(a != null && a == b && a == s.Configuration(1), "two configurations");
        });

        [Fact]
        public void Atomic_ClosedStaysClosed() => Holds(async () =>
        {
            var s = new Samples.Good.Atomic.Stats();
            bool seenClosed = false, laterOpen = false;
            await All(Task.Run(s.Close), Task.Run(() => { if (!s.Open()) { seenClosed = true; laterOpen = s.Open(); } }));
            Check(!(seenClosed && laterOpen), "opened again");
            Check(!s.Open(), "open after Close");
        });

        [Fact]
        public void Atomic_Use() => Holds(async () =>
        {
            // (Use's own Spec.Asserts are compiled away: it runs here for deadlocks and exceptions, and its end state is checked)
            var s = new Samples.Good.Atomic.Stats();
            await Samples.Good.Atomic.Stats.Use(s);
            Check(s.Hits() == 2 && Get<int>(s, "_peak") == 10 && !s.Open(), "state after Use");
        });

        // ---- InterlockedTryLock.cs: a flag as a try-lock ----

        [Fact]
        public void TryLock_CountsOnlyWhereTheFlagWasTaken() => Holds(async () =>
        {
            var t = typeof(Samples.Good.Atomic.Stats).Assembly.GetType("Samples.Good.TryLock.MyInterlockedExchangeExampleClass")!;
            SetStatic(t, "usingResource", 0);
            SetStatic(t, "uses", 0);
            var use = t.GetMethod("UseResource", BindingFlags.NonPublic | BindingFlags.Static)!;
            int taken = 0;
            Task One(string name) => Task.Run(() => { if ((bool)use.Invoke(null, new object[] { name })!) Interlocked.Increment(ref taken); });
            var output = Console.Out;
            Console.SetOut(System.IO.TextWriter.Null);
            try { await All(One("a"), One("b"), One("c")); }
            finally { Console.SetOut(output); }
            Check(GetStatic<int>(t, "uses") == taken && taken >= 1, "uses {0}, taken {1}", GetStatic<int>(t, "uses"), taken);
            Check(GetStatic<int>(t, "usingResource") == 0, "flag left taken");
        });

        // ---- LockLevels.cs: no deadlock ----

        [Fact]
        public void Levels_TransfersAndSweepsDontDeadlock() => Holds(async () =>
        {
            var a = new Samples.Good.Levels.Account(1) { Balance = 100 };
            var b = new Samples.Good.Levels.Account(2) { Balance = 100 };
            var savings = new Samples.Good.Levels.Account(3);
            var ledger = new Samples.Good.Levels.Ledger();
            Samples.Good.Levels.Notify notify = (from, to, amount) => { };
            await All(Task.Run(() => Samples.Good.Levels.Bank.Transfer(a, b, 30, ledger, notify)),
                      Task.Run(() => Samples.Good.Levels.Bank.Transfer(b, a, 20, ledger, notify)),
                      Task.Run(() => Samples.Good.Levels.Bank.Sweep(a, savings, 50, ledger)),
                      Task.Run(() => Samples.Good.Levels.Bank.Sweep(b, savings, 50, ledger)));
            lock (a.Lock) lock (b.Lock) lock (savings.Lock)
                Check(a.Balance + b.Balance + savings.Balance == 200 && a.Balance >= 0 && b.Balance >= 0,
                    "money: {0} {1} {2}", a.Balance, b.Balance, savings.Balance);
        });

        [Fact]
        public void Levels_AuditLogWritesEach() => Holds(async () =>
        {
            var log = new Samples.Good.Levels.AuditLog();
            await All(log.WriteAsync(default), log.WriteAsync(default), log.WriteAsync(default));
            Check(Get<int>(log, "_written") == 3, "written {0}", Get<int>(log, "_written"));
        });

        // ---- DiningPhilosophers.cs: forks in order ----

        [Fact]
        public void Table_EveryoneEats() => Holds(async () =>
        {
            var t = new Samples.Good.Table(3);
            await All(Task.Run(() => t.Dine(0)), Task.Run(() => t.Dine(1)), Task.Run(() => t.Dine(2)));
            Check(t.Meals(0) == 1 && t.Meals(1) == 1 && t.Meals(2) == 1, "meals");
        });

        // ---- ParallelWork.cs: disjoint parts, a lock held across an await ----

        [Fact]
        public void Parts_CopyWithRunAndThreads() => Holds(async () =>
        {
            int[] from = { 1, 2, 3, 4, 5 };
            int[] a = new int[5], b = new int[5];
            await ParallelWorkSample.Parts.CopyWithRun(from, a);
            ParallelWorkSample.Parts.CopyWithThreads(from, b);
            Check(a.SequenceEqual(from) && b.SequenceEqual(from), "copy");
        });

        [Fact]
        public void Parts_CopyWithTasks() => Holds(async () =>
        {
            int[] from = { 1, 2, 3, 4, 5 };
            int[] a = new int[5];
            await ParallelWorkSample.Parts.CopyWithTasks(from, a);
            Check(a.SequenceEqual(from), "copy");
        }, uncontrolled: true); // (it awaits Task.WhenAll, which Coyote 1.7.11 doesn't control on .NET 10)

        [Fact]
        public void Balance_OneOfTwoWithdrawalsGoesThrough() => Holds(async () =>
        {
            var balance = new ParallelWorkSample.Balance();
            Set(balance, "_cents", 100L);
            bool x = false, y = false;
            await All(Task.Run(async () => x = await balance.TryWithdraw(60, default)),
                      Task.Run(async () => y = await balance.TryWithdraw(60, default)));
            Check(x ^ y, "withdrawals that went through: {0} {1}", x, y);
            Check(Get<long>(balance, "_cents") == 40, "cents {0}", Get<long>(balance, "_cents"));
        });

        // ---- AsyncService.cs: a semaphore held across a load ----

        private sealed class Store : AsyncServiceSample.IOrderStore
        {
            public int Finds;
            public async Task<AsyncServiceSample.Order?> FindAsync(int id, CancellationToken ct)
            {
                Interlocked.Increment(ref Finds);
                await Task.Yield();
                return new AsyncServiceSample.Order(id, "c", 1);
            }
            public async Task SaveAsync(AsyncServiceSample.Order order, CancellationToken ct) => await Task.Yield();
        }

        [Fact]
        public void Cache_LoadsAnIdOnce() => Holds(async () =>
        {
            var store = new Store();
            var cache = new AsyncServiceSample.OrderCache(store);
            await All(cache.GetAsync(1, default), cache.GetAsync(1, default), cache.GetAsync(1, default),
                      cache.PutAsync(new AsyncServiceSample.Order(2, "d", 5), default));
            Check(store.Finds == 1, "id 1 loaded {0} times", store.Finds);
            Check(await cache.HitsAsync() == 2, "hits {0}", await cache.HitsAsync());
        });

        [Fact]
        public void Throttle_RunsAtMostItsSlots() => Holds(async () =>
        {
            using var throttle = new AsyncServiceSample.Throttle(2);
            int now = 0, most = 0;
            async Task<int> Work(CancellationToken ct)
            {
                int n = Interlocked.Increment(ref now);
                lock (throttle) most = Math.Max(most, n);
                await Task.Yield();
                Interlocked.Decrement(ref now);
                return n;
            }
            await All(throttle.RunAsync(Work, default), throttle.RunAsync(Work, default),
                      throttle.RunAsync(Work, default), throttle.RunAsync(Work, default));
            Check(most <= 2, "{0} at once", most);
        });
    }
}
