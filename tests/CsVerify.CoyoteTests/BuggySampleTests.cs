// The planted bugs of samples/Buggy that a test can make happen, each found by Coyote: so these harnesses can see a
// broken schedule, and GoodSampleTests passing means something. (The others, which CsVerify reports but no schedule of
// these programs shows, are listed in docs/coyote.md.)
using System;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Coyote.Specifications;
using Monitor = System.Threading.Monitor;
using Xunit;
using static CsVerify.CoyoteTests.Coyote;

namespace CsVerify.CoyoteTests
{
    public class BuggySampleTests
    {
        private const string Deadlock = "Deadlock detected";
        private static void Check(bool ok, string what, params object[] args) => Specification.Assert(ok, what, args);

        // ---- AtomicBugs.cs ----

        [Fact]
        public void Atomic_LostUpdate() => Finds(async () =>
        {
            var c = new Samples.Buggy.Atomic.Counter();
            await All(Task.Run(c.LostUpdate), Task.Run(c.LostUpdate));
            Check(Get<int>(c, "_hits") == 2, "an increment was lost");
        }, "an increment was lost");

        [Fact]
        public void Atomic_Wraps() => Finds(async () =>
        {
            var c = new Samples.Buggy.Atomic.Counter();
            Set(c, "_hits", int.MaxValue);
            await Task.Run(c.Wraps);
            Check(Get<int>(c, "_hits") >= int.MaxValue, "the count went down");
        }, "step failed: Interlocked.Increment(ref _hits)");

        [Fact]
        public void Atomic_TwoReads() => Finds(async () =>
        {
            // (the method's own Spec.Assert, kept by the checked build)
            var c = new Samples.Buggy.Atomic.Counter();
            await All(Task.Run(c.TwoReads), Task.Run(c.Wraps));
        }, "assertion failed: a == b");

        // ---- TryLockBugs.cs ----

        [Fact]
        public void TryLock_Denied() => Finds(async () =>
        {
            var r = new Samples.Buggy.TryLock.Resource();
            int taken = 0;
            await All(Task.Run(() => { if (r.Denied()) Interlocked.Increment(ref taken); }),
                      Task.Run(() => { if (r.Denied()) Interlocked.Increment(ref taken); }));
            Check(Get<int>(r, "_uses") == taken, "uses don't match the flag");
        }, "uses don't match the flag");

        [Fact]
        public void TryLock_BrokenInvariant() => Finds(async () =>
        {
            var r = new Samples.Buggy.TryLock.Resource();
            await Task.Run(r.BrokenInvariant);
            Check(Get<int>(r, "_uses") >= 0, "the invariant is broken with the flag free");
        }, "the invariant is broken");

        // ---- LockLevelBugs.cs ----

        [Fact]
        public void Levels_Transfer() => Finds(async () =>
        {
            var a = new Samples.Buggy.Levels.Account(1);
            var b = new Samples.Buggy.Levels.Account(2);
            await All(Task.Run(() => Samples.Buggy.Levels.LevelBugs.Transfer(a, b)), Task.Run(() => Samples.Buggy.Levels.LevelBugs.Transfer(b, a)));
        }, "lock level failed: to.Lock"); // (before the schedules that deadlock: the transfer that locks the higher id first)

        [Fact]
        public void Levels_LowUnderHigh() => Finds(async () =>
        {
            // (no other code takes them the other way round, so it can't deadlock here: the lock level is what's broken)
            var l = new Samples.Buggy.Levels.LevelBugs();
            await Task.Run(l.LowUnderHigh);
        }, "lock level failed: _low");

        [Fact]
        public void Levels_Callback() => Finds(async () =>
        {
            // the callback waits for a task that needs the lock its caller holds
            var l = new Samples.Buggy.Levels.LevelBugs();
            await Task.Run(() => l.Callback(() => Task.Run(() => l.Callback(() => { })).Wait()));
        }, Deadlock);

        [Fact]
        public void Levels_WaitUnder() => Finds(async () =>
        {
            var l = new Samples.Buggy.Levels.LevelBugs();
            var low = Get<object>(l, "_low");
            var go = new TaskCompletionSource();
            var needsLow = Task.Run(async () => { await go.Task; lock (low) { } });
            go.SetResult();
            await Task.Run(() => l.WaitUnder(needsLow));
        }, Deadlock);

        [Fact]
        public void Levels_WaitHolding() => Finds(async () =>
        {
            var l = new Samples.Buggy.Levels.LevelBugs();
            var low = Get<object>(l, "_low");
            var high = Get<object>(l, "_high");
            await All(Task.Run(l.WaitHolding), Task.Run(() => { lock (low) lock (high) Monitor.PulseAll(high); }));
        }, Deadlock);

        // ---- LockBugs.cs ----

        [Fact]
        public void Locks_Undo() => Finds(async () =>
        {
            var t = new Samples.Buggy.Locks.Tally();
            await Task.Run(t.Undo);
            lock (Get<object>(t, "_lock")) Check(Get<int>(t, "_count") >= 0, "the invariant is broken with the lock free");
        }, "lock invariant failed"); // (when Undo gives the lock back)

        [Fact]
        public void Gate_Twice() => Finds(() => new Samples.Buggy.Locks.Gate().Twice(), Deadlock);

        [Fact]
        public void Gate_GetOrCompute() => Finds(async () =>
        {
            var g = new Samples.Buggy.Locks.Gate();
            await g.GetOrCompute(() => g.GetOrCompute(() => Task.FromResult("x")));
        }, Deadlock);
    }
}
