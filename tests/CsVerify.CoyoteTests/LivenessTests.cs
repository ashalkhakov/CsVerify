// Every wait ends: what CsVerify doesn't prove (it proves no cycle of threads waiting on each other's locks, not that a
// waiter is woken), checked under Coyote by the liveness monitor the checked build's waits feed (Coyote.EveryWaitEnds).
using System.Threading.Tasks;
using CsVerify.CoyoteTests.Waits;
using Xunit;
using static CsVerify.CoyoteTests.Coyote;

namespace CsVerify.CoyoteTests
{
    public class LivenessTests
    {
        [Fact]
        public void Mailbox_EveryWaitEnds() => Holds(async () =>
        {
            var box = new Mailbox();
            int a = 0, b = 0;
            await All(Task.Run(() => box.Put(1)), Task.Run(() => box.Put(2)), Task.Run(() => a = box.Take()), Task.Run(() => b = box.Take()));
            Microsoft.Coyote.Specifications.Specification.Assert(a + b == 3, "took {0} and {1}", a, b);
        });

        /// <summary>
        /// The waiter isn't awaited (it would be a deadlock, which Coyote finds alone): the test ends while it waits,
        /// and only the monitor sees a wait that never ended.
        /// </summary>
        [Fact]
        public void Latch_LostWakeup_IsFound() => Finds(async () =>
        {
            var latch = new Latch();
            _ = Task.Run(latch.Await);
            await Task.Run(latch.Open);
        }, "detected liveness bug");

        /// <summary>Without the monitor, the same schedules end with the waiter still waiting, and nothing is reported.</summary>
        [Fact]
        public void Latch_LostWakeup_WithoutTheMonitor_IsMissed() => Assert.Null(Bug(async () =>
        {
            var latch = new Latch();
            _ = Task.Run(latch.Await);
            await Task.Run(latch.Open);
        }, monitor: false));

        [Fact]
        public void AuditLog_EveryWaitOnTheSemaphoreEnds() => Holds(async () =>
        {
            var log = new Samples.Good.Levels.AuditLog();
            await All(log.WriteAsync(default), log.WriteAsync(default), log.WriteAsync(default));
        });
    }
}
