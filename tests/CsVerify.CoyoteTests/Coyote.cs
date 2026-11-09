using System;
using System.Linq;
using System.Reflection;
using System.Threading.Tasks;
using Microsoft.Coyote;
using Microsoft.Coyote.Specifications;
using Microsoft.Coyote.SystematicTesting;
using Xunit;

// (Coyote's testing engine is one per test, and they aren't run side by side)
[assembly: CollectionBehavior(DisableTestParallelization = true)]

namespace CsVerify.CoyoteTests
{
    /// <summary>
    /// Runs a test under Coyote's scheduler, over many schedules, with interleaving at every memory access. The code
    /// under test is a checked build: a specification that fails is a Coyote assertion that fails, and each wait it
    /// makes is followed by <see cref="EveryWaitEnds"/>, so a waiter no one wakes is a liveness bug.
    /// </summary>
    internal static class Coyote
    {
        /// <summary>Schedules per test: CSVERIFY_COYOTE_ITERATIONS, or 1000.</summary>
        private static uint Iterations =>
            uint.TryParse(Environment.GetEnvironmentVariable("CSVERIFY_COYOTE_ITERATIONS"), out var n) && n > 0 ? n : 1000;

        /// <summary>The first bug found, or null when every schedule passed (without the liveness monitor, if not <paramref name="monitor"/>).</summary>
        public static string? Bug(Func<Task> test, bool uncontrolled = false, bool monitor = true)
        {
            var config = Configuration.Create()
                .WithTestingIterations(Iterations)
                .WithMaxSchedulingSteps(10000)
                .WithDeadlockTimeout(5000)
                .WithPartiallyControlledConcurrencyAllowed(uncontrolled)
                .WithMemoryAccessRaceCheckingEnabled(true)
                .WithVolatileOperationRaceCheckingEnabled(true)
                .WithAtomicOperationRaceCheckingEnabled(true)
                .WithControlFlowRaceCheckingEnabled(true)
                .WithLockAccessRaceCheckingEnabled(true)
                .WithCollectionAccessRaceCheckingEnabled(true)
                .WithTelemetryEnabled(false)
                .WithConsoleLoggingEnabled(false);
            Checked.Failed = message => Specification.Assert(false, message);
            Checked.Waiting = monitor ? _ => EveryWaitEnds.Count(+1) : null;
            Checked.Woken = monitor ? _ => EveryWaitEnds.Count(-1) : null;
            using var engine = TestingEngine.Create(config, async () =>
            {
                if (monitor)
                {
                    EveryWaitEnds.Reset();
                    Specification.RegisterMonitor<EveryWaitEnds>();
                }
                await test();
            });
            engine.Run();
            var report = engine.TestReport;
            return report.NumOfFoundBugs > 0 ? report.BugReports.First() : null;
        }

        /// <summary>No schedule breaks it.</summary>
        public static void Holds(Func<Task> test, bool uncontrolled = false)
        {
            var bug = Bug(test, uncontrolled);
            Assert.True(bug == null, bug);
        }

        /// <summary>Some schedule breaks it, as <paramref name="expected"/> says.</summary>
        public static void Finds(Func<Task> test, string expected)
        {
            var bug = Bug(test);
            Assert.NotNull(bug);
            Assert.Contains(expected, bug);
        }

        /// <summary>Awaits each in turn (Task.WhenAll isn't controlled by Coyote 1.7.11 on .NET 10).</summary>
        public static async Task All(params Task[] tasks) { foreach (var t in tasks) await t; }

        private const BindingFlags Any = BindingFlags.NonPublic | BindingFlags.Public | BindingFlags.Instance | BindingFlags.Static;
        public static T Get<T>(object o, string field) => (T)o.GetType().GetField(field, Any)!.GetValue(o)!;
        public static void Set(object o, string field, object value) => o.GetType().GetField(field, Any)!.SetValue(o, value);
        public static T GetStatic<T>(Type t, string field) => (T)t.GetField(field, Any)!.GetValue(null)!;
        public static void SetStatic(Type t, string field, object value) => t.GetField(field, Any)!.SetValue(null, value);
    }

    /// <summary>
    /// A liveness monitor: hot while some wait hasn't ended, so one that never ends is a bug. (Coyote runs a monitor
    /// atomically, and this assembly is rewritten, so the monitor has no code of its own: the count is kept outside.)
    /// </summary>
    internal sealed class EveryWaitEnds : Monitor
    {
        internal sealed class Some : Event { }
        internal sealed class None : Event { }

        // (made anew in each schedule: Coyote controls the lock, and one lock object shared by its runs is an error)
        private static object _gate = new object();
        private static int _waiting;

        /// <summary>A wait begins (+1) or ends (-1).</summary>
        public static void Count(int change)
        {
            lock (_gate)
            {
                _waiting += change;
                if (_waiting > 0) Specification.Monitor<EveryWaitEnds>(new Some());
                else Specification.Monitor<EveryWaitEnds>(new None());
            }
        }

        /// <summary>At the start of a schedule: no waits.</summary>
        public static void Reset()
        {
            _gate = new object();
            _waiting = 0;
        }

        [Start, Cold, OnEventGotoState(typeof(Some), typeof(SomeWaiting)), IgnoreEvents(typeof(None))]
        private sealed class NoneWaiting : State { }

        [Hot, OnEventGotoState(typeof(None), typeof(NoneWaiting)), IgnoreEvents(typeof(Some))]
        private sealed class SomeWaiting : State { }
    }
}
