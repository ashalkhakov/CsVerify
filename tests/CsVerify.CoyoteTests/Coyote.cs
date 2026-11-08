using System;
using System.Linq;
using System.Reflection;
using System.Threading.Tasks;
using Microsoft.Coyote;
using Microsoft.Coyote.SystematicTesting;
using Xunit;

// (Coyote's testing engine is one per test, and they aren't run side by side)
[assembly: CollectionBehavior(DisableTestParallelization = true)]

namespace CsVerify.CoyoteTests
{
    /// <summary>Runs a test under Coyote's scheduler, over many schedules, with interleaving at every memory access.</summary>
    internal static class Coyote
    {
        /// <summary>Schedules per test: CSVERIFY_COYOTE_ITERATIONS, or 1000.</summary>
        private static uint Iterations =>
            uint.TryParse(Environment.GetEnvironmentVariable("CSVERIFY_COYOTE_ITERATIONS"), out var n) && n > 0 ? n : 1000;

        /// <summary>The first bug found, or null when every schedule passed.</summary>
        public static string? Bug(Func<Task> test, bool uncontrolled = false)
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
            using var engine = TestingEngine.Create(config, test);
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
}
