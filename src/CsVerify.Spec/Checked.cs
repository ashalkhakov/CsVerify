#nullable enable
namespace CsVerify
{
    // (inside the namespace: a program's own top-level List or Task doesn't hide these)
    using System;
    using System.Collections.Generic;
    using System.Threading;
    using System.Threading.Tasks;

    /// <summary>A specification that failed at run time, in a checked build (<c>csverify erase --checked</c>).</summary>
    public sealed class SpecificationFailedException : Exception
    {
        public SpecificationFailedException(string message) : base(message) { }
    }

    /// <summary>
    /// The run-time checks of a checked build: <c>csverify erase --checked</c> (or <c>-p:CsVerifyChecked=true</c>) keeps
    /// the specifications that can run as calls of these: preconditions, postconditions, assertions and loop
    /// invariants; lock invariants where their lock is taken and given back; each change of an <c>[Atomic]</c> field
    /// as a step; the lock levels of <c>lock</c> statements. <see cref="Failed"/> says what a failure does (by
    /// default it throws), and <see cref="Waiting"/>/<see cref="Woken"/> report each wait, for a test (such as a
    /// liveness monitor under Coyote) to follow. A check that passes changes nothing ([Pure]), so checks may stand in
    /// [Pure] methods.
    /// </summary>
    public static class Checked
    {
        /// <summary>What a failed check does, given its message: throws <see cref="SpecificationFailedException"/> unless set.</summary>
        public static Action<string>? Failed;

        /// <summary>A thread is about to wait (Monitor.Wait, SemaphoreSlim.Wait and WaitAsync), on this object.</summary>
        public static Action<object>? Waiting;

        /// <summary>The wait on this object returned.</summary>
        public static Action<object>? Woken;

        private static void Fail(string message)
        {
            var failed = Failed;
            if (failed != null) failed(message);
            else throw new SpecificationFailedException(message);
        }

        private static void That(bool condition, string kind, string what)
        {
            if (!condition) Fail(kind + " failed: " + what);
        }

        // ------------------------------------------------------------------ contracts

        [Pure] public static void Requires(bool condition, string what) => That(condition, "precondition", what);
        [Pure] public static void Assert(bool condition, string what) => That(condition, "assertion", what);
        [Pure] public static void Invariant(bool condition, string what) => That(condition, "loop invariant", what);
        [Pure] public static void Ensures(bool condition, string what) => That(condition, "postcondition", what);

        /// <summary>A postcondition of what is returned: checked, then the value is returned.</summary>
        [Pure] public static R Ensures<R>(R result, Func<R, bool> condition, string what)
        {
            That(condition(result), "postcondition", what);
            return result;
        }

        /// <summary>Spec.Forall(from, to, body), run.</summary>
        [Pure] public static bool Forall(int from, int to, Func<int, bool> body)
        {
            for (int i = from; i < to; i++) if (!body(i)) return false;
            return true;
        }

        [Pure] public static void LockInvariant(bool condition, string what) => That(condition, "lock invariant", what);

        // ------------------------------------------------------------------ [Atomic] steps

        /// <summary>A write of an [Atomic] field: whether it was a step from what it overwrote.</summary>
        [Pure] public static void Step(bool step, string what) => That(step, "step", what);

        public static int CompareExchange(ref int field, int value, int comparand, Func<int, int, bool> step, string what)
        {
            int was = Interlocked.CompareExchange(ref field, value, comparand);
            if (was == comparand) That(step(was, value), "step", what);
            return was;
        }

        public static long CompareExchange(ref long field, long value, long comparand, Func<long, long, bool> step, string what)
        {
            long was = Interlocked.CompareExchange(ref field, value, comparand);
            if (was == comparand) That(step(was, value), "step", what);
            return was;
        }

        public static T CompareExchange<T>(ref T field, T value, T comparand, Func<T, T, bool> step, string what) where T : class?
        {
            T was = Interlocked.CompareExchange(ref field, value, comparand);
            if (ReferenceEquals(was, comparand)) That(step(was, value), "step", what);
            return was;
        }

        public static int Exchange(ref int field, int value, Func<int, int, bool> step, string what)
        {
            int was = Interlocked.Exchange(ref field, value);
            That(step(was, value), "step", what);
            return was;
        }

        public static long Exchange(ref long field, long value, Func<long, long, bool> step, string what)
        {
            long was = Interlocked.Exchange(ref field, value);
            That(step(was, value), "step", what);
            return was;
        }

        public static T Exchange<T>(ref T field, T value, Func<T, T, bool> step, string what) where T : class?
        {
            T was = Interlocked.Exchange(ref field, value);
            That(step(was, value), "step", what);
            return was;
        }

        public static int Increment(ref int field, Func<int, int, bool> step, string what) => Add(ref field, 1, step, what);
        public static long Increment(ref long field, Func<long, long, bool> step, string what) => Add(ref field, 1, step, what);
        public static int Decrement(ref int field, Func<int, int, bool> step, string what) => Add(ref field, -1, step, what);
        public static long Decrement(ref long field, Func<long, long, bool> step, string what) => Add(ref field, -1, step, what);

        public static int Add(ref int field, int value, Func<int, int, bool> step, string what)
        {
            int now = Interlocked.Add(ref field, value);
            That(step(unchecked(now - value), now), "step", what);
            return now;
        }

        public static long Add(ref long field, long value, Func<long, long, bool> step, string what)
        {
            long now = Interlocked.Add(ref field, value);
            That(step(unchecked(now - value), now), "step", what);
            return now;
        }

        // ------------------------------------------------------------------ lock levels

        [ThreadStatic] private static List<(int level, long order, string name)>? _held;

        /// <summary>
        /// Before taking a lock of this level (and order, for locks of one field ordered by an id or an index): every
        /// lock the thread holds must be lower, or of the same level and a lower order.
        /// </summary>
        public static void Taking(int level, long order, bool ordered, string what)
        {
            var held = _held;
            if (held == null) return;
            foreach (var (l, o, name) in held)
                if (!(l < level || ordered && l == level && o < order))
                    Fail($"lock level failed: {what} (level {level}{(ordered ? ", order " + order : "")}) taken while holding {name} (level {l}{(ordered ? ", order " + o : "")})");
        }

        public static void Took(int level, long order, string what) => (_held ??= new List<(int, long, string)>()).Add((level, order, what));

        public static void Released(int level, long order)
        {
            var held = _held;
            if (held == null) return;
            for (int i = held.Count - 1; i >= 0; i--)
                if (held[i].level == level && held[i].order == order) { held.RemoveAt(i); return; }
        }

        // ------------------------------------------------------------------ waits

        public static bool MonitorWait(object o)
        {
            Waiting?.Invoke(o);
            try { return Monitor.Wait(o); }
            finally { Woken?.Invoke(o); }
        }

        public static bool MonitorWait(object o, int millisecondsTimeout)
        {
            Waiting?.Invoke(o);
            try { return Monitor.Wait(o, millisecondsTimeout); }
            finally { Woken?.Invoke(o); }
        }

        public static void SemaphoreWait(SemaphoreSlim s)
        {
            Waiting?.Invoke(s);
            try { s.Wait(); }
            finally { Woken?.Invoke(s); }
        }

        public static void SemaphoreWait(SemaphoreSlim s, CancellationToken token)
        {
            Waiting?.Invoke(s);
            try { s.Wait(token); }
            finally { Woken?.Invoke(s); }
        }

        public static async Task SemaphoreWaitAsync(SemaphoreSlim s)
        {
            Waiting?.Invoke(s);
            try { await s.WaitAsync().ConfigureAwait(false); }
            finally { Woken?.Invoke(s); }
        }

        public static async Task SemaphoreWaitAsync(SemaphoreSlim s, CancellationToken token)
        {
            Waiting?.Invoke(s);
            try { await s.WaitAsync(token).ConfigureAwait(false); }
            finally { Woken?.Invoke(s); }
        }
    }
}
