using System.Linq;
using Xunit;

namespace CsVerify.Tests
{
    /// <summary>Tasks and threads get what their contract names when they start, and give it back when they are awaited or joined: so work split between them is proved to stay apart.</summary>
    public class TaskPermissionTests
    {
        private const string Program = "using CsVerify; using System; using System.Threading; using System.Threading.Tasks; " +
            "public static class C { " +
            "static async Task Fill(int[] a, int from, int to, int v) { " +
            "Spec.Requires(0 <= from && from <= to && to <= a.Length && Spec.Acc(a, from, to)); " +
            "Spec.Ensures(Spec.Acc(a, from, to) && Spec.Forall(from, to, i => a[i] == v)); " +
            "await Task.Yield(); for (int k = from; k < to; k++) { Spec.Invariant(from <= k && k <= to && Spec.Acc(a, from, to) && Spec.Forall(from, k, i => a[i] == v)); a[k] = v; } } " +
            "static void FillNow(int[] a, int from, int to, int v) { " +
            "Spec.Requires(0 <= from && from <= to && to <= a.Length && Spec.Acc(a, from, to)); " +
            "Spec.Ensures(Spec.Acc(a, from, to) && Spec.Forall(from, to, i => a[i] == v)); " +
            "for (int k = from; k < to; k++) { Spec.Invariant(from <= k && k <= to && Spec.Acc(a, from, to) && Spec.Forall(from, k, i => a[i] == v)); a[k] = v; } } " +
            "static async Task<int> First(int[] a) { Spec.Requires(a.Length > 0 && Spec.AccRead(a, 0, 1)); Spec.Ensures((int r) => Spec.AccRead(a, 0, 1) && r == a[0]); await Task.Yield(); return a[0]; } ";

        private static string[] Errors(string m) => Harness.Verify(Program + m + " }").Diagnostics.Where(d => d.IsError).Select(d => d.Id + " " + d.Message).ToArray();
        private static string[] Ids(string m) => Harness.Verify(Program + m + " }").Diagnostics.Where(d => d.IsError).Select(d => d.Id).ToArray();

        private const string Whole = "Spec.Requires(a.Length >= 2 && Spec.Acc(a)); Spec.Ensures(Spec.Acc(a)); int mid = a.Length / 2; ";

        [Theory]
        // two tasks on two parts
        [InlineData("static async Task M(int[] a) { " + Whole + "var l = Fill(a, 0, mid, 1); var r = Fill(a, mid, a.Length, 2); await l; await r; Spec.Assert(a[0] == 1 && a[mid] == 2); }")]
        [InlineData("static async Task M(int[] a) { " + Whole + "await Task.WhenAll(Fill(a, 0, mid, 1), Fill(a, mid, a.Length, 2)); Spec.Assert(a[0] == 1 && a[mid] == 2); }")]
        [InlineData("static async Task M(int[] a) { " + Whole + "var l = Fill(a, 0, mid, 1); var r = Fill(a, mid, a.Length, 2); await Task.WhenAll(l, r); Spec.Assert(a[0] == 1 && a[mid] == 2); }")]
        // by Task.Run
        [InlineData("static async Task M(int[] a) { " + Whole + "var l = Task.Run(() => FillNow(a, 0, mid, 1)); var r = Task.Run(() => FillNow(a, mid, a.Length, 2)); await l; await r; Spec.Assert(a[0] == 1 && a[mid] == 2); }")]
        [InlineData("static async Task M(int[] a) { " + Whole + "await Task.WhenAll(Task.Run(() => FillNow(a, 0, mid, 1)), Task.Run(() => FillNow(a, mid, a.Length, 2))); Spec.Assert(a[0] == 1 && a[mid] == 2); }")]
        [InlineData("static async Task M(int[] a) { " + Whole + "await Task.Run(() => FillNow(a, 0, mid, 1)); Spec.Assert(a[0] == 1); }")]
        [InlineData("static async Task M(int[] a) { " + Whole + "var l = Task.Run(() => Fill(a, 0, mid, 1)); await l; Spec.Assert(a[0] == 1); }")]
        // by threads
        [InlineData("static void M(int[] a) { " + Whole + "var l = new Thread(() => FillNow(a, 0, mid, 1)); var r = new Thread(() => FillNow(a, mid, a.Length, 2)); l.Start(); r.Start(); l.Join(); r.Join(); Spec.Assert(a[0] == 1 && a[mid] == 2); }")]
        // what it keeps is its own all along
        [InlineData("static async Task M(int[] a) { " + Whole + "a[0] = 7; var r = Fill(a, mid, a.Length, 2); a[0] = 8; await Task.Yield(); Spec.Assert(a[0] == 8); await r; Spec.Assert(a[0] == 8 && a[mid] == 2); }")]
        // shares to read: any number at once, and nothing changes
        [InlineData("static async Task M(int[] a) { Spec.Requires(a.Length > 0 && Spec.Acc(a)); Spec.Ensures(Spec.Acc(a)); a[0] = 5; var x = First(a); var y = First(a); int p = await x; int q = await y; Spec.Assert(p == 5 && q == 5 && a[0] == 5); }")]
        [InlineData("static async Task M(int[] a) { Spec.Requires(a.Length > 0 && Spec.Acc(a)); Spec.Ensures(Spec.Acc(a)); a[0] = 5; int p = await First(a); a[0] = 6; Spec.Assert(p == 5 && a[0] == 6); }")]
        public void Proved(string m) => Assert.Empty(Errors(m));

        [Theory]
        // two tasks on one cell
        [InlineData("CSV1016", "static async Task M(int[] a) { " + Whole + "var l = Fill(a, 0, mid + 1, 1); var r = Fill(a, mid, a.Length, 2); await l; await r; }")]
        [InlineData("CSV1016", "static async Task M(int[] a) { " + Whole + "await Task.WhenAll(Fill(a, 0, a.Length, 1), Fill(a, 0, a.Length, 2)); }")]
        [InlineData("CSV1016", "static async Task M(int[] a) { " + Whole + "await Task.WhenAll(Task.Run(() => FillNow(a, 0, a.Length, 1)), Task.Run(() => FillNow(a, 0, a.Length, 2))); }")]
        [InlineData("CSV1016", "static void M(int[] a) { " + Whole + "var l = new Thread(() => FillNow(a, 0, a.Length, 1)); var r = new Thread(() => FillNow(a, 0, 1, 2)); l.Start(); r.Start(); l.Join(); r.Join(); }")]
        // writing or reading what it has given away, until it's back
        [InlineData("CSV1016", "static async Task M(int[] a) { " + Whole + "var l = Fill(a, 0, mid, 1); a[0] = 3; await l; }")]
        [InlineData("CSV1016", "static async Task M(int[] a) { " + Whole + "var l = Fill(a, 0, mid, 1); var x = a[0]; await l; }")]
        [InlineData("CSV1016", "static async Task M(int[] a) { " + Whole + "var l = Task.Run(() => FillNow(a, 0, mid, 1)); a[0] = 3; await l; }")]
        [InlineData("CSV1016", "static void M(int[] a) { " + Whole + "var l = new Thread(() => FillNow(a, 0, mid, 1)); l.Start(); a[0] = 3; l.Join(); }")]
        // a share leaves the rest no way to write
        [InlineData("CSV1016", "static async Task M(int[] a) { Spec.Requires(a.Length > 0 && Spec.Acc(a)); Spec.Ensures(Spec.Acc(a)); var x = First(a); a[0] = 1; await x; }")]
        [InlineData("CSV1016", "static async Task M(int[] a) { Spec.Requires(a.Length > 0 && Spec.Acc(a)); Spec.Ensures(Spec.Acc(a)); var x = First(a); await Task.WhenAll(x, Fill(a, 0, a.Length, 1)); }")]
        // a share to read can't be used to write
        [InlineData("CSV1016", "static void M(int[] a) { Spec.Requires(a.Length > 0 && Spec.AccRead(a)); Spec.Ensures(Spec.AccRead(a)); a[0] = 1; }")]
        // not back unless the contract gives it back
        [InlineData("CSV1016", "static async Task Keep(int[] a) { Spec.Requires(Spec.Acc(a)); await Task.Yield(); } static async Task M(int[] a) { Spec.Requires(a.Length > 0 && Spec.Acc(a)); Spec.Ensures(Spec.Acc(a)); await Keep(a); }")]
        // a thread not joined, a task not awaited: never back
        [InlineData("CSV1016", "static void M(int[] a) { " + Whole + "var l = new Thread(() => FillNow(a, 0, mid, 1)); l.Start(); }")]
        [InlineData("CSV1016", "static void M(int[] a) { " + Whole + "_ = Task.Run(() => FillNow(a, 0, mid, 1)); }")]
        // the precondition is proved where it starts
        [InlineData("CSV1001", "static async Task M(int[] a) { Spec.Requires(Spec.Acc(a)); await Fill(a, 0, a.Length + 1, 1); }")]
        [InlineData("CSV1001", "static async Task M(int[] a) { Spec.Requires(Spec.Acc(a)); var t = Task.Run(() => FillNow(a, 0, a.Length + 1, 1)); await t; }")]
        // code that runs alongside reads only what it holds
        [InlineData("CSV1016", "static async Task<int> Peek(int[] a) { Spec.Requires(a.Length > 1 && Spec.Acc(a, 0, 1)); Spec.Ensures(Spec.Acc(a, 0, 1)); await Task.Yield(); return a[1]; } static async Task M(int[] a) { Spec.Requires(a.Length > 1 && Spec.Acc(a)); var t = Peek(a); await t; }")]
        [InlineData("CSV1027", "static int Sum(int[] a) { int s = 0; foreach (var x in a) s = unchecked(s + x); return s; } static async Task<int> Peek(int[] a) { Spec.Requires(Spec.Acc(a, 0, 0)); Spec.Ensures(Spec.Acc(a, 0, 0)); await Task.Yield(); return Sum(a); } static async Task M(int[] a) { Spec.Requires(Spec.Acc(a)); var t = Peek(a); await t; }")]
        public void Reported(string id, string m) => Assert.Contains(id, Ids(m));

        [Theory]
        // what it says of anything else isn't kept: it may have changed since it finished
        [InlineData("static int[] _s = new int[1]; static async Task F(int[] a, int[] o) { Spec.Requires(Spec.Acc(a) && o.Length == 1); Spec.Ensures(Spec.Acc(a) && o[0] == 3); await Task.Yield(); Spec.Assume(o[0] == 3); } static async Task M(int[] a, int[] o) { Spec.Requires(Spec.Acc(a) && o.Length == 1 && Spec.Acc(o)); var t = F(a, o); await t; Spec.Assert(o[0] == 3); }")]
        // the old state of a delegate is of when it starts, not of when it was handed over
        [InlineData("public class D { public int V; } static void G(int[] a, D d, int w) { Spec.Requires(Spec.Acc(a)); Spec.Ensures(Spec.Acc(a) && w == Spec.Old(d.V)); Spec.Assume(w == d.V); } static async Task M(int[] a, D d, int w) { Spec.Requires(Spec.Acc(a) && d.V == 1); var t = Task.Run(() => G(a, d, w)); await t; Spec.Assert(w == 1); }")]
        // not back before it is finished
        [InlineData("static async Task M(int[] a) { " + Whole + "var l = Fill(a, 0, mid, 1); await Task.Yield(); Spec.Assert(a[0] == 1); await l; }")]
        // a failure gives nothing back
        [InlineData("static async Task M(int[] a) { " + Whole + "var l = Fill(a, 0, mid, 1); try { await l; } catch (InvalidOperationException) { a[0] = 2; throw; } }")]
        public void NotProved(string m) => Assert.NotEmpty(Errors(m));

        // (a delegate that can't be fixed where it's made is on its own, and knows nothing)
        [Theory]
        [InlineData("static async Task M(int[] a) { Spec.Requires(a.Length > 2 && Spec.Acc(a)); int n = 1; var t = Task.Run(() => FillNow(a, 0, n, 1)); n = 2; await t; }")]
        [InlineData("static async Task M(int[] a) { Spec.Requires(a.Length > 2 && Spec.Acc(a)); var t = Task.Run(() => { FillNow(a, 0, 1, 1); FillNow(a, 1, 2, 1); }); await t; }")]
        public void NotFixed(string m) => Assert.Contains("CSV1001", Ids(m));

        // the await after a catch that has the task again doesn't give back twice
        [Fact]
        public void AwaitedOnOnePath_NotGivenBackTwice() => Assert.Contains("CSV1004", Ids(
            "static void Boom() { if (DateTime.Now.Year > 0) throw new InvalidOperationException(); } static async Task M(int[] a) { " + Whole +
            "bool done = false; var l = Fill(a, 0, mid, 1); try { Boom(); await l; done = true; Boom(); } catch (InvalidOperationException) { await l; if (done) Spec.Assert(false); } }"));

        [Fact]
        public void AnOwnedReceiver_IsNotStarted() => Assert.Contains("CSV1901", Harness.Verify("using CsVerify; using System.Threading.Tasks; [Owned] public sealed class O { public int V; public async Task W() { await Task.Yield(); V = 2; } } " +
            "public static class C { static async Task M(O o) { Spec.Requires(Spec.Acc(o)); Spec.Ensures(Spec.Acc(o)); var t = o.W(); o.V = 1; await t; } }").Diagnostics.Select(d => d.Id));
    }
}
