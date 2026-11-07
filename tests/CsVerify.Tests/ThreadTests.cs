using System.Linq;
using Xunit;

namespace CsVerify.Tests
{
    /// <summary>Task.Run and threads: they run alongside the method that started them, which can rely on nothing they could touch until it has awaited or joined them.</summary>
    public class ThreadTests
    {
        private const string Program = "using CsVerify; using System; using System.Threading; using System.Threading.Tasks; public class Cell { public int V; } " +
            "public class G { private readonly object _l = new object(); [GuardedBy(nameof(_l))] private int _n; [RunsConcurrently] public void Inc() { lock (_l) { if (_n < 100) _n = _n + 1; } } } public static class C { ";

        private static string[] Errors(string m) => Harness.Verify(Program + m + " }").Errors("M");

        private static bool WarnedOfARace(string m) =>
            Harness.Verify(Program + m + " }").Diagnostics.Any(d => d.Id == "CSV1900" && (d.Message.Contains("could race")));

        [Theory]
        [InlineData("static async Task M(Cell c) { await Task.Run(() => { c.V = 2; }); }")]
        [InlineData("static async Task M() { var r = await Task.Run(() => 3); }")]
        [InlineData("static async Task M() { var t = Task.Run(() => 3); var r = await t; }")]
        [InlineData("static async Task M() { var r = await Task.Run(() => new Cell()); var x = r.V; }")]
        [InlineData("static async Task M() { var t = Task.Run(() => new Cell()); var r = await t; var x = r.V; }")]
        [InlineData("static async Task M(G g) { var a = Task.Run(() => g.Inc()); var b = Task.Run(() => g.Inc()); await Task.WhenAll(a, b); }")]
        [InlineData("static async Task M(G g) { await Task.WhenAll(Task.Run(() => g.Inc()), Task.Run(() => g.Inc())); }")]
        // once it has finished, what this method does is its own again
        [InlineData("static async Task M(Cell c) { var t = Task.Run(() => { c.V = 2; }); await t; c.V = 1; var x = c.V; Spec.Assert(x == 1); }")]
        [InlineData("static async Task M(Cell c) { await Task.Run(() => { c.V = 2; }); c.V = 1; var x = c.V; Spec.Assert(x == 1); }")]
        [InlineData("static void M(Cell c) { var th = new Thread(() => { c.V = 2; }); th.Start(); th.Join(); c.V = 1; var x = c.V; Spec.Assert(x == 1); }")]
        [InlineData("static void M() { var th = new Thread(() => { }); th.IsBackground = true; th.Start(); }")]
        [InlineData("static async Task M() { int k = 3; var t = Task.Run(() => { }); var a = k; await t; Spec.Assert(a == 3); }")]
        public void Proved(string m) => Assert.Empty(Errors(m));

        [Theory]
        // it may write at any moment, so what it could touch isn't known, even just after writing it
        [InlineData("CSV1004", "static async Task M(Cell c) { var t = Task.Run(() => { c.V = 2; }); c.V = 1; var x = c.V; Spec.Assert(x == 1); await t; }")]
        [InlineData("CSV1004", "static async Task M(Cell c) { c.V = 1; var t = Task.Run(() => { c.V = 2; }); Spec.Assert(c.V == 1); await t; }")]
        [InlineData("CSV1004", "static async Task M(int[] a) { Spec.Requires(a.Length > 0); var t = Task.Run(() => { if (a.Length > 0) a[0] = 2; }); a[0] = 3; var x = a[0]; Spec.Assert(x == 3); await t; }")]
        [InlineData("CSV1004", "static async Task M() { int n = 0; var t = Task.Run(() => { n = 1; }); n = 2; var x = n; Spec.Assert(x == 2); await t; }")]
        [InlineData("CSV1004", "static void M(Cell c) { var th = new Thread(() => { c.V = 2; }); th.Start(); c.V = 1; var x = c.V; Spec.Assert(x == 1); th.Join(); }")]
        // a thread that isn't joined goes on, to the end of the method
        [InlineData("CSV1004", "static void M(Cell c) { var th = new Thread(() => { c.V = 2; }); th.Start(); c.V = 1; var x = c.V; Spec.Assert(x == 1); }")]
        // so does a task kept somewhere else
        [InlineData("CSV1004", "static Task? keep; static void M(Cell c) { keep = Task.Run(() => { c.V = 2; }); c.V = 1; var x = c.V; Spec.Assert(x == 1); }")]
        [InlineData("CSV1004", "static void M(Cell c) { _ = Task.Run(() => { c.V = 2; }); c.V = 1; var x = c.V; Spec.Assert(x == 1); }")]
        // waited for some other way, it isn't known to have finished
        [InlineData("CSV1004", "static void M(Cell c) { var t = Task.Run(() => { c.V = 2; }); t.Wait(); c.V = 1; var x = c.V; Spec.Assert(x == 1); }")]
        // never awaited
        [InlineData("CSV1026", "static void M() { Task.Run(() => { }); }")]
        [InlineData("CSV1026", "static void M() { var t = Task.Run(() => { }); }")]
        [InlineData("CSV1026", "static async Task M(bool b) { var t = Task.Run(() => { }); if (b) await t; }")]
        [InlineData("CSV1026", "static int M() { var t = Task.Run(() => 3); return t.Result; }")]
        // an unguarded field: outside a lock, even in the delegate
        [InlineData("CSV1023", "private static readonly object _l = new object(); [GuardedBy(nameof(_l))] private static int _g; static async Task M() { await Task.Run(() => { _g = 1; }); }")]
        public void Reported(string id, string m) => Assert.Contains(id, Errors(m));

        // (the code in it knows nothing of who started it)
        [Fact]
        public void TheDelegate_KnowsNothingOfItsStarter() => Assert.Contains(Harness.Verify(Program +
            "static async Task M(int[] a) { Spec.Requires(a.Length > 0); var t = Task.Run(() => { a[0] = 2; }); await t; } }").Diagnostics, d => d.Id == "CSV1003");

        // right after starting it, before the next statement, it may have run
        [Fact]
        public void AtOnce() => Assert.Contains("CSV1004", Errors("static async Task M(Cell c) { var v = c.V; var t = Task.Run(() => { c.V = 2; }); if (c.V == v) { } else { Spec.Assert(false); } await t; }"));

        // a task from code it can't follow, or from a method that isn't async, may run alongside too
        [Theory]
        [InlineData("CSV1004", "static async Task M(IW w, Cell c) { var t = w.G(c); c.V = 1; var x = c.V; Spec.Assert(x == 1); await t; }")]
        [InlineData("CSV1004", "static async Task M(Func<Cell, Task> w, Cell c) { var t = w(c); c.V = 1; var x = c.V; Spec.Assert(x == 1); await t; }")]
        [InlineData("CSV1004", "[RunsConcurrently] static Task W(Cell c) { return Task.Run(() => { c.V = 2; }); } static async Task M(Cell c) { var t = W(c); c.V = 1; var x = c.V; Spec.Assert(x == 1); await t; }")]
        [InlineData("CSV1026", "static async Task M(IW w, Cell c) { w.G(c); await Task.Yield(); }")]
        [InlineData("CSV1026", "static async Task M(IW w, Cell c) { var t = w.G(c); await Task.Yield(); }")]
        [InlineData("CSV1004", "[RunsConcurrently] static async Task<int> A(int id) { await Task.Yield(); return id; } static void M(int[] ids, Cell c) { var ts = ids.Select(id => A(id)).ToArray(); c.V = 1; var x = c.V; Spec.Assert(x == 1); }")]
        public void TasksFromElsewhere(string id, string m) => Assert.Contains(id, Harness.Verify(Program.Replace("public static class C {", "public interface IW { [RunsConcurrently] Task G(Cell c); } public static class C {").Replace("using System;", "using System; using System.Linq;") + m + " }").Errors("M"));

        [Theory]
        [InlineData("static async Task M(IW w, Cell c) { await w.G(c); c.V = 1; var x = c.V; Spec.Assert(x == 1); }")]
        [InlineData("static async Task M(IW w, Cell c) { var t = w.G(c); await t; c.V = 1; var x = c.V; Spec.Assert(x == 1); }")]
        [InlineData("static Task M(IW w, Cell c) { return w.G(c); }")]
        [InlineData("static async Task M(Cell c) { c.V = 1; var t = Task.Delay(1); var x = c.V; Spec.Assert(x == 1); await t; }")]
        [InlineData("[RunsConcurrently] static async Task<int> A(int id) { await Task.Yield(); return id; } static async Task M() { await Task.WhenAll(A(1), A(2)); }")]
        [InlineData("[RunsConcurrently] static async Task<int> A(int id) { Spec.Ensures<int>(r => r == id); await Task.Yield(); return id; } static async Task M() { var r = await Task.WhenAll(A(1), A(2)); Spec.Assert(r[0] == 1 && r[1] == 2); }")]
        [InlineData("[RunsConcurrently] static async Task<int> A(int id) { await Task.Yield(); return id; } static async Task M(int[] ids) { var ts = ids.Select(id => A(id)).ToArray(); await Task.WhenAll(ts); }")]
        [InlineData("[RunsConcurrently] static async Task<int> A() { await Task.Yield(); return 1; } static async Task M() { await Task.Run(() => A()); }")]
        // (a lambda inside a using or a try, that may throw: that's its own, not theirs)
        [InlineData("[RunsConcurrently] static async Task<int> A(int id) { await Task.Yield(); return id; } static async Task M(int[] ids) { using var s = new CancellationTokenSource(); var ts = ids.Select(id => A(id)).ToArray(); await Task.WhenAll(ts); }")]
        [InlineData("static string Th(int i) { if (i < 0) throw new InvalidOperationException(); return \"a\"; } static void M(int[] ids) { using var s = new CancellationTokenSource(); var q = ids.Select(i => s.Token.ToString()).ToArray(); }")]
        public void TasksFromElsewhere_Proved(string m) => Assert.Empty(Harness.Verify(Program.Replace("public static class C {", "public interface IW { [RunsConcurrently] Task G(Cell c); } public static class C {").Replace("using System;", "using System; using System.Linq;") + m + " }")
            .Diagnostics.Where(d => d.IsError).Select(d => d.Id + " " + d.Message));

        [Theory]
        [InlineData("static async Task M(Cell c) { var a = Task.Run(() => { c.V = 1; }); var b = Task.Run(() => { c.V = 2; }); await a; await b; }")]
        [InlineData("static async Task M(Cell c) { await Task.WhenAll(Task.Run(() => { c.V = 1; }), Task.Run(() => { c.V = 2; })); }")]
        [InlineData("static async Task<int> M(Cell c) { var a = Task.Run(() => { c.V = 1; }); await a; return 0; } static async Task<int> N(Cell c) { var a = Task.Run(() => { return c.V; }); c.V = 3; return await a; }")]
        [InlineData("[RunsConcurrently] static void W(Cell c) { c.V = 1; } static async Task M(Cell c) { var a = Task.Run(() => W(c)); var b = Task.Run(() => W(c)); await a; await b; }")]
        [InlineData("static void M(Cell c) { var th = new Thread(() => { c.V = 2; }); th.Start(); }")]
        [InlineData("static async Task M(int[] a) { await Task.WhenAll(Task.Run(() => { if (a.Length > 0) a[0] = 1; }), Task.Run(() => { if (a.Length > 0) a[0] = 2; })); }")]
        [InlineData("static Task M(Cell c) { return Task.Run(() => { c.V = 2; }); }")]
        // that they may be one object, it has to say otherwise
        [InlineData("static async Task M(Cell c, Cell d) { var a = Task.Run(() => { c.V = 1; }); var b = Task.Run(() => { d.V = 2; }); await a; await b; }")]
        // a local that changes isn't one object
        [InlineData("static async Task M(Cell c, Cell d) { Spec.Requires(c != d); var x = c; x = d; var a = Task.Run(() => { x.V = 1; }); var b = Task.Run(() => { d.V = 2; }); await a; await b; }")]
        // what it is told apart by is only what a method can see: a field's object isn't
        [InlineData("public class H { public Cell Cc = new Cell(); } static async Task M(H h, Cell d) { Spec.Requires(h.Cc != d); var a = Task.Run(() => { h.Cc.V = 1; }); var b = Task.Run(() => { d.V = 2; }); await a; await b; }")]
        // this method, before the task is awaited
        [InlineData("static async Task M(Cell c) { var t = Task.Run(() => { c.V = 2; }); c.V = 1; await t; }")]
        [InlineData("static async Task M(Cell c, bool b) { var t = Task.Run(() => { c.V = 2; }); if (b) await t; c.V = 1; await t; }")]
        [InlineData("static void M(Cell c) { var th = new Thread(() => { c.V = 2; }); th.Start(); c.V = 3; th.Join(); }")]
        // and in a catch, which the await may have sent it to
        [InlineData("static void Boom() { } static async Task M(Cell c) { var t = Task.Run(() => { c.V = 2; }); try { Boom(); await t; } catch (InvalidOperationException) { c.V = 1; throw; } }")]
        public void Warned(string m) => Assert.True(WarnedOfARace(m));

        [Theory]
        [InlineData("static async Task M(G g) { var a = Task.Run(() => g.Inc()); var b = Task.Run(() => g.Inc()); await a; await b; }")]
        [InlineData("static async Task M(G g) { await Task.WhenAll(Task.Run(() => g.Inc()), Task.Run(() => g.Inc())); }")]
        [InlineData("static async Task M(Cell c) { await Task.Run(() => { c.V = 2; }); c.V = 1; }")]
        [InlineData("static void M(Cell c) { var t = Task.Run(() => { }); t.Wait(); }")]
        [InlineData("static async Task M(Cell c, Cell d) { var a = Task.Run(() => { return c.V; }); var b = Task.Run(() => { return d.V; }); await a; await b; }")]
        // on objects known to be different
        [InlineData("static async Task M(Cell c, Cell d) { Spec.Requires(c != d); var a = Task.Run(() => { c.V = 1; }); var b = Task.Run(() => { d.V = 2; }); await a; await b; }")]
        [InlineData("static async Task M() { var c = new Cell(); var d = new Cell(); var a = Task.Run(() => { c.V = 1; }); var b = Task.Run(() => { d.V = 2; }); await a; await b; }")]
        [InlineData("static async Task M(Cell c, Cell d) { Spec.Requires(c != d); await Task.WhenAll(Task.Run(() => { c.V = 1; }), Task.Run(() => { d.V = 2; })); }")]
        [InlineData("[RunsConcurrently] static void W(Cell x) { x.V = 1; } static async Task M(Cell c, Cell d) { Spec.Requires(c != d); var a = Task.Run(() => W(c)); var b = Task.Run(() => W(d)); await a; await b; }")]
        [InlineData("static async Task M(int[] x, int[] y) { Spec.Requires(x != y && x.Length > 0 && y.Length > 0); var a = Task.Run(() => { if (x.Length > 0) x[0] = 1; }); var b = Task.Run(() => { if (y.Length > 0) y[0] = 2; }); await a; await b; }")]
        // this method writes it, but on another object, or once the task is over, or before it starts
        [InlineData("static async Task M(Cell c, Cell d) { Spec.Requires(c != d); var a = Task.Run(() => { c.V = 1; }); d.V = 2; await a; }")]
        [InlineData("static async Task M(Cell c) { var t = Task.Run(() => { c.V = 2; }); await t; c.V = 1; }")]
        [InlineData("static async Task M(Cell c) { c.V = 1; var t = Task.Run(() => { c.V = 2; }); await t; }")]
        [InlineData("static void M(Cell c) { c.V = 1; var th = new Thread(() => { c.V = 2; }); th.Start(); th.Join(); c.V = 3; }")]
        [InlineData("static async Task M(Cell c) { var t = Task.Run(() => { c.V = 2; }); await Task.WhenAll(t, Task.Delay(1)); c.V = 1; }")]
        public void NotWarned(string m) => Assert.False(WarnedOfARace(m));
    }
}
