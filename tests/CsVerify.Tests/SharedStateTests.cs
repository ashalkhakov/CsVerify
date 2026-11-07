using System.Linq;
using Xunit;

namespace CsVerify.Tests
{
    /// <summary>Code that runs alongside other code must hold what it uses: a lock, a permission, or an object only it has. Everything else is an error, so what is proved is free of races.</summary>
    public class SharedStateTests
    {
        private const string Program = "using CsVerify; using System; using System.Threading; using System.Threading.Tasks; " +
            "public class Cell { public int V; public int P { get { return V; } } public readonly int R = 1; public int I { get; init; } public static int S; public volatile int Vol; public int[] A = new int[1]; } " +
            "[Owned] public sealed class O { public int V; } " +
            "public class G { private readonly object _l = new object(); [GuardedBy(nameof(_l))] private int _n; [RunsConcurrently] public void Inc() { lock (_l) { if (_n < 100) _n = _n + 1; } } } ";

        private static string[] Ids(string code) => Harness.Verify(Program + code).Diagnostics.Where(d => d.IsError).Select(d => d.Id).ToArray();
        private static string[] All(string code) => Harness.Verify(Program + code).Diagnostics.Where(d => d.IsError).Select(d => d.Id + " " + d.Message).ToArray();

        private const string C = "public static class C { ";

        [Theory]
        // a delegate given to a task or thread
        [InlineData(C + "static async Task M(Cell c) { var t = Task.Run(() => { c.V = 2; }); await t; } }")]
        [InlineData(C + "static async Task M(Cell c) { var t = Task.Run(() => { var x = c.V; }); await t; } }")]
        [InlineData(C + "static void M(Cell c) { var t = new Thread(() => { c.V = 2; }); t.Start(); t.Join(); } }")]
        [InlineData(C + "[RunsConcurrently] static void W(Cell c) { c.V = 1; } static void M(Cell c) { var t = new Thread(() => W(c)); t.Start(); t.Join(); } }")]
        [InlineData(C + "static Cell X = new Cell(); [RunsConcurrently] static void W() { X.V = 1; } static void M() { var t = new Thread(W); t.Start(); t.Join(); } }")]
        [InlineData(C + "static void M(Cell c) { Parallel.For(0, 3, i => { c.V = i; }); } }")]
        // a task not awaited at once, and what it calls
        [InlineData(C + "[RunsConcurrently] static async Task A(Cell c) { await Task.Yield(); c.V = 1; } static async Task M(Cell c) { var t = A(c); await t; } }")]
        [InlineData(C + "[RunsConcurrently] static void H(Cell c) { c.V = 1; } [RunsConcurrently] static async Task A(Cell c) { await Task.Yield(); H(c); } static async Task M(Cell c) { var t = A(c); await t; } }")]
        [InlineData(C + "[RunsConcurrently] static async Task A(Cell c) { Action a = () => { c.V = 1; }; a(); await Task.Yield(); } static async Task M(Cell c) { var t = A(c); await t; } }")]
        // forwarded, it is who takes it that starts it
        [InlineData(C + "[RunsConcurrently] static async Task A(Cell c) { await Task.Yield(); c.V = 1; } static Task F(Cell c) => A(c); static async Task M(Cell c) { var t = F(c); await t; } }")]
        // the method itself, until it's over, and what it calls meanwhile
        [InlineData(C + "static async Task M(Cell c) { var t = Task.Run(() => { }); c.V = 1; await t; } }")]
        [InlineData(C + "static async Task M(Cell c) { var t = Task.Run(() => { }); var x = c.V; await t; } }")]
        [InlineData(C + "[RunsConcurrently] static void W(Cell c) { c.V = 1; } static async Task M(Cell c) { var t = Task.Run(() => { }); W(c); await t; } }")]
        [InlineData(C + "static void M(Cell c) { var t = new Thread(() => { }); t.Start(); c.V = 1; t.Join(); } }")]
        // statics, volatile, arrays
        [InlineData(C + "static async Task M() { var t = Task.Run(() => { Cell.S = 1; }); await t; } }")]
        [InlineData(C + "static async Task M(Cell c) { var t = Task.Run(() => { c.Vol = 1; }); await t; } }")]
        [InlineData(C + "static async Task M(int[] a) { var t = Task.Run(() => { if (a.Length > 0) a[0] = 1; }); await t; } }")]
        [InlineData(C + "static async Task M(int[] a) { var t = Task.Run(() => { foreach (var x in a) { } }); await t; } }")]
        [InlineData(C + "static async Task M(int[] a) { var t = Task.Run(() => { }); if (a.Length > 0) a[0] = 1; await t; } }")]
        // lock-free: not understood
        [InlineData(C + "static async Task M(Cell c) { var t = Task.Run(() => { Interlocked.Increment(ref c.V); }); await t; } }")]
        // said to be run so
        [InlineData(C + "[RunsConcurrently] static void M(Cell c) { c.V = 1; } }")]
        [InlineData("[RunsConcurrently] public class H { private int _n; public void M() { _n = 1; } }")]
        [InlineData("[RunsConcurrently] public class H { private int _n; private void N() { _n = 1; } public void M() { N(); } }")]
        public void Reported(string code) => Assert.Contains("CSV1027", Ids(code));

        [Theory]
        // alone: nothing runs alongside
        [InlineData(C + "static void M(Cell c) { c.V = 1; } }")]
        [InlineData(C + "static async Task A(Cell c) { await Task.Yield(); c.V = 1; } static async Task M(Cell c) { await A(c); c.V = 2; } }")]
        [InlineData(C + "static async Task M(Cell c) { await Task.Run(() => { c.V = 2; }); c.V = 3; } }")]
        // once it's over, or before it starts
        [InlineData(C + "static async Task M(Cell c) { c.V = 1; var t = Task.Run(() => { }); await t; c.V = 2; } }")]
        [InlineData(C + "static void M(Cell c) { c.V = 1; var t = new Thread(() => { }); t.Start(); t.Join(); c.V = 2; } }")]
        // what never changes
        [InlineData(C + "static async Task M(Cell c) { var t = Task.Run(() => { var x = c.R; var y = c.I; }); await t; var a = c.R; } }")]
        // a lock
        [InlineData(C + "static async Task M(G g) { await Task.WhenAll(Task.Run(() => g.Inc()), Task.Run(() => g.Inc())); } }")]
        // a permission
        [InlineData(C + "[RunsConcurrently] static async Task A(O o) { Spec.Requires(Spec.Acc(o)); Spec.Ensures(Spec.Acc(o)); await Task.Yield(); o.V = 1; var x = o.V; } static async Task M(O p, O q) { Spec.Requires(Spec.Acc(p) && Spec.Acc(q)); Spec.Ensures(Spec.Acc(p) && Spec.Acc(q)); await Task.WhenAll(A(p), A(q)); } }")]
        // what only it has
        [InlineData(C + "[RunsConcurrently] static async Task A() { var c = new Cell(); await Task.Yield(); c.V = 1; var x = c.V; var a = new int[2]; a[0] = x; } static async Task M() { var t = A(); await t; } }")]
        [InlineData(C + "static async Task M() { var c = new Cell(); var t = Task.Run(() => { }); c.V = 1; await t; } }")]
        // what it is building
        [InlineData("public class B { public int V; public int W; [RunsConcurrently] public B() { V = 1; } } " + C + "[RunsConcurrently] static async Task A() { var b = new B { W = 2 }; await Task.Yield(); } static async Task M() { var t = A(); await t; } }")]
        // specifications aren't run
        [InlineData(C + "[RunsConcurrently] static async Task A(Cell c) { Spec.Requires(c.V > 0); await Task.Yield(); } static async Task M(Cell c) { Spec.Requires(c.V > 0); var t = A(c); await t; } }")]
        [InlineData(C + "static async Task M(Cell c) { var t = Task.Run(() => { }); Spec.Assert(c.V == c.V); await t; } }")]
        // forwarded from a method that isn't async, it's started by whoever has the task: here, awaited at once
        [InlineData(C + "static Task G(Cell c) { c.V = 1; return Task.CompletedTask; } static Task F(Cell c) => G(c); static async Task M(Cell c) { await F(c); } }")]
        // what's said not to be looked at
        [InlineData(C + "[Trusted] static void W(Cell c) { c.V = 1; } static async Task M(Cell c) { await Task.WhenAll(Task.Run(() => W(c)), Task.Run(() => W(c))); } }")]
        // a method that's only run alone, for all that another with the same class isn't
        [InlineData(C + "[RunsConcurrently] static async Task A(int[] a) { Spec.Requires(a.Length > 0 && Spec.Acc(a, 0, 1)); Spec.Ensures(Spec.Acc(a, 0, 1)); await Task.Yield(); a[0] = a[0] / 2; } static void Alone(Cell c) { c.V = 1; } static async Task M(int[] a, Cell c) { Spec.Requires(a.Length > 0 && Spec.Acc(a)); Spec.Ensures(Spec.Acc(a)); var t = A(a); await t; Alone(c); } }")]
        public void Proved(string code) => Assert.Empty(All(code));

        // what runs concurrently must say so, where that can be seen: a start, a hand-off, a call from concurrent code, an override
        [Theory]
        [InlineData(C + "static async Task A(Cell c) { await Task.Yield(); } static async Task M(Cell c) { var t = A(c); await t; } }")]
        [InlineData(C + "static async Task A(Cell c) { await Task.Yield(); } static async Task M(Cell c) { await Task.WhenAll(A(c), A(c)); } }")]
        [InlineData(C + "static void W() { } static void M() { var t = new Thread(W); t.Start(); t.Join(); } }")]
        [InlineData(C + "static void W() { } static async Task M() { await Task.WhenAll(Task.Run(() => W()), Task.Run(() => W())); } }")]
        [InlineData(C + "static void H() { } [RunsConcurrently] static async Task A() { H(); await Task.Yield(); } }")]
        [InlineData(C + "[RunsConcurrently] static async Task A(Cell c) { var x = c.P; await Task.Yield(); } }")]
        [InlineData("public class B { public B() { } } " + C + "[RunsConcurrently] static void A() { var b = new B(); } }")]
        [InlineData(C + "static void H() { } static async Task M() { var t = Task.Run(() => { }); H(); await t; } }")]
        [InlineData("public class P { [RunsConcurrently] public virtual void F() { } } public class Q : P { public override void F() { } } " + C + " }")]
        [InlineData("public interface I { [RunsConcurrently] void F(); } public class Q : I { public void F() { } } " + C + " }")]
        public void Unmarked_IsReported(string code) => Assert.Contains("CSV1028", Ids(code));

        [Theory]
        [InlineData(C + "[RunsConcurrently] static async Task A(Cell c) { await Task.Yield(); } static async Task M(Cell c) { var t = A(c); await t; } }")]
        [InlineData(C + "static async Task A(Cell c) { await Task.Yield(); } static async Task M(Cell c) { await A(c); } }")]
        [InlineData("[RunsConcurrently] public class K { void H() { } public async Task A() { H(); await Task.Yield(); } } " + C + " }")]
        [InlineData("public sealed record R(int X); " + C + "[RunsConcurrently] static int A() { var r = new R(1); return r.X; } }")]
        [InlineData(C + "[Trusted] static void H() { } [RunsConcurrently] static async Task A() { H(); await Task.Yield(); } }")]
        [InlineData(C + "[RunsConcurrently] static async Task A() { void L() { } L(); Action f = () => { }; f(); await Task.Yield(); } }")]
        public void Marked_IsFine(string code) => Assert.DoesNotContain("CSV1028", Ids(code));

        // an error isn't assumed away: what comes after is still looked at
        [Fact]
        public void ErrorsDoNotHideOthers()
        {
            var ids = Ids(C + "static async Task M(Cell c) { var t = Task.Run(() => { }); c.V = 1; var x = c.V; Spec.Assert(x == 2); await t; } }");
            Assert.Contains("CSV1027", ids);
            Assert.Contains("CSV1004", ids);
        }
    }
}
