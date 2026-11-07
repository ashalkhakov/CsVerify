using System.Linq;
using Xunit;

namespace CsVerify.Tests
{
    /// <summary>Spec.Pre, Spec.Post and Spec.Total of a Func or Action (Dafny's f.requires and f.ensures): no delegate is taken to accept anything unless that is said or proved.</summary>
    public class HigherOrderTests
    {
        private const string Program = "using CsVerify; using System; using System.Linq; using System.Collections.Generic; using System.Threading.Tasks; public class Cell { public int V; } ";

        private static string[] Ids(string code) => Harness.Verify(Program + code).Diagnostics.Where(d => d.IsError).Select(d => d.Id).ToArray();
        private static string[] All(string code) => Harness.Verify(Program + code).Diagnostics.Where(d => d.IsError).Select(d => d.Id + " " + d.Message).ToArray();

        private const string C = "public static class C { ";
        private const string Apply = "static int Apply(Func<int, int> g, int x) { Spec.Requires(Spec.Pre(g, x)); Spec.Ensures<int>(r => Spec.Post(g, x, r)); return g(x); } ";

        [Theory]
        // a call gives Spec.Post; a lambda's is its value
        [InlineData(C + Apply + "static void M() { var y = Apply(x => x < 100 ? x + 1 : 0, 1); Spec.Assert(y == 2); } }")]
        [InlineData(C + Apply + "static void M(int k) { var y = Apply(x => k, 5); Spec.Assert(y == k); } }")]
        // and what it ensures
        [InlineData(C + Apply + "static void M() { var y = Apply(x => { Spec.Ensures<int>(r => r >= 0); return x < 0 ? 0 : x; }, 5); Spec.Assert(y >= 0); } }")]
        // one with a precondition, given what it accepts
        [InlineData(C + Apply + "static void M() { var y = Apply(x => { Spec.Requires(0 < x && x < 100); return x * 2; }, 3); Spec.Assert(y == 6); } }")]
        [InlineData(C + "static void M() { Func<int, int> h = x => { Spec.Requires(x < 10); return x; }; var a = h(3); } }")]
        [InlineData(C + "static int Sum(Func<int, int> g, int n) { Spec.Requires(0 <= n && n < 100); Spec.Requires(Spec.Forall(0, n, i => Spec.Pre(g, i))); int s = 0; for (int i = 0; i < n; i++) { Spec.Invariant(0 <= i && i <= n); s = g(i); } return s; } }")]
        // said total
        [InlineData(C + "static void M(Func<int, int> g) { Spec.Requires(Spec.Total(g)); var a = g(-5); var b = g(int.MaxValue); } }")]
        [InlineData(C + "static void T(Func<int, int> g) { Spec.Requires(Spec.Total(g)); } static void M() { T(x => x); T(x => { Spec.Requires(x > 0 || x <= 0); return x; }); } }")]
        [InlineData(C + "static void T(Func<int, int> g) { Spec.Requires(Spec.Total(g)); } static void M(Func<int, int> g) { Spec.Requires(Spec.Total(g)); T(g); var y = Apply(g, 1); } " + Apply + "}")]
        // handed to a library: a lambda without a precondition, or one said total
        [InlineData(C + "static void M(List<int> l) { l.ForEach(x => { }); var s = l.Select(x => x / 2).ToList(); } }")]
        [InlineData(C + "static void M(Action work) { Spec.Requires(Spec.Total(work)); Task.Run(work).Wait(); } }")]
        // a lambda knows what its method requires of what never changes
        [InlineData(C + "static async Task M(Action work) { Spec.Requires(Spec.Total(work)); await Task.Run(() => work()); } }")]
        // stored or returned: whoever calls it proves what it accepts
        [InlineData(C + "static Func<int, int> M() { Func<int, int> h = x => { Spec.Requires(x < 10); return x; }; return h; } }")]
        // Actions too
        [InlineData(C + "static void Run(Action<int> a, int x) { Spec.Requires(Spec.Pre(a, x)); a(x); } static void M() { Run(x => { Spec.Requires(x > 0); }, 1); } }")]
        // a captured variable that changes isn't part of what the lambda gives, but that's no error
        [InlineData(C + Apply + "static void M() { int k = 1; k = 2; var y = Apply(x => k, 5); } }")]
        public void Proved(string code) => Assert.Empty(All(code));

        [Theory]
        // nothing is known of a delegate no specification speaks of
        [InlineData("CSV1001", C + "static void M(Func<int, int> g) { var a = g(1); } }")]
        [InlineData("CSV1001", C + "static Func<int, int> F = x => x; static void M() { var f = F; if (f != null) { var a = f(3); } } }")]
        [InlineData("CSV1001", C + "static void M(Func<int, int> g) { Spec.Requires(Spec.Pre(g, 1)); var a = g(2); } }")]
        [InlineData("CSV1001", C + "static void M(Func<int, int> g) { Spec.Requires(Spec.Total(g)); Func<int> k = () => g(1); g = x => { Spec.Requires(x > 5); return x; }; } }")]
        // what the callee doesn't say isn't known
        [InlineData("CSV1004", C + "static int Apply(Func<int, int> g, int x) { Spec.Requires(Spec.Total(g)); return g(x); } static void M() { var y = Apply(x => 2, 1); Spec.Assert(y == 2); } }")]
        [InlineData("CSV1004", C + Apply + "static void M() { int k = 1; k = 2; var y = Apply(x => k, 5); Spec.Assert(y == 2); } }")]
        // a precondition is proved at each call
        [InlineData("CSV1001", C + Apply + "static void M() { var y = Apply(x => { Spec.Requires(x > 0); return x; }, 0); } }")]
        [InlineData("CSV1001", C + "static void M() { Func<int, int> h = x => { Spec.Requires(x < 10); return x; }; var a = h(20); } }")]
        [InlineData("CSV1001", C + "static void M(bool b) { Func<int, int> h = x => x; if (b) h = x => { Spec.Requires(x < 10); return x; }; var a = h(20); } }")]
        [InlineData("CSV1001", C + "static void M() { Func<int, int> h = x => { Spec.Requires(x < 10); return x; }; Func<int> k = () => h(1); } }")]
        [InlineData("CSV1001", C + "static void T(Func<int, int> g) { Spec.Requires(Spec.Total(g)); } static void M() { T(x => { Spec.Requires(x > 0); return x; }); } }")]
        // a library may call it with anything
        [InlineData("CSV1029", C + "static void M(List<int> l) { l.ForEach(x => { Spec.Requires(x > 0); }); } }")]
        [InlineData("CSV1029", C + "static void M(Action work) { Task.Run(work).Wait(); } }")]
        [InlineData("CSV1029", C + "static void M(Action<int> a, List<int> l) { Spec.Requires(Spec.Pre(a, 1)); l.ForEach(a); } }")]
        // a precondition that reads state can't be a Spec.Pre
        [InlineData("CSV1029", C + "static int Field; static void M() { Func<int, int> h = x => { Spec.Requires(x < Field); return x; }; } }")]
        public void Reported(string id, string code) => Assert.Contains(id, Ids(code));
    }
}
