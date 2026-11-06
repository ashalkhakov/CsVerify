using System.Linq;
using Xunit;

namespace CsVerify.Tests
{
    /// <summary>Tasks held in locals and awaited later: what they give, what they may do meanwhile, and what is refused.</summary>
    public class TaskLaterTests
    {
        private const string Helpers = "public class Cell { public int V; } public static class C { " +
            "static async Task<int> Twice(int x) { Spec.Requires(0 <= x && x <= 1000); Spec.Ensures<int>(r => r == 2 * x); await Task.Yield(); return 2 * x; } " +
            "static async Task Work() { await Task.Yield(); } " +
            "static async Task Bump(Cell c) { Spec.Requires(c.V < 1000); await Task.Yield(); c.V = c.V < 1000 ? c.V + 1 : 0; } " +
            "static async Task<int> ReadC(Cell c) { await Task.Yield(); return c.V; } ";

        private static string[] Errors(string m) =>
            Harness.Verify("using CsVerify; using System; using System.Threading.Tasks; " + Helpers + m + " }").Errors("M");

        [Theory]
        [InlineData("static async Task M() { var t = Twice(4); await Task.Yield(); int r = await t; Spec.Assert(r == 8); }")]
        [InlineData("static async Task M() { var a = Twice(1); var b = Twice(2); int x = await a; int y = await b; Spec.Assert(x + y == 6); }")]
        [InlineData("static async Task M() { var a = Twice(1); var b = Twice(2); await Task.WhenAll(a, b); Spec.Assert(a.Result + b.Result == 6); }")]
        [InlineData("static async Task M() { var a = Twice(1); var b = Twice(2); int[] rs = await Task.WhenAll(a, b); Spec.Assert(rs.Length == 2 && rs[0] == 2 && rs[1] == 4); }")]
        [InlineData("static async Task M() { var t = Work(); await t.ConfigureAwait(false); }")]
        [InlineData("static async Task M(int x) { Spec.Requires(0 <= x && x <= 10); var t = Twice(x); int y = x + 1; int r = await t; Spec.Assert(r == 2 * x && y == x + 1); }")]
        [InlineData("static async Task M() { var c = new Cell(); c.V = 5; var t = Work(); c.V = 6; await t; Spec.Assert(c.V == 6); }")]
        [InlineData("static async Task M(bool f) { var t = Work(); if (f) { await t; } else { await t; } }")]
        [InlineData("static async Task M() { var t = Twice(1); await t; int a = await t; Spec.Assert(a == 2); }")]
        [InlineData("static async Task M(int n) { for (int i = 0; i < n; i++) { var t = Work(); await t; } }")]
        [InlineData("static async Task M(int n) { var t = Twice(1); for (int i = 0; i < n; i++) { await Task.Yield(); } var r = await t; Spec.Assert(r == 2); }")]
        [InlineData("static async Task M(bool b) { var t = Work(); if (b) await t; else await t; }")]
        [InlineData("static async Task M() { var t = Twice(1); var a = await t; var b = await t; Spec.Assert(a == b); }")]
        [InlineData("static async Task M() { var t = Work(); try { await Work(); } finally { await t; } }")]
        [InlineData("static async Task<int> Old(Cell c) { Spec.Ensures<int>(r => r == Spec.Old(c.V)); var v = c.V; await Task.Yield(); return v; } static async Task M(Cell c) { var v = c.V; var t = Old(c); var r = await t; Spec.Assert(r == v); }")]
        [InlineData("static async Task M(bool b, bool c) { var t = Work(); try { await t; if (b) throw new InvalidOperationException(); if (c) throw new InvalidOperationException(); } catch (InvalidOperationException) { } }")]
        public void Proved(string m) => Assert.Empty(Errors(m));

        [Theory]
        [InlineData("CSV1026", "static async Task M() { var t = Work(); await Task.Yield(); }")]
        [InlineData("CSV1026", "static async Task M(bool f) { var t = Work(); if (f) await t; }")]
        [InlineData("CSV1001", "static async Task M() { var t = Twice(5000); await t; }")]
        [InlineData("CSV1004", "static async Task M() { var t = Twice(4); int r = await t; Spec.Assert(r == 9); }")]
        [InlineData("CSV1004", "static async Task M(Cell c) { c.V = 1; var t = Work(); Spec.Assert(c.V == 1); await t; }")]
        [InlineData("CSV1004", "static async Task M(Cell c) { Spec.Requires(c.V == 1); var t = Work(); await t; Spec.Assert(c.V == 1); }")]
        [InlineData("CSV1026", "static async Task M() { var t = Twice(1); int r = t.Result; await t; }")]
        [InlineData("CSV1901", "static Task<int> M() { var t = Twice(1); return t; }")]
        [InlineData("CSV1901", "static async Task M() { var t = Work(); Func<Task> g = () => t; await g(); }")]
        [InlineData("CSV1004", "static async Task M() { var a = Twice(1); var b = Twice(2); int[] rs = await Task.WhenAll(a, b); Spec.Assert(rs[0] == 4); }")]
        [InlineData("CSV1026", "static async Task M() { var a = Twice(1); var b = Twice(2); await Task.WhenAll(a); await Task.Yield(); }")]
        [InlineData("CSV1901", "static async Task M() { var t = Work(); t = Work(); await t; }")]
        [InlineData("CSV1901", "static void M() { var t = Twice(1); t.Wait(); }")]
        [InlineData("CSV1004", "static async Task<int> Post(Cell c) { Spec.Ensures<int>(r => r == c.V); await Task.Yield(); return c.V; } static async Task M(Cell c) { var v = c.V; var t = Post(c); var r = await t; Spec.Assert(r == v); }")]
        [InlineData("CSV1004", "static async Task<int> Post(Cell c) { Spec.Ensures<int>(r => r == c.V); await Task.Yield(); return c.V; } static async Task M(Cell c) { var t = Post(c); var r = await t; Spec.Assert(r == c.V); }")]
        [InlineData("CSV1004", "static async Task SetFive(Cell c) { Spec.Ensures(c.V == 5); await Task.Yield(); c.V = 5; } static async Task M() { var c = new Cell(); var t = SetFive(c); Spec.Assert(c.V == 5); await t; }")]
        [InlineData("CSV1004", "static async Task SetFive(Cell c) { Spec.Ensures(c.V == 5); await Task.Yield(); c.V = 5; } static async Task M() { var c = new Cell(); c.V = 1; var t = SetFive(c); Spec.Assert(c.V == 1); await t; }")]
        [InlineData("CSV1026", "static async Task M(int n) { for (int i = 0; i < n; i++) { var t = Work(); } }")]
        [InlineData("CSV1026", "static async Task M(int n) { for (int i = 0; i < n; i++) { var t = Work(); if (i == 1) break; await t; } }")]
        [InlineData("CSV1026", "static async Task M(int n) { for (int i = 0; i < n; i++) { var t = Work(); if (i == 1) continue; await t; } }")]
        [InlineData("CSV1026", "static async Task M(int[] a) { foreach (var x in a) { var t = Work(); } }")]
        [InlineData("CSV1026", "static async Task M(int n) { var t = Work(); for (int i = 0; i < n; i++) { await t; } }")]
        [InlineData("CSV1026", "static async Task M(bool b) { var t = Work(); try { if (b) await t; } finally { } }")]
        [InlineData("CSV1026", "static async Task M() { var t = Work(); try { await Work(); } catch (InvalidOperationException) { return; } await t; }")]
        [InlineData("CSV1004", "static async Task M(Cell c) { var t = Work(); var a = c.V; var b = c.V; Spec.Assert(a == b); await t; }")]
        [InlineData("CSV1004", "static async Task M(Cell c) { var v = c.V; var t = Work(); if (c.V == v) { } else { Spec.Assert(false); } await t; }")]
        [InlineData("CSV1026", "static async Task M() { var t = Work(); try { await Work(); await t; } catch (InvalidOperationException) { } }")]
        [InlineData("CSV1026", "static async Task M() { var t = Work(); var u = Work(); try { await t; await Work(); await u; } catch (InvalidOperationException) { } }")]
        [InlineData("CSV1026", "static async Task M(bool b, bool c) { var t = Work(); try { if (b) throw new InvalidOperationException(); await t; if (c) throw new InvalidOperationException(); } catch (InvalidOperationException) { } }")]
        [InlineData("CSV1026", "static async Task M(bool b) { var t = Work(); try { if (b) { await t; throw new InvalidOperationException(); } throw new InvalidOperationException(); } catch (InvalidOperationException) { } }")]
        public void Reported(string id, string m) => Assert.Contains(id, Errors(m));

        [Fact]
        public void Stored_IsRefused() => Assert.Contains("CSV1901", Errors("static Task? keep; static async Task M() { var t = Work(); keep = t; await t; }"));

        [Fact]
        public void InATry_AFailureIsSeenAtTheAwait() => Assert.Empty(Errors(
            "static async Task M() { var t = Work(); try { await t; } catch (InvalidOperationException) { } }"));

        [Fact]
        public void LentAView_IsRefused() => Assert.Contains("CSV1901", Harness.Verify("using CsVerify; using System.Threading.Tasks; " +
            "[Owned] public sealed class O { public int V; } public static class C { " +
            "static async Task G(Own<O> v, O o) { Spec.Requires(v.Obj.Value == o); await Task.Yield(); Own.Drop(v); } " +
            "static async Task M() { var o = Own.New(new O(), out var v); var t = G(v, o); await t; } }").Errors("M"));

        [Fact]
        public void TwoTasksOnOneField_IsWarned()
        {
            var r = Harness.Verify("using CsVerify; using System; using System.Threading.Tasks; " + Helpers +
                "static async Task M(Cell c) { Spec.Requires(c.V < 1000); var a = Bump(c); var b = ReadC(c); await a; await b; } }");
            Assert.Contains(r.Diagnostics, d => d.Id == "CSV1900" && d.Message.Contains("could race"));
        }

        [Fact]
        public void TwoTasksOnOneField_UnderItsLock_IsNotWarned()
        {
            var r = Harness.Verify("using CsVerify; using System.Threading.Tasks; public class Cell { readonly object _l = new object(); [GuardedBy(nameof(_l))] int _v; " +
                "public async Task Set(int x) { await Task.Yield(); lock (_l) { _v = x; } } public async Task<int> Get() { await Task.Yield(); lock (_l) { return _v; } } } " +
                "public static class C { static async Task M(Cell c) { var a = c.Set(1); var b = c.Get(); await a; await b; } }");
            Assert.DoesNotContain(r.Diagnostics, d => d.Message.Contains("could race"));
        }
    }
}
