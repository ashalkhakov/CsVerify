using System.Linq;
using Xunit;

namespace CsVerify.Tests
{
    /// <summary>try/catch/finally and exceptional postconditions (Spec.EnsuresOnThrow).</summary>
    public class ExceptionTests
    {
        private const string Parse = @"
    static int Parse(int x) {
        Spec.Ensures((int r) => r == x && x >= 0);
        Spec.EnsuresOnThrow<System.ArgumentException>(x < 0);
        if (x < 0) throw new System.ArgumentException(""negative"");
        return x; }";

        // (a try's raises are merged at its handler: each call in a try may raise, and followed one by one, each
        // ran the handler and the rest of the method again)
        private const string Raising = @"
    static int F(int x) { Spec.Requires(0 <= x && x <= 1000); Spec.Ensures((int r) => r == x); return x; }";

        [Fact]
        public void Raises_AreMergedAtTheHandler_Exactly()
        {
            var r = Harness.Verify("public static class C {" + Raising + @"
    static int Exact(int a) {
        Spec.Requires(0 <= a && a <= 10);
        int r = 1;
        try { r = 2; int t = F(a); r = 3; int u = F(a); r = 4; }
        catch (System.InvalidOperationException) { Spec.Assert(r == 2 || r == 3); r = 5; }
        Spec.Assert(r == 4 || r == 5);
        return r; }
    static int Wrong(int a) {
        Spec.Requires(0 <= a && a <= 10);
        int r = 1;
        try { r = 2; int t = F(a); r = 3; int u = F(a); r = 4; }
        catch (System.InvalidOperationException) { Spec.Assert(r == 3); }
        return r; }
}");
            // the handler knows each raise's state (r is 2 or 3), and no more than that
            Assert.Empty(r.Errors("Exact"));
            Assert.Equal(new[] { "CSV1004" }, r.Errors("Wrong"));
        }

        [Fact]
        public void Raises_AreMerged_SoTheRestIsExploredOnce()
        {
            var r = Harness.Verify("public static class C {" + Raising + @"
    static int Many(int a, int b) {
        Spec.Requires(0 <= a && a <= 1000 && 0 <= b && b <= 1000);
        int r = 0;
        try { int t1 = F(a); int t2 = F(b); int t3 = F(t1); int t4 = F(t2); int t5 = F(t3); int t6 = F(t4); int t7 = F(t5); int t8 = F(t6); r = t7 + t8; }
        catch (System.InvalidOperationException) { r = 0; }
        if (a > 1) r = r + 1;
        if (b > 2) r = r + 1;
        if (a > 3) r = r + 1;
        if (b > 4) r = r + 1;
        if (a > 5) r = r + 1;
        if (b > 6) r = r + 1;
        Spec.Assert(r >= 0);
        return r; }
}");
            var many = r.Methods.Single(m => m.Name == "C.Many");
            Assert.Empty(r.Errors("Many"));
            // one by one, each of the 8 raises explored the handler and the 64 paths after it: 300 obligations
            Assert.True(many.Obligations <= 100, $"{many.Obligations} obligations");
        }

        [Fact]
        public void Catch_SeesWhatTheCalleePromisedOnThrow()
        {
            var r = Harness.Verify("public static class C {" + Parse + @"
    static int Safe(int x) {
        Spec.Ensures((int r) => r >= 0);
        try { return Parse(x); } catch (System.ArgumentException) { Spec.Assert(x < 0); return 0; } }
    static int Wrong(int x) {
        Spec.Ensures((int r) => r > 0);
        try { return Parse(x) >= 0 ? 1 : 1; } catch (System.ArgumentException) { return 0; } }
    static int Unrelated(int x) {
        Spec.Ensures((int r) => r >= 0);
        try { return Parse(x); } catch (System.InvalidOperationException) { return -1; } }
}");
            Assert.Empty(r.Errors("Parse"));
            Assert.Empty(r.Errors("Safe"));
            Assert.Equal(new[] { "CSV1002" }, r.Errors("Wrong"));
            // any call may throw anything: an InvalidOperationException too, so -1 is a possible result
            Assert.Equal(new[] { "CSV1002" }, r.Errors("Unrelated"));
        }

        [Fact]
        public void Finally_RunsOnEveryWayOut()
        {
            var r = Harness.Verify("public static class C {" + Parse + @"
    static int OnReturn(int[] a) {
        Spec.Requires(a.Length == 1);
        Spec.Ensures((int r) => r == 1 && a[0] == 9);
        try { a[0] = 1; return a[0]; } finally { a[0] = 9; } }
    static void OnThrow(int[] a, int x) {
        Spec.Requires(a.Length == 1);
        Spec.EnsuresOnThrow<System.Exception>(a[0] == 9);
        try { Parse(x); } finally { a[0] = 9; } }
    static void Forgot(int[] a, int x) {
        Spec.Requires(a.Length == 1);
        Spec.EnsuresOnThrow<System.Exception>(a[0] == 9);
        a[0] = 1; Parse(x); a[0] = 9; }
}");
            Assert.Empty(r.Errors("OnReturn"));
            Assert.Empty(r.Errors("OnThrow"));
            Assert.Equal(new[] { "CSV1002" }, r.Errors("Forgot"));
        }

        [Fact]
        public void ImplicitThrows_AreCaught()
        {
            var r = Harness.Verify(@"public static class C {
    static int Doubled(int x) {
        Spec.Ensures((int r) => r == 2 * x || r == -1);
        try { return checked(x * 2); } catch (System.OverflowException) { return -1; } }
    static int Missed(int x) {
        Spec.Ensures((int r) => r == 2 * x);
        try { return checked(x * 2); } catch (System.OverflowException) { return -1; } }
    static int Cast(object o) {
        Spec.Ensures((int r) => r >= 0);
        try { var s = (string)o; return 1; } catch (System.InvalidCastException) { return 0; } }
}");
            Assert.Empty(r.Errors("Doubled"));
            Assert.Equal(new[] { "CSV1002" }, r.Errors("Missed"));
            Assert.Empty(r.Errors("Cast"));
        }
    
        [Fact]
        public void Handlers_LoseTheViewsTheTryMayHaveUsedUp()
        {
            const string cell = "[Owned] public sealed class Cell { public int V; }\n";
            // a view the try never touches is still there in the handler
            Assert.Empty(Harness.Analyze(cell + @"
public static class C { static void Work() { } static void M() {
    var c = Own.New(new Cell(), out var v);
    try { Work(); } catch (System.Exception) { }
    Own.Drop(v); } }"));
            // one it may have consumed is not (the call that consumed it may have thrown after)
            Assert.Contains("CSV0002", Harness.Analyze(cell + @"
public static class C { static void M() {
    var c = Own.New(new Cell(), out var v);
    try { Own.Drop(v); } catch (System.Exception) { Own.Drop(v); } } }"));
            // a finally may not touch views from outside it
            Assert.Contains("CSV0002", Harness.Analyze(cell + @"
public static class C { static void Work() { } static void M() {
    var c = Own.New(new Cell(), out var v);
    try { Work(); } finally { Own.Drop(v); } } }"));
        }

        [Fact]
        public void ProgramExceptionClasses_HaveFieldsAndDynamicTypes()
        {
            var r = Harness.Verify(@"
public class AppException : System.InvalidOperationException { public readonly int Level; public AppException(string m, int level) : base(m) { Spec.Ensures(Level == level); Level = level; } }
public sealed class DbException : AppException { public DbException(int level) : base(""db"", level) { Spec.Ensures(Level == level); } }
public static class C
{
    static int Read() { Spec.Ensures((int r) => r == 3); try { throw new DbException(3); } catch (AppException e) { return e.Level; } }
    static int ReadBad() { Spec.Ensures((int r) => r == 4); try { throw new DbException(3); } catch (AppException e) { return e.Level; } }
    static int ByBase() { Spec.Ensures((int r) => r == 3); try { throw new DbException(3); } catch (System.InvalidOperationException e) { return e is AppException a ? a.Level : -1; } }
    static bool Other() { Spec.Ensures((bool r) => r); try { throw new System.ArgumentException(""x""); } catch (System.Exception e) { return !(e is AppException); } }
    static bool OtherBad() { Spec.Ensures((bool r) => r); try { throw new DbException(1); } catch (System.Exception e) { return !(e is AppException); } }
    static int InLock(object l) { Spec.Requires(l != null); Spec.Ensures((int r) => r == 1); try { lock (l) { throw new DbException(1); } } catch (AppException e) { return e.Level; } }
}");
            foreach (var good in new[] { "AppException..ctor", "DbException..ctor", "C.Read", "C.ByBase", "C.Other", "C.InLock" })
                Assert.True(r[good].Verified, good + ": " + string.Join("; ", r[good].Diagnostics.Select(d => d.Message)));
            Assert.Equal(new[] { "CSV1002" }, r.Errors("ReadBad"));
            Assert.Equal(new[] { "CSV1002" }, r.Errors("OtherBad"));
        }
}
}
