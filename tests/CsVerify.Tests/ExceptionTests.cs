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
}
}
