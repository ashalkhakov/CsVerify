using Xunit;

namespace CsVerify.Tests
{
    /// <summary>
    /// Facts inferred for loops without invariants: candidates from the condition and from what the loop changes,
    /// assumed only if they hold on entry and at every back edge (else the method is verified again without them).
    /// </summary>
    public class LoopFactTests
    {
        [Fact]
        public void CountingLoops_NeedNoInvariants()
        {
            var r = Harness.Verify(@"
public static class P
{
    public static int Up(int[] a) { int s = 0; for (int i = 0; i < a.Length; i++) s = a[i]; return s; }
    public static int Down(int[] a) { int s = 0; for (int i = a.Length - 1; i >= 0; i--) s = a[i]; return s; }
    public static int While(int[] a, int lo)
    {
        if (lo < 0) return 0;
        int i = lo;
        while (i < a.Length) { if (a[i] == 0) break; i++; }
        return i;
    }
    public static int Inclusive(int[] a, int n) { Spec.Requires(n < a.Length); int s = 0; for (int i = 0; i <= n; i++) s = a[i]; return s; }
}");
            Assert.True(r.Success, string.Join("\n", r.Diagnostics));
        }

        [Fact]
        public void AFactThatFailsAtABackEdge_IsDropped_SoBugsStillShow()
        {
            var r = Harness.Verify(@"
public static class P
{
    // i += 2 can step past a.Length: i <= a.Length fails at the back edge and is dropped; i >= 0 stays
    public static int Step(int[] a) { int s = 0; for (int i = 0; i < a.Length; i += 2) s = a[i]; return s; }
    public static int StepBad(int[] a) { int s = 0; for (int i = 0; i < a.Length; i += 2) s = a[i + 1]; return s; }
    // the loop moves i both ways: neither of its direction facts holds
    public static int Wobble(int[] a, bool b)
    {
        int i = 1;
        while (i < a.Length) { if (b) i--; else i += 2; if (i < 0) return 0; }
        return a[i - 1];
    }
}", overflow: false);
            Assert.Empty(r.Errors("Step"));
            Assert.Equal(new[] { "CSV1003" }, r.Errors("StepBad"));
            Assert.Equal(new[] { "CSV1003" }, r.Errors("Wobble"));
        }

        [Fact]
        public void LoopsWithInvariants_AreLeftAsTheyAre()
        {
            var r = Harness.Verify(@"
public static class P
{
    // its invariant says nothing of i's bounds, and nothing is inferred for it
    public static int Weak(int[] a)
    {
        int s = 0;
        for (int i = 0; i < a.Length; i++) { Spec.Invariant(s == s); s = a[i]; }
        return s;
    }
}");
            Assert.Equal(new[] { "CSV1003" }, r.Errors("Weak"));
        }
    }
}
