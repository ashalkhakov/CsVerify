using System.IO;
using System.Linq;
using CsVerify.Verifier;
using Xunit;

namespace CsVerify.Tests
{
    /// <summary>
    /// Faster re-verification (#67): --only translates only what the selected methods reach, and --cache keeps the methods
    /// proved, proving one again only when what its proof depends on changes.
    /// </summary>
    public class IncrementalTests
    {
        private const string Shapes = @"
public abstract class Shape { public abstract int Area(); }
public sealed class Square : Shape
{
    public int Side;
    public override int Area() { Spec.Ensures<int>(r => r == 0); return 0; }
}
public sealed class Disc : Shape
{
    public override int Area() { Spec.Ensures<int>(r => r == 0); return 0; }
}
public static class Use
{
    public static int Twice(int x) { Spec.Requires(0 <= x && x < 1000); Spec.Ensures<int>(r => r == 2 * x); return x + x; }
    public static int Four(int x) { Spec.Requires(0 <= x && x < 100); Spec.Ensures<int>(r => r == 4 * x); return Twice(Twice(x)); }
    public static int Total(Shape s) => s.Area();
    public static int Wrong(int x) { Spec.Requires(0 <= x && x < 100); Spec.Ensures<int>(r => r == 3 * x); return Twice(x); }
}
public static class Lonely
{
    public static int Alone(int y) { Spec.Ensures<int>(r => r == y); return y; }
    [Pure] public static int Same(int y) => y;
}";

        private static VerificationResult Run(string source, string cache = null, string boogie = null, params string[] only)
        {
            var o = new VerifierOptions { CachePath = cache, BoogieOut = boogie };
            foreach (var x in only)
            {
                o.AddOnly(x);
            }
            var r = Engine.VerifySources(new[] { ("Test.cs", Harness.Usings + source) }, o);
            Assert.True(r.CompilationErrors.Count == 0, string.Join("\n", r.CompilationErrors));
            return r;
        }

        [Fact]
        public void Only_TranslatesWhatTheSelectedMethodsReach()
        {
            var bpl = Path.GetTempFileName();
            try
            {
                var r = Run(Shapes, boogie: bpl, only: "Use.");
                Assert.Equal(new[] { "Use.Four", "Use.Total", "Use.Twice", "Use.Wrong" }, r.Methods.Select(m => m.Name).OrderBy(n => n));
                foreach (var ok in new[] { "Four", "Total", "Twice" })
                {
                    Assert.True(r.Errors(ok).Length == 0, r.Explain(ok));
                }
                Assert.Equal(new[] { "CSV1002" }, r.Errors("Wrong"));
                var text = File.ReadAllText(bpl);
                // (a virtual call's overrides are reached, a class nothing selected uses isn't)
                Assert.Contains("Square.Area", text);
                Assert.Contains("Disc.Area", text);
                Assert.DoesNotContain("Lonely", text);
                Assert.Contains(r.Phases, p => p.phase == "translate");
            }
            finally
            {
                File.Delete(bpl);
            }
        }

        [Fact]
        public void Only_AConstructorLeftOutSetsTheNewObjectsFields()
        {
            // (a constructor not selected is its contract alone: it still sets the new object's fields, so its
            // postcondition about them doesn't contradict their defaults, and the wrong assertion is found)
            const string boxes = @"
public sealed class Box { public int V; public Box(int v) { Spec.Ensures(V == v); V = v; } }
public static class Make
{
    public static void Right() { var b = new Box(1); var c = new Box(2); Spec.Assert(b.V == 1 && c.V == 2); }
    public static void Wrong() { var b = new Box(1); Spec.Assert(b.V == 2); }
}";
            var r = Run(boxes, only: "Make.");
            Assert.True(r.Errors("Right").Length == 0, r.Explain("Right"));
            Assert.Equal(new[] { "CSV1004" }, r.Errors("Wrong"));
        }

        [Fact]
        public void Cache_ProvesAgainOnlyWhatChanged()
        {
            var cache = Path.GetTempFileName();
            File.Delete(cache);
            try
            {
                var first = Run(Shapes, cache);
                Assert.DoesNotContain(first.Methods, m => m.Cached);
                Assert.Equal(new[] { "CSV1002" }, first.Errors("Wrong"));
                // (unchanged: all proved before, the failure found again)
                var again = Run(Shapes, cache);
                Assert.Equal(first.Methods.Where(m => m.Verified).Select(m => m.Name).OrderBy(n => n),
                    again.Methods.Where(m => m.Cached).Select(m => m.Name).OrderBy(n => n));
                Assert.Equal(new[] { "CSV1002" }, again.Errors("Wrong"));
                Assert.False(again["Use.Wrong"].Cached);
                // (a body changed: that method; a contract changed: it and its callers)
                var body = Run(Shapes.Replace("return x + x;", "return 2 * x;"), cache);
                Assert.Equal(new[] { "Use.Twice", "Use.Wrong" }, body.Methods.Where(m => !m.Cached).Select(m => m.Name).OrderBy(n => n));
                var contract = Run(Shapes.Replace("return x + x;", "return 2 * x;").Replace("x < 1000); Spec.Ensures<int>(r => r == 2 * x)", "x < 2000); Spec.Ensures<int>(r => r == 2 * x)"), cache);
                Assert.Equal(new[] { "Use.Four", "Use.Twice", "Use.Wrong" }, contract.Methods.Where(m => !m.Cached).Select(m => m.Name).OrderBy(n => n));
                Assert.All(contract.Methods.Where(m => m.Name != "Use.Wrong"), m => Assert.True(m.Verified, m.Name));
                // (a wrong method proved before isn't: what changed is found)
                var broken = Run(Shapes.Replace("return x + x;", "return x + x + 1;"), cache);
                Assert.Equal(new[] { "CSV1002" }, broken.Errors("Twice"));
            }
            finally
            {
                File.Delete(cache);
            }
        }
    }
}
