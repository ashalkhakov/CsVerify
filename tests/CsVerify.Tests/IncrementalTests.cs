using System;
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
        public void TheState_IsNamedOnce_WhereAnExpressionReadsItAgain()
        {
            // (a contract that reads a list through an interface several times: each read is of the whole state, which the
            // expression names once instead of writing its every map out at each)
            var boogie = Path.Combine(Path.GetTempPath(), "csverify-state-" + Guid.NewGuid().ToString("N") + ".bpl");
            try
            {
                var r = Run(@"using System.Collections.Generic;
public static class Lists
{
    public static int First(IReadOnlyList<int> xs)
    {
        Spec.Requires(xs.Count >= 2 && xs[0] == 1 && xs[1] == 2);
        Spec.Ensures<int>(r => r == xs[0] && xs.Count >= 2 && xs[1] == 2);
        return xs[0];
    }
}", boogie: boogie);
                Assert.True(r.Errors("First").Length == 0, r.Explain("First"));
                var text = File.ReadAllText(boogie);
                Assert.Contains("(var $stNow := $st(", text);
                // (its maps written out a few times in the procedure, not once a read)
                var procedure = text.Substring(text.IndexOf("procedure Lists.First", StringComparison.Ordinal));
                Assert.True(System.Text.RegularExpressions.Regex.Matches(procedure, @"\$stNow\b").Count > System.Text.RegularExpressions.Regex.Matches(procedure, @"\$st\(").Count);
            }
            finally
            {
                File.Delete(boogie);
            }
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
        public void TheState_IsLinearInTheMaps()
        {
            // (#123: a count of an interface's collection takes the state, every map; declared as n projection axioms of
            // n binders each, the program was quadratic in the fields; one axiom with a let is linear)
            var fields = string.Concat(Enumerable.Range(0, 40).Select(i => $"    public int F{i};\n"));
            var bpl = Path.GetTempFileName();
            try
            {
                var r = Run("public sealed class Row\n{\n" + fields + "}\n" + @"
public static class Counts
{
    public static int N(System.Collections.Generic.IReadOnlyCollection<int> xs) { Spec.Requires(xs != null); Spec.Ensures<int>(r => r >= 0); return xs.Count; }
    public static int Wrong(System.Collections.Generic.IReadOnlyCollection<int> xs) { Spec.Requires(xs != null); Spec.Ensures<int>(r => r > 0); return xs.Count; }
    public static int Same(System.Collections.Generic.IReadOnlyCollection<int> xs, Row row)
    {
        Spec.Requires(xs != null && row != null);
        Spec.Ensures<int>(r => r == 0);
        var a = xs.Count;
        row.F7 = 1;
        var b = xs.Count;
        return 0;
    }
}", boogie: bpl);
                Assert.True(r.Errors("N").Length == 0, r.Explain("N"));
                Assert.Equal(new[] { "CSV1002" }, r.Errors("Wrong"));
                Assert.True(r.Errors("Same").Length == 0, r.Explain("Same"));
                var text = File.ReadAllText(bpl);
                Assert.Contains("$ocount(", text);
                Assert.DoesNotContain("datatype St", text);
                Assert.Single(System.Text.RegularExpressions.Regex.Matches(text, @"\{ \$st\("));
                Assert.True(text.Length < 2_000_000, $"{text.Length} characters of Boogie");
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
        public void AMethodNotSelected_ThatReachesAnEmptyArray_ChangesNoField()
        {
            // (a method not selected is its contract and what the effects analysis says it writes: Array.Empty<T>(),
            // the same array each time, runs nothing of T's, so it writes no field)
            const string desk = @"using System.Collections.Generic;
public abstract record Answer<T>
{
    private Answer() { }
    public static Answer<T> Nothing() { Spec.Ensures<Answer<T>>(r => r is Listed l && l.Items.Count == 0); return new Listed(Array.Empty<T>()); }
    public sealed record Listed(IReadOnlyList<T> Items) : Answer<T>;
}
public sealed record Note(string Text);
public sealed record Ticket(string Value);
public sealed class Desk
{
    public int Served { get; private set; }
    public Ticket? Held { get; private set; }
    public void Reset() { Served = 0; Held = null; }
    public Answer<Note> Idle() { Spec.Ensures<Answer<Note>>(r => r is Answer<Note>.Listed l && l.Items.Count == 0); return Answer<Note>.Nothing(); }
}
public static class Use
{
    public static Answer<Note> Ask(Desk d) { Spec.Ensures<Answer<Note>>(r => d.Served == Spec.Old(d.Served) && d.Held == Spec.Old(d.Held)); return d.Idle(); }
    public static bool Same(Desk d, Ticket asked)
    {
        Spec.Ensures<bool>(r => !r || d.Held == asked);
        if (d.Held is not { } known) { return false; }
        if (known != asked) { return false; }
        var none = d.Idle();
        return true;
    }
    public static void Wrong(Desk d) { Spec.Ensures(d.Served == Spec.Old(d.Served)); d.Reset(); }
}";
            var r = Run(desk, only: "Use.");
            Assert.True(r.Errors("Ask").Length == 0, r.Explain("Ask"));
            Assert.True(r.Errors("Same").Length == 0, r.Explain("Same"));
            Assert.Equal(new[] { "CSV1002" }, r.Errors("Wrong"));
        }

        [Fact]
        public void AMethodNotSelected_ThatRunsAQuery_WritesWhatItsLambdasWrite()
        {
            // (a library member is judged by what each call hands it: it runs the lambdas and the methods it is handed,
            // so what they write, it writes; a query made where it is handed on, a list interface and a record that
            // only compares its fields hand over nothing more. A sequence that came from elsewhere may run anything)
            const string routes = @"using System.Collections.Generic; using System.Linq;
public sealed record Tag { public Tag(string v) { Value = v; } public string Value { get; } public override string ToString() => Value; }
public sealed record Leg(Tag Carrier, int Miles);
public enum Mark { Late, Lost }
public sealed class Route
{
    private readonly List<Leg> legs = new();
    private string? marks;
    public int State { get; private set; }
    public int Seen { get; private set; }
    public IReadOnlyCollection<Mark> Marks => (marks ?? string.Empty).Split(',').Select(Enum.Parse<Mark>).ToHashSet();
    private int Unknown(IReadOnlyList<Leg> offered) { var known = legs.Select(l => l.Carrier).ToHashSet(); return offered.Where(l => !known.Contains(l.Carrier)).DistinctBy(l => l.Carrier).ToList().Count; }
    private bool Marked(Mark m) { return Marks.Contains(m); }
    private int Counting(List<int> xs) { return xs.Where(x => { Seen = x; return x > 1; }).ToList().Count; }
    private int Lazy(IEnumerable<int> xs) { return xs.Where(x => x > 1).ToList().Count; }
    public int Offer(IReadOnlyList<Leg> offered) { Spec.Ensures<int>(r => State == Spec.Old(State) && Seen == Spec.Old(Seen)); return Unknown(offered); }
    public bool Check(Mark m) { Spec.Ensures<bool>(r => State == Spec.Old(State)); return Marked(m); }
    public int Tally(List<int> xs) { Spec.Ensures<int>(r => State == Spec.Old(State)); return Counting(xs); }
    public int Overlooked(List<int> xs) { Spec.Ensures<int>(r => Seen == Spec.Old(Seen)); return Counting(xs); }
    public int Trusted(IEnumerable<int> xs) { Spec.Ensures<int>(r => Seen == Spec.Old(Seen)); return Lazy(xs); }
}";
            var r = Run(routes, only: new[] { "Route.Offer", "Route.Check", "Route.Tally", "Route.Overlooked", "Route.Trusted" });
            foreach (var ok in new[] { "Offer", "Check", "Tally" })
            {
                Assert.True(r.Errors(ok).Length == 0, r.Explain(ok));
            }
            Assert.Equal(new[] { "CSV1002" }, r.Errors("Overlooked"));
            Assert.Equal(new[] { "CSV1002" }, r.Errors("Trusted"));
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
