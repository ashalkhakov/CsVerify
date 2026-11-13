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
        // what a library calls it with: each element, when it changes neither the list nor an array
        [InlineData(C + "static void M(List<int> l) { Spec.Requires(Spec.Forall(0, l.Count, i => l[i] > 0)); l.ForEach(x => { Spec.Requires(x > 0); }); } }")]
        [InlineData(C + "static void M(int[] a) { Spec.Requires(Spec.Forall(0, a.Length, i => a[i] != 0)); var b = Array.Exists(a, x => { Spec.Requires(x != 0); return 10 / x > 1; }); } }")]
        [InlineData(C + "static void M(int[] a) { Spec.Requires(Spec.Forall(0, a.Length, i => a[i] != 0)); var b = a.Any(x => { Spec.Requires(x != 0); return 10 / x > 1; }); } }")]
        [InlineData(C + "static void M(int[] a) { Spec.Requires(Spec.Forall(0, a.Length, i => a[i] != 0)); var c = a.Count(x => { Spec.Requires(x != 0); return 10 / x > 1; }); } }")]
        [InlineData(C + "static void M(List<string> l) { Spec.Requires(Spec.Forall(0, l.Count, i => l[i] != null)); var n = l.FindIndex(s => { Spec.Requires(s != null); return s.Length == 1; }); } }")]
        // each index, for Parallel.For
        [InlineData(C + "static void M(int n) { Spec.Requires(n >= 0); Parallel.For(0, n, i => { Spec.Requires(0 <= i && i < n); }); } }")]
        // no arguments: total is its precondition now
        [InlineData(C + "static void M(int k) { Spec.Requires(k > 0); Task.Run(() => { Spec.Requires(k > 0); }).Wait(); } }")]
        // a stub that says what it needs of the delegate
        [InlineData("[ContractsFor(typeof(Lazy<>))] public static class LazyContracts<T> { public static Lazy<T> @new(Func<T> valueFactory) { Spec.Requires(Spec.Pre(valueFactory)); throw null!; } } " +
                    C + "static void M(int k) { Spec.Requires(k > 0); var l = new Lazy<int>(() => { Spec.Requires(k > 0); return k; }); } }")]
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
        [InlineData("CSV1029", C + "static void M(Action work) { Task.Run(work).Wait(); } }")]
        [InlineData("CSV1029", C + "static void M(Action<int> a, List<int> l) { Spec.Requires(Spec.Pre(a, 1)); l.ForEach(a); } }")]
        [InlineData("CSV1001", C + "static void M(List<int> l) { l.ForEach(x => { Spec.Requires(x > 0); }); } }")]
        [InlineData("CSV1001", C + "static void M(int n) { Spec.Requires(n >= 0 && n < 100); Parallel.For(0, n + 1, i => { Spec.Requires(i < n); }); } }")]
        [InlineData("CSV1001", "[ContractsFor(typeof(Lazy<>))] public static class LazyContracts<T> { public static Lazy<T> @new(Func<T> valueFactory) { Spec.Requires(Spec.Pre(valueFactory)); throw null!; } } " +
                               C + "static void M(int k) { var l = new Lazy<int>(() => { Spec.Requires(k > 0); return k; }); } }")]
        // a lambda that may change the list: what it is called with could be anything it put there
        [InlineData("CSV1029", C + "static void M(List<int> l) { Spec.Requires(Spec.Forall(0, l.Count, i => l[i] > 0)); var b = l.Exists(x => { Spec.Requires(x > 0); l.Add(0); return x > 1; }); } }")]
        // a lazy query, a lambda that may change the array, nothing known of the arguments: total
        [InlineData("CSV1029", C + "static void M(int[] a) { Spec.Requires(Spec.Forall(0, a.Length, i => a[i] != 0)); var b = a.Where(x => { Spec.Requires(x != 0); return 10 / x > 1; }).ToList(); } }")]
        [InlineData("CSV1029", C + "static void M(int[] a) { Spec.Requires(a.Length > 0 && Spec.Forall(0, a.Length, i => a[i] != 0)); Array.ForEach(a, x => { Spec.Requires(x != 0); a[0] = 0; }); } }")]
        [InlineData("CSV1029", C + "static void M(int k) { Task.Run(() => { Spec.Requires(k > 0); }).Wait(); } }")]
        // a precondition that reads state can't be a Spec.Pre
        [InlineData("CSV1029", C + "static int Field; static void M() { Func<int, int> h = x => { Spec.Requires(x < Field); return x; }; } }")]
        public void Reported(string id, string code) => Assert.Contains(id, Ids(code));

        // a library member that only reads changes what the code it runs changes: a lambda in sight that writes none keeps them
        [Theory]
        [InlineData(C + "static void M(int[] a) { Spec.Requires(Spec.Forall(0, a.Length, i => a[i] != 0)); var b = a.Any(x => { Spec.Requires(x != 0); return 10 / x > 1; }); var c = a.Count(x => { Spec.Requires(x != 0); return 10 / x > 1; }); } }")]
        [InlineData(C + "static void M(int[] a, Cell c) { Spec.Requires(a.Length > 0); a[0] = 5; c.V = 3; var b = Array.Exists(a, x => x > 1); Spec.Assert(a[0] == 5); Spec.Assert(c.V == 3); } }")]
        [InlineData(C + "static void M(List<int> l, int[] a) { Spec.Requires(a.Length > 0 && l.Count > 0); a[0] = 5; var n = l.FindIndex(x => x > 2); Spec.Assert(a[0] == 5); Spec.Assert(l.Count > 0); } }")]
        public void ReadOnlyLibrary_Keeps(string code) => Assert.Empty(All(code));

        [Theory]
        // the lambda writes an array; the delegate's code isn't in sight; the member writes what it's given
        [InlineData(C + "static void M(int[] a, int[] other) { Spec.Requires(other.Length > 0 && a.Length > 0); a[0] = 5; var b = Array.Exists(other, x => { other[0] = 1; return x > 1; }); Spec.Assert(a[0] == 5); } }")]
        [InlineData(C + "static void M(int[] a, Predicate<int> p) { Spec.Requires(Spec.Total(p) && a.Length > 0); a[0] = 5; var b = Array.Exists(a, p); Spec.Assert(a[0] == 5); } }")]
        [InlineData(C + "static void M(int[] a) { Spec.Requires(a.Length > 0); a[0] = 5; Array.Sort(a, (x, y) => x < y ? -1 : x > y ? 1 : 0); Spec.Assert(a[0] == 5); } }")]
        [InlineData(C + "static void M(int[] a, Cell c) { Spec.Requires(a.Length > 0); c.V = 3; var b = Array.Exists(a, x => { c.V = 4; return x > 1; }); Spec.Assert(c.V == 3); } }")]
        public void ReadOnlyLibrary_Forgets(string code) => Assert.Contains("CSV1004", Ids(code));

        // what a delegate may change: Spec.ChangesNothing, Spec.Changes(f, x => frame), a lambda's own Spec.Modifies
        [Theory]
        [InlineData(C + "static void M(int[] a, Predicate<int> p) { Spec.Requires(Spec.Total(p) && Spec.ChangesNothing(p) && a.Length > 0); a[0] = 5; var b = Array.Exists(a, p); Spec.Assert(a[0] == 5); } }")]
        [InlineData(C + "static void M(Cell c, Func<int, int> g) { Spec.Requires(Spec.Total(g) && Spec.ChangesNothing(g)); c.V = 3; var r = g(1); Spec.Assert(c.V == 3); } }")]
        [InlineData(C + "static void M(Cell c, Cell d, Action<Cell> g) { Spec.Requires(Spec.Total(g) && Spec.Changes(g, x => ObjSet.Of(x))); Spec.Requires(c != d); c.V = 3; d.V = 4; g(d); Spec.Assert(c.V == 3); } }")]
        [InlineData(C + "static void M(int[] a, int[] b, Action<int[]> g) { Spec.Requires(Spec.Total(g) && Spec.Changes(g, x => ObjSet.Of(x))); Spec.Requires(a != b && a.Length > 0); a[0] = 5; g(b); Spec.Assert(a[0] == 5); } }")]
        // given lambdas: one that writes nothing, one within its own Spec.Modifies
        [InlineData(C + "static void N(Cell c, Func<int, int> g) { Spec.Requires(Spec.Total(g) && Spec.ChangesNothing(g)); } static void P(Action<Cell> g) { Spec.Requires(Spec.Total(g) && Spec.Changes(g, x => ObjSet.Of(x))); } " +
                    "static void M() { N(new Cell(), x => x); P(x => { Spec.Modifies(ObjSet.Of(x)); x.V = 1; }); P(x => { }); } }")]
        public void Frames_Proved(string code) => Assert.Empty(All(code));

        [Theory]
        // nothing said: anything may change
        [InlineData("CSV1004", C + "static void M(Cell c, Func<int, int> g) { Spec.Requires(Spec.Total(g)); c.V = 3; var r = g(1); Spec.Assert(c.V == 3); } }")]
        // the frame has it
        [InlineData("CSV1004", C + "static void M(Cell c, Action<Cell> g) { Spec.Requires(Spec.Total(g) && Spec.Changes(g, x => ObjSet.Of(x))); c.V = 3; g(c); Spec.Assert(c.V == 3); } }")]
        // a lambda that writes isn't one that changes nothing; nor one outside its own frame
        [InlineData("CSV1001", C + "static void N(Cell c, Func<int, int> g) { Spec.Requires(Spec.Total(g) && Spec.ChangesNothing(g)); } static void M() { var c = new Cell(); N(c, x => { c.V = 9; return x; }); } }")]
        [InlineData("CSV1001", C + "static void P(Action<Cell> g) { Spec.Requires(Spec.Total(g) && Spec.Changes(g, x => ObjSet.Of(x))); } static void M() { var c = new Cell(); P(x => { c.V = 1; }); } }")]
        [InlineData("CSV1017", C + "static void M() { var c = new Cell(); Action<Cell> h = x => { Spec.Modifies(ObjSet.Of(x)); c.V = 1; }; } }")]
        public void Frames_Reported(string id, string code) => Assert.Contains(id, Ids(code));

        // reads frames: a precondition of state, kept while what it reads is
        private const string Lim = "Func<int, int> h = x => { Spec.Reads(ObjSet.Of(lim)); Spec.Requires(x < lim.V); return x; }; ";
        private const string ApplyR = "static int Apply(Func<int, int> g, Cell c, Cell d, int x) { Spec.Requires(Spec.Reads(g, y => ObjSet.Of(c))); Spec.Requires(Spec.Pre(g, x) && c != d); d.V = 7; return g(x); } ";

        [Theory]
        [InlineData(C + "static void M(Cell lim) { lim.V = 10; " + Lim + "var a = h(3); } }")]
        [InlineData(C + "static void M(Cell lim, Cell other) { Spec.Requires(lim != other); lim.V = 10; " + Lim + "var a = h(3); other.V = 0; var b = h(4); } }")]
        [InlineData(C + "static void M(int[] a, int[] b) { Spec.Requires(a.Length > 0 && b.Length > 0 && a != b); b[0] = 5; Func<int, int> h = i => { Spec.Reads(ObjSet.Of(b)); Spec.Requires(0 <= i && i < b.Length && b[i] > 0); return 10 / b[i]; }; a[0] = 1; var r = h(0); } }")]
        [InlineData(C + ApplyR + "static void M(Cell lim, Cell d) { Spec.Requires(lim != d); lim.V = 10; var r = Apply(x => { Spec.Reads(ObjSet.Of(lim)); Spec.Requires(x < lim.V); return x; }, lim, d, 3); } }")]
        [InlineData(C + "static void M(int[] a) { Spec.Requires(a.Length > 2); a[0] = 5; Func<int, int> h = i => { Spec.Reads(ObjSet.Of(a)); Spec.Requires(0 <= i && i < a.Length && a[i] > 0); return 10 / a[i]; }; var r = h(0); } }")]
        public void Reads_Proved(string code) => Assert.Empty(All(code));

        [Theory]
        // what it reads changed
        [InlineData("CSV1001", C + "static void M(Cell lim) { lim.V = 10; " + Lim + "lim.V = 2; var c = h(5); } }")]
        [InlineData("CSV1001", C + "static void M(Cell lim, Cell other) { lim.V = 10; " + Lim + "other.V = 0; var b = h(4); } }")]
        // no frame, or reading outside it
        [InlineData("CSV1029", C + "static void M(Cell lim) { Func<int, int> h = x => { Spec.Requires(x < lim.V); return x; }; } }")]
        [InlineData("CSV1029", C + "static void M(Cell lim, Cell o) { Func<int, int> h = x => { Spec.Reads(ObjSet.Of(lim)); Spec.Requires(x < o.V); return x; }; } }")]
        // a callee that takes it to be steady
        [InlineData("CSV1001", C + "static int ApplyS(Func<int, int> g, int x) { Spec.Requires(Spec.Pre(g, x)); return g(x); } static void M(Cell lim) { lim.V = 10; var r = ApplyS(x => { Spec.Reads(ObjSet.Of(lim)); Spec.Requires(x < lim.V); return x; }, 3); } }")]
        // a callee that changes what it reads
        [InlineData("CSV1001", C + "static int Apply(Func<int, int> g, Cell c, int x) { Spec.Requires(Spec.Reads(g, y => ObjSet.Of(c))); Spec.Requires(Spec.Pre(g, x)); c.V = 0; return g(x); } } ")]
        public void Reads_Reported(string id, string code) => Assert.Contains(id, Ids(code));

        // Dafny's f.reads(x): Spec.ReadsOf, so a method takes any delegate that reads state, and says what it mustn't read
        private const string MR = "static int M(Func<int, int> g, int[] a) { Spec.Requires(Spec.Pre(g, 0) && a.Length > 0); Spec.Requires(Spec.ReadsOf(g, 0).IsDisjointFrom(ObjSet.Of(a))); a[0] = 1; return g(0); } ";
        private const string ReadsB = "i => { Spec.Reads(ObjSet.Of(b)); Spec.Requires(b.Length > 0 && b[0] > 0); return 10 / b[0]; }";

        [Theory]
        [InlineData(C + MR + "static void N(int[] a, int[] b) { Spec.Requires(a.Length > 0 && b.Length > 0 && a != b); b[0] = 5; var r = M(" + ReadsB + ", a); } }")]
        [InlineData(C + MR + "static void N(int[] a) { Spec.Requires(a.Length > 0); var r = M(i => i, a); } }")]
        // what it gives, of state: its value, and what it ensures if it changes nothing
        [InlineData(C + "static void N(Cell c, Cell other) { Spec.Requires(c != other); c.V = 7; Func<int, int> h = x => { Spec.Reads(ObjSet.Of(c)); Spec.Requires(c.V > 0 && c.V < 100); return x < 100 && x > -100 ? x + c.V : 0; }; other.V = 1; var r = h(1); Spec.Assert(r == 8); } }")]
        [InlineData(C + "static void N(Cell c) { c.V = 7; Func<int, int> h = x => { Spec.Reads(ObjSet.Of(c)); Spec.Requires(c.V > 0); Spec.Ensures<int>(r => r == c.V); return c.V; }; var r = h(1); Spec.Assert(r == 7); } }")]
        public void ReadsOf_Proved(string code) => Assert.Empty(All(code));

        [Theory]
        // it may read what the method writes
        [InlineData("CSV1001", C + "static int M(Func<int, int> g, int[] a) { Spec.Requires(Spec.Pre(g, 0) && Spec.ReadsOf(g, 0).IsSubsetOf(ObjSet.Of(a)) && a.Length > 0); a[0] = 1; return g(0); } } ")]
        [InlineData("CSV1001", C + MR + "static void N(int[] b) { Spec.Requires(b.Length > 0); b[0] = 5; var r = M(" + ReadsB + ", b); } }")]
        // what it gives changed with what it reads
        [InlineData("CSV1004", C + "static void N(Cell c) { c.V = 7; Func<int, int> h = x => { Spec.Reads(ObjSet.Of(c)); Spec.Requires(c.V > 0 && c.V < 100); return x < 100 && x > -100 ? x + c.V : 0; }; c.V = 8; var r = h(1); Spec.Assert(r == 8); } }")]
        // a lambda that writes: what it ensures of state isn't kept; one that reads outside its frame gives no value
        [InlineData("CSV1004", C + "static void N(Cell c, Cell d) { c.V = 7; Func<int, int> h = x => { Spec.Reads(ObjSet.Of(c)); Spec.Requires(c.V > 0); Spec.Ensures<int>(r => r == c.V); d.V = 0; return c.V; }; var r = h(1); Spec.Assert(r == 7); } }")]
        [InlineData("CSV1004", C + "static void N(Cell c, Cell d) { c.V = 7; d.V = 1; Func<int, int> h = x => { Spec.Reads(ObjSet.Of(c)); Spec.Requires(c.V > 0); return d.V; }; var r = h(1); Spec.Assert(r == 1); } }")]
        public void ReadsOf_Reported(string id, string code) => Assert.Contains(id, Ids(code));

        // (Spec.Total of a delegate that reads state: it accepts every argument in this state)
        [Fact]
        public void Total_OfADelegateThatReadsState() => Assert.Empty(Ids(C + "static int M(Cell c) { Spec.Requires(c != null); " +
            "Func<int, int> f = x => { Spec.Reads(ObjSet.Of(c)); return c.V; }; Spec.Assert(Spec.Total(f)); return 0; } }"));

        [Fact]
        public void Total_OfADelegateThatReadsState_WithAPrecondition() => Assert.Contains("CSV1004", Ids(C + "static int M(Cell c) { Spec.Requires(c != null && c.V > 0); " +
            "Func<int, int> f = x => { Spec.Reads(ObjSet.Of(c)); Spec.Requires(x < c.V); return c.V; }; Spec.Assert(Spec.Total(f)); return 0; } }"));

        // (under Spec.Modifies: a lambda that changes nothing is called freely; one that may change anything breaks the frame)
        [Fact]
        public void Lambdas_UnderSpecModifies() => Assert.Empty(Ids(C + "static int M(Cell c) { Spec.Requires(c != null); Spec.Modifies(ObjSet.Of(c)); c.V = 1; " +
            "Func<int, int> f = x => { Spec.Requires(x < 100); return x + 1; }; return f(2); } }"));

        [Fact]
        public void Lambdas_UnderSpecModifies_ThatMayWriteAnything() => Assert.Contains("CSV1017", Ids(C + "static void M(Cell c, Cell d) { Spec.Requires(c != null && d != null); " +
            "Spec.Modifies(ObjSet.Of(c)); Action a = () => { d.V = 5; }; a(); } }"));

        // (a generic method's group, Twice<int>: its contract, its T's values boxed)
        private const string Generic = "public static class G { public static int Twice<T>(T x, int n) { Spec.Requires(n >= 0 && n < 100); Spec.Ensures<int>(r => r == 2 * n); return 2 * n; } } ";

        [Fact]
        public void GenericMethodGroup_HasItsContract() => Assert.Empty(Ids(Generic + C + "static int M() { Spec.Ensures<int>(r => r == 6); Func<int, int, int> f = G.Twice<int>; return f(7, 3); } }"));

        [Theory]
        [InlineData("CSV1002", C + "static int M() { Spec.Ensures<int>(r => r == 7); Func<int, int, int> f = G.Twice<int>; return f(7, 3); } }")]
        [InlineData("CSV1001", C + "static int M() { Func<string, int, int> f = G.Twice<string>; return f(\"a\", 300); } }")]
        public void GenericMethodGroup_Reported(string id, string code) => Assert.Contains(id, Ids(Generic + code));

        // (o.M as a delegate: o evaluated where it's made, M's contract the delegate's)
        private const string Doubler = "public sealed class Dbl { public Dbl() { } public int Twice(int x) { Spec.Requires(x >= 0 && x < 100); Spec.Ensures<int>(r => r == 2 * x); return 2 * x; } } ";

        [Fact]
        public void InstanceMethodGroup_HasItsContract() => Assert.Empty(Ids(Doubler + C + "static int M(Dbl a) { Spec.Requires(a != null); Spec.Ensures<int>(r => r == 6); Func<int, int> f = a.Twice; return f(3); } }"));

        [Theory]
        [InlineData("CSV1002", C + "static int M(Dbl a) { Spec.Requires(a != null); Spec.Ensures<int>(r => r == 7); Func<int, int> f = a.Twice; return f(3); } }")]
        [InlineData("CSV1001", C + "static int M(Dbl a) { Spec.Requires(a != null); Func<int, int> f = a.Twice; return f(300); } }")]
        [InlineData("CSV1013", C + "static int M(Dbl? a) { Func<int, int> f = a!.Twice; return 0; } }")]
        public void InstanceMethodGroup_Reported(string id, string code) => Assert.Contains(id, Ids(Doubler + code));
    }
}
