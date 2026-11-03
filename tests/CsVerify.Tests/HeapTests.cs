using Xunit;

namespace CsVerify.Tests
{
    /// <summary>Mutable fields of source classes: maps from object to value, with an inferred frame per field.</summary>
    public class HeapTests
    {
        private const string Classes = @"
public sealed class Counter
{
    public int Count;
    public int Step { get; set; } = 1;
    public Counter(int start) { Spec.Requires(start >= 0); Spec.Ensures(Count == start && Step == 1); Count = start; }
    public void Tick() { Spec.Ensures(Count == Spec.Old(Count) + Step && Step == Spec.Old(Step)); Count = checked(Count + Step); }
}
public sealed class Other { public int X; public void Bump() { X++; } }
";

        private static string[] Errors(string method, string body) =>
            Harness.Verify(Classes + "public static class C { " + body + " }").Errors(method);

        [Fact]
        public void Constructors_AndMethods_UpdateFields()
        {
            var r = Harness.Verify(Classes);
            Assert.Empty(r.Errors("Counter..ctor"));
            Assert.Empty(r.Errors("Tick"));
            Assert.Empty(Errors("M", "static int M() { Spec.Ensures((int r) => r == 7); var c = new Counter(5); c.Tick(); c.Tick(); return c.Count; }"));
            Assert.Equal(new[] { "CSV1001" }, Errors("M", "static Counter M() => new Counter(-1);"));
        }

        [Fact]
        public void LibraryCalls_ChangeFieldsOnlyThroughUserCode()
        {
            // a dictionary holding Counters can run none of their code: their fields stay as they were
            const string dict = "System.Collections.Generic.Dictionary<string, Counter>";
            Assert.Empty(Errors("M", "static void M(" + dict + " d, Counter c) { int old = c.Count; d[\"k\"] = c; d.Remove(\"j\"); Spec.Assert(c.Count == old); }"));
            // a key whose Equals is user code: anything it writes may have changed
            Assert.Equal(new[] { "CSV1004" }, Harness.Verify(Classes +
                "public sealed class Key { public override bool Equals(object o) { return false; } public override int GetHashCode() => 0; } " +
                "public static class C { static void M(System.Collections.Generic.Dictionary<Key, int> d, Key k, Counter c) { int old = c.Count; d[k] = 1; Spec.Assert(c.Count == old); } }").Errors("M"));
            // a delegate may do anything
            Assert.Equal(new[] { "CSV1004" }, Errors("M", "static void M(System.Action a, Counter c) { int old = c.Count; a(); Spec.Assert(c.Count == old); }"));
            Assert.Equal(new[] { "CSV1004" }, Errors("M", "static void M(System.Action a, int[] x) { Spec.Requires(x.Length > 0); int old = x[0]; a(); Spec.Assert(x[0] == old); }"));
        }

        [Fact]
        public void NewArrays_AreInNoField()
        {
            const string box = "public sealed class Box { public int[] A = new int[0]; } ";
            Assert.Empty(Harness.Verify(box + "public static class C { static void M(Box b) { var n = new int[1]; Spec.Assert(n != b.A); } }").Errors("M"));
            Assert.Empty(Harness.Verify(box + "public static class C { static void M(Box b) { b.A = new int[1]; var n = new int[1]; Spec.Assert(n != b.A); } }").Errors("M"));
        }

        [Fact]
        public void LibraryCalls_DoNotWriteStrings()
        {
            // Debug.Assert takes the condition's text (a string): it writes no array
            Assert.Empty(Errors("M", "static void M(int[] a) { Spec.Requires(a.Length > 0); a[0] = 1; System.Diagnostics.Debug.Assert(a.Length > 0); Spec.Assert(a[0] == 1); }"));
            Assert.Equal(new[] { "CSV1004" }, Errors("M", "static void M(int[] a) { Spec.Requires(a.Length > 0); a[0] = 1; System.Array.Clear(a); Spec.Assert(a[0] == 1); }"));
        }

        [Fact]
        public void DataValues_ChangeNoState()
        {
            // building a data value (a record of a closed hierarchy) writes no field
            const string data = "public abstract record W { private W() { } public sealed record Nil() : W; public sealed record Cons(int H, W T) : W; } ";
            Assert.Empty(Harness.Verify(Classes + data + "public static class C { static W Make() => new W.Cons(1, new W.Nil()); " +
                "static void M(Counter c) { int old = c.Count; var w = Make(); Spec.Assert(c.Count == old); } }").Errors("M"));
        }

        [Fact]
        public void ReadingAnElement_IsNoWrite()
        {
            // !a[i], -a[i] and a[i]! read the element: a callee doing so writes no array
            const string callees = "static bool Not(bool[] b) => b.Length > 0 && !b[0]; static int Neg(int[] b) => b.Length > 0 ? -b[0] : 0; ";
            Assert.Empty(Errors("M", callees + "static void M(int[] a, bool[] b, int[] c) { Spec.Requires(a.Length > 0); a[0] = 1; Not(b); Neg(c); Spec.Assert(a[0] == 1); }"));
            Assert.Equal(new[] { "CSV1004" }, Errors("M", "static void Inc(int[] b) { if (b.Length > 0) b[0]++; } " +
                "static void M(int[] a, int[] c) { Spec.Requires(a.Length > 0); a[0] = 1; Inc(c); Spec.Assert(a[0] == 1); }"));
        }

        [Fact]
        public void Aliasing_IsTracked()
        {
            Assert.Empty(Errors("M", "static void M(Counter a, Counter b) { Spec.Requires(a != b); int old = b.Count; a.Count = 10; Spec.Assert(b.Count == old); }"));
            Assert.Equal(new[] { "CSV1004" }, Errors("M", "static void M(Counter a, Counter b) { int old = b.Count; a.Count = 10; Spec.Assert(b.Count == old); }"));
            Assert.Empty(Errors("M", "static void M(Counter a) { int old = a.Count; var b = new Counter(0); b.Count = 3; Spec.Assert(a.Count == old && b.Count == 3); }"));
        }

        [Fact]
        public void Calls_ChangeOnlyTheFieldsTheyWrite()
        {
            Assert.Empty(Errors("M", "static void M(Counter a, Other o) { int old = a.Count; o.Bump(); Spec.Assert(a.Count == old); }"));
            Assert.Equal(new[] { "CSV1004" }, Errors("M", "static void M(Counter a, Counter b) { int old = a.Count; b.Tick(); Spec.Assert(a.Count == old); }"));
            Assert.Empty(Errors("M", "static void M(Counter a, Counter b) { int old = a.Step; b.Tick(); Spec.Assert(a.Step == old); }"));
        }

        [Fact]
        public void Loops_ForgetOnlyTheFieldsTheyWrite() =>
            Assert.Empty(Errors("M", @"static int M(Counter c, int n) {
                Spec.Requires(n >= 0 && c.Step == 1);
                int s = c.Count;
                for (int i = 0; i < n; i++) { Spec.Invariant(0 <= i && i <= n && c.Count == s + i); c.Tick(); }
                Spec.Assert(c.Step == 1);
                return c.Count; }"));

        [Fact]
        public void FieldsAreMaybeNull_AndDereferencesAreChecked()
        {
            const string node = "public sealed class Node { public Node? Next; public int V; } public static class C { BODY }";
            Assert.Equal(new[] { "CSV1013" }, Harness.Verify(node.Replace("BODY", "static int M(Node n) => n.Next.V;")).Errors("M"));
            Assert.Empty(Harness.Verify(node.Replace("BODY", "static int M(Node n) => n.Next == null ? 0 : n.Next.V;")).Errors("M"));
        }

        [Fact]
        public void PureFunctions_ReadTheCurrentFields()
        {
            const string get = "[Pure] static int Get(Counter c) => c.Count; ";
            Assert.Empty(Errors("M", get + "static void M(Counter c) { int g = Get(c); c.Count = checked(g + 1); Spec.Assert(Get(c) == g + 1); }"));
            Assert.Equal(new[] { "CSV1004" }, Errors("M", get + "static void M(Counter c) { int g = Get(c); c.Count = checked(g + 1); Spec.Assert(Get(c) == g); }"));
            Assert.Empty(Errors("M", get + "static void M(Counter c, Other o) { int g = Get(c); o.Bump(); Spec.Assert(Get(c) == g); }"));
        }

        [Fact]
        public void PureFunctions_OverArrays_SeeArrayWrites()
        {
            // through a field: the function depends on the array heap, so a write makes it a new value
            Assert.Equal(new[] { "CSV1004" }, Harness.Verify(@"
public sealed class Box { public int[]? Items; [Pure] public int First() { Spec.Requires(Items != null && Items.Length > 0); return Items[0]; } }
public static class C { static void M(Box b) { Spec.Requires(b.Items != null && b.Items.Length > 0); int f = b.First(); b.Items[0] = checked(f + 1); Spec.Assert(b.First() == f); } }").Errors("M"));
            // through a parameter: only that array matters, so writing another one changes nothing
            Assert.Empty(Harness.Verify(@"
public static class C {
    [Pure] static int Head(int[] a) { Spec.Requires(a.Length > 0); return a[0]; }
    static void M(int[] a, int[] b) { Spec.Requires(a.Length > 0 && b.Length > 0 && a != b); int h = Head(a); b[0] = 7; Spec.Assert(Head(a) == h); }
    static void W(int[] a) { Spec.Requires(a.Length > 0); int h = Head(a); a[0] = checked(h + 1); Spec.Assert(Head(a) == h + 1); } }").Errors("M"));
        }

        [Fact]
        public void VirtualCalls_MayWriteAnything() =>
            Assert.Equal(new[] { "CSV1004" }, Harness.Verify(Classes + @"
public interface IAction { void Run(); }
public static class C { static void M(Counter a, IAction act) { int old = a.Count; act.Run(); Spec.Assert(a.Count == old); } }").Errors("M"));
    }
}
