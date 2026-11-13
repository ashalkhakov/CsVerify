using System.Linq;
using CsVerify.Verifier;
using Xunit;

namespace CsVerify.Tests
{
    /// <summary>
    /// Language that applications use everywhere: Nullable&lt;T&gt;, interpolated strings, property, list and positional
    /// patterns, with on structs, struct members passed by reference; check profiles; the reasons null diagnostics give.
    /// </summary>
    public class CoverageTests
    {
        // ------------------------------------------------------------------------------------------ Nullable<T>

        [Fact]
        public void Nullable_WrapsUnwrapsAndTests()
        {
            var r = Harness.Verify(@"
public static class P
{
    public static int Coalesce(int? x) { Spec.Ensures<int>(r => x == null ? r == 0 : r == x); return x ?? 0; }
    public static int HasValue(int? x) { Spec.Ensures<int>(r => x == null ? r == -1 : r == x); return x.HasValue ? x.Value : -1; }
    public static int Is(int? x) { Spec.Ensures<int>(r => x == null ? r == -1 : r == x); return x is int v ? v : -1; }
    public static int OrDefault(int? x) { Spec.Ensures<int>(r => x != null || r == 5); return x.GetValueOrDefault(5); }
    public static int? Wrap(int x) { Spec.Ensures<int?>(r => r != null && r == x); return x; }
    public static int? None() { Spec.Ensures<int?>(r => r == null); return null; }
    public static long? Widen(int? x) { Spec.Ensures<long?>(r => (r == null) == (x == null)); return x; }
    public static bool Patterns(int? x) { Spec.Ensures<bool>(r => r == (x != null && 0 < x && x < 10)); return x is > 0 and < 10; }
    public static bool IsNull(int? x) { Spec.Ensures<bool>(r => r == (x == null)); return x is null; }
}");
            Assert.True(r.Success, string.Join("\n", r.Diagnostics));
        }

        [Fact]
        public void Nullable_LiftedOperators_AsCSharpDefinesThem()
        {
            var r = Harness.Verify(@"
public static class P
{
    public static int? Add(int? x, int? y)
    {
        Spec.Requires(x == null || y == null || -1000 < x && x < 1000 && -1000 < y && y < 1000);
        Spec.Ensures<int?>(r => (r == null) == (x == null || y == null));
        return x + y;
    }
    public static bool Less(int? x, int y) { Spec.Ensures<bool>(r => r == (x != null && x < y)); return x < y; }
    public static bool Equal(int? x, int? y) { Spec.Ensures<bool>(r => !(x == null && y == null) || r); return x == y; }
    public static int? Overflows(int? x) => x + 1;
}");
            Assert.Empty(r.Errors("Add"));
            Assert.Empty(r.Errors("Less"));
            Assert.Empty(r.Errors("Equal"));
            Assert.Equal(new[] { "CSV1010" }, r.Errors("Overflows"));
        }

        [Fact]
        public void Nullable_ValueOfNull_IsAnError_AndIsNullIsNotFalse()
        {
            var r = Harness.Verify(@"
public static class P
{
    public static int Value(int? x) => x.Value;
    public static int Cast(int? x) => (int)x;
    public static int Checked(int? x) => x.HasValue ? x.Value : 0;
    // (x is null on an int? was once taken to be false)
    public static int NotFalse(int? x) { Spec.Ensures<int>(r => r == 1); return x is null ? 0 : 1; }
}");
            Assert.Equal(new[] { "CSV1013" }, r.Errors("Value"));
            Assert.Equal(new[] { "CSV1013" }, r.Errors("Cast"));
            Assert.Empty(r.Errors("Checked"));
            Assert.Equal(new[] { "CSV1002" }, r.Errors("NotFalse"));
        }

        // ----------------------------------------------------------------------------------------- the rest

        [Fact]
        public void InterpolatedStrings_AreStringsThatAreNotNull_WithTheirHolesChecked()
        {
            var r = Harness.Verify(@"
public static class P
{
    public static string Show(int a, string b) => $""{a} and {b,5}"";
    public static string Hole(int[] a) => $""first: {a[0]}"";
}");
            Assert.Empty(r.Errors("Show"));
            Assert.Equal(new[] { "CSV1003" }, r.Errors("Hole"));
        }

        [Fact]
        public void Patterns_Property_List_AndPositional()
        {
            var r = Harness.Verify(@"
public sealed class Person { public int Age; public Person(int age) { Age = age; } }
public static class P
{
    public static bool Adult(Person? p) { Spec.Ensures<bool>(r => r == (p != null && p.Age >= 18)); return p is { Age: >= 18 }; }
    public static bool NotNull(Person? p) { Spec.Ensures<bool>(r => r == (p != null)); return p is { }; }
    public static bool Starts(int[] a)
    {
        Spec.Ensures<bool>(r => r == (a.Length >= 2 && a[0] == 1 && a[a.Length - 1] == 9));
        return a is [1, .., 9];
    }
    public static bool Exactly(int[] a) { Spec.Ensures<bool>(r => r == (a.Length == 2 && a[1] == 0)); return a is [_, 0]; }
    public static int Tuple((int, int) t) { Spec.Ensures<int>(r => t.Item1 == 0 ? r == t.Item2 : r == t.Item1); return t switch { (0, var y) => y, (var x, _) => x }; }
}");
            Assert.True(r.Success, string.Join("\n", r.Diagnostics));
        }

        // (.. var rest: a new array of the elements between)
        [Fact]
        public void Patterns_SliceWithAPatternOfItsOwn()
        {
            var r = Harness.Verify(@"
public static class P
{
    public static int Rest(int[] a) { Spec.Requires(a != null); if (a is [1, .. var rest, 9]) { Spec.Assert(rest.Length == a.Length - 2 && (rest.Length == 0 || rest[0] == a[1])); return rest.Length; } return -1; }
    public static bool Nested(int[] a) { Spec.Requires(a != null); Spec.Ensures<bool>(r => !r || a.Length >= 3 && a[1] == 2); return a is [_, .. [2, ..], _]; }
    public static int Wrong(int[] a) { Spec.Requires(a != null); if (a is [1, .. var rest]) { Spec.Assert(rest.Length == a.Length); return 0; } return -1; }
}");
            Assert.Empty(r.Errors("Rest"));
            Assert.Empty(r.Errors("Nested"));
            Assert.Equal(new[] { "CSV1004" }, r.Errors("Wrong"));
        }

        // (a is [1, ..] b: b is the array matched)
        [Fact]
        public void Patterns_ListThatDeclaresItsValue()
        {
            var r = Harness.Verify(@"
public static class P
{
    public static int Whole(int[] a) { Spec.Requires(a != null); if (a is [1, ..] b) { Spec.Assert(b == a && b[0] == 1); return b.Length; } return 0; }
    public static int Wrong(int[] a) { Spec.Requires(a != null); if (a is [1, ..] b) { Spec.Assert(b[0] == 2); return b.Length; } return 0; }
}");
            Assert.Empty(r.Errors("Whole"));
            Assert.Equal(new[] { "CSV1004" }, r.Errors("Wrong"));
        }

        [Fact]
        public void With_OnAStruct_CopiesIt()
        {
            var r = Harness.Verify(@"
public struct Point { public int X; public int Y; }
public static class P
{
    public static int Copy(Point p) { Spec.Ensures<int>(r => r == 5); var q = p with { X = 5 }; return q.X; }
    public static int Keeps(Point p) { Spec.Ensures<int>(r => r == p.X); var q = p with { X = 5 }; return p.X; }
    // (with once wrote its source as well)
    public static int Wrong(Point p) { Spec.Ensures<int>(r => r == 5); var q = p with { X = 5 }; return p.X; }
}");
            Assert.Empty(r.Errors("Copy"));
            Assert.Empty(r.Errors("Keeps"));
            Assert.Equal(new[] { "CSV1002" }, r.Errors("Wrong"));
        }

        [Fact]
        public void StructMembers_ByReference_AreWrittenBack()
        {
            var r = Harness.Verify(@"
public struct H { public int A; public int B; }
public static class P
{
    private static void Set(out int x) { x = 7; Spec.Ensures(x == 7); }
    public static int Cell(H[] hs) { Spec.Requires(hs.Length > 0); Spec.Ensures<int>(r => r == 7); Set(out hs[0].A); return hs[0].A; }
    public static int Other(H[] hs) { Spec.Requires(hs.Length > 0); Spec.Ensures<int>(r => r == Spec.Old(hs[0].B)); Set(out hs[0].A); return hs[0].B; }
    public static int Local() { Spec.Ensures<int>(r => r == 7); var h = new H(); Set(out h.A); return h.A; }
    // a callee that may touch arrays could see the cell: not supported
    private static void Fill(int[] a, out int x) { x = a.Length > 0 ? a[0] : 0; }
    public static void Lent(H[] hs, int[] a) { Spec.Requires(hs.Length > 0); Fill(a, out hs[0].A); }
}");
            Assert.Empty(r.Errors("Cell"));
            Assert.Empty(r.Errors("Other"));
            Assert.Empty(r.Errors("Local"));
            Assert.Contains("CSV1901", r.Errors("Lent"));
        }

        // ------------------------------------------------------------------------------------- check profiles

        private static VerificationResult VerifyWith(string source, string checks) =>
            Engine.VerifySources(new[] { ("Test.cs", "using System; using CsVerify;\n" + source) },
                new VerifierOptions { CheckKinds = checks == null ? null : Checks.Parse(checks) });

        [Fact]
        public void Checks_ProveOnlyTheirKinds_AndAssumeTheRest()
        {
            const string source = @"
public static class P
{
    public static int Mixed(string? s, int[] a, int x) => s.Length + a[x] + (x + 1);
}";
            var all = VerifyWith(source, null);
            Assert.Equal(new[] { "CSV1003", "CSV1010", "CSV1010", "CSV1013" }, all.Errors("Mixed"));
            var nulls = VerifyWith(source, "null");
            Assert.Equal(new[] { "CSV1013" }, nulls.Errors("Mixed"));
            Assert.True(nulls["Mixed"].AssumedObligations >= 4);
            var bounds = VerifyWith(source, "bounds,overflow");
            Assert.Equal(new[] { "CSV1003", "CSV1010", "CSV1010" }, bounds.Errors("Mixed"));
            Assert.Throws<System.ArgumentException>(() => Checks.Parse("nulls"));
        }

        [Fact]
        public void Checks_TurnUnsupportedConstructs_IntoUnknownValues()
        {
            const string source = @"
public static class P
{
    public static int Lent(int[] a, int[] b) { Spec.Requires(a.Length > 0); Fill(b, out a[0]); return a[0]; }
    private static void Fill(int[] b, out int x) { x = b.Length > 0 ? b[0] : 0; }
}";
            var all = VerifyWith(source, null);
            Assert.Contains("CSV1901", all.Errors("Lent"));
            var some = VerifyWith(source, "bounds");
            Assert.Empty(some.Errors("Lent"));
            Assert.Equal(1, some["Lent"].Unmodeled);
            Assert.Contains(some["Lent"].Diagnostics, d => d.Id == "CSV1901" && !d.IsError && d.Message.EndsWith("(not modeled: treated as unknown)"));
        }

        // ----------------------------------------------------------------------------- reasons for null

        [Fact]
        public void NullDiagnostics_SayWhereTheNullComesFrom()
        {
            var r = Harness.Verify(@"
public sealed class User { public string Name = """"; public User? Boss; public override string ToString() => Name; }
public sealed class Repo { public User? Find(int id) => null; }
public static class P
{
    public static int Param(string? s) => s.Length;
    public static int Call(Repo r) { var u = r.Find(1); return u.Name.Length; }
    public static string Library() => System.IO.Path.GetDirectoryName(""x"");
    public static int AfterCall(User u) { if (u.Boss != null) { System.Console.WriteLine(u); return u.Boss.Name.Length; } return 0; }
    public static int Copied(User u) { var b = u.Boss; if (b != null) { System.Console.WriteLine(u); return b.Name.Length; } return 0; }
}");
            string Message(string m) => r[m].Diagnostics.Single(d => d.IsError).Message;
            Assert.Contains("parameter 's' is declared 'string?'", Message("Param"));
            Assert.Contains("'Find' may return null (line 8)", Message("Call"));
            Assert.Contains("'GetDirectoryName' may return null (line 9)", Message("Library"));
            Assert.Contains("the call to 'WriteLine' (line 10) may change what was checked before it", Message("AfterCall"));
            Assert.Contains("copy the value to a local", Message("AfterCall"));
            Assert.Empty(r.Errors("Copied"));
        }
    }
}
