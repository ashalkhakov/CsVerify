using Xunit;

namespace CsVerify.Tests
{
    /// <summary>
    /// What applications need for null safety: objects their frameworks build, constructors they never write,
    /// guard clauses, Debug.Assert, library calls handed their objects, and awaited library reads.
    /// </summary>
    public class AppTests
    {
        [Fact]
        public void ClassesWithoutConstructors_HaveTheirInitializersChecked()
        {
            var r = Harness.Verify(@"
#nullable enable
public sealed class Implicit { public string Name { get; set; } = null!; }
public sealed class Field { public string Name = null!; }
public sealed class Missing { public string Name; }
public sealed class Fine
{
    public string A { get; set; } = """";
    public string B = $""{1}"";
    public int[] C = new int[0];
    public string D = string.Empty;
    public string? E;
    public required string F { get; set; }
}
public sealed class Primary(string name) { public string Name = name; }
public static class P { public static int Read() => new Implicit().Name.Length; }");
            Assert.Equal(new[] { "CSV1014" }, r.Errors("Implicit..ctor"));
            Assert.Equal(new[] { "CSV1014" }, r.Errors("Field..ctor"));
            Assert.Equal(new[] { "CSV1014" }, r.Errors("Missing..ctor"));
            Assert.Null(r["Fine..ctor"]);
            Assert.Null(r["Primary..ctor"]);
        }

        [Fact]
        public void JsonRequired_IsTrusted_LikeRequired()
        {
            var r = Harness.Verify(@"
#nullable enable
public sealed class Dto
{
    public required string Title { get; set; }
    [System.Text.Json.Serialization.JsonRequired] public string Owner { get; set; } = null!;
}
public static class P { public static int Read(Dto d) => d.Title.Length + d.Owner.Length; }", overflow: false);
            Assert.Null(r["Dto..ctor"]);
            Assert.Empty(r.Errors("Read"));
        }

        [Fact]
        public void GuardClauses_GiveWhatTheyCheck()
        {
            var r = Harness.Verify(@"
#nullable enable
public static class P
{
    public static int Index(int[] a, int i)
    {
        ArgumentOutOfRangeException.ThrowIfNegative(i);
        ArgumentOutOfRangeException.ThrowIfGreaterThanOrEqual(i, a.Length);
        return a[i];
    }
    public static int Positive(int n) { ArgumentOutOfRangeException.ThrowIfNegativeOrZero(n); return 10 / n; }
    public static char First(string? s) { ArgumentException.ThrowIfNullOrEmpty(s); return s[0]; }
    public static int Unguarded(int[] a, int i) { ArgumentOutOfRangeException.ThrowIfNegative(i); return a[i]; }
}");
            Assert.Empty(r.Errors("Index"));
            Assert.Empty(r.Errors("Positive"));
            Assert.Empty(r.Errors("First"));
            Assert.Equal(new[] { "CSV1003" }, r.Errors("Unguarded"));
        }

        [Fact]
        public void DebugAssert_IsProved()
        {
            var r = Harness.Verify(@"
public static class P
{
    public static void True(int[] a) { Debug.Assert(a.Length >= 0); }
    public static void False(int x) { Debug.Assert(x > 0, ""x is positive""); }
    public static int Assumed(int[] a, int i) { if (i < 0 || i >= a.Length) return 0; Debug.Assert(i < a.Length); return a[i]; }
}");
            Assert.Empty(r.Errors("True"));
            Assert.Equal(new[] { "CSV1004" }, r.Errors("False"));
            Assert.Empty(r.Errors("Assumed"));
        }

        [Fact]
        public void LibraryCallsHandedPlainObjects_KeepTheirFields()
        {
            var r = Harness.Verify(@"
#nullable enable
public sealed class Plain { public string? Notes; }
public sealed class Shown { public string? Notes; public override string ToString() { Notes = null; return """"; } }
public static class P
{
    public static int Plain(Plain d) { if (d.Notes != null) { Console.WriteLine(d); return d.Notes.Length; } return 0; }
    // its ToString could run, and writes Notes
    public static int Shown(Shown d) { if (d.Notes != null) { Console.WriteLine(d); return d.Notes.Length; } return 0; }
}");
            Assert.Empty(r.Errors("Plain"));
            Assert.Equal(new[] { "CSV1013" }, r.Errors("P.Shown"));
        }

        [Fact]
        public void AwaitedLibraryReads_HaveTheirAsyncStubsContracts()
        {
            var r = Harness.Verify(@"
using System.IO;
using System.Threading.Tasks;
public static class P
{
    public static async Task<byte> Last(Stream s, byte[] buf)
    {
        if (buf.Length < 4) return 0;
        int n = await s.ReadAsync(buf, 0, 4);
        return n > 0 ? buf[n - 1] : (byte)0;
    }
    public static async Task<byte> Past(Stream s, byte[] buf)
    {
        if (buf.Length < 4) return 0;
        int n = await s.ReadAsync(buf, 0, 4);
        return buf[n];
    }
    public static Task<int> NotAwaited(Stream s, byte[] buf) => s.ReadAsync(buf, 0, 1);
}");
            Assert.Empty(r.Errors("Last"));
            Assert.Equal(new[] { "CSV1003" }, r.Errors("Past"));
            // (a task not awaited at once is the library's: no contract, so no precondition either)
            Assert.Empty(r.Errors("NotAwaited"));
        }
    }
}
