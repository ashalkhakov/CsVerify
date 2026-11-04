using Xunit;

namespace CsVerify.Tests
{
    /// <summary>
    /// Spans as views of memory: a base, an offset and a length. Their cells are the heap's, so writes through a span
    /// are seen in its array and the other way round; Slice, CopyTo, Fill, Clear, stackalloc; the span stubs.
    /// </summary>
    public class SpanTests
    {
        [Fact]
        public void Spans_ReadAndWriteTheirArraysCells()
        {
            var r = Harness.Verify(@"
public static class P
{
    public static int Read(int[] a) { Spec.Requires(a.Length > 2 && a[1] == 7); Spec.Ensures<int>(r => r == 7); Span<int> s = a; return s[1]; }
    public static int Slice(int[] a) { Spec.Requires(a.Length > 3 && a[3] == 9); Spec.Ensures<int>(r => r == 9); return a.AsSpan(1).Slice(1)[1]; }
    public static void Write(int[] a) { Spec.Requires(a.Length > 2); Span<int> s = a.AsSpan(1, 2); s[1] = 5; Spec.Assert(a[2] == 5); }
    public static void Built(int[] a) { Spec.Requires(a.Length > 2); var s = new Span<int>(a, 1, 2); s[0] = 4; Spec.Assert(a[1] == 4); }
    public static int Stack() { Spec.Ensures<int>(r => r == 8); Span<int> s = stackalloc int[4]; s[3] = 8; return s[3]; }
    public static int Same(ReadOnlySpan<byte> buf, int i) { Spec.Requires(0 <= i && i < buf.Length); var x = buf[i]; Spec.Assert(x == buf[i]); return x; }
    public static bool Empty(int[] a) { Spec.Ensures<bool>(r => r == (a.Length == 0)); return a.AsSpan().IsEmpty; }
    // (a write through the span changes the array)
    public static int Wrong(int[] a) { Spec.Requires(a.Length > 2 && a[1] == 7); Spec.Ensures<int>(r => r == 7); Span<int> s = a; s[1] = 3; return a[1]; }
}");
            foreach (var m in new[] { "Read", "Slice", "Write", "Built", "Stack", "Same", "Empty" }) Assert.Empty(r.Errors("P." + m));
            Assert.Equal(new[] { "CSV1002" }, r.Errors("Wrong"));
        }

        [Fact]
        public void CopyToFillAndClear_WriteTheirCellsOnly()
        {
            var r = Harness.Verify(@"
public static class P
{
    public static void Copy(int[] a, int[] b)
    {
        Spec.Requires(a.Length == 2 && b.Length == 3 && a[0] == 4 && a[1] == 6 && b[2] == 1);
        a.AsSpan().CopyTo(b);
        Spec.Assert(b[0] == 4 && b[1] == 6 && b[2] == 1);
    }
    public static void Overlap(int[] a)
    {
        Spec.Requires(a.Length == 3 && a[0] == 1 && a[1] == 2);
        a.AsSpan(0, 2).CopyTo(a.AsSpan(1));
        Spec.Assert(a[1] == 1 && a[2] == 2);
    }
    public static void Fill(int[] a) { Spec.Requires(a.Length == 3 && a[0] == 9); a.AsSpan(1).Fill(2); Spec.Assert(a[0] == 9 && a[1] == 2 && a[2] == 2); }
    public static void Clear(int[] a) { Spec.Requires(a.Length == 2); a.AsSpan().Clear(); Spec.Assert(a[1] == 0); }
    public static void Short(int[] a, int[] b) { Spec.Requires(a.Length == 3 && b.Length == 2); a.AsSpan().CopyTo(b); }
    public static int Past(ReadOnlySpan<byte> buf) => buf.Slice(1)[0];
}");
            foreach (var m in new[] { "Copy", "Overlap", "Fill", "Clear" }) Assert.Empty(r.Errors("P." + m));
            Assert.Equal(new[] { "CSV1001" }, r.Errors("Short"));
            Assert.Equal(new[] { "CSV1001", "CSV1003" }, r.Errors("Past"));
        }

        [Fact]
        public void SpanStubs_GiveRangesAndLengths()
        {
            var r = Harness.Verify(@"
using System.Buffers.Binary;
public static class P
{
    public static byte Colon(ReadOnlySpan<byte> line) { int i = line.IndexOf((byte)':'); return i < 0 ? (byte)0 : line[i]; }
    public static int Frame(ReadOnlySpan<byte> f) => f.Length >= 4 ? BinaryPrimitives.ReadInt32BigEndian(f) : 0;
    public static int Short(ReadOnlySpan<byte> f) => BinaryPrimitives.ReadInt32BigEndian(f);
    public static byte Prefix(ReadOnlySpan<byte> s, ReadOnlySpan<byte> p) => s.StartsWith(p) && p.Length > 0 ? s[p.Length - 1] : (byte)0;
}");
            Assert.Empty(r.Errors("Colon"));
            Assert.Empty(r.Errors("Frame"));
            Assert.Equal(new[] { "CSV1001" }, r.Errors("Short"));
            Assert.Empty(r.Errors("Prefix"));
        }
    }
}
