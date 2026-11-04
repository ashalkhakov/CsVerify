using System.Linq;
using Xunit;

namespace CsVerify.Tests
{
    /// <summary>
    /// Disposables as linear resources: disposed exactly once on every path, not used after, or handed over; a class
    /// owning one disposes it in its Dispose, and is disposed in turn.
    /// </summary>
    public class DisposalTests
    {
        private static string[] Ids(string source) => Harness.Analyze("#nullable enable\nusing System.IO;\n" + source).Where(id => id.StartsWith("CSV002")).ToArray();

        [Fact]
        public void Disposed_Returned_OrHandedOver_IsFine()
        {
            Assert.Empty(Ids(@"
public static class P
{
    public static long Using(string p) { using var fs = File.OpenRead(p); return fs.Length; }
    public static long Statement(string p) { using (var fs = File.OpenRead(p)) { return fs.Length; } }
    public static long UsingVar(string p) { var fs = File.OpenRead(p); using (fs) { return fs.Length; } }
    public static long Disposed(string p) { var fs = File.OpenRead(p); var n = fs.Length; fs.Dispose(); return n; }
    public static long Finally(string p) { var fs = File.OpenRead(p); try { return fs.Length; } finally { fs.Dispose(); } }
    public static void NullChecked(string p, bool b) { FileStream? fs = b ? File.OpenRead(p) : null; if (fs != null) fs.Dispose(); }
    public static void Conditional(string p) { var fs = File.OpenRead(p); fs?.Dispose(); }
    public static FileStream Returned(string p) { var fs = File.OpenRead(p); return fs; }
    public static string Wrapped(string p) { var fs = File.OpenRead(p); using var r = new StreamReader(fs); return r.ReadToEnd(); }
    public static void Handed(string p, System.Collections.Generic.List<System.IDisposable> bag) { var fs = File.OpenRead(p); bag.Add(fs); Spec.HandOver(fs); }
    public static void Taken(string p) { var fs = File.OpenRead(p); Keep(fs); }
    private static void Keep([TakesOwnership] FileStream fs) { fs.Dispose(); }
    public static long Borrowed(FileStream fs) => fs.Length;
    public static long Harmless() { var m = new MemoryStream(); return m.Length; }
}"));
        }

        [Fact]
        public void Leaks_DoubleDisposals_AndUsesAfter_AreReported()
        {
            Assert.Equal(new[] { "CSV0020" }, Ids("public static class P { public static long M(string p) { var fs = File.OpenRead(p); return fs.Length; } }"));
            Assert.Equal(new[] { "CSV0020" }, Ids("public static class P { public static void M(string p, bool b) { var fs = File.OpenRead(p); if (b) fs.Dispose(); } }"));
            Assert.Equal(new[] { "CSV0020" }, Ids("public static class P { public static void M(string p) { var fs = File.OpenRead(p); fs = File.OpenRead(p); fs.Dispose(); } }"));
            Assert.Equal(new[] { "CSV0021" }, Ids("public static class P { public static void M(string p) { var fs = File.OpenRead(p); fs.Dispose(); fs.Dispose(); } }"));
            Assert.Equal(new[] { "CSV0021" }, Ids("public static class P { public static long M(string p) { var fs = File.OpenRead(p); fs.Dispose(); return fs.Length; } }"));
            // a borrowed parameter is not the method's to dispose, but one it takes is
            Assert.Equal(new[] { "CSV0020" }, Ids("public static class P { public static void M([TakesOwnership] FileStream fs) { } }"));
            Assert.Empty(Ids("public static class P { public static void M(FileStream fs) { } }"));
        }

        [Fact]
        public void Owners_DisposeWhatTheyHold_AndAreDisposed()
        {
            const string owner = @"
public sealed class Owner : System.IDisposable
{
    private readonly FileStream _fs;
    public Owner(string p) { _fs = File.OpenRead(p); }
    public void Dispose() => _fs.Dispose();
}
";
            Assert.Empty(Ids(owner + "public static class P { public static void M() { using var o = new Owner(\"x\"); } }"));
            Assert.Equal(new[] { "CSV0020" }, Ids(owner + "public static class P { public static void M() { var o = new Owner(\"x\"); } }"));
            Assert.Equal(new[] { "CSV0022" }, Ids(@"
public sealed class Forgets : System.IDisposable
{
    private readonly FileStream _fs;
    public Forgets(string p) { _fs = File.OpenRead(p); }
    public void Dispose() { }
}"));
            Assert.Equal(new[] { "CSV0022" }, Ids("public sealed class NotDisposable { private readonly FileStream _fs = File.OpenRead(\"x\"); }"));
            Assert.Empty(Ids("public sealed class Borrows { [NotOwned] private readonly FileStream _fs; public Borrows(FileStream fs) { _fs = fs; } }"));
            Assert.Empty(Ids(@"
public class Base : System.IDisposable
{
    private FileStream? _fs = null;
    protected virtual void Dispose(bool disposing) { if (disposing) _fs?.Dispose(); }
    public void Dispose() { Dispose(true); }
}"));
        }

        [Fact]
        public void MustDispose_MarksTheProgramsOwnClasses()
        {
            const string marked = "[MustDispose] public sealed class Lease : System.IDisposable { public void Dispose() { } }\n";
            Assert.Equal(new[] { "CSV0020" }, Ids(marked + "public static class P { public static void M() { var l = new Lease(); } }"));
            Assert.Empty(Ids(marked + "public static class P { public static void M() { using var l = new Lease(); } }"));
        }
    }
}
