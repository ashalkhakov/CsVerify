using System.Linq;
using Xunit;

namespace CsVerify.Tests
{
    /// <summary>Atomic fields: shared with no lock, read after the others' steps, and written only by steps.</summary>
    public class AtomicTests
    {
        private const string Usings = "using CsVerify; using System; using System.Threading; using System.Threading.Tasks; ";
        private const string Atomic = "CSV1030";

        // a counter that only grows, a flag that once set stays set, and a field any thread may set to anything
        private const string Members =
            "[Atomic(Step = nameof(Grows))] volatile int _n; [Pure] static bool Grows(int old, int now) => old <= now; " +
            "[Atomic(Step = nameof(Stays))] volatile bool _done; [Pure] static bool Stays(bool old, bool now) => !old || now; " +
            "[Atomic(Step = nameof(Up))] long _total; [Pure] static bool Up(long old, long now) => old <= now; " +
            "[Atomic] int _any; [Atomic] volatile object _box; ";

        private static string[] Errors(string members) =>
            Harness.Verify(Usings + "public class C { " + Members + members + " }").Errors("M");

        private static string[] AllErrors(string source) =>
            Harness.Verify(Usings + source).Diagnostics.Where(d => d.IsError).Select(d => d.Id).ToArray();

        private static string Explain(string members) =>
            Harness.Verify(Usings + "public class C { " + Members + members + " }").Explain("M");

        [Theory]
        // two reads: the second is a step on from the first
        [InlineData("int M() { int a = _n; int b = _n; Spec.Assert(a <= b); return b; }")]
        [InlineData("long M() { long a = Interlocked.Read(ref _total); long b = Volatile.Read(ref _total); Spec.Assert(a <= b); return b; }")]
        // a flag once set stays set, whoever looks
        [InlineData("void M() { Volatile.Write(ref _done, true); bool d = Volatile.Read(ref _done); Spec.Assert(d && _done); }")]
        [InlineData("void M() { _done = true; bool d = _done; Spec.Assert(d); }")]
        // read, modify, write in one step
        [InlineData("void M() { while (true) { int c = _n; if (c == int.MaxValue) return; if (Interlocked.CompareExchange(ref _n, c + 1, c) == c) return; } }")]
        [InlineData("long M(int d) { Spec.Requires(d >= 0); long was = Interlocked.Read(ref _total); if (was > long.MaxValue - d) return was; long now = Interlocked.CompareExchange(ref _total, was + d, was); return now; }")]
        // with no step, anything goes, and increments wrap as at run time
        [InlineData("int M() { int a = Interlocked.Increment(ref _any); Interlocked.Add(ref _any, -3); Interlocked.Exchange(ref _any, 7); return a; }")]
        [InlineData("int M() { int was = Interlocked.Exchange(ref _any, 5); int b = Interlocked.CompareExchange(ref _any, 6, 5); return was + 0 * b; }")]
        [InlineData("object M() { var b = new object(); return Interlocked.Exchange(ref _box, b); }")]
        [InlineData("void M() { Interlocked.Or(ref _any, 4); Interlocked.And(ref _any, 3); }")]
        // what the others did is a step, across a call, a loop, an await
        [InlineData("void Bump() { int c = _n; if (c < int.MaxValue) Interlocked.CompareExchange(ref _n, c + 1, c); } void M() { int a = _n; Bump(); int b = _n; Spec.Assert(a <= b); }")]
        [InlineData("[Atomic(Step = nameof(Grows))] static volatile int _s; [RunsConcurrently] static void Up() { int c = _s; if (c < int.MaxValue) Interlocked.CompareExchange(ref _s, c + 1, c); } [RunsConcurrently] static void M() { int a = _s; Up(); int b = Volatile.Read(ref _s); Spec.Assert(a <= b); }")]
        [InlineData("void Bump() { int c = _n; if (c < int.MaxValue) Interlocked.CompareExchange(ref _n, c + 1, c); } void M() { int a = _n; for (int i = 0; i < 3; i++) { Bump(); } int b = _n; Spec.Assert(a <= b); }")]
        [InlineData("async Task M() { int a = _n; await Task.Yield(); int b = _n; Spec.Assert(a <= b); }")]
        // a contract of what it saw: stable under the others' steps
        [InlineData("int M() { Spec.Ensures<int>(r => r <= _n); return _n; }")]
        [InlineData("void M() { Spec.Ensures(Spec.Old(_n) <= _n); int c = _n; if (c < int.MaxValue) Interlocked.CompareExchange(ref _n, c + 1, c); }")]
        [InlineData("int Seen() { Spec.Ensures<int>(r => r <= _n); return _n; } void M() { int a = Seen(); int b = _n; Spec.Assert(a <= b); }")]
        [InlineData("static int Seen(C c) { Spec.Ensures<int>(r => Spec.Old(c._n) <= r && r <= c._n); return c._n; } static void M(C c) { int a = c._n; int r = Seen(c); int b = Seen(c); Spec.Assert(a <= b && r <= b); }")]
        // shared by concurrent code with no lock
        [InlineData("[RunsConcurrently] void M() { int c = _n; if (c < int.MaxValue) Interlocked.CompareExchange(ref _n, c + 1, c); }")]
        [InlineData("async Task M() { var t = Task.Run(() => { Volatile.Write(ref _done, true); }); bool d = _done; await t; }")]
        public void Proved(string members) => Assert.True(Errors(members).Length == 0, Explain(members));

        [Fact]
        public void Steps_AreProvedTransitive()
        {
            Assert.DoesNotContain(Atomic, AllErrors("public class C { " + Members + " }"));
            Assert.Contains(Atomic, AllErrors("public class C { [Atomic(Step = nameof(Next))] volatile int _n; [Pure] static bool Next(int old, int now) => now == old + 1; }"));
        }

        [Fact]
        public void A_Constructor_SetsItsOwnObjectsFreely() =>
            Assert.Empty(AllErrors("public class C { [Atomic(Step = nameof(Grows))] long _n; [Pure] static bool Grows(long a, long b) => a <= b; public C(long n) { _n = n; _n = n - 0; } }"));

        [Theory]
        // a plain read and write is two steps: the others may come between
        [InlineData("void M() { int c = _n; if (c < int.MaxValue) _n = c + 1; }")]
        [InlineData("void M() { if (_n < int.MaxValue) _n++; }")]
        // a write that isn't a step
        [InlineData("void M() { Interlocked.Decrement(ref _n); }")]
        [InlineData("void M() { Interlocked.Increment(ref _n); }")] // (it wraps)
        [InlineData("void M() { int c = _n; Interlocked.CompareExchange(ref _n, c - 1, c); }")]
        [InlineData("void M() { Volatile.Write(ref _done, false); }")]
        [InlineData("void M() { Interlocked.Exchange(ref _total, 0); }")]
        // a plain use of one that isn't volatile
        [InlineData("long M() { return _total; }")]
        [InlineData("void M() { _total = long.MaxValue; }")]
        public void Reported(string members) => Assert.Contains(Atomic, Errors(members));

        [Theory]
        // the others may have moved it
        [InlineData("CSV1004", "int M() { int a = _n; int b = _n; Spec.Assert(a == b); return b; }")]
        [InlineData("CSV1004", "void M() { Volatile.Write(ref _any, 1); Spec.Assert(Volatile.Read(ref _any) == 1); }")]
        [InlineData("CSV1004", "void Bump() { Interlocked.Exchange(ref _any, 0); } void M() { int a = _any; Bump(); Spec.Assert(_any == a); }")]
        [InlineData("CSV1004", "async Task M() { bool a = _done; await Task.Yield(); Spec.Assert(_done == a); }")]
        // nothing contradicts: what is known after the others' steps leaves false unproved
        [InlineData("CSV1004", "int M() { int a = _n; int b = _n; Spec.Assert(false); return b; }")]
        [InlineData("CSV1004", "void Bump() { int c = _n; if (c < int.MaxValue) Interlocked.CompareExchange(ref _n, c + 1, c); } void M() { int a = _n; Bump(); var d = new C(); d.Bump(); int b = _n; Spec.Assert(false); }")]
        [InlineData("CSV1004", "void Bump() { int c = _n; if (c < int.MaxValue) Interlocked.CompareExchange(ref _n, c + 1, c); } void M() { for (int i = 0; i < 3; i++) { Bump(); new C().Bump(); } Spec.Assert(false); }")]
        [InlineData("CSV1004", "async Task M() { int a = _n; await Task.Yield(); var d = new C(); int b = d._n; Spec.Assert(false); }")]
        [InlineData("CSV1004", "void M() { while (true) { int c = _n; if (c == int.MaxValue) break; if (Interlocked.CompareExchange(ref _n, c + 1, c) == c) break; } Spec.Assert(false); }")]
        // a callee's read is of a later value than the caller's
        [InlineData("CSV1004", "int Seen() { Spec.Ensures<int>(r => r <= _n); return _n; } void M() { int x = _n; int r = Seen(); Spec.Assert(r <= x); }")]
        [InlineData("CSV1004", "static int Seen(C c) { Spec.Ensures<int>(r => r <= c._n); return c._n; } static void M(C c) { int x = c._n; int r = Seen(c); Spec.Assert(r <= x); }")]
        // Interlocked on what isn't atomic, or a ref to an atomic field passed on
        [InlineData("CSV1901", "int _plain; void M() { Interlocked.Increment(ref _plain); }")]
        [InlineData("CSV1027", "int _plain; [RunsConcurrently] void M() { Interlocked.Increment(ref _plain); }")]
        [InlineData("CSV1901", "static void Inc(ref int x) { x = x + 1; } void M() { Inc(ref _any); }")]
        // a field that isn't atomic, shared all the same
        [InlineData("CSV1027", "int _plain; [RunsConcurrently] void M() { _plain = 1; }")]
        public void Reported_As(string id, string members) => Assert.Contains(id, Errors(members));

        [Theory]
        [InlineData("[Atomic] volatile float _f;")]
        [InlineData("[Atomic] readonly int _r;")]
        [InlineData("readonly object _l = new object(); [Atomic, GuardedBy(nameof(_l))] volatile int _g;")]
        [InlineData("[Atomic(Step = nameof(S))] volatile int _s; bool S(int a, int b) => a <= b;")]
        [InlineData("[Atomic(Step = nameof(S))] volatile int _s; [Pure] static bool S(long a, long b) => a <= b;")]
        [InlineData("static int _k; [Atomic(Step = nameof(S))] volatile int _s; [Pure] static bool S(int a, int b) => a <= b + _k;")]
        [InlineData("[Atomic(Step = \"Missing\")] volatile int _s;")]
        [InlineData("[Atomic] volatile int _s; [Pure] bool Positive() => _s > 0;")]
        [InlineData("[Owned] class O { [Atomic] public volatile int X; }")]
        [InlineData("} public struct S { [Atomic] public volatile int X; ")]
        public void Misdeclared(string members) => Assert.Contains(Atomic, AllErrors("public class C { void M() { } " + members + " }"));
    }
}
