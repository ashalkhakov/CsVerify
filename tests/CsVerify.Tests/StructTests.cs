using Xunit;

namespace CsVerify.Tests
{
    /// <summary>
    /// Structs of any values (#65): a struct of structs or of tuples, and a generic struct (one struct for all its
    /// instantiations, its T fields boxes), read, written, made, compared and matched at any depth.
    /// </summary>
    public class StructTests
    {
        [Fact]
        public void AStructOfStructs_IsReadWrittenAndComparedAtAnyDepth()
        {
            var r = Harness.Verify(@"public readonly record struct Money(decimal Amount, string Currency);
public readonly record struct Line(Money Price, int Quantity);
public struct Point { public int X; public int Y; }
public struct Segment { public Point From; public Point To; }
public readonly record struct Span2((int, int) Range);
public static class N
{
    public static int Qty(Line l) => l.Quantity;
    public static int Len(Line l) => l.Price.Currency.Length;
    public static int First(Span2 s) => s.Range.Item1;
    public static Line Make(Money m) { Spec.Ensures<Line>(r => r.Price == m && r.Quantity == 1); return new Line(m, 1); }
    public static Segment Move(Segment s) { Spec.Requires(s.From.X < 1000); Spec.Ensures<Segment>(r => r.From.X == Spec.Old(s.From.X) + 1 && r.From.Y == Spec.Old(s.From.Y) && r.To.X == Spec.Old(s.To.X) && r.To.Y == Spec.Old(s.To.Y)); s.From.X = s.From.X + 1; return s; }
    public static Segment Zero() { Spec.Ensures<Segment>(r => r.From.X == 0 && r.To.Y == 0); return default; }
    public static bool Same(Line a, Line b) { Spec.Ensures<bool>(r => r == (a.Price.Amount == b.Price.Amount && a.Price.Currency == b.Price.Currency && a.Quantity == b.Quantity)); return a == b; }
    public static Line Twice(Line l) { Spec.Ensures<Line>(r => r.Price == l.Price && r.Quantity == 2); return l with { Quantity = 2 }; }
    public static long Widen(Segment s) { Spec.Ensures<long>(r => r <= 2147483648L); return (long)s.From.X + 1; }
    public static Segment Back(Segment s) => s;
    public static void ViaCall(Segment s) { var t = Back(s); Spec.Assert(t.To.Y <= int.MaxValue); }
    public static int Priced(Line l) { Spec.Ensures<int>(r => r == (l.Price.Amount > 0m ? l.Quantity : 0)); return l is { Price.Amount: > 0m, Quantity: var q } ? q : 0; }
    public static bool Usd(Money m) { Spec.Ensures<bool>(r => r == (m.Amount > 0m && m.Currency == ""USD"")); return m is (> 0m, ""USD""); }
    public static int Where(Point p) { Spec.Ensures<int>(r => r == (p.X == 0 ? 1 : p.Y > 0 ? 2 : 3)); return p switch { { X: 0 } => 1, { Y: > 0 } => 2, _ => 3 }; }
    public static int Wrong(Segment s) { Spec.Ensures<int>(x => x == s.To.X); return s.From.X; }
    public static int WrongOverflow(Segment s) => s.From.X + 1;
    public static bool WrongSame(Line a, Line b) { Spec.Ensures<bool>(r => r == (a.Quantity == b.Quantity)); return a == b; }
}");
            foreach (var ok in new[] { "Qty", "Len", "First", "Make", "Move", "Zero", "Same", "Twice", "Widen", "Back", "ViaCall", "Priced", "Usd", "Where" })
            {
                Assert.True(r.Errors(ok).Length == 0, r.Explain(ok));
            }
            Assert.Equal(new[] { "CSV1002" }, r.Errors("Wrong"));
            Assert.Equal(new[] { "CSV1010" }, r.Errors("WrongOverflow"));
            Assert.Equal(new[] { "CSV1002" }, r.Errors("WrongSame"));
        }

        [Fact]
        public void AGenericStruct_IsOneStructForAllItsInstantiations()
        {
            var r = Harness.Verify(@"using System.Collections.Generic;
public readonly record struct Wrap<T>(T Value)
{
    public Wrap<T> Self() { Spec.Ensures(Spec.Result<Wrap<T>>() == this); return this; }
    public T Read() { Spec.Ensures(EqualityComparer<T>.Default.Equals(Spec.Result<T>(), Value)); return Value; }
    public Wrap<T> Put(T v) { Spec.Ensures(EqualityComparer<T>.Default.Equals(Spec.Result<Wrap<T>>().Value, v)); return this with { Value = v }; }
}
public readonly record struct Pair<A, B>(A First, B Second);
public struct Cell<T> { public T Item; public int Count; }
public static class G
{
    public static Wrap<int> Make(int x) { Spec.Ensures<Wrap<int>>(r => r.Value == x); return new Wrap<int>(x); }
    public static string Text(Wrap<string> w) { Spec.Ensures<string>(s => s == w.Value); return w.Value; }
    public static T Get<T>(Wrap<T> w) { Spec.Ensures<T>(r => EqualityComparer<T>.Default.Equals(r, w.Value)); return w.Value; }
    public static Wrap<T> Of<T>(T x) { Spec.Ensures<Wrap<T>>(r => EqualityComparer<T>.Default.Equals(r.Value, x)); return new Wrap<T>(x); }
    public static int Round(int x) { Spec.Ensures<int>(r => r == x); var w = Of(x); return Get(w); }
    public static int ReadIt(Wrap<int> w) { Spec.Ensures<int>(r => r == w.Value); return w.Read(); }
    public static int PutIt(Wrap<int> w) { Spec.Ensures<int>(r => r == 5); return w.Put(5).Value; }
    public static Pair<int, string> Swap(Pair<string, int> p) { Spec.Ensures<Pair<int, string>>(r => r.First == p.Second && r.Second == p.First); return new Pair<int, string>(p.Second, p.First); }
    public static Cell<int> Bump(Cell<int> c) { Spec.Requires(c.Count < 1000); Spec.Ensures<Cell<int>>(r => r.Count == Spec.Old(c.Count) + 1 && r.Item == Spec.Old(c.Item)); c.Count = c.Count + 1; return c; }
    public static Cell<T> Store<T>(Cell<T> c, T x) { Spec.Ensures<Cell<T>>(r => EqualityComparer<T>.Default.Equals(r.Item, x)); c.Item = x; return c; }
    public static int Stored(Cell<int> c) { Spec.Ensures<int>(r => r == 7); var d = Store(c, 7); return d.Item; }
    public static bool Same(Wrap<int> a, Wrap<int> b) { Spec.Ensures<bool>(r => r == (a.Value == b.Value)); return a == b; }
    public static int Default() { Spec.Ensures<int>(r => r == 0); Wrap<int> w = default; return w.Value; }
    public static long Widen(Wrap<int> w) { Spec.Ensures<long>(r => r <= 2147483648L); return (long)w.Value + 1; }
    public static int WrongRound(int x) { Spec.Ensures<int>(r => r == x + 1); return Get(new Wrap<int>(x)); }
    public static bool WrongSame(Wrap<string> a, Wrap<string> b) { Spec.Ensures<bool>(r => r); return a == b; }
}");
            foreach (var ok in new[] { "Self", "Make", "Text", "Get", "Of", "Round", "ReadIt", "PutIt", "Swap", "Bump", "Store", "Stored", "Same", "Default", "Widen" })
            {
                Assert.True(r.Errors(ok).Length == 0, r.Explain(ok));
            }
            Assert.Equal(new[] { "CSV1002" }, r.Errors("WrongRound"));
            Assert.Equal(new[] { "CSV1002" }, r.Errors("WrongSame"));
        }

        [Fact]
        public void ANullableStruct_IsNull_OrItsValue()
        {
            // (#135: a nullable record struct as a parameter, a field, a result; its == the struct's, lifted)
            var r = Harness.Verify(@"public readonly record struct Key(Guid Value);
public readonly record struct Range(int Lo, int Hi);
public struct Plain { public int A; }
public sealed class Holder { public Key? Kept { get; set; } }
public sealed record Moved(Key From, Key? To);
public static class Use
{
    public static Moved Move(Key from, Key? to) { Spec.Ensures<Moved>(r => r.To == null || r.To != r.From); return new Moved(from, to == from ? null : to); }
    public static bool Has(Key? k) { Spec.Ensures<bool>(r => r == (k != null) && r == k.HasValue); return k.HasValue; }
    public static Key ValueOf(Key? k) { Spec.Requires(k != null); Spec.Ensures<Key>(r => r == k.Value); return k.Value; }
    public static Key Unchecked(Key? k) { return k.Value; }
    public static Key Or(Key? k, Key other) { Spec.Ensures<Key>(r => r == (k ?? other)); return k ?? other; }
    public static int LoOf(Range? s) { Spec.Ensures<int>(r => s == null ? r == 0 : r == s.Value.Lo); return s is { } v ? v.Lo : 0; }
    public static int LoOrDefault(Range? s) { Spec.Ensures<int>(r => s != null || r == 0); return s.GetValueOrDefault().Lo; }
    public static Range? Widen(Range? s) { Spec.Ensures<Range?>(r => (r == null) == (s == null)); if (s is Range v && v.Hi < 100) { return new Range(v.Lo, v.Hi + 1); } return s; }
    public static bool Same(Key? a, Key? b) { Spec.Requires(a != null && b != null && a.Value.Value == b.Value.Value); Spec.Ensures<bool>(r => r); return a == b; }
    public static bool SameWrong(Key? a, Key? b) { Spec.Requires(a != null && b != null); Spec.Ensures<bool>(r => r); return a == b; }
    public static bool NullWrong(Key? a, Key b) { Spec.Requires(a == null); Spec.Ensures<bool>(r => r); return a == b; }
    public static bool BothNull(Key? a, Key? b) { Spec.Requires(a == null && b == null); Spec.Ensures<bool>(r => r); return a == b; }
    public static void Keep(Holder h, Key k) { Spec.Ensures(h.Kept != null && h.Kept.Value == k); h.Kept = k; }
    public static void Drop(Holder h) { Spec.Ensures(h.Kept == null); h.Kept = null; }
    public static int OfPlain(Plain? p) { Spec.Ensures<int>(r => p == null ? r == -1 : r == p.Value.A); return p.HasValue ? p.Value.A : -1; }
}");
            foreach (var ok in new[] { "Move", "Has", "ValueOf", "Or", "LoOf", "LoOrDefault", "Widen", "Same", "BothNull", "Keep", "Drop", "OfPlain" })
            {
                Assert.True(r.Errors(ok).Length == 0, r.Explain(ok));
            }
            Assert.Equal(new[] { "CSV1013" }, r.Errors("Unchecked"));
            Assert.Equal(new[] { "CSV1002" }, r.Errors("SameWrong"));
            Assert.Equal(new[] { "CSV1002" }, r.Errors("NullWrong"));
        }
    }
}
