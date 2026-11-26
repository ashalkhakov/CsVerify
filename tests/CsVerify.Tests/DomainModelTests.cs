using CsVerify.Verifier;
using Microsoft.CodeAnalysis;
using System.Linq;
using Xunit;

namespace CsVerify.Tests
{
    /// <summary>
    /// What an event-style domain model needs (#44): closed command and event hierarchies with a throwing default arm,
    /// value objects, typed ids, collections through their read-only interfaces, decision records, decimal money.
    /// </summary>
    public class DomainModelTests
    {
        private const string Commands = @"public abstract record Command
{
    private Command() { }
    public sealed record Open(int N) : Command;
    public sealed record Close(int N) : Command;
}
";

        [Fact]
        public void AThrowingDefaultArm_IsAThrow()
        {
            var r = Harness.Verify(Commands + @"public static class Handle
{
    public static int Of(Command c)
    {
        Spec.Requires(c is Command.Open o0 ? o0.N >= 0 : c is Command.Close c0 && c0.N >= 0);
        Spec.Ensures<int>(r => r >= 0);
        Spec.EnsuresOnThrow<InvalidOperationException>(false);
        return c switch
        {
            Command.Open o when o.N >= 0 => o.N,
            Command.Close cl when cl.N >= 0 => cl.N,
            _ => throw new InvalidOperationException(""unknown command""),
        };
    }
    public static int Reached(Command c)
    {
        Spec.EnsuresOnThrow<InvalidOperationException>(false);
        return c switch { Command.Open o when o.N >= 0 => o.N, _ => throw new InvalidOperationException() };
    }
}");
            Assert.True(r.Errors("Of").Length == 0, r.Explain("Of"));
            Assert.Equal(new[] { "CSV1002" }, r.Errors("Reached"));
        }

        [Fact]
        public void ReadOnlyLists_OfData_AreParametersAndResults()
        {
            var r = Harness.Verify(@"using System.Collections.Generic;
public sealed record Item(int Qty);
public sealed record Logged(int N);
public static class Totals
{
    public static int Count(IReadOnlyList<Item> items) { Spec.Ensures<int>(n => n == items.Count); return items.Count; }
    public static long Sum(IReadOnlyList<Item> items)
    {
        long total = 0;
        foreach (var item in items)
        {
            if (item != null && item.Qty > 0 && item.Qty < 100 && total < 1000000) total += item.Qty;
        }
        return total;
    }
}
public sealed class Ledger
{
    private readonly List<Logged> pending = new();
    public IReadOnlyList<Logged> Pending => pending;
    public void Log(int n) => pending.Add(new Logged(n));
}");
            Assert.True(r.Errors("Count").Length == 0, r.Explain("Count"));
            Assert.True(r.Errors("Sum").Length == 0, r.Explain("Sum"));
            Assert.True(r.Errors("get_Pending").Length == 0, r.Explain("get_Pending"));
        }

        [Fact]
        public void TypedIds_OfGuidsAndTimes_AreValues()
        {
            var r = Harness.Verify(@"public readonly record struct OrderId(Guid Value);
public readonly record struct At(DateTime When);
public sealed class Order { public OrderId Id { get; } public Order(OrderId id) { Spec.Ensures(Id == id); Id = id; } }
public static class Ids
{
    public static OrderId Same(OrderId id) { Spec.Ensures<OrderId>(r => r == id); return id; }
    public static Guid Raw(OrderId a) { Spec.Ensures<Guid>(g => g == a.Value); return a.Value; }
    public static bool Later(At a, At b) => a.When > b.When;
    public static OrderId New() => new OrderId(Guid.NewGuid());
    public static bool IsEmpty(OrderId a) => a.Value == Guid.Empty;
    public static void ById(Guid g) { var a = new OrderId(g); var b = new OrderId(g); Spec.Assert(a == b && a.Value == g); }
    public static void Keeps(Guid g) { var o = new Order(new OrderId(g)); Spec.Assert(o.Id.Value == g); }
    public static void Wrong(OrderId a, OrderId b) { Spec.Assert(a == b); }
    public static void WrongEmpty() { var a = new OrderId(Guid.NewGuid()); Spec.Assert(a.Value != Guid.Empty); }
}");
            foreach (var ok in new[] { "Same", "Raw", "Later", "New", "IsEmpty", "ById", "Keeps", "Order..ctor" })
            {
                Assert.True(r.Errors(ok).Length == 0, r.Explain(ok));
            }
            Assert.Equal(new[] { "CSV1004" }, r.Errors("Wrong"));
            Assert.Equal(new[] { "CSV1004" }, r.Errors("WrongEmpty"));
        }

        [Fact]
        public void AGenericDecisionRecord_TakesParamsAndKeepsTheList()
        {
            var r = Harness.Verify(@"using System.Collections.Generic;
public sealed record Shipped(int Qty);
public enum Why { NoStock }
public abstract record Verdict<TChange, TWhy>
{
    private Verdict() { }
    public static Verdict<TChange, TWhy> Grant(params TChange[] changes) { Spec.Ensures<Verdict<TChange, TWhy>>(r => r is Granted a && (object)a.Changes == changes); return new Granted(changes); }
    public static Verdict<TChange, TWhy> Refuse(TWhy why) { Spec.Ensures<Verdict<TChange, TWhy>>(r => r is Refused); return new Refused(why); }
    public sealed record Granted(IReadOnlyList<TChange> Changes) : Verdict<TChange, TWhy>;
    public sealed record Refused(TWhy Cause) : Verdict<TChange, TWhy>;
}
public static class Dispatch
{
    public static Verdict<Shipped, Why> Ship(int qty)
    {
        Spec.Ensures<Verdict<Shipped, Why>>(r => (r is Verdict<Shipped, Why>.Granted) == (qty > 0));
        return qty > 0 ? Verdict<Shipped, Why>.Grant(new Shipped(qty)) : Verdict<Shipped, Why>.Refuse(Why.NoStock);
    }
    public static int First(Verdict<Shipped, Why> o)
    {
        Spec.Requires(o is Verdict<Shipped, Why>.Granted a0 && a0.Changes.Count > 0);
        var e = ((Verdict<Shipped, Why>.Granted)o).Changes[0];
        return e == null ? 0 : e.Qty;
    }
    public static Verdict<Shipped, Why> Wrong(int qty)
    {
        Spec.Ensures<Verdict<Shipped, Why>>(r => r is Verdict<Shipped, Why>.Granted);
        return qty > 0 ? Verdict<Shipped, Why>.Grant(new Shipped(qty)) : Verdict<Shipped, Why>.Refuse(Why.NoStock);
    }
}");
            foreach (var ok in new[] { "Grant", "Refuse", "Ship", "First" })
            {
                Assert.True(r.Errors(ok).Length == 0, r.Explain(ok));
            }
            Assert.Equal(new[] { "CSV1002" }, r.Errors("Wrong"));
        }

        [Fact]
        public void ADecisionsPureCases_AreSeenByItsCallers()
        {
            // (a call knows a member's body where it is one expression with no effects, [Pure] or not)
            const string Source = @"using System.Collections.Generic;
public sealed record Shipped(int Qty);
public enum Why { NoStock }
public abstract record Verdict<TChange, TWhy>
{
    private Verdict() { }
    PURE public static Verdict<TChange, TWhy> Grant(params TChange[] changes) => new Granted(changes);
    PURE public static Verdict<TChange, TWhy> Refuse(TWhy why) => new Refused(why);
    public sealed record Granted(IReadOnlyList<TChange> Changes) : Verdict<TChange, TWhy>;
    public sealed record Refused(TWhy Cause) : Verdict<TChange, TWhy>;
}
public static class Dispatch
{
    public static Verdict<Shipped, Why> Ship(int qty)
    {
        Spec.Ensures<Verdict<Shipped, Why>>(r => (r is Verdict<Shipped, Why>.Granted) == (qty > 0));
        return qty > 0 ? Verdict<Shipped, Why>.Grant(new Shipped(qty)) : Verdict<Shipped, Why>.Refuse(Why.NoStock);
    }
}";
            foreach (var pure in new[] { Harness.Verify(Source.Replace("PURE", "[Pure]")), Harness.Verify(Source.Replace("PURE", "")) })
            {
                foreach (var ok in new[] { "Grant", "Refuse", "Ship" })
                {
                    Assert.True(pure.Errors(ok).Length == 0, pure.Explain(ok));
                }
            }
            // (a body of statements, with no contract: only its type)
            var opaque = Source.Replace("PURE public static Verdict<TChange, TWhy> Refuse(TWhy why) => new Refused(why);",
                "public static Verdict<TChange, TWhy> Refuse(TWhy why) { var refused = new Refused(why); return refused; }").Replace("PURE", "");
            Assert.Equal(new[] { "CSV1002" }, Harness.Verify(opaque).Errors("Ship"));
        }

        [Fact]
        public void AFieldsValue_IsOneOfItsType()
        {
            // (a record made of a field's value is a record: the decimal is a decimal, the DateTime's and the TimeSpan's
            // ticks are in their ranges, as an integer field's value is in its)
            var r = Harness.Verify(@"public sealed class Fund
{
    public decimal Price { get; set; }
    public DateTime At { get; set; }
    public TimeSpan Took { get; set; }
    public long Units { get; set; }
}
public sealed record Quote(decimal Price);
public sealed record Stamp(DateTime At);
public sealed record Lap(TimeSpan Took);
public sealed record Count(long Units);
public static class Reads
{
    public static Quote Price(Fund f) => new Quote(f.Price);
    public static Stamp At(Fund f) => new Stamp(f.At);
    public static Lap Took(Fund f) => new Lap(f.Took);
    public static Count Units(Fund f) => new Count(f.Units);
}");
            foreach (var m in new[] { "Price", "At", "Took", "Units" })
            {
                Assert.True(r.Errors("Reads." + m).Length == 0, r.Explain("Reads." + m));
            }
        }

        [Fact]
        public void Decimals_AreExact_WhereTheyAreRepresentable()
        {
            var r = Harness.Verify(@"public sealed record Payment(decimal Amount);
public static class Amounts
{
    public static bool Positive(decimal amount) { Spec.Ensures<bool>(r => r == (amount > 0m)); return amount > 0m; }
    public static decimal Sum(decimal a, decimal b) { Spec.Ensures<decimal>(r => r == a + b); return a + b; }
    public static decimal Neg(decimal a) { Spec.Ensures<decimal>(r => r == -a); return -a; }
    public static void Exact() { decimal x = 1.5m; decimal y = 2.25m; Spec.Assert(x + y == 3.75m); Spec.Assert(x - y == -0.75m); }
    public static void Ints(int n) { Spec.Requires(n > 0 && n < 1000); decimal d = n; Spec.Assert(d > 0m && d + 1 > d); }
    public static decimal Total(Payment[] ps)
    {
        decimal total = 0m;
        for (int i = 0; i < ps.Length; i++)
        {
            Spec.Invariant(0 <= i && total >= 0m);
            var p = ps[i];
            if (p != null && p.Amount > 0m && p.Amount < 1000000m && total < 1000000000m) total += p.Amount;
        }
        Spec.Assert(total >= 0m);
        return total;
    }
    public static decimal Overflows(decimal a) { Spec.Requires(a > 0m); Spec.EnsuresOnThrow<OverflowException>(false); return a + decimal.MaxValue; }
    // (79228162514264337593543950334 + 10^-28 needs 57 digits: it rounds)
    public static void Rounds() { decimal big = 79228162514264337593543950334m; decimal tiny = 0.0000000000000000000000000001m; Spec.Assert(big + tiny - big == tiny); }
    public static void MayRound(decimal a) { Spec.Assert(a + 1m > a); }
}");
            foreach (var ok in new[] { "Positive", "Sum", "Neg", "Exact", "Ints", "Total" })
            {
                Assert.True(r.Errors(ok).Length == 0, r.Explain(ok));
            }
            Assert.Equal(new[] { "CSV1002" }, r.Errors("Overflows"));
            Assert.Equal(new[] { "CSV1004" }, r.Errors("Rounds"));
            Assert.Equal(new[] { "CSV1004" }, r.Errors("MayRound"));
        }

        [Fact]
        public void ADecimalSumOrDifference_KeepsItsSign()
        {
            // (a whole number of units under 2^96 is representable, so what rounds is far from zero)
            var r = Harness.Verify(@"public static class Rests
{
    public static decimal Rest(decimal total, decimal fee) { Spec.Requires(total > fee); Spec.Ensures<decimal>(r => r > 0m); return total - fee; }
    public static decimal Owed(decimal paid, decimal due) { Spec.Requires(paid < due); Spec.Ensures<decimal>(r => r < 0m); return paid - due; }
    public static decimal Both(decimal a, decimal b) { Spec.Requires(a > 0m && b > 0m); Spec.Ensures<decimal>(r => r > 0m); return a + b; }
    public static decimal RestOrNone(decimal total, decimal fee) { Spec.Requires(total >= fee); Spec.Ensures<decimal>(r => r > 0m); return total - fee; }
    public static void BackAgain(decimal total, decimal fee) { Spec.Assert(total - fee + fee == total); }
}");
            foreach (var ok in new[] { "Rest", "Owed", "Both" })
            {
                Assert.True(r.Errors(ok).Length == 0, r.Explain(ok));
            }
            Assert.Equal(new[] { "CSV1002" }, r.Errors("RestOrNone"));
            // (the difference may round, and the sum again)
            Assert.Equal(new[] { "CSV1004" }, r.Errors("BackAgain"));
        }

        [Fact]
        public void ACollectionOfGuidsOrTimes_HoldsThemAsValues()
        {
            // (#136, P: a Guid, a DateTime or a TimeSpan is the integer the kernel keeps for it, in a collection too)
            var r = Harness.Verify(@"using System.Collections.Generic; using System.Linq;
public sealed class Line
{
    public Line(Guid item, int count) { Item = item; Count = count; }
    public Guid Item { get; }
    public int Count { get; }
}
public sealed class Basket
{
    private readonly List<Line> lines = new();
    public IReadOnlyList<Guid> Items => lines.Select(l => l.Item).ToList();
    public int Size() { Spec.Ensures<int>(r => r >= 0); return Items.Count; }
}
public sealed record Named(Guid Id, string Name);
public static class Ids
{
    public static bool Kept(List<Guid> ids, Guid id)
    {
        Spec.Requires(ids.Count < 1000);
        Spec.Ensures<bool>(r => r && ids.Count == Spec.Old(ids.Count) + 1 && ids[ids.Count - 1] == id);
        ids.Add(id);
        return ids.Contains(id);
    }
    public static Guid First(IReadOnlyList<Guid> ids) { Spec.Requires(ids.Count > 0); Spec.Ensures<Guid>(r => r == ids[0]); return ids[0]; }
    public static DateTime Latest(List<DateTime> at)
    {
        Spec.Requires(at.Count == 2);
        Spec.Ensures<DateTime>(r => r >= at[0] && r >= at[1]);
        return at[0] > at[1] ? at[0] : at[1];
    }
    public static int Stock(Dictionary<Guid, int> stock, Guid item) { Spec.Requires(stock.ContainsKey(item) && stock[item] == 3); Spec.Ensures<int>(r => r == 3); return stock[item]; }
    public static bool Seen(HashSet<Guid> seen, Guid id) { Spec.Ensures<bool>(r => !r && seen.Contains(id)); return seen.Add(id) && !seen.Contains(id); }
    public static IReadOnlyList<Guid> IdsOf(List<Named> named) { Spec.Ensures<IReadOnlyList<Guid>>(r => r.Count == named.Count); return named.Select(n => n.Id).ToList(); }
    public static void Put(IList<Guid> ids, Guid id) { Spec.Requires(ids.Count > 0); ids[0] = id; }
    public static int Waiting(Queue<TimeSpan> q) { Spec.Ensures<int>(r => r == q.Count); return q.Count; }
    public static bool Wrong(List<Guid> ids, Guid id) { Spec.Ensures<bool>(r => r); return ids.Contains(id); }
    public static bool WrongStock(Dictionary<Guid, int> stock, Guid a, Guid b) { Spec.Requires(stock.ContainsKey(a)); Spec.Ensures<bool>(r => r); return stock.ContainsKey(b); }
}");
            foreach (var ok in new[] { "get_Items", "Size", "Kept", "First", "Latest", "Stock", "Seen", "IdsOf", "Put", "Waiting" })
            {
                Assert.True(r.Errors(ok).Length == 0, r.Explain(ok));
            }
            Assert.Equal(new[] { "CSV1002" }, r.Errors("Wrong"));
            Assert.Equal(new[] { "CSV1002" }, r.Errors("WrongStock"));
        }

        [Fact]
        public void ACollectionOfRecordStructs_AndADateOnly()
        {
            // (#136, P' and S: a typed id is a value a collection may hold and compare; a DateOnly is its day's number)
            var r = Harness.Verify(@"using System.Collections.Generic; using System.Linq;
public readonly record struct ItemId(Guid Value);
public readonly record struct Named(string Name, int No);
public sealed record Part(ItemId Item, decimal Amount);
public sealed record Slot(Guid Id, DateOnly Day);
public sealed class Order
{
    private readonly List<Part> parts = new();
    public Guid Id { get; private set; }
    internal DateOnly Day { get; private set; }
    public IReadOnlyList<ItemId> Items => parts.Select(p => p.Item).ToList();
    public Slot Current => new(Id, Day);
    public int Size() { Spec.Ensures<int>(r => r >= 0); return Items.Count; }
    public bool Later(Order other) { Spec.Ensures<bool>(r => r == (Day > other.Day)); return Day > other.Day; }
}
public static class Keys
{
    public static int Stock(Dictionary<ItemId, int> stock, ItemId item) { Spec.Requires(stock.ContainsKey(item) && stock[item] == 3); Spec.Ensures<int>(r => r == 3); return stock[item]; }
    public static bool Seen(HashSet<ItemId> seen, ItemId id) { Spec.Ensures<bool>(r => !r && seen.Contains(id)); return seen.Add(id) && !seen.Contains(id); }
    public static bool Has(List<ItemId> ids, ItemId id) { Spec.Ensures<bool>(r => r == ids.Contains(id)); return ids.Contains(id); }
    public static ItemId First(IReadOnlyList<ItemId> ids) { Spec.Requires(ids.Count > 0); Spec.Ensures<ItemId>(r => r == ids[0]); return ids[0]; }
    public static IReadOnlyList<ItemId> Of(List<Part> parts) { Spec.Ensures<IReadOnlyList<ItemId>>(r => r.Count == parts.Count); return parts.Select(p => p.Item).ToList(); }
    public static int Names(List<Named> names) { Spec.Ensures<int>(r => r == names.Count); return names.Count; }
    public static bool HasName(List<Named> names, Named n) { return names.Contains(n); }
    public static int ByName(Dictionary<Named, int> d) { return d.Count; }
    public static bool WrongStock(Dictionary<ItemId, int> stock, ItemId a, ItemId b) { Spec.Requires(stock.ContainsKey(a)); Spec.Ensures<bool>(r => r); return stock.ContainsKey(b); }
}");
            foreach (var ok in new[] { "get_Items", "get_Current", "Size", "Later", "Stock", "Seen", "Has", "First", "Of", "Names" })
            {
                Assert.True(r.Errors(ok).Length == 0, r.Explain(ok));
            }
            Assert.Equal(new[] { "CSV1002" }, r.Errors("WrongStock"));
            // (a struct with a string compares it by its characters, which a collection's model doesn't: no key, and no Contains)
            Assert.Equal(new[] { "CSV1902" }, r.Errors("HasName"));
            Assert.Equal(new[] { "CSV1902" }, r.Errors("ByName"));
        }

        [Fact]
        public void AComputedListsCount_IsItsSources_WhereItIs()
        {
            // (#136, P'': a member of one expression that makes a list states no contract; that its result has as many
            // elements as a collection it names is a candidate, proved in its body and assumed by its callers while it holds)
            var r = Harness.Verify(@"using System.Collections.Generic; using System.Linq;
public sealed class Line
{
    public Line(Guid item, int count) { Item = item; Count = count; }
    public Guid Item { get; }
    public int Count { get; }
}
public sealed class Basket
{
    private readonly List<Line> lines = new();
    public IReadOnlyList<Guid> Items => lines.Select(l => l.Item).ToList();
    public IReadOnlyList<Guid> Big => lines.Where(l => l.Count > 1).Select(l => l.Item).ToList();
    public List<int> Counts() => lines.Select(l => l.Count).ToList();
    public static IReadOnlyList<Guid> Of(List<Line> given) => given.Select(l => l.Item).ToList();
    public int Size() { Spec.Ensures<int>(r => r == lines.Count); return Items.Count; }
    public int Sizes() { Spec.Ensures<int>(r => r == lines.Count); return Counts().Count; }
    public static int OfSize(List<Line> given) { Spec.Ensures<int>(r => r == given.Count); return Of(given).Count; }
    public int Bigs() { Spec.Ensures<int>(r => r == lines.Count); return Big.Count; }
    public int After() { Spec.Ensures<int>(r => r == lines.Count); var items = Items; lines.Add(new Line(Guid.Empty, 1)); return items.Count; }
}");
            foreach (var ok in new[] { "get_Items", "get_Big", "Counts", "Of", "Size", "Sizes", "OfSize" })
            {
                Assert.True(r.Errors(ok).Length == 0, r.Explain(ok));
            }
            // (a filter keeps fewer: no such fact, and the member is none the worse; a count is of the list as it was made)
            Assert.Equal(new[] { "CSV1002" }, r.Errors("Bigs"));
            Assert.Equal(new[] { "CSV1002" }, r.Errors("After"));
        }

        [Fact]
        public void AListThroughAGetter_IsThatList()
        {
            // (what a collection behind an interface is goes with it where it is converted, in the getter: a candidate
            // postcondition, so that its caller reads the list)
            var r = Harness.Verify(@"using System.Collections.Generic;
public sealed record Part(int No);
public sealed class Order
{
    private readonly List<int> ids = new();
    private readonly List<Part> parts = new();
    private readonly int[] codes = new int[4];
    public IReadOnlyList<int> Ids => ids;
    public IReadOnlyList<Part> Parts => parts;
    public IReadOnlyList<int> Codes() { return codes; }
    public IReadOnlyList<int> Either(bool a) { if (a) { return ids; } return codes; }
    public int First() { Spec.Requires(ids.Count > 0); Spec.Ensures<int>(r => r == ids[0]); return Ids[0]; }
    public int Size() { Spec.Ensures<int>(r => r == ids.Count); return Ids.Count; }
    public Part FirstPart() { Spec.Requires(parts.Count > 0); Spec.Ensures<Part>(r => r == parts[0]); return Parts[0]; }
    public int Code() { Spec.Requires(codes.Length == 4); Spec.Ensures<int>(r => r == codes[0]); return Codes()[0]; }
    public int After() { Spec.Requires(ids.Count == 1); Spec.Ensures<int>(r => r == 2); var seen = Ids; ids.Add(7); return seen.Count; }
    public static int Other(Order o) { Spec.Requires(o.ids.Count > 0); Spec.Ensures<int>(r => r == o.ids[0]); return o.Ids[0]; }
    public int Unknown(bool a) { Spec.Requires(ids.Count > 0 && codes.Length > 0); return Either(a)[0]; }
    public static bool Has(IReadOnlyList<int> xs, int x)
    {
        Spec.Ensures<bool>(r => !r || xs.Count > 0);
        for (int i = 0; i < xs.Count; i++) { if (xs[i] == x) { return true; } }
        return false;
    }
}");
            foreach (var ok in new[] { "First", "Size", "FirstPart", "Code", "After", "Other", "Has" })
            {
                Assert.True(r.Errors(ok).Length == 0, r.Explain(ok));
            }
            // (a list or an array, by the path taken: neither is said)
            Assert.Equal(new[] { "CSV1003" }, r.Errors("Unknown"));
        }

        [Fact]
        public void ARecordsEquality_ComparesAStructADateAndADecimalField()
        {
            // (a record's synthesized Equals compares each field as its type does: a typed id by its value)
            var r = Harness.Verify(@"public readonly record struct TicketId
{
    public TicketId(Guid value) { if (value == Guid.Empty) { throw new ArgumentException(""empty"", nameof(value)); } Value = value; }
    public Guid Value { get; }
}
public sealed record Seat
{
    public Seat(TicketId id, string row, DateOnly day, decimal price) { Id = id; Row = row; Day = day; Price = price; }
    public TicketId Id { get; }
    public string Row { get; }
    public DateOnly Day { get; }
    public decimal Price { get; }
}
public static class Seats
{
    public static bool Same(Seat a, Seat b) { Spec.Ensures<bool>(r => r == (a.Id == b.Id && a.Row == b.Row && a.Day == b.Day && a.Price == b.Price)); return a == b; }
    public static bool SameId(TicketId a, TicketId b) { Spec.Ensures<bool>(r => r == (a.Value == b.Value)); return a == b; }
    public static bool Wrong(Seat a, Seat b) { Spec.Ensures<bool>(r => r == (a.Id == b.Id)); return a == b; }
}");
            Assert.True(r.Errors("Same").Length == 0, r.Explain("Same"));
            Assert.True(r.Errors("SameId").Length == 0, r.Explain("SameId"));
            Assert.Equal(new[] { "CSV1002" }, r.Errors("Wrong"));
        }

        [Fact]
        public void AnEmptyPropertyPattern_OfANullableValue_IsItsValue()
        {
            // (x is { } v of an int?, an enum?, a date?: where it has a value, v is it; xs is { Count: > 0 }: not null, and its count)
            var r = Harness.Verify(@"using System.Collections.Generic;
public enum Step { One, Two }
public readonly record struct Fee(decimal Amount);
public sealed class Flow
{
    public Step? Failed { get; private set; }
    public DateTime? LockedUntil { get; private set; }
    public DateOnly? Start { get; private set; }
    public int? Enrolment { get; private set; }
    public Fee? Goal { get; private set; }
    public Guid? Owner { get; private set; }
    public bool CanRestart => Failed is { } failed && failed == Step.Two;
    public bool Restarts() { Spec.Ensures<bool>(r => r == (Failed == Step.Two)); return CanRestart; }
    public bool Locked(DateTime now) { Spec.Ensures<bool>(r => r == (LockedUntil != null && now < LockedUntil.Value)); return LockedUntil is { } until && now < until; }
    public bool Within(int cap) { Spec.Ensures<bool>(r => r == (Enrolment != null && Enrolment.Value <= cap)); return Enrolment is { } number && number <= cap; }
    public bool Started(DateOnly today) { Spec.Ensures<bool>(r => !r || Start != null); if (Start is not { } start || start > today) { return false; } return true; }
    public decimal GoalOr(decimal none) { Spec.Ensures<decimal>(r => Goal != null || r == none); if (Goal is not { } goal) { return none; } return goal.Amount; }
    public bool Owned(Guid by) { Spec.Ensures<bool>(r => r == (Owner != null && Owner.Value == by)); return Owner is { } owner && owner == by; }
    public static int Size(IReadOnlyList<int> xs) { Spec.Ensures<int>(r => r >= 0 && (r == 0 || xs != null)); return xs is { Count: > 0 } ? xs.Count : 0; }
    public static bool Text(string s) { Spec.Ensures<bool>(r => r == (s != null && s.Length == 3)); return s is { Length: 3 }; }
    public static bool Wrong(int? x) { Spec.Ensures<bool>(r => r); return x is { } v && v > 0; }
}");
            foreach (var ok in new[] { "get_CanRestart", "Restarts", "Locked", "Within", "Started", "GoalOr", "Owned", "Size", "Text" })
            {
                Assert.True(r.Errors(ok).Length == 0, r.Explain(ok));
            }
            Assert.Equal(new[] { "CSV1002" }, r.Errors("Wrong"));
        }

        [Fact]
        public void ASensitiveValueObject_WithItsOwnEquals_IsOfTheSubset()
        {
            // ([Sensitive] is the taint analysis's; a record's own Equals is its ==, a function where it is one; a set
            // through its interface is the set; string.Empty is the empty string)
            var r = Harness.Verify(@"using System.Collections.Generic; using System.Linq;
public enum Step { Ask, Wait, Done }
[Sensitive]
public sealed record Email
{
    private Email(string value) => Value = value;
    public string Value { get; }
    public static Email Parse(string value) => value.Length > 3 ? new Email(value) : throw new FormatException(""no"");
    public bool Equals(Email? other) => other is not null && string.Equals(Value, other.Value, StringComparison.OrdinalIgnoreCase);
    public override int GetHashCode() => StringComparer.OrdinalIgnoreCase.GetHashCode(Value);
    public override string ToString() => Value;
}
public sealed record Code
{
    public Code(string text) { Text = text; }
    public string Text { get; }
    public bool Equals(Code? other) => other is not null && Text.Length == other.Text.Length;
    public override int GetHashCode() => Text.Length;
}
public static class Steps
{
    public static readonly IReadOnlySet<Step> Waits = new HashSet<Step> { Step.Wait };
}
public sealed class Flow
{
    public string? Digits { get; private set; }
    public Email? Contact { get; private set; }
    public bool Waiting(Step step) { return Steps.Waits.Contains(step) && Steps.Waits.Count > 0; }
    public static bool In(HashSet<Step> steps, Step step) { Spec.Requires(steps.Contains(step)); Spec.Ensures<bool>(r => r); IReadOnlySet<Step> seen = steps; return seen.Contains(step); }
    public string Shown() { Spec.Ensures<string>(r => r != null && (Digits != null || r.Length == 0)); return Digits ?? string.Empty; }
    public bool Has(Email e) { return Contact == e; }
    public int Len() { Spec.Ensures<int>(r => r >= 0 && (Contact != null || r == 0)); return Contact == null ? 0 : Contact.Value.Length; }
    public static bool Same(Code a, Code b) { Spec.Ensures<bool>(r => r == (a.Text.Length == b.Text.Length)); return a == b; }
    public static bool Wrong(Code a, Code b) { Spec.Ensures<bool>(r => r == (a.Text == b.Text)); return a == b; }
}");
            foreach (var ok in new[] { "Parse", "Waiting", "In", "Shown", "Has", "Len", "Same" })
            {
                Assert.True(r.Errors(ok).Length == 0, r.Explain(ok));
            }
            Assert.Equal(new[] { "CSV1002" }, r.Errors("Wrong"));
        }

        [Fact]
        public void ADecimal_IsWithinItsRange_WhereverItComesFrom()
        {
            // (#136, T: a record's constructor takes a decimal of decimal's range, which a parameter, a result, a
            // struct's part and what arithmetic gives without overflowing are)
            var r = Harness.Verify(@"public readonly record struct Fee(decimal Amount);
public sealed record Pair(int? A, decimal B)
{
    public Pair Make(int a, decimal b) => new Pair(a, b);
    public static Pair Of(int a, decimal b) { return new Pair(a, b); }
    public static Pair Sum(decimal a, decimal b) { var s = a + b; return new Pair(1, s); }
    public static Pair Times(decimal a, decimal b) { var s = a * b; return new Pair(1, s); }
    public static Pair Over(decimal a, decimal b) { Spec.Requires(b != 0m); var s = a / b; return new Pair(1, s); }
    public static Pair OfFee(Fee f) { return new Pair(2, f.Amount); }
    public static Pair Again(Pair p) { return new Pair(p.A, Twice(p.B)); }
    public static decimal Twice(decimal x) { return x + x; }
}");
            Assert.True(r.Success, string.Join("\n", r.Diagnostics.Where(d => d.IsError).Select(d => d.Id + " " + d.Message)));
        }

        [Fact]
        public void ANewArray_ChangesNoArray_SoAListsCountStays()
        {
            // (a new array is an object not allocated before whose cells are what it is made with: no cell is written,
            // so what a list read through an interface held before a params array was made, it holds after)
            var r = Harness.Verify(@"using System.Collections.Generic; using System.Linq;
public readonly record struct BatchId(Guid Value);
public readonly record struct Fee(decimal Amount);
public sealed record Member(BatchId Item, Fee Amount);
public sealed record Terms(BatchId Id, DateOnly Day, IReadOnlyList<Member> Members, string Note, DateTime At, BatchId Other);
public abstract record Command { private protected Command(DateTime now) => Now = now; public DateTime Now { get; } }
public sealed record Request(Terms Terms, DateTime Now) : Command(Now);
public abstract record Event;
public sealed record Requested(Terms Terms, DateTime At) : Event;
public enum Why { Nothing }
public abstract record Decision<TEvent, TWhy>
{
    private Decision() { }
    public static Decision<TEvent, TWhy> Accept(params TEvent[] events) { Spec.Ensures<Decision<TEvent, TWhy>>(r => r is Accepted a && a.Events == events); return new Accepted(events); }
    public static Decision<TEvent, TWhy> Reject(TWhy why) { Spec.Ensures<Decision<TEvent, TWhy>>(r => r is Rejected j && j.Events.Count == 0); return new Rejected(why); }
    public sealed record Accepted(IReadOnlyList<TEvent> Events) : Decision<TEvent, TWhy>;
    public sealed record Rejected(TWhy Reason) : Decision<TEvent, TWhy> { public IReadOnlyList<TEvent> Events { get; init; } = Array.Empty<TEvent>(); }
}
public static class Batches
{
    public static Decision<Event, Why> DecideNew(Request command)
    {
        Spec.Ensures<Decision<Event, Why>>(r =>
            r is Decision<Event, Why>.Accepted a
                ? a.Events.Count == 1 && a.Events[0] is Requested b && b.Terms == command.Terms && command.Terms.Members.Count > 0
                : r is Decision<Event, Why>.Rejected j && j.Events.Count == 0);
        return command.Terms.Members.Count == 0 || command.Terms.Members.Any(m => m.Amount.Amount <= 0m)
            ? Decision<Event, Why>.Reject(Why.Nothing)
            : Decision<Event, Why>.Accept(new Requested(command.Terms, command.Now));
    }
}
public static class Arrays
{
    public static int[] Three() { Spec.Ensures<int[]>(r => r.Length == 3 && r[0] == 1 && r[2] == 3); return new[] { 1, 2, 3 }; }
    public static int[] Zeros(int n) { Spec.Requires(n > 0); Spec.Ensures<int[]>(r => r.Length == n && r[0] == 0); return new int[n]; }
    public static int Kept(int[] a) { Spec.Requires(a.Length > 0 && a[0] == 7); Spec.Ensures<int>(r => r == 7); var b = new int[2]; b[0] = 9; return a[0]; }
    public static bool Fresh(int[] a) { Spec.Ensures<bool>(r => r); var b = new int[1]; return !ReferenceEquals(a, b); }
    public static int Loop(int n) { Spec.Requires(0 < n && n < 100); Spec.Ensures<int>(r => r == 5); int[] last = new[] { 5 }; for (int i = 0; i < n; i++) { Spec.Invariant(last.Length == 1 && last[0] == 5); last = new[] { 5 }; } return last[0]; }
    public static int Count(IReadOnlyList<int> xs) { Spec.Requires(xs.Count > 0); Spec.Ensures<int>(r => r > 0); var tmp = new[] { 1, 2 }; return xs.Count; }
    public static bool Wrong() { Spec.Ensures<bool>(r => r); var a = new[] { 1 }; var b = new[] { 2 }; return a[0] == b[0]; }
}");
            foreach (var ok in new[] { "DecideNew", "Three", "Zeros", "Kept", "Fresh", "Loop", "Arrays.Count" })
            {
                Assert.True(r.Errors(ok).Length == 0, r.Explain(ok));
            }
            Assert.Equal(new[] { "CSV1002" }, r.Errors("Wrong"));
        }

        [Fact]
        public void ALambdaInARecordsMember_ANullableDecimal_ASequenceOfDates()
        {
            // (a data type's member may hold a lambda; a decimal? is a nullable value; an IEnumerable of dates, structs
            // or tuples is a reference as any other's)
            var r = Harness.Verify(@"using System.Collections.Generic; using System.Linq;
public readonly record struct Fee(decimal Amount);
public sealed record Prize(int Level, DateTime? PaidAt, DateTime? SeenAt);
public sealed record Stage(int Id, int Level);
public sealed record Standing(int? Enrolment, IReadOnlyList<Prize> Prizes, Fee Saved, decimal? Bonus)
{
    public bool Has(Stage s) => Prizes.Any(p => p.Level == s.Level);
    public Prize? PrizeFor(Stage s) => Prizes.FirstOrDefault(p => p.Level == s.Level);
    public decimal BonusOr(decimal none) { Spec.Ensures<decimal>(r => Bonus != null || r == none); return Bonus ?? none; }
}
public enum Step { One, Two }
public sealed record Progress(Step? Done, Step? Failed, string? Reason);
public sealed class Flow
{
    public Progress SetUp { get; private set; } = new Progress(null, null, null);
    public int Count { get; private set; }
    public void Done(Step step) => SetUp = SetUp.Failed == step ? SetUp with { Done = step, Failed = null, Reason = null } : SetUp with { Done = step };
    public void Bump(bool twice) { Spec.Requires(Count < 100); Spec.Ensures(Count == Spec.Old(Count) + (twice ? 2 : 1)); Count = twice ? Count + 2 : Count + 1; }
}
public static class Uses
{
    public static decimal Half(decimal? x) { Spec.Ensures<decimal>(r => x != null || r == 0m); return x is { } v ? v : 0m; }
    public static bool Wrong(decimal? x) { Spec.Ensures<bool>(r => r); return x is { } v && v > 0m; }
    public static int Days(IEnumerable<DateOnly> days) { Spec.Ensures<int>(r => r >= 0); return days.Count(); }
    public static int Fees(IEnumerable<Fee> fees) { Spec.Ensures<int>(r => r >= 0); return fees.Count(); }
    public static int Pairs(IEnumerable<(DateTime At, decimal Amount)> xs) { Spec.Ensures<int>(r => r >= 0); return xs.Count(); }
    public static int Listed(IReadOnlyList<(int No, string Name)> xs) { Spec.Ensures<int>(r => r == xs.Count); return xs.Count; }
}");
            // (and an auto-property assigned a value that branches, P = c ? a : b: its field)
            foreach (var ok in new[] { "Has", "PrizeFor", "BonusOr", "Half", "Days", "Fees", "Pairs", "Listed", "Flow.Done", "Bump" })
            {
                Assert.True(r.Errors(ok).Length == 0, r.Explain(ok));
            }
            Assert.Equal(new[] { "CSV1002" }, r.Errors("Wrong"));
        }

        [Fact]
        public void ASetMadeOfASequence_HoldsItsElements()
        {
            // (ToHashSet: a new set whose members are what some element is; as many as the elements where no two are
            // the same, fewer otherwise)
            var r = Harness.Verify(@"using System.Collections.Generic; using System.Linq;
public static class Sets
{
    public static bool Has(int[] xs) { Spec.Requires(xs.Length > 2); Spec.Ensures<bool>(r => r); var s = xs.ToHashSet(); return s.Contains(xs[1]) && s.Count > 0 && s.Count <= xs.Length; }
    public static bool Lacks(List<int> xs, int y) { Spec.Requires(Spec.Forall(0, xs.Count, i => xs[i] != y)); Spec.Ensures<bool>(r => !r); return xs.ToHashSet().Contains(y); }
    public static int Three() { Spec.Ensures<int>(r => r == 3); return new[] { 1, 2, 3 }.ToHashSet().Count; }
    public static bool Names(List<string> xs) { Spec.Requires(xs.Count > 0); Spec.Ensures<bool>(r => r); return xs.ToHashSet().Contains(xs[0]); }
    public static int Miscounted(int[] xs) { Spec.Ensures<int>(r => r == xs.Length); return xs.ToHashSet().Count; }
    public static bool Guessed(int[] xs, int y) { Spec.Ensures<bool>(r => r); return xs.ToHashSet().Contains(y); }
}");
            foreach (var ok in new[] { "Has", "Lacks", "Three", "Names" })
            {
                Assert.True(r.Errors(ok).Length == 0, r.Explain(ok));
            }
            Assert.Equal(new[] { "CSV1002" }, r.Errors("Miscounted"));
            Assert.Equal(new[] { "CSV1002" }, r.Errors("Guessed"));
        }

        [Fact]
        public void AQuerysCopy_ChangesNoCollection_AndAHelperThatRunsAQuery_NoField()
        {
            // (a list, an array or a set a query is copied to is a new object that holds what it is made with: nothing
            // is written, so a list read through an interface holds what it held. A library member handed a lambda
            // that writes nothing changes nothing; nor does a set that compares records whose equality is their
            // fields'. One whose Equals writes, does)
            var r = Harness.Verify(@"using System.Collections.Generic; using System.Linq;
public sealed record Tag { public Tag(string v) { Value = v; } public string Value { get; } public override string ToString() => Value; }
public sealed record Leg(Tag Carrier, int Miles);
public sealed record Loud { public static int Seen; public Loud(string v) { Value = v; } public string Value { get; } public bool Equals(Loud? other) { Seen = 1; return other is not null && other.Value == Value; } public override int GetHashCode() => 0; }
public sealed class Route
{
    private readonly List<Leg> legs = new();
    public int State { get; private set; }
    public Tag? Via { get; private set; }
    public int Listed(IReadOnlyList<Leg> offered) { Spec.Ensures<int>(r => r <= offered.Count); var added = offered.Where(l => l.Miles > 0).ToList(); return added.Count; }
    public int Arrayed(IReadOnlyList<Leg> offered) { Spec.Ensures<int>(r => r <= offered.Count); var added = offered.Where(l => l.Miles > 0).ToArray(); return added.Length; }
    public int Fresh(IReadOnlyList<Leg> offered) { Spec.Ensures<int>(r => 0 <= r && r <= offered.Count && State == Spec.Old(State)); var known = legs.Select(l => l.Carrier).ToHashSet(); return offered.Where(l => !known.Contains(l.Carrier)).ToList().Count; }
    private int Unknown(IReadOnlyList<Leg> offered) { var known = legs.Select(l => l.Carrier).ToHashSet(); return offered.Where(l => !known.Contains(l.Carrier)).DistinctBy(l => l.Carrier).ToList().Count; }
    public bool Steady(IReadOnlyList<Leg> offered, Tag via) { Spec.Requires(Via == via); Spec.Ensures<bool>(r => r && State == Spec.Old(State)); Unknown(offered); return Via == via; }
    public bool Quiet(Tag t) { Spec.Ensures<bool>(r => State == Spec.Old(State)); var known = new HashSet<Tag>(); return known.Contains(t); }
    public bool Heard(Loud t) { Spec.Requires(Loud.Seen == 0); Spec.Ensures<bool>(r => Loud.Seen == 0); var known = new HashSet<Loud>(); return known.Contains(t); }
}
public sealed class Person { public string Name = """"; public string Email = """"; }
public static class Pairs
{
    public static void Joined(List<Person> xs, List<Person> ys) { var r = xs.Join(ys, a => a.Name, b => b.Email, (a, b) => new { a.Name, b.Email }).ToList(); Spec.Assert(Spec.Forall(0, r.Count, i => r[i].Name == r[i].Email)); }
}");
            foreach (var ok in new[] { "Listed", "Arrayed", "Fresh", "Route.Unknown", "Steady", "Quiet", "Joined" })
            {
                Assert.True(r.Errors(ok).Length == 0, r.Explain(ok));
            }
            Assert.Equal(new[] { "CSV1002" }, r.Errors("Heard"));
        }

        [Fact]
        public void ASumOfDecimals_IsAddedInOrder()
        {
            // (Sum of decimals: from 0, each sum as decimal + gives it; what needs induction over its elements, their
            // sign say, isn't known of it)
            var r = Harness.Verify(@"using System.Collections.Generic; using System.Linq;
public readonly record struct Fee(decimal Amount);
public sealed record Line(int Kind, Fee Fee);
public sealed class Bill
{
    private readonly List<Line> lines = new();
    public decimal Total() { return lines.Sum(x => x.Fee.Amount); }
    public decimal Due(Func<Line, bool> include) { Spec.Requires(Spec.Total(include)); return lines.Where(x => x.Kind == 1 && include(x)).Sum(x => x.Fee.Amount); }
    public static decimal None(List<Line> ls) { Spec.Requires(ls.Count == 0); Spec.Ensures<decimal>(r => r == 0m); return ls.Sum(x => x.Fee.Amount); }
    public static decimal Half(List<Line> ls) { Spec.Requires(ls.Count == 1 && ls[0] != null && ls[0].Fee.Amount == 0.5m); Spec.Ensures<decimal>(r => r == 0.5m); return ls.Sum(x => x.Fee.Amount); }
    public static decimal Hoped(List<Line> ls) { Spec.Ensures<decimal>(r => r >= 0m); return ls.Sum(x => x.Fee.Amount); }
    public static decimal Feared(List<Line> ls) { Spec.Requires(ls.Count == 1 && ls[0] != null && ls[0].Fee.Amount == 0.5m); Spec.Ensures<decimal>(r => r == 1m); return ls.Sum(x => x.Fee.Amount); }
}");
            foreach (var ok in new[] { "Bill.Total", "Due", "None", "Half" })
            {
                Assert.True(r.Errors(ok).Length == 0, r.Explain(ok));
            }
            foreach (var wrong in new[] { "Hoped", "Feared" })
            {
                Assert.Equal(new[] { "CSV1002" }, r.Errors(wrong));
            }
        }

        [Fact]
        public void AFuncsResult_IsNotNull_WhereItsTypeSaysSo()
        {
            // (#136, Q: each lambda made one is checked to return what its type says; and a Func may give a generic record)
            var r = Harness.Verify(@"public sealed record Outcome(int Code);
public abstract record Verdict<T> { private Verdict() { } public sealed record Yes(T Value) : Verdict<T>; public sealed record No : Verdict<T>; }
public static class Runs
{
    public static Outcome When(bool open, Func<Outcome> then) { Spec.Requires(Spec.Pre(then)); Spec.Ensures<Outcome>(r => open || r.Code == 0); return open ? then() : new Outcome(0); }
    public static Outcome Maybe(Func<Outcome?> then) { Spec.Requires(Spec.Pre(then)); return then(); }
    public static Outcome Use() { return When(true, () => new Outcome(1)); }
    public static Outcome Bad() { return When(true, () => null!); }
    public static int Code(Func<Verdict<int>> then) { Spec.Requires(Spec.Pre(then)); Spec.Ensures<int>(r => r >= 0); return then() is Verdict<int>.Yes y && y.Value > 0 ? y.Value : 0; }
}");
            foreach (var ok in new[] { "Runs.When", "Runs.Use", "Runs.Bad", "Runs.Code" })
            {
                Assert.True(r.Errors(ok).Length == 0, r.Explain(ok));
            }
            Assert.Equal(new[] { "CSV1014" }, r.Errors("Maybe"));
            Assert.Contains(r.Methods, m => m.Name.Contains("Bad.<lambda") && m.Diagnostics.Any(d => d.Id == "CSV1014"));
        }

        [Fact]
        public void DecimalProductsAndQuotients_AreExact_WhereTheyAreRepresentable()
        {
            var r = Harness.Verify(@"public static class Prices
{
    public static void Exact() { Spec.Assert(1.5m * 2m == 3m); Spec.Assert(10m / 4m == 2.5m); Spec.Assert(7.5m % 2m == 1.5m); Spec.Assert(-7.5m % 2m == -1.5m); }
    public static decimal Line(decimal unit, int qty)
    {
        Spec.Requires(unit >= 0m && unit < 1000000m && qty >= 0 && qty <= 1000);
        Spec.Ensures<decimal>(r => r >= 0m);
        return unit * qty;
    }
    public static decimal Share(decimal total, int n) { Spec.Requires(total >= 0m && n > 0); Spec.Ensures<decimal>(r => r >= 0m); return total / n; }
    public static decimal Scaled(decimal a) { Spec.Requires(a > 0m && a < 1000m); var b = a; b *= 2m; Spec.Assert(b >= 0m); return b; }
    public static decimal ByZero(decimal a, decimal b) => a / b;
    public static decimal RemByZero(decimal a, decimal b) => a % b;
    public static decimal Overflows(decimal a) { Spec.Requires(a > 1m); Spec.EnsuresOnThrow<OverflowException>(false); return a * decimal.MaxValue; }
    // (1 / 3 isn't representable: it rounds)
    public static void WrongExact() { Spec.Assert(10m / 4m == 2m); }
    public static void Thirds() { decimal third = 1m / 3m; Spec.Assert(third * 3m == 1m); }
}");
            foreach (var ok in new[] { "Exact", "Line", "Share", "Scaled" })
            {
                Assert.True(r.Errors(ok).Length == 0, r.Explain(ok));
            }
            Assert.Equal(new[] { "CSV1009" }, r.Errors("ByZero"));
            Assert.Equal(new[] { "CSV1009" }, r.Errors("RemByZero"));
            Assert.Equal(new[] { "CSV1002" }, r.Errors("Overflows"));
            Assert.Equal(new[] { "CSV1004" }, r.Errors("WrongExact"));
            Assert.Equal(new[] { "CSV1004" }, r.Errors("Thirds"));
        }

        private const string Prices = @"using System.Linq;
public readonly record struct Price
{
    public Price(decimal value, string currency)
    {
        Spec.Ensures(Value == value && Currency == currency);
        if (currency.Length != 3 || !currency.All(char.IsAsciiLetter)) throw new ArgumentException(""currency"");
        Value = value;
        Currency = currency;
    }
    public decimal Value { get; }
    public string Currency { get; }
    public static Price operator +(Price a, Price b)
    {
        Spec.Requires(a.Currency == b.Currency);
        Spec.Ensures<Price>(r => r.Value == a.Value + b.Value && r.Currency == a.Currency);
        return new(a.Value + b.Value, a.Currency);
    }
    public static Price operator -(Price a) { Spec.Ensures<Price>(r => r.Value == -a.Value && r.Currency == a.Currency); return new(-a.Value, a.Currency); }
    public static bool operator <(Price a, Price b) { Spec.Requires(a.Currency == b.Currency); Spec.Ensures<bool>(r => r == (a.Value < b.Value)); return a.Order(b) < 0; }
    public static bool operator >(Price a, Price b) { Spec.Requires(a.Currency == b.Currency); return a.Order(b) > 0; }
    [Pure] public int Order(Price other) => Value.CompareTo(other.Value);
}
";

        [Fact]
        public void UserDefinedOperators_AreCallsOfTheirMethods_UnderTheirContracts()
        {
            var r = Harness.Verify(Prices + @"public static class Basket
{
    public static Price Total(Price a, Price b) { Spec.Requires(a.Currency == b.Currency); Spec.Ensures<Price>(p => p.Value == a.Value + b.Value); return a + b; }
    public static bool Cheaper(Price a, Price b) { Spec.Requires(a.Currency == b.Currency); Spec.Ensures<bool>(c => c == (a.Value < b.Value)); return a < b; }
    public static Price Refund(Price a) { Spec.Ensures<Price>(p => p.Value == -a.Value); return -a; }
    // (a sum of two currencies: the operator's precondition)
    public static Price Mixed(Price a, Price b) => a + b;
    public static void Wrong(Price a, Price b) { Spec.Requires(a.Currency == b.Currency); var c = a + b; Spec.Assert(c.Value == a.Value); }
    public static void Letters() { Spec.Assert(char.IsAsciiLetterUpper('Q') && char.IsAsciiDigit('7') && !char.IsAsciiLetter('7')); }
    public static void NotLetters() { Spec.Assert(char.IsAsciiLetterLower('Q')); }
}");
            foreach (var ok in new[] { "Price..ctor", "op_Addition", "op_UnaryNegation", "op_LessThan", "op_GreaterThan", "Order", "Total", "Cheaper", "Refund", "Letters" })
            {
                Assert.True(r.Errors(ok).Length == 0, r.Explain(ok));
            }
            Assert.Equal(new[] { "CSV1001" }, r.Errors("Mixed"));
            Assert.Equal(new[] { "CSV1004" }, r.Errors("Wrong"));
            Assert.Equal(new[] { "CSV1004" }, r.Errors("NotLetters"));
        }

        [Fact]
        public void AnOperatorWithoutAContract_IsNoInternalError()
        {
            // (#48: an operator's declaration had no syntax for the static checks; a callee's decimal postcondition had no model)
            var r = Harness.Verify(@"public readonly record struct Weight(decimal Kg)
{
    public static Weight operator +(Weight a, Weight b) => new(a.Kg + b.Kg);
    public static Weight Twice(Weight a) { Spec.Ensures<Weight>(w => w.Kg == a.Kg + a.Kg); return new(a.Kg + a.Kg); }
}
public static class Loads { public static Weight Four(Weight a) { var b = Weight.Twice(a); return b + b; } }");
            Assert.DoesNotContain(r.Methods.SelectMany(m => m.Diagnostics), d => d.Id == "CSV1999");
            foreach (var ok in new[] { "op_Addition", "Twice", "Four" })
            {
                Assert.True(r.Errors(ok).Length == 0, r.Explain(ok));
            }
        }

        [Fact]
        public void ACasesInitProperty_IsAFieldOfItsValue()
        {
            var r = Harness.Verify(@"using System.Collections.Generic;
public abstract record Verdict<TChange, TWhy>
{
    private Verdict() { }
    public static Verdict<TChange, TWhy> Grant(params TChange[] changes) { Spec.Ensures<Verdict<TChange, TWhy>>(r => r is Granted); return new Granted(changes); }
    [Pure] public static Verdict<TChange, TWhy> Unchanged() => new Granted(Array.Empty<TChange>());
    public static Verdict<TChange, TWhy> Refuse(TWhy why) { Spec.Ensures<Verdict<TChange, TWhy>>(r => r is Refused); return new Refused(why); }
    public static Verdict<TChange, TWhy> RefuseAfter(TWhy why, IReadOnlyList<TChange> done)
    {
        Spec.Ensures<Verdict<TChange, TWhy>>(r => r is Refused f && (object)f.Done == done);
        return new Refused(why) { Done = done };
    }
    [Pure] public bool IsGranted => this is Granted;
    public sealed record Granted(IReadOnlyList<TChange> Changes) : Verdict<TChange, TWhy>;
    public sealed record Refused(TWhy Why) : Verdict<TChange, TWhy>
    {
        public IReadOnlyList<TChange> Done { get; init; } = Array.Empty<TChange>();
    }
}
public sealed record Shipped(int Qty);
public enum Why { NoStock }
public static class Dispatch
{
    public static Verdict<Shipped, Why> Ship(int qty)
    {
        Spec.Ensures<Verdict<Shipped, Why>>(r => (r is Verdict<Shipped, Why>.Granted) == (qty > 0));
        return qty > 0 ? Verdict<Shipped, Why>.Grant(new Shipped(qty)) : Verdict<Shipped, Why>.Refuse(Why.NoStock);
    }
    public static bool Granted(int qty) { Spec.Requires(qty > 0); Spec.Ensures<bool>(r => r); return Ship(qty).IsGranted; }
    public static void None() { var v = Verdict<Shipped, Why>.Unchanged(); Spec.Assert(v is Verdict<Shipped, Why>.Granted g && g.Changes.Count == 0 && v.IsGranted); }
    public static void Kept(IReadOnlyList<Shipped> done) { var v = Verdict<Shipped, Why>.RefuseAfter(Why.NoStock, done); Spec.Assert(!v.IsGranted); }
    public static void Plain() { var v = new Verdict<Shipped, Why>.Refused(Why.NoStock); Spec.Assert(v.Done.Count == 0); }
    public static void Same(IReadOnlyList<Shipped> d) { var a = new Verdict<Shipped, Why>.Refused(Why.NoStock) { Done = d }; var b = a with { }; Spec.Assert(b.Done == d && b.Why == a.Why); }
    public static void Wrong() { var v = new Verdict<Shipped, Why>.Refused(Why.NoStock); Spec.Assert(v.Done.Count == 1); }
}");
            foreach (var ok in new[] { "Grant", "Unchanged", "Refuse", "RefuseAfter", "get_IsGranted", "Ship", "Granted", "None", "Kept", "Plain", "Same" })
            {
                Assert.True(r.Errors(ok).Length == 0, r.Explain(ok));
            }
            Assert.Equal(new[] { "CSV1004" }, r.Errors("Wrong"));
        }

        [Fact]
        public void ElementsOfANonNullableType_AreNotNull()
        {
            var r = Harness.Verify(@"using System.Collections.Generic;
public sealed record Reading(int Value);
public sealed class Probe { public int Value; }
public static class Meter
{
    public static int Last(int start, IReadOnlyList<Reading> readings) { var v = start; foreach (var x in readings) { v = x.Value; } return v; }
    public static int First(IReadOnlyList<Reading> readings) { Spec.Requires(readings.Count > 0); return readings[0].Value; }
    public static int Seq(IEnumerable<Reading> readings) { var n = 0; foreach (var x in readings) { n = x.Value; } return n; }
    public static int Objects(IReadOnlyList<Probe> ps) { var n = 0; foreach (var p in ps) { n = p.Value; } return n; }
    public static int List(List<Reading> readings) { var n = 0; foreach (var x in readings) { n = x.Value; } return n; }
    public static int Array(Reading[] readings) { Spec.Requires(Spec.Forall(0, readings.Length, i => readings[i] != null)); var n = 0; foreach (var x in readings) { n = x.Value; } return n; }
    public static int Maybe(IReadOnlyList<Reading?> readings) { var n = 0; foreach (var x in readings) { n = x.Value; } return n; }
    // (an array may hold nulls, new Reading[2]'s: only a precondition says it doesn't)
    public static int Made() { var a = new Reading[2]; return a[0].Value; }
    public static int Given(Reading[] readings) { var n = 0; foreach (var x in readings) { n = x.Value; } return n; }
}");
            foreach (var ok in new[] { "Last", "First", "Seq", "Objects", "List", "Array" })
            {
                Assert.True(r.Errors(ok).Length == 0, r.Explain(ok));
            }
            Assert.Equal(new[] { "CSV1013" }, r.Errors("Maybe"));
            Assert.Equal(new[] { "CSV1013" }, r.Errors("Made"));
            Assert.Equal(new[] { "CSV1013" }, r.Errors("Given"));
        }

        [Fact]
        public void WithExpressions_AndNullableTimes_AreValues()
        {
            var r = Harness.Verify(@"using System.Collections.Generic;
using System.Linq;
public sealed record Ticket(int Seen, DateTime? Closed);
public static class Desk
{
    public static Ticket Bump(Ticket t)
    {
        Spec.Requires(t.Seen < int.MaxValue);
        Spec.Ensures<Ticket>(r => r.Seen == t.Seen + 1 && r.Closed == t.Closed);
        return t with { Seen = t.Seen + 1 };
    }
    public static Ticket Close(Ticket t, DateTime at) { Spec.Ensures<Ticket>(r => r.Closed == at && r.Seen == t.Seen); return t with { Closed = at }; }
    public static bool ClosedAt(Ticket t, DateTime? at) { Spec.Ensures<bool>(r => r == (t.Closed == at)); return t.Closed == at; }
    public static bool Open(Ticket t) { Spec.Ensures<bool>(r => r == (t.Closed == null)); return !t.Closed.HasValue; }
    public static bool AnyAt(IReadOnlyList<Ticket> ts, DateTime? at) => ts.Any(t => t.Closed == at);
    public static bool After(DateTime? a, DateTime b) => a.HasValue && a.Value > b;
    public static void Wrong(Ticket t) { var u = t with { Seen = 3 }; Spec.Assert(u.Seen == t.Seen); }
    public static void Closed(Ticket t) { Spec.Assert(t.Closed != null); }
    public static int OfNull(Ticket? t) => (t with { Seen = 1 }).Seen;
}");
            foreach (var ok in new[] { "Bump", "Close", "ClosedAt", "Open", "AnyAt", "After" })
            {
                Assert.True(r.Errors(ok).Length == 0, r.Explain(ok));
            }
            Assert.Equal(new[] { "CSV1004" }, r.Errors("Wrong"));
            Assert.Equal(new[] { "CSV1004" }, r.Errors("Closed"));
            Assert.Equal(new[] { "CSV1013" }, r.Errors("OfNull"));
        }

        [Fact]
        public void Only_ChecksItsMethods_AndCallsTheOthersByTheirContracts()
        {
            const string source = @"using System.Collections.Generic;
public sealed record Shipped(int Qty);
public sealed class Depot
{
    public bool Ship(int qty) { Spec.Ensures<bool>(r => r == (qty > 0)); return qty > 0 ? Verdict.Grant(new Shipped(qty)) : Verdict.Refuse(); }
    public int Twice(int n) { Spec.Requires(n >= 0 && n < 1000); Spec.Ensures<int>(r => r == 2 * n); return Helpers.Double(n); }
    public int Square(int n) { Spec.Requires(n >= 0 && n < 100); Spec.Ensures<int>(r => r == n * n); return Helpers.Square(n); }
    private static class Verdict
    {
        public static bool Grant(params Shipped[] changes) { Spec.Ensures<bool>(r => r); return true; }
        public static bool Refuse() { Spec.Ensures<bool>(r => !r); return false; }
    }
}
public static class Helpers
{
    // (wrong: checked only where it's selected)
    public static int Double(int n) { Spec.Requires(n >= 0 && n < 1000); Spec.Ensures<int>(r => r == 2 * n); return n; }
    [Pure] public static int Square(int n) => n * n;
}";
            VerificationResult Run(params string[] only)
            {
                var o = new VerifierOptions();
                foreach (var x in only)
                {
                    o.AddOnly(x);
                }
                return Engine.VerifySources(new[] { ("Test.cs", Harness.Usings + source) }, o);
            }
            var depot = Run("Depot.");
            Assert.Equal(new[] { "Depot.Ship", "Depot.Twice", "Depot.Square", "Verdict.Grant", "Verdict.Refuse" }, depot.Methods.Select(m => m.Name));
            Assert.All(depot.Methods, m => Assert.True(m.Verified, m.Name + ": " + string.Join("; ", m.Diagnostics.Select(d => d.Message))));
            // (a nested type's methods by their full name)
            Assert.Equal(new[] { "Verdict.Grant", "Verdict.Refuse" }, Run("Depot.Verdict.").Methods.Select(m => m.Name));
            Assert.Equal(new[] { "CSV1002" }, Run("Helpers.").Errors("Double"));
        }

        [Fact]
        public void AForeachOverAListOfAnyExpression_ReadsItsElements()
        {
            var r = Harness.Verify(@"using System.Collections.Generic;
public sealed record Entry(int Line);
public sealed record Batch(IReadOnlyList<Entry> Entries);
public sealed class Journal
{
    private readonly List<Entry> pending = new();
    private IReadOnlyList<Entry> last = new List<Entry>();
    public int Line { get; private set; }
    public void Take(Batch batch) { foreach (var e in batch.Entries) { Line = e.Line; pending.Add(e); } }
    public int Again() { var n = 0; foreach (var e in last) { n = e.Line; } return n; }
    public static IReadOnlyList<Entry> Of(Batch b) => b.Entries;
    public static int Called(Batch b) { var n = 0; foreach (var e in Of(b)) { n = e.Line; } return n; }
    public static void Wrong(Batch b) { var n = 0; foreach (var e in b.Entries) { n = e.Line; } Spec.Assert(n == 0); }
}");
            foreach (var ok in new[] { "Take", "Again", "Of", "Called" })
            {
                Assert.True(r.Errors(ok).Length == 0, r.Explain(ok));
            }
            Assert.Equal(new[] { "CSV1004" }, r.Errors("Wrong"));
        }

        [Fact]
        public void AWithCopyOfAProperty_AssignedBack_IsARead_ACopy_AndAWrite()
        {
            var r = Harness.Verify(@"public enum Status { Packed, Posted }
public sealed record Label(string Code, Status Status);
public sealed class Parcel
{
    public Label? Label { get; private set; }
    public void Pack(string code) { Spec.Ensures(Label != null && Label.Status == Status.Packed); Label = new Label(code, Status.Packed); }
    public void Post()
    {
        Spec.Ensures(Label == null || Label.Status == Status.Posted);
        if (Label is not null)
        {
            Label = Label with { Status = Status.Posted };
        }
    }
    public void PostAnyway() { Spec.Requires(Label != null); Spec.Ensures(Label != null && Label.Status == Status.Posted && Label.Code == Spec.Old(Label).Code); Label = Label! with { Status = Status.Posted }; }
    public void Wrong() { Spec.Requires(Label != null); Spec.Ensures(Label != null && Label.Status == Status.Packed); Label = Label! with { Status = Status.Posted }; }
}");
            foreach (var ok in new[] { "Pack", "Post", "PostAnyway" })
            {
                Assert.True(r.Errors(ok).Length == 0, r.Explain(ok));
            }
            Assert.Equal(new[] { "CSV1002" }, r.Errors("Wrong"));
        }

        [Fact]
        public void TimeArithmetic_IsOnTicks()
        {
            var r = Harness.Verify(@"public static class Timer
{
    public static bool Expired(DateTime from, TimeSpan grace, DateTime now) { var deadline = from + grace; return now >= deadline; }
    public static TimeSpan Remaining(DateTime deadline, DateTime now) => deadline - now;
    public static TimeSpan Both(TimeSpan a, TimeSpan b) { Spec.EnsuresOnThrow<OverflowException>(true); return a + b; }
    public static void Order(DateTime from, TimeSpan grace) { Spec.Requires(grace > TimeSpan.Zero && from < DateTime.MaxValue - grace); Spec.Assert(from + grace > from); }
    public static void Back(DateTime a, DateTime b) { Spec.Assert(b + (a - b) == a); }
    public static DateTime Throws(DateTime at, TimeSpan by) { Spec.EnsuresOnThrow<ArgumentOutOfRangeException>(false); return at + by; }
    public static DateTime Safe(DateTime at, TimeSpan by) { Spec.Requires(by >= TimeSpan.Zero && at <= DateTime.MaxValue - by); Spec.EnsuresOnThrow<ArgumentOutOfRangeException>(false); return at + by; }
    public static void Wrong(DateTime from, TimeSpan grace) { Spec.Assert(from + grace >= from); }
}");
            foreach (var ok in new[] { "Expired", "Remaining", "Both", "Order", "Back", "Safe" })
            {
                Assert.True(r.Errors(ok).Length == 0, r.Explain(ok));
            }
            Assert.Equal(new[] { "CSV1002" }, r.Errors("Throws"));
            Assert.Equal(new[] { "CSV1004" }, r.Errors("Wrong"));
        }

        [Fact]
        public void APropertyPattern_ReadsAClassProperty()
        {
            var r = Harness.Verify(@"public enum Stage { Stored, Sent, Held }
public sealed class Pin { public Stage State { get; set; } public int? Count { get; set; } }
public sealed class Card { public Pin Pin { get; set; } = new(); }
public static class Cards
{
    public static bool Stored(Card? c) { Spec.Ensures(Spec.Result<bool>() == (c != null && c.Pin.State == Stage.Stored)); return c is { Pin.State: Stage.Stored }; }
    public static bool Sent(Pin? p) { Spec.Ensures(Spec.Result<bool>() == (p != null && p.State == Stage.Sent)); return p is { State: Stage.Sent }; }
    public static int Of(Pin? p) => p switch { null => 0, { State: Stage.Sent or Stage.Held } => 1, { State: Stage.Stored } => 2, _ => throw new ArgumentOutOfRangeException(nameof(p)) };
    public static bool Three(Pin p) { Spec.Ensures(Spec.Result<bool>() == (p.Count != null && p.Count.Value == 3)); return p is { Count: 3 }; }
    public static bool Wrong(Pin? p) { Spec.Ensures(Spec.Result<bool>() == (p != null)); return p is { State: Stage.Sent }; }
}");
            foreach (var ok in new[] { "Stored", "Sent", "Of", "Three" })
            {
                Assert.True(r.Errors(ok).Length == 0, r.Explain(ok));
            }
            Assert.Equal(new[] { "CSV1002" }, r.Errors("Wrong"));
        }

        [Fact]
        public void APropertyPattern_ReadsAComputedProperty()
        {
            // (#104: its getter called where the pattern so far matched; in a contract, a [Pure] one's function)
            var r = Harness.Verify(@"public sealed class Account
{
    public string? Portfolio { get; private set; }
    public bool IsOpen => Portfolio is not null;
    [Pure] public bool Funded => Portfolio != null;
}
public static class Uses
{
    public static bool Pattern(Account? a) { Spec.Ensures<bool>(r => !r || a != null); return a is { IsOpen: true }; }
    public static bool Two(Account? a) { Spec.Ensures<bool>(r => !r || a != null && a.Portfolio != null); return a is { IsOpen: true, Portfolio: { } }; }
    public static bool Pure(Account? a) { Spec.Ensures<bool>(r => r == (a != null && a.Funded)); return a is { Funded: true }; }
    public static bool InContract(Account? a) { Spec.Ensures<bool>(r => r == a is { Funded: true }); return a != null && a.Funded; }
    public static int Switch(Account? a) { Spec.Ensures<int>(r => r == 0 || a != null && a.Portfolio != null); return a switch { { IsOpen: true } x when x.Portfolio != null => 1, _ => 0 }; }
    public static bool Wrong(Account? a) { Spec.Ensures<bool>(r => r); return a is { IsOpen: true }; }
}");
            foreach (var ok in new[] { "Pattern", "Two", "Pure", "InContract", "Switch" })
            {
                Assert.True(r.Errors(ok).Length == 0, r.Explain(ok));
            }
            Assert.Equal(new[] { "CSV1002" }, r.Errors("Wrong"));
        }

        [Fact]
        public void AClassEquatableToItself_IsOfTheSubset()
        {
            // (#104: its Equals(C) is what EqualityComparer<C>.Default calls, as an override of Equals(object) would be)
            var r = Harness.Verify(@"using System.Collections.Generic;
public enum Item { Opened, Funded }
public sealed class Checklist : IEquatable<Checklist>
{
    private readonly Dictionary<Item, bool> done = new();
    public bool this[Item item] => done[item];
    public bool Equals(Checklist? other) => other is not null && done.Count == other.done.Count;
}
public static class Uses
{
    public static bool Opened(Checklist c) => c[Item.Opened];
}");
            Assert.True(r.Errors("Equals").Length == 0, r.Explain("Equals"));
            Assert.True(r.Errors("Opened").Length == 0, r.Explain("Opened"));
            Assert.Equal(new[] { "CSV1001" }, r.Errors("get_Item"));
        }

        [Fact]
        public void AClassImplementingAReferencedInterface_IsOfTheSubset()
        {
            // (#106: its members are the class's own methods; a call through the interface may run any implementation)
            var r = Harness.VerifyWithLibrary(@"namespace Lib { public interface IMarker { } public interface IRepo { int Get(int x); } }", @"using Lib;
public sealed class Counter { public int N; }
public sealed class Marked : IMarker
{
    public int Plain(int x) => x + 0;
}
public sealed class Repo : IRepo
{
    private readonly Counter c;
    public Repo(Counter c) { this.c = c; }
    public int Get(int x) { c.N = 5; return 1; }
}
public sealed class Strict : IRepo
{
    public int Get(int x) { Spec.Requires(x < 10); return x + 1; }
}
public static class Uses
{
    public static void Forgets(IRepo r, Counter c) { c.N = 1; r.Get(0); Spec.Assert(c.N == 1); }
    public static void Unknown(IRepo r) { var v = r.Get(0); Spec.Assert(v == 1); }
    public static int Direct(Repo r) => r.Get(1);
}");
            Assert.True(r.Errors("Plain").Length == 0, r.Explain("Plain"));
            Assert.True(r.Errors("Repo.Get").Length == 0, r.Explain("Repo.Get"));
            Assert.True(r.Errors("Direct").Length == 0, r.Explain("Direct"));
            // (the library's interface promises nothing of its arguments: an implementation may not require more)
            Assert.Equal(new[] { "CSV1018" }, r.Errors("Strict.Get"));
            Assert.Equal(new[] { "CSV1004" }, r.Errors("Forgets"));
            Assert.Equal(new[] { "CSV1004" }, r.Errors("Unknown"));
        }

        [Fact]
        public void AnInheritedPrecondition_IsWellDefined_InTheInterfacesNullableContext()
        {
            // (#121: a nullable-disabled project, its interface and contract class in an enabled region)
            const string source = @"public sealed class Row { public long Id { get; set; } }
#nullable enable
public interface IStore { void Add(Row row); }
[ContractClassFor(typeof(IStore))]
internal abstract class StoreContract : IStore
{
    public void Add(Row row) { Spec.Requires(row.Id == 0); }
}
#nullable restore
public sealed class Store : IStore
{
    public void Add(Row row) { }
}
public static class Uses
{
    public static void Adds(Store s) { Spec.Requires(s != null); s.Add(new Row()); }
    public static void AddsNull(Store s) { Spec.Requires(s != null); s.Add(null); }
}";
            var r = Engine.VerifySources(new[] { ("Test.cs", Harness.Usings + source) }, new VerifierOptions { Nullable = NullableContextOptions.Disable });
            Assert.True(r.CompilationErrors.Count == 0, string.Join("\n", r.CompilationErrors));
            Assert.True(r.Errors("Store.Add").Length == 0, r.Explain("Store.Add"));
            Assert.True(r.Errors("Uses.Adds").Length == 0, r.Explain("Uses.Adds"));
            // (the interface's parameter is not null: a caller of the implementation gives one)
            Assert.Contains("CSV1014", r.Errors("Uses.AddsNull"));
        }

        [Fact]
        public void APatternOverABoxedValue_IsNotVerified_Unboxing()
        {
            // (#118: a boxed value's value isn't modeled; the other methods verify as they would without it)
            var r = Harness.Verify(@"public sealed class Account { public long Balance { get; set; } }
public static class Failures
{
    public static bool IsDuplicate(Exception exception)
    {
        var number = exception.InnerException?.GetType().GetProperty(""Number"")?.GetValue(exception.InnerException);
        return number is 2601 or 2627;
    }
    public static bool IsDuplicateTyped(object number) => number is int n && n is 2601 or 2627;
    public static bool IsSmall(object number) => number is < 10;
    public static bool IsNotOne(object number) => number is not 1;
    public static bool IsText(object o) => o is ""text"";
    public static void Credit(Account a, long amount)
    {
        Spec.Requires(amount > 0 && a.Balance >= 0 && a.Balance <= long.MaxValue - amount);
        a.Balance += amount;
        Spec.Assert(a.Balance > 0);
    }
}");
            foreach (var m in new[] { "IsDuplicate", "IsDuplicateTyped", "IsSmall", "IsNotOne" })
            {
                Assert.Contains(r[m].Diagnostics, d => d.Id == "CSV1902" && d.Message.Contains("unboxing"));
            }
            Assert.True(r.Errors("IsText").Length == 0, r.Explain("IsText"));
            Assert.True(r.Errors("Credit").Length == 0, r.Explain("Credit"));
        }

        [Fact]
        public void AClassOutsideTheSubset_SaysWhichInterface()
        {
            var r = Harness.Verify(@"public sealed class Ordered : IComparable<Ordered>
{
    public int Key;
    public int CompareTo(Ordered? other) => 0;
}");
            Assert.Contains(r["CompareTo"].Diagnostics, d => d.Id == "CSV1902" && d.Message.Contains("implements System.IComparable<Ordered>"));
        }

        [Fact]
        public void ALibraryInterfaceParameter_IsAReference()
        {
            // (#107: stored, it is a reference; a call through it is a library call, which may run the program's code)
            var r = Harness.Verify(@"public sealed class Counter { public int N; }
public sealed class Scoped
{
    private readonly IServiceProvider services;
    public Scoped(IServiceProvider services) => this.services = services;
    public object? Service(Type t, Counter c) { c.N = 1; var s = services.GetService(t); Spec.Assert(c.N == 1); return s; }
    public static void Null(IServiceProvider? p, Type t) { p!.GetService(t); }
}");
            Assert.True(r.Errors("Scoped..ctor").Length == 0, r.Explain("Scoped..ctor"));
            Assert.Equal(new[] { "CSV1004" }, r.Errors("Service"));
            Assert.Equal(new[] { "CSV1013" }, r.Errors("Null"));
        }

        [Fact]
        public void AnArrayAsAList_HasItsLengthAndCells()
        {
            var r = Harness.Verify(@"using System.Collections.Generic;
public abstract record Reply
{
    private Reply() { }
    public static Reply Give(params string[] notes) { Spec.Ensures<Reply>(r => r is Given g && g.Notes == notes); return new Given(notes); }
    public sealed record Given(IReadOnlyList<string> Notes) : Reply;
}
public abstract record Reply<T>
{
    private Reply() { }
    public static Reply<T> Make(params T[] items) { Spec.Ensures<Reply<T>>(r => r is Given g && g.Items == items); return new Given(items); }
    public static Reply<T> None() { Spec.Ensures<Reply<T>>(r => r is Given g && g.Items.Count == 0); return new Given(Array.Empty<T>()); }
    public sealed record Given(IReadOnlyList<T> Items) : Reply<T>;
}
public static class Replies
{
    public static Reply One(string note) { Spec.Ensures<Reply>(r => r is Reply.Given g && g.Notes.Count == 1 && g.Notes[0] == note); return Reply.Give(note); }
    public static Reply<int> Two(int x) { Spec.Ensures<Reply<int>>(r => r is Reply<int>.Given g && g.Items.Count == 2 && g.Items[1] == x); return Reply<int>.Make(0, x); }
    public static int CountOf<T>(IReadOnlyList<T> xs) { Spec.Ensures<int>(n => n == xs.Count); return xs.Count; }
    public static int Counted() { Spec.Ensures<int>(n => n == 2); return CountOf(new[] { 1, 2 }); }
    public static Reply<int> Wrong(int x) { Spec.Ensures<Reply<int>>(r => r is Reply<int>.Given g && g.Items.Count == 1); return Reply<int>.Make(0, x); }
    public static int WrongCount() { Spec.Ensures<int>(n => n == 3); return CountOf(new[] { 1, 2 }); }
}");
            foreach (var ok in new[] { "Give", "Make", "None", "One", "Two", "CountOf", "Counted" })
            {
                Assert.True(r.Errors(ok).Length == 0, r.Explain(ok));
            }
            Assert.Equal(new[] { "CSV1002" }, r.Errors("Wrong"));
            Assert.Equal(new[] { "CSV1002" }, r.Errors("WrongCount"));
        }

        [Fact]
        public void ARecordsSynthesizedEquality_IsItsFields()
        {
            var r = Harness.Verify(@"public readonly record struct Price(decimal Amount, string Currency);
public sealed record Tag(string Value);
public sealed record Labelled(Tag Label, int N);
public abstract record Mark { public sealed record Dot(string Name) : Mark; public sealed record Dash(string Name, int Len) : Mark; }
public sealed record Loose(string V) { public bool Equals(Loose? o) => o is not null; public override int GetHashCode() => 0; }
public static class Eqs
{
    public static bool Same(Price a, Price b) { Spec.Ensures<bool>(r => r == (a.Amount == b.Amount && a.Currency == b.Currency)); return a == b; }
    public static bool Differs(Price a, Price b) { Spec.Ensures<bool>(r => r == (a.Amount != b.Amount || a.Currency != b.Currency)); return a != b; }
    public static bool SameTag(Tag a, Tag b) { Spec.Ensures<bool>(r => r == (a.Value == b.Value)); return a == b; }
    public static bool Copies() { Spec.Ensures<bool>(r => r); return new Tag(""x"") == new Tag(""x""); }
    public static bool Nested() { Spec.Ensures<bool>(r => r); return new Labelled(new Tag(""a""), 1) == new Labelled(new Tag(""a""), 1); }
    public static bool OtherCase() { Spec.Ensures<bool>(r => !r); Mark a = new Mark.Dot(""a""); Mark b = new Mark.Dash(""a"", 1); return a == b; }
    public static bool SameCase() { Spec.Ensures<bool>(r => r); Mark a = new Mark.Dot(""a""); Mark b = new Mark.Dot(""a""); return a == b; }
    public static bool InSpec(Tag a) { Spec.Ensures<bool>(r => r == (a == new Tag(a.Value))); return true; }
    public static bool WrongPrice(Price a, Price b) { Spec.Ensures<bool>(r => r == (a.Amount == b.Amount)); return a == b; }
    public static bool WrongTag() { Spec.Ensures<bool>(r => r); return new Tag(""x"") == new Tag(""y""); }
    public static bool WrongOwn() { Spec.Ensures<bool>(r => !r); return new Loose(""x"") == new Loose(""y""); }
}");
            foreach (var ok in new[] { "Same", "Differs", "SameTag", "Copies", "Nested", "OtherCase", "SameCase", "InSpec" })
            {
                Assert.True(r.Errors(ok).Length == 0, r.Explain(ok));
            }
            foreach (var wrong in new[] { "WrongPrice", "WrongTag", "WrongOwn" })
            {
                Assert.Equal(new[] { "CSV1002" }, r.Errors(wrong));
            }
        }

        private const string ValueObjects =@"public sealed record Ref
{
    private Ref(string value) { Spec.Requires(value.Length > 0); Spec.Ensures(Value == value); Value = value; }
    public string Value { get; }
    public static Ref? Parse(string s)
    {
        Spec.Ensures<Ref?>(r => (r != null) == (s.Length > 0));
        Spec.Ensures<Ref?>(r => r == null || r.Value == s);
        return s.Length > 0 ? new Ref(s) : null;
    }
}
public sealed record Money
{
    public Money(long cents, Ref payer) { Spec.Ensures(Cents == cents && (object)Payer == payer); Cents = cents; Payer = payer; }
    public long Cents { get; }
    public Ref Payer { get; }
}
";

        [Fact]
        public void AValueObject_IsAClass_WhoseEqualityIsItsFields()
        {
            var r = Harness.Verify(ValueObjects + @"public static class Account
{
    public static bool SameAccount(Ref r, Ref mine) => r == mine;
    public static void Same(string s) { Spec.Requires(s.Length > 0); var a = Ref.Parse(s); var b = Ref.Parse(s); Spec.Assert(a != null && a == b); }
    public static void Differ(string s, string t) { Spec.Requires(s.Length > 0 && t.Length > 0 && s != t); var a = Ref.Parse(s); var b = Ref.Parse(t); Spec.Assert(a != b); }
    public static void Wrong(string s) { Spec.Requires(s.Length > 0); var a = Ref.Parse(s); var b = Ref.Parse(s); Spec.Assert(a != b); }
    public static void Nested(Ref p, Ref q) { Spec.Requires(p == q); var a = new Money(5, p); var b = new Money(5, q); Spec.Assert(a == b); }
    public static void NestedWrong(Ref p) { var a = new Money(5, p); var b = new Money(6, p); Spec.Assert(a == b); }
}");
            foreach (var ok in new[] { "Ref..ctor", "Parse", "SameAccount", "Same", "Differ", "Nested" })
            {
                Assert.True(r.Errors(ok).Length == 0, r.Explain(ok));
            }
            Assert.Equal(new[] { "CSV1004" }, r.Errors("Wrong"));
            Assert.Equal(new[] { "CSV1004" }, r.Errors("NestedWrong"));
        }

        [Fact]
        public void AValueOfATypeWithARange_IsWithinIt_WhereverItComesFrom()
        {
            // (a decimal, a DateTime's or a TimeSpan's ticks, an integer: within its type's range as a nullable value's
            // value, a struct's field, a tuple's item, an out parameter's or a result's value, a field's, a record's
            // member's part, a static readonly field's. A field of a data type holds one of its cases. A nullable
            // struct's parts are its value's, where it has one. A record made of one exists, then: its constructor takes
            // values of its members' types)
            var r = Harness.Verify(@"using System.Collections.Generic;
public enum Tone { Low, High }
public readonly record struct Slot(decimal Amount, DateTime At);
public sealed record Reading(decimal Total, DateTime At, TimeSpan Took, int Count, Tone Tone);
public sealed record Stamp(DateTime At, string? Text);
public sealed record Stamps(Stamp? First, DateTime? Second, bool Both);
public readonly record struct Weight(decimal Grams);
public sealed record Loads(Weight Total, Weight Net);
public sealed record Dials(bool A, bool B, DateTime? ChangedAt) { public static readonly Dials Off = new(false, false, null); }
public abstract record Note;
public sealed record Turned(Dials From, Dials To) : Note;
public sealed class Panel
{
    public Dials Current { get; private set; } = Dials.Off;
    public List<Note> Turn(bool a, bool b, DateTime at) { var saved = new Dials(a, b, at); var notes = new List<Note>(); if (saved.A != Current.A) { notes.Add(new Turned(Current, saved)); } return notes; }
    public Turned Kept(Dials saved) => new Turned(Current, saved);
}
public readonly record struct Mass
{
    public Mass(decimal grams, string unit) { Spec.Ensures(Grams == grams && Unit == unit); Grams = grams; Unit = unit; }
    public decimal Grams { get; }
    public string Unit { get; }
    public static Mass Of(decimal grams) => new(grams, ""g"");
}
public sealed record Tariff(Mass Fee, int Free, Mass Limit, Mass? Least = null)
{
    public static readonly Mass Standard = Mass.Of(0.20m);
    public static readonly decimal Rate = 0.5m;
    public static readonly DateTime Epoch = DateTime.MinValue;
    public static Mass Mutable = Mass.Of(0.40m);
    public static Tariff WithLeast(int free, decimal limit, decimal? least) => new(Standard, free, Mass.Of(limit), least is { } l ? Mass.Of(l) : null);
    public static Tariff Plain(int free, decimal limit) => new(Standard, free, Mass.Of(limit));
    public static Tariff OfMutable(int free, decimal limit) => new(Mutable, free, Mass.Of(limit));
    public static Reading OfConstants() => new Reading(Rate, Epoch, TimeSpan.Zero, 0, Tone.Low);
    public static Turned OfOff(Dials saved) => new Turned(Dials.Off, saved);
}
public sealed class Source
{
    public decimal? Amount { get; set; }
    public DateTime? At { get; set; }
    public TimeSpan? Took { get; set; }
    public int? Count { get; set; }
    public Tone? Tone { get; set; }
    public Slot? Slot { get; set; }
    public Slot Kept { get; set; }
    public Dictionary<string, DateTime> Seen { get; } = new Dictionary<string, DateTime>();
}
public static class Readings
{
    public static Reading OrElse(decimal? a, DateTime? at, TimeSpan? took, int? n, Tone? tone, DateTime now) => new Reading(a ?? 0m, at ?? now, took ?? TimeSpan.Zero, n ?? 0, tone ?? Tone.Low);
    public static Reading Later(decimal total, DateTime? last, DateTime now) { var at = last ?? now; return new Reading(total, at, TimeSpan.Zero, 0, Tone.Low); }
    public static Stamps Both(DateTime? first, DateTime? second) { var stamp = first is { } t ? new Stamp(t, null) : null; return new Stamps(stamp, second, false); }
    public static Reading Values(decimal? a, DateTime? at, TimeSpan? took)
    {
        if (a is null || at is null || took is null) { return new Reading(0m, DateTime.MinValue, TimeSpan.Zero, 0, Tone.Low); }
        return new Reading(a.Value, at.Value, took.Value, 0, Tone.Low);
    }
    public static Reading OfProperties(Source s, DateTime now) => new Reading(s.Amount ?? 0m, s.At ?? now, s.Took ?? TimeSpan.Zero, s.Count ?? 0, s.Tone ?? Tone.Low);
    public static Reading OfSlot(Slot? slot, DateTime now) => slot is { } s ? new Reading(s.Amount, s.At, TimeSpan.Zero, 0, Tone.Low) : new Reading(0m, now, TimeSpan.Zero, 0, Tone.Low);
    public static Reading OfSlotProperty(Source s, DateTime now) { var slot = s.Slot; return slot is null ? new Reading(0m, now, TimeSpan.Zero, 0, Tone.Low) : new Reading(slot.Value.Amount, slot.Value.At, TimeSpan.Zero, 0, Tone.Low); }
    public static Reading OfKept(Source s) => new Reading(s.Kept.Amount, s.Kept.At, TimeSpan.Zero, 0, Tone.Low);
    public static Reading OfTuple((decimal a, DateTime at) t) => new Reading(t.a, t.at, TimeSpan.Zero, 0, Tone.Low);
    public static Reading OfMap(Source s, string key, DateTime now) => new Reading(0m, s.Seen.TryGetValue(key, out var at) ? at : now, TimeSpan.Zero, 0, Tone.Low);
    public static DateTime Pick(DateTime? at, DateTime now) => at ?? now;
    public static Reading OfResult(DateTime? at, DateTime now) => new Reading(0m, Pick(at, now), TimeSpan.Zero, 0, Tone.Low);
    public static Reading Again(Reading r) => new Reading(r.Total, r.At, r.Took, r.Count, r.Tone);
    public static Reading OfMember(Loads l, DateTime now) => new Reading(l.Total.Grams, now, TimeSpan.Zero, 0, Tone.Low);
    // (a range says no more than it is)
    public static bool Hoped(DateTime? at) { Spec.Ensures<bool>(r => r); return at == null; }
    public static bool Feared(decimal? a) { Spec.Ensures<bool>(r => r); return a is { } v && v >= 0m; }
    public static Reading Total(Reading r) { Spec.Ensures<Reading>(x => x.Total > 0m); return new Reading(r.Total, r.At, r.Took, r.Count, r.Tone); }
}");
            foreach (var ok in new[] { "OrElse", "Later", "Both", "Values", "OfProperties", "OfSlot", "OfSlotProperty", "OfKept", "OfTuple", "OfMap", "Pick", "OfResult", "Again", "OfMember", "Turn", "Kept", "WithLeast", "Plain", "OfMutable", "OfConstants", "OfOff" })
            {
                Assert.True(r.Errors(ok).Length == 0, r.Explain(ok));
            }
            Assert.Equal(new[] { "CSV1002" }, r.Errors("Hoped"));
            Assert.Equal(new[] { "CSV1002" }, r.Errors("Feared"));
            Assert.Equal(new[] { "CSV1002" }, r.Errors("Readings.Total"));
        }

        [Fact]
        public void ThisIsHandedOver_OnceItsObjectIsBuilt()
        {
            // (this as a value in its constructor (an argument, a receiver, a value stored): whoever gets it takes it for
            // an object of its class, so each non-nullable field is set and its invariant holds there, CSV1015. From
            // there on it is an object like any other: what a call leaves in its fields is not null)
            var r = Harness.Verify(@"using System.Collections.Generic; using System.Diagnostics.CodeAnalysis;
public sealed class Leaf { public Tree? Owner { get; set; } public object? Holder { get; set; } }
public sealed class Tree
{
    public string Name { get; private set; }
    public string Label { get; private set; }
    public Tree(string name, Leaf? leaf) { Name = name; Label = name; if (leaf is not null) { leaf.Owner = this; } }
}
public sealed class Early { public string Name; public string Label; public Early(string name, Leaf leaf) { Name = name; leaf.Holder = this; Label = name; } }
public sealed class Renamed
{
    public string Name; public string Label;
    public Renamed(string name) { Name = name; Label = name; Rename(name); Spec.Assert(Label.Length >= 0); }
    public void Rename(string to) { Label = to; }
}
public sealed class Hasty
{
    public string Name; public string Label;
    public Hasty(string name) { Name = name; Rename(name); Label = name; }
    public void Rename(string to) { Label = to; }
}
public sealed class Nulled { public string Name; public string Label; public Nulled(string name, Leaf leaf, string? maybe) { Name = name; Label = name; leaf.Holder = this; Label = maybe!; } }
public sealed class Looped { public string Name; public Looped(string name, List<Leaf> leaves) { Name = name; foreach (var leaf in leaves) { leaf.Holder = this; } } }
public sealed class LoopedEarly { public string Name; public LoopedEarly(string name, List<Leaf> leaves) { foreach (var leaf in leaves) { leaf.Holder = this; } Name = name; } }
public sealed record Maker(string Id, string Name);
public sealed class Link
{
    private string makerId = string.Empty;
    private string makerName = string.Empty;
    public Link() { }
    [SetsRequiredMembers] public Link(Maker maker, DateTime at) { At = at; Maker = maker; }
    public required DateTime At { get; init; }
    public required Maker Maker { get => new(makerId, makerName); init { makerId = value.Id; makerName = value.Name; } }
}
public static class Uses
{
    public static void Made(Leaf leaf) { var t = new Tree(""a"", leaf); Spec.Assert(leaf.Owner != t); }
    public static int Read(Leaf leaf) { var t = new Tree(""a"", leaf); return leaf.Owner is { } o ? o.Name.Length : 0; }
}
public sealed class Book { public object? Last; public void Note(object s) { Last = s; } }
public sealed class Seal
{
    public readonly int Id;
    [Invariant, Pure] public bool Valid() => Id > 0;
    public Seal(int id, Book book) { Spec.Requires(id > 0); Id = id; book.Note(this); }
}
public sealed class SealEarly
{
    public readonly int Id;
    [Invariant, Pure] public bool Valid() => Id > 0;
    public SealEarly(int id, Book book) { Spec.Requires(id > 0); book.Note(this); Id = id; }
}
public sealed class SealChanged
{
    public readonly int Id;
    [Invariant, Pure] public bool Valid() => Id > 0;
    public SealChanged(int id, Book book) { Spec.Requires(id > 1); Id = id; book.Note(this); Id = id - 1; }
}
public class Shape { public string Kind; public Shape(string kind, List<Shape> all) { Kind = kind; all.Add(this); } }
public sealed class Square : Shape { public string Side; public Square(string side, List<Shape> all) : base(""square"", all) { Side = side; } }
public class Pet { public string Kind; public Pet(string kind, List<Pet> all) { Kind = kind; all.Add(this); } }
public sealed class Cat : Pet { public string Sound = ""meow""; public Cat(List<Pet> all) : base(""cat"", all) { } }");
            foreach (var ok in new[] { "Tree..ctor", "Renamed..ctor", "Looped..ctor", "Read", "Seal..ctor", "Pet..ctor", "Cat..ctor", "Square..ctor" })
            {
                Assert.True(r.Errors(ok).Length == 0, r.Explain(ok));
            }
            // (a property's init accessor run by a constructor that sets the required members)
            Assert.Empty(r.Methods.Where(m => m.Name.StartsWith("Link.")).SelectMany(m => m.Diagnostics).Where(d => d.IsError).Select(d => d.Id + " " + d.Message));
            // (before a field is set: as a value stored, as a receiver, in a loop)
            Assert.Equal(new[] { "CSV1015" }, r.Errors("Early..ctor"));
            Assert.Equal(new[] { "CSV1015" }, r.Errors("Hasty..ctor"));
            Assert.Equal(new[] { "CSV1015" }, r.Errors("LoopedEarly..ctor"));
            // (a built object's field takes no null; the new object is known to who was handed it)
            Assert.Equal(new[] { "CSV1014" }, r.Errors("Nulled..ctor"));
            Assert.Equal(new[] { "CSV1004" }, r.Errors("Made"));
            // (an immutable object's invariant: holding where it is handed over, and its fields as they were from there)
            Assert.Equal(new[] { "CSV1015" }, r.Errors("SealEarly..ctor"));
            Assert.Equal(new[] { "CSV1015" }, r.Errors("SealChanged..ctor"));
            // (a derived class's object isn't built while its base's constructor runs, unless initializers set its fields)
            Assert.Equal(new[] { "CSV1015" }, r.Errors("Shape..ctor"));
        }
    }
}
