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
            // (a call knows a [Pure] member's body, and only the postconditions of any other)
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
            var pure = Harness.Verify(Source.Replace("PURE", "[Pure]"));
            foreach (var ok in new[] { "Grant", "Refuse", "Ship" })
            {
                Assert.True(pure.Errors(ok).Length == 0, pure.Explain(ok));
            }
            Assert.Equal(new[] { "CSV1002" }, Harness.Verify(Source.Replace("PURE", "")).Errors("Ship"));
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

        private const string ValueObjects = @"public sealed record Ref
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
    }
}
