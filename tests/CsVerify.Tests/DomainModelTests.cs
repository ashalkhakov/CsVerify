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
        Spec.EnsuresOnThrow<ArgumentOutOfRangeException>(false);
        return c switch
        {
            Command.Open o when o.N >= 0 => o.N,
            Command.Close cl when cl.N >= 0 => cl.N,
            _ => throw new ArgumentOutOfRangeException(nameof(c), c, ""Not a command this knows.""),
        };
    }
    public static int Reached(Command c)
    {
        Spec.EnsuresOnThrow<ArgumentOutOfRangeException>(false);
        return c switch { Command.Open o when o.N >= 0 => o.N, _ => throw new ArgumentOutOfRangeException(nameof(c)) };
    }
}");
            Assert.True(r.Errors("Of").Length == 0, r.Explain("Of"));
            Assert.Equal(new[] { "CSV1002" }, r.Errors("Reached"));
        }

        [Fact]
        public void ReadOnlyLists_OfData_AreParametersAndResults()
        {
            var r = Harness.Verify(@"using System.Collections.Generic;
public sealed record Item(int Pence);
public sealed record Happened(int N);
public static class Totals
{
    public static int Count(IReadOnlyList<Item> items) { Spec.Ensures<int>(n => n == items.Count); return items.Count; }
    public static long Sum(IReadOnlyList<Item> items)
    {
        long total = 0;
        foreach (var item in items)
        {
            if (item != null && item.Pence > 0 && item.Pence < 100 && total < 1000000) total += item.Pence;
        }
        return total;
    }
}
public sealed class Aggregate
{
    private readonly List<Happened> unsaved = new();
    public IReadOnlyList<Happened> Unsaved => unsaved;
    public void Raise(int n) => unsaved.Add(new Happened(n));
}");
            Assert.True(r.Errors("Count").Length == 0, r.Explain("Count"));
            Assert.True(r.Errors("Sum").Length == 0, r.Explain("Sum"));
            Assert.True(r.Errors("get_Unsaved").Length == 0, r.Explain("get_Unsaved"));
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
    public Money(long pence, Ref payer) { Spec.Ensures(Pence == pence && (object)Payer == payer); Pence = pence; Payer = payer; }
    public long Pence { get; }
    public Ref Payer { get; }
}
";

        [Fact]
        public void AValueObject_IsAClass_WhoseEqualityIsItsFields()
        {
            var r = Harness.Verify(ValueObjects + @"public static class Account
{
    public static bool PaidByThis(Ref r, Ref mine) => r == mine;
    public static void Same(string s) { Spec.Requires(s.Length > 0); var a = Ref.Parse(s); var b = Ref.Parse(s); Spec.Assert(a != null && a == b); }
    public static void Differ(string s, string t) { Spec.Requires(s.Length > 0 && t.Length > 0 && s != t); var a = Ref.Parse(s); var b = Ref.Parse(t); Spec.Assert(a != b); }
    public static void Wrong(string s) { Spec.Requires(s.Length > 0); var a = Ref.Parse(s); var b = Ref.Parse(s); Spec.Assert(a != b); }
    public static void Nested(Ref p, Ref q) { Spec.Requires(p == q); var a = new Money(5, p); var b = new Money(5, q); Spec.Assert(a == b); }
    public static void NestedWrong(Ref p) { var a = new Money(5, p); var b = new Money(6, p); Spec.Assert(a == b); }
}");
            foreach (var ok in new[] { "Ref..ctor", "Parse", "PaidByThis", "Same", "Differ", "Nested" })
            {
                Assert.True(r.Errors(ok).Length == 0, r.Explain(ok));
            }
            Assert.Equal(new[] { "CSV1004" }, r.Errors("Wrong"));
            Assert.Equal(new[] { "CSV1004" }, r.Errors("NestedWrong"));
        }
    }
}
