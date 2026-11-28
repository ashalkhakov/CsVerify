using System.Linq;
using CsVerify.Verifier;
using Xunit;

namespace CsVerify.Tests
{
    /// <summary>
    /// C# shapes a domain project uses (#139): each one verifies, and beside it what must still fail, so that no shape
    /// verifies for saying nothing.
    /// </summary>
    public class DomainShapesTests
    {
        private static void Verifies(VerificationResult r, params string[] methods)
        {
            var failed = methods.Where(m => r.Errors(m).Length > 0).Select(r.Explain).ToList();
            Assert.True(failed.Count == 0, string.Join("\n", failed));
        }

        private static void Fails(VerificationResult r, string id, params string[] methods)
        {
            var wrong = methods.Where(m => !r.Errors(m).SequenceEqual(new[] { id })).Select(m => m + ": " + string.Join(",", r.Errors(m))).ToList();
            Assert.True(wrong.Count == 0, "expected " + id + " alone: " + string.Join("; ", wrong));
        }

        [Fact]
        public void AFieldOnlyConstructionWrites_IsWhatItWas_AfterCodeCalledFromHere()
        {
            // (S14: a sequence's MoveNext runs code not known, which may change anything code called may. A readonly field
            // of an object that exists isn't one of those: only that object's construction writes it. Across a loop too)
            var r = Harness.Verify(@"using System.Collections.Generic;
public sealed class Tally
{
    private readonly List<int> seen;
    private int last;
    public Tally(IEnumerable<int>? given = null)
    {
        this.seen = new List<int>();
        if (given is not null)
        {
            foreach (var x in given) { Keep(x); }
        }
    }
    private void Keep(int x) => seen.Add(x);
    public int Count => seen.Count;
    public void Fixed(IEnumerable<int> given) { var s = seen; foreach (var x in given) { } Spec.Assert(s == seen); }
    public void Written(IEnumerable<int> given) { last = 1; foreach (var x in given) { } Spec.Assert(last == 1); }
    public void Once(Action act) { Spec.Requires(Spec.Total(act)); var s = seen; act(); Spec.Assert(s == seen); }
    public void OnceWritten(Action act) { Spec.Requires(Spec.Total(act)); last = 1; act(); Spec.Assert(last == 1); }
}");
            Verifies(r, "Tally..ctor", "Keep", "Fixed", "Once");
            Fails(r, "CSV1004", "Written", "OnceWritten");
        }

        [Fact]
        public void InItsConstructor_AnObjectIsNobodyElses_UntilItIsHandedOver()
        {
            // (S14, as the code it was reduced from has it: members with private setters. Until the constructor hands this
            // over, code not known reaches none of the object; once it has, the object is one like any other)
            var r = Harness.Verify(@"using System.Collections.Generic;
using System.Linq;
public sealed record Row(int Units);
public sealed class Sums { public static readonly Sums None = new Sums(); }
public sealed class Ledger
{
    private readonly List<Row> rows;
    public Sums Sums { get; private set; }
    public int Limit { get; private set; }
    public Ledger(Sums? sums, int limit, IEnumerable<Row>? given = null)
    {
        Sums = sums ?? Sums.None;
        Limit = limit;
        this.rows = new List<Row>();
        foreach (var row in given ?? Enumerable.Empty<Row>()) { Take(row); }
    }
    private void Take(Row row) => rows.Add(row);
}
public sealed class Kept
{
    public int Limit { get; private set; }
    public Kept(int limit, IEnumerable<int> given) { Limit = limit; foreach (var x in given) { } Spec.Assert(Limit == limit); }
}
public sealed class Handed
{
    public static Handed? Last;
    public int Limit { get; private set; }
    public Handed(int limit, IEnumerable<int> given) { Limit = limit; Last = this; foreach (var x in given) { } Spec.Assert(Limit == limit); }
}
public sealed class Called
{
    public int Limit { get; private set; }
    public Called(int limit, Action act) { Spec.Requires(Spec.Total(act)); Limit = limit; act(); Spec.Assert(Limit == limit); }
}
public sealed class Caught
{
    public int Limit { get; private set; }
    public Caught(int limit, Action<Caught> act) { Spec.Requires(Spec.Total(act)); Limit = limit; act(this); Spec.Assert(Limit == limit); }
}
public sealed class Wired
{
    public static Action? Later;
    public int Limit { get; private set; }
    public Wired(int limit, IEnumerable<int> given) { Limit = limit; Later = Reset; foreach (var x in given) { } Spec.Assert(Limit == limit); }
    private void Reset() { Limit = 0; }
}");
            Verifies(r, "Ledger..ctor", "Kept..ctor", "Called..ctor");
            Fails(r, "CSV1004", "Handed..ctor", "Caught..ctor", "Wired..ctor");
        }

        [Fact]
        public void AFunctionsValue_IsItsExpressionConvertedToItsType()
        {
            // (S10: b ? Kind.A : default is a Kind, default its first member, and the function gives that as a Kind?;
            // the conversion C# adds was left out of the definition, which then didn't type check)
            var r = Harness.Verify(@"public enum Kind { A, B }
public static class Picks
{
    public static Kind? Pick(bool b) => b ? Kind.B : default;
    public static int? Number(bool b) => b ? 1 : default;
    public static long Wide(int x) => x;
    public static Kind? Block(bool b) { return b ? Kind.B : Kind.A; }
    public static void First() { Spec.Assert(Pick(false) == Kind.A); Spec.Assert(Number(false) == 0); Spec.Assert(Block(true) == Kind.B); }
    public static void NotNull() { Spec.Assert(Pick(false) == null); }
}");
            Verifies(r, "Pick", "Number", "Wide", "Block", "First");
            Fails(r, "CSV1004", "NotNull");
        }

        [Fact]
        public void AValueTypesOwnToString_IsAMethodOfIt()
        {
            // (S01: a record struct's ToString says how a value is written, and is verified as its other methods are)
            var r = Harness.Verify(@"public readonly record struct Tag(Guid Value)
{
    public override string ToString() => Value.ToString();
}
public readonly record struct Span(int From, int To)
{
    public override string ToString() => $""{From}..{To}"";
    public int Next() => To + 1;
}
public static class Texts
{
    public static string Of(Tag t) => t.ToString();
    public static string In(Span s) => $""{s}"";
}");
            Verifies(r, "Tag.ToString", "Span.ToString", "Of", "In");
            Fails(r, "CSV1010", "Next");
        }

        [Fact]
        public void ARecordsConstructorThatChainsToAnother_BuildsThatOnesValue()
        {
            // (S09: the record stays data: a value built by the second constructor is the primary one's, of what it hands
            // on; what it computes on the way is checked in the constructor itself)
            var r = Harness.Verify(@"public abstract record Note
{
    public static readonly Note None = new Blank();
    private sealed record Blank : Note;
}
public sealed record Mark(int At, int Weight, Note Note)
{
    public Mark(int at) : this(at, 1) { }
    public Mark(int at, int weight) : this(at, weight, Note.None) { }
}
public sealed record Step(int From, int To)
{
    public Step(int from) : this(from, 10 / from) { }
}
public static class Marks
{
    public static int Weight(int at) { var m = new Mark(at); Spec.Assert(m.At == at && m.Weight == 1); return m.Weight; }
    public static void Same(int at) { Spec.Assert(new Mark(at) == new Mark(at, 1)); Spec.Assert(new Mark(at, 2).Weight == 2); }
    public static void Heavier(int at) { Spec.Assert(new Mark(at).Weight == 2); }
    public static int Read(Mark m) => m.Note == Note.None ? 0 : m.Weight;
}");
            Verifies(r, "Weight", "Same", "Read");
            Fails(r, "CSV1004", "Heavier");
            // (the division is the constructor's to answer for)
            Assert.Contains("CSV1009", r.Diagnostics.Where(d => d.IsError).Select(d => d.Id));
        }

        [Fact]
        public void AWithExpressionOfARecordClass_IsANewObjectOfTheOriginalsMembers()
        {
            // (S12: a sealed record class with its own constructors is an object; with copies it, then sets what it names)
            var r = Harness.Verify(@"public sealed record Detail
{
    public Detail(int born, string? number) { Spec.Ensures(Born == born && Number == number); Born = born; Number = number; }
    public int Born { get; private init; }
    public string? Number { get; init; }
}
public static class Details
{
    public static Detail Renumber(Detail d, string? number)
    {
        Spec.Ensures<Detail>(r => r.Born == d.Born && r.Number == number);
        return d with { Number = number };
    }
    public static void Kept(Detail d) { var was = d.Number; var e = d with { Number = ""x"" }; Spec.Assert(d.Number == was && e.Number == ""x"" && e.Born == d.Born); }
    public static void Changed(Detail d) { var e = d with { Number = ""x"" }; Spec.Assert(d.Number == ""x""); }
    public static void OfNull(Detail? d) { var e = d with { Number = ""x"" }; }
}");
            Verifies(r, "Renumber", "Kept");
            Fails(r, "CSV1004", "Changed");
            Fails(r, "CSV1013", "OfNull");
        }

        [Fact]
        public void ACharsUnicodeTest_IsAFunctionOfTheCharacter()
        {
            // (S04: char.IsWhiteSpace and the like read no culture: pure, in a LINQ lambda or handed over by name; which
            // characters they hold for isn't said)
            var r = Harness.Verify(@"using System.Linq;
public static class Text
{
    public static bool HasSpace(string s) => s.Any(char.IsWhiteSpace);
    public static bool HasLetter(string s) => s.Any(c => char.IsLetter(c));
    public static void Same(char c) { Spec.Assert(char.IsWhiteSpace(c) == char.IsWhiteSpace(c)); }
    public static void Is(char c) { Spec.Assert(char.IsWhiteSpace(c)); }
}");
            Verifies(r, "HasSpace", "HasLetter", "Same");
            Fails(r, "CSV1004", "Is");
        }

        private const string Owners = @"using System.Collections.Generic;
using System.Linq;
public sealed class Account { public bool IsMain { get; set; } public string? Number { get; init; } }
public sealed class Ring : IReadOnlyList<int>
{
    public int N;
    public int Count => N;
    public int this[int index] => index;
    public IEnumerator<int> GetEnumerator() { for (var i = 0; i < N; i++) { yield return i; } }
    System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator() => GetEnumerator();
}
";

        [Fact]
        public void APureMemberThatIsAQuery_IsAFunctionOfItsContractAlone()
        {
            // (S08: a [Pure] getter whose expression is a LINQ query no specification reads is still a function of the
            // state: a specification reads it, and what it gives is what its body, verified as code, gives. It moves with
            // what it reads; and one that reads a collection behind an interface is refused, as its value is of whatever
            // is behind it)
            var r = Harness.Verify(Owners + @"public sealed class Owner
{
    private readonly List<Account> accounts = new();
    private readonly IReadOnlyList<int> given;
    public Owner(IReadOnlyList<int> given) { this.given = given; }
    public IReadOnlyList<Account> Accounts => accounts;
    [Pure] public Account? Main => Accounts.FirstOrDefault(a => a.IsMain);
    [Pure] public int Mains => accounts.Count(a => a.IsMain);
    [Pure] public int Positive => given.Count(x => x > 0);
    public string? Refusal()
    {
        Spec.Ensures<string?>(r => r != null || (Main != null && Main.Number != null));
        if (Main is not { Number: not null }) { return ""no main account""; }
        return null;
    }
    public void Same() { var a = Main; var b = Main; Spec.Assert(a == b); }
    public void AfterAdd(Account x) { var a = Main; accounts.Add(x); Spec.Assert(a == Main); }
    public void AfterSet(Account x) { var a = Mains; x.IsMain = true; Spec.Assert(a == Mains); }
    public void Known() { Spec.Assert(Main != null); }
}");
            Verifies(r, "get_Main", "get_Mains", "Refusal", "Same");
            Fails(r, "CSV1004", "AfterAdd", "AfterSet", "Known");
            Fails(r, "CSV1902", "get_Positive");
        }

        [Fact]
        public void PureCode_MayCallAQuery_WhoseLambdasArePure()
        {
            // (the purity analyzer: a LINQ query has the effects of what it is handed; and a property written as one
            // expression is checked as any [Pure] body is)
            const string members = @"using System.Collections.Generic;
using System.Linq;
public sealed class Seen
{
    private readonly List<int> xs = new();
    private int count;
    private bool Mark(int a) { count = 1; return a > 0; }
    [Pure] public bool Clean => xs.Any(a => a > 0);
    BODY
}";
            Assert.DoesNotContain("CSV0013", Harness.Analyze(members.Replace("BODY", "")));
            Assert.Contains("CSV0013", Harness.Analyze(members.Replace("BODY", "[Pure] public bool Named => xs.Any(Mark);")));
            Assert.Contains("CSV0013", Harness.Analyze(members.Replace("BODY", "[Pure] public bool Written => xs.Any(a => { count = 1; return a > 0; });")));
            Assert.Contains("CSV0013", Harness.Analyze(members.Replace("BODY", "[Pure] public bool Called => Mark(1);")));
        }

        [Fact]
        public void AnEmptySequence_IsOne_AndAForEachReadsItsCollectionAsTheFlowGraphHasIt()
        {
            // (S15: xs ?? Enumerable.Empty<T>() and xs ?? Array.Empty<T>() in a foreach; Enumerable.Empty has no elements)
            var r = Harness.Verify(@"using System.Collections.Generic;
using System.Linq;
public sealed record Line(int Units);
public static class Baskets
{
    public static int Total(IEnumerable<Line>? lines)
    {
        var total = 0;
        foreach (var line in lines ?? Enumerable.Empty<Line>()) { total = checked(total + line.Units); }
        return total;
    }
    public static int OfArray(IEnumerable<Line>? lines)
    {
        var total = 0;
        foreach (var line in lines ?? Array.Empty<Line>()) { total = line.Units; }
        return total;
    }
    public static void None() { var n = Enumerable.Empty<int>().Count(); Spec.Assert(n == 0); }
    public static void Some(bool b, List<int> xs)
    {
        Spec.Requires(xs.Count > 0);
        IEnumerable<int> q = b ? xs : Enumerable.Empty<int>();
        var any = q.Any();
        Spec.Assert(any);
    }
}");
            Verifies(r, "Total", "OfArray", "None");
            Fails(r, "CSV1004", "Some");
        }

        [Fact]
        public void ASwitchOverATuple_TestsItsPartsInTurn()
        {
            // (S11: a discard arm of a tuple's switch expression; a part that is a nullable value, { } and null)
            var r = Harness.Verify(@"public enum Phase { Waiting, Done }
public enum Reply { Yes, No }
public static class Holds
{
    public static int Decide(Phase phase, Reply reply)
    {
        Spec.Ensures<int>(r => (phase == Phase.Waiting && reply == Reply.Yes) == (r == 1));
        return (phase, reply) switch
        {
            (Phase.Waiting, Reply.Yes) => 1,
            (Phase.Waiting, Reply.No) => 2,
            (Phase.Done, Reply.Yes or Reply.No) => 0,
            _ => throw new ArgumentOutOfRangeException(nameof(phase), ""no such phase""),
        };
    }
    public static int Parse(string kind, int parts) => (kind, parts) switch
    {
        (""a"", 2) => 1,
        (""b"", 3) => 2,
        _ => throw new InvalidOperationException(""not a kind""),
    };
    public static int Names(Guid? a, Guid? b)
    {
        Spec.Ensures<int>(r => (r == 0) == (a == null && b == null));
        Spec.Ensures<int>(r => (r == 2) == (a != null && b != null));
        return (a, b) switch { (null, { }) => 1, ({ }, { }) => 2, ({ }, null) => 3, _ => 0 };
    }
    public static int Never(Guid? a, Guid? b)
    {
        Spec.Ensures<int>(r => r != 0);
        return (a, b) switch { (null, { }) => 1, ({ }, { }) => 2, ({ }, null) => 3, _ => 0 };
    }
}");
            Verifies(r, "Decide", "Parse", "Names");
            Fails(r, "CSV1002", "Never");
        }

        [Fact]
        public void ATuple_MayHoldATuple()
        {
            // (S13: (a, (b, c)), which a tuple of more than seven parts is too: its parts read, and kept as an object; what
            // Equals of two such objects gives isn't known)
            var r = Harness.Verify(@"public sealed class Entry
{
    public string A { get; init; } = """";
    public string B { get; init; } = """";
    public string C { get; init; } = """";
    public string D { get; init; } = """";
    public string E { get; init; } = """";
    public string F { get; init; } = """";
    public string G { get; init; } = """";
    public decimal H { get; init; }
    public bool I { get; init; }
    public bool ReadsAs(Entry other) => Published.Equals(other.Published);
    private object Published => (A, B, C, D, E, F, G, (H, I));
    public static void Parts(int a, int b, int c)
    {
        var t = (a, (b, c));
        var inner = t.Item2;
        Spec.Assert(t.Item1 == a && inner.Item1 == b && t.Item2.Item2 == c);
    }
    public static void Other(int a, int b, int c) { var t = (a, (b, c)); Spec.Assert(t.Item2.Item2 == b); }
}");
            Verifies(r, "ReadsAs", "get_Published", "Parts");
            Fails(r, "CSV1004", "Other");
        }

        [Fact]
        public void ALibrarysOperatorOfValues_GivesAValueNotKnown_AndMayThrow()
        {
            // (S05: TimeSpan * double, with Math.Pow: no model of it, so nothing is known of the product, and it may throw)
            var r = Harness.Verify(@"public sealed record Backoff(TimeSpan Interval, TimeSpan Max)
{
    public TimeSpan After(int attempt)
    {
        var wait = Interval * Math.Pow(2, Math.Min(attempt, 30));
        return wait < Max ? wait : Max;
    }
    public static TimeSpan Half(TimeSpan t) => t / 2.0;
    public static double Ratio(TimeSpan t, TimeSpan u) => t / u;
    public static void Longer(TimeSpan t) { var a = t * 2.0; Spec.Assert(a >= t); }
    public static void Quiet(TimeSpan t, double f)
    {
        var r = 0;
        try { var a = t * f; r = 1; } catch (OverflowException) { r = 2; }
        Spec.Assert(r == 1);
    }
}");
            Verifies(r, "After", "Half", "Ratio");
            Fails(r, "CSV1004", "Longer", "Quiet");
        }

        [Fact]
        public void AStaticAutoProperty_IsTheStaticFieldItIsKeptIn()
        {
            // (S02: one without a setter is a static readonly field, a value that never changes; one with a setter a
            // static field. A library's call of values and of its own objects (a time zone), in a LINQ predicate: a value
            // of each element as it is read, not known, nor that it is the same again)
            var r = Harness.Verify(@"using System.Collections.Generic;
using System.Linq;
public static class Local
{
    public static TimeZoneInfo Zone { get; } = TimeZoneInfo.FindSystemTimeZoneById(""Europe/Paris"");
    public static int Limit { get; } = 5;
    public static int Count { get; set; }
    public static DateOnly DateAt(DateTime utc) => DateOnly.FromDateTime(TimeZoneInfo.ConvertTimeFromUtc(utc, Zone));
    public static int OnTheDay(List<DateTime> times, DateTime now)
    {
        Spec.Ensures<int>(r => 0 <= r && r <= times.Count);
        var today = DateAt(now);
        return times.Count(t => DateAt(t) == today);
    }
    public static void All(List<DateTime> times, DateTime now)
    {
        Spec.Requires(times.Count == 1 && times[0] == now);
        var today = DateAt(now);
        var n = times.Count(t => DateAt(t) == today);
        Spec.Assert(n == 1);
    }
    public static void Bump() { Spec.Requires(Count < 100); Spec.Ensures(Count == Spec.Old(Count) + 1); Count = Count + 1; }
    public static void Fixed() { Spec.Requires(Count < 100); var a = Limit; Bump(); Spec.Assert(a == Limit); }
    public static void Moved() { Spec.Requires(Count < 100); var a = Count; Bump(); Spec.Assert(a == Count); }
    public static void Which() { Spec.Assert(Limit == 5); }
}");
            Verifies(r, "DateAt", "OnTheDay", "Bump", "Fixed");
            Fails(r, "CSV1004", "All", "Moved", "Which");
        }

        [Fact]
        public void APartialMethodAGeneratorWrites_IsCalledByItsContract()
        {
            // (S03: the body of [GeneratedRegex]'s method is in generated code, which the run compiles and doesn't verify:
            // its callers call it by its contract, and by what that body may change)
            var options = new VerifierOptions();
            var r = Engine.VerifySources(new[]
            {
                ("Codes.cs", Harness.Usings + @"public sealed partial class Codes
{
    public static int made;
    public static bool Known(string code) { made = 3; var ok = Pattern().Length == 3; Spec.Assert(made == 3); return ok; }
    public static bool Counted(string code) { made = 3; var n = Next(); Spec.Assert(made == 3); return n > 0; }
    private static partial string Pattern();
    private static partial int Next();
}"),
                ("Codes.g.cs", @"public sealed partial class Codes
{
    private static partial string Pattern() => ""abc"";
    private static partial int Next() { made = made + 1; return made; }
}"),
            }, options);
            Assert.True(r.CompilationErrors.Count == 0, string.Join("\n", r.CompilationErrors));
            Verifies(r, "Known");
            Fails(r, "CSV1004", "Counted");
        }

        [Fact]
        public void ADelegateKeptInAField_AcceptsWhatItsObjectsInvariantSays()
        {
            // (S06: a Func of an interface's parameter; what a field's delegate accepts is its object's invariant to say,
            // Spec.Total of a readonly field, proved where the object is made)
            var r = Harness.Verify(@"public sealed class Account { public Guid Id { get; init; } }
public interface IAccounts { Account? ById(Guid id); }
public sealed class Lookup
{
    private readonly Func<IAccounts, Account?> find;
    private Lookup(Func<IAccounts, Account?> find) { Spec.Requires(Spec.Total(find)); this.find = find; }
    [Invariant, Pure] private bool AcceptsAny() => Spec.Total(find);
    public static Lookup ById(Guid id) => new(accounts => accounts.ById(id));
    public Account? FindIn(IAccounts accounts) => find(accounts);
}
public sealed class Scale
{
    private readonly Func<int, int> step;
    public Scale(Func<int, int> step) { Spec.Requires(Spec.Total(step)); this.step = step; }
    [Invariant, Pure] private bool AcceptsAny() => Spec.Total(step);
    public static Scale Picky() => new Scale(x => { Spec.Requires(x > 0); return x; });
}
public sealed class Loose
{
    private readonly Func<int, int> step;
    public Loose(Func<int, int> step) { this.step = step; }
    [Invariant, Pure] private bool AcceptsAny() => Spec.Total(step);
}
public sealed class Silent
{
    private readonly Func<int, int> step;
    public Silent(Func<int, int> step) { Spec.Requires(Spec.Total(step)); this.step = step; }
    public int At(int x) => step(x);
}");
            Verifies(r, "Lookup..ctor", "ById", "FindIn", "Scale..ctor");
            Fails(r, "CSV1001", "Picky", "At");
            Fails(r, "CSV1015", "Loose..ctor");
        }

        [Fact]
        public void ADictionary_GivesItsValuesAndKeys_AndIsReadThroughItsInterface()
        {
            // (S07: GetValueOrDefault, of the dictionary's models; Values and Keys as sequences and as collections; MaxBy
            // of no elements gives null where their type has one; IReadOnlyDictionary, whose members say nothing)
            var r = Harness.Verify(@"using System.Collections.Generic;
using System.Linq;
public sealed record Part(string Code, int Version);
public sealed class Catalogue
{
    private readonly Dictionary<int, Part> parts = new();
    private readonly IReadOnlyDictionary<string, int> limits;
    public Catalogue(IReadOnlyDictionary<string, int> limits) { this.limits = limits; }
    public static Catalogue Of(Dictionary<string, int> limits) => new Catalogue(limits);
    public IReadOnlyCollection<Part> Parts => parts.Values;
    public void Put(int key, Part part) { parts[key] = part; var found = parts.GetValueOrDefault(key); Spec.Assert(found == part); }
    public void Missing(int key) { Spec.Requires(!parts.ContainsKey(key)); var found = parts.GetValueOrDefault(key); Spec.Assert(found == null); }
    public void Any(int key) { var found = parts.GetValueOrDefault(key); Spec.Assert(found != null); }
    public int LimitOf(string code) => limits.TryGetValue(code, out var limit) ? limit : 0;
    public void Limited(string code) { var has = limits.ContainsKey(code); Spec.Assert(has); }
    public Part? Latest() => parts.Values.MaxBy(p => p.Version);
    public void OfSome() { Spec.Requires(parts.Count > 0); var latest = parts.Values.MaxBy(p => p.Version); Spec.Assert(latest != null); }
    public void OfNone() { Spec.Requires(parts.Count == 0); var latest = parts.Values.MaxBy(p => p.Version); Spec.Assert(latest == null); }
    public void OfAny() { var latest = parts.Values.MaxBy(p => p.Version); Spec.Assert(latest != null); }
    public int Versions() { var n = 0; foreach (var p in parts.Values) { n = p.Version; } return n; }
    public void Keys() { var n = parts.Keys.Count(); Spec.Assert(n == parts.Count); }
    public static int Least(List<int> xs) => xs.MinBy(x => x);
}");
            Verifies(r, "Catalogue..ctor", "Of", "get_Parts", "Put", "Missing", "LimitOf", "Latest", "OfSome", "OfNone", "Versions", "Keys");
            Fails(r, "CSV1004", "Any", "Limited", "OfAny");
            // (of a value type there is no null to give: an empty source throws)
            Fails(r, "CSV1001", "Least");
        }
    }
}
