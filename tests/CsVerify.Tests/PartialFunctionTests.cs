using System.Linq;
using Xunit;

namespace CsVerify.Tests
{
    /// <summary>
    /// Functions that may throw (#135): defined where they don't. Code that reads one may see the exception; a
    /// specification may read it only where it is defined (CSV1012). And getters taken as [Pure] where their body is
    /// one expression with no effects.
    /// </summary>
    public class PartialFunctionTests
    {
        private const string Account = @"public enum State { Open, Closed }
public sealed class Account
{
    public Account(State? stored, int balance) { Stored = stored; Balance = balance; }
    public State? Stored { get; }
    public int Balance { get; }
    private int _reads;
    PURE public State Current => Stored ?? throw new InvalidOperationException($""No state: {Balance}."");
    public bool Opened => Stored == State.Open;
    public bool OpenNow => Current == State.Open;
    public int Spendable => Balance >= 0 ? Balance : throw new InvalidOperationException(""Overdrawn."");
    public int Code => Stored switch { State.Open => 1, State.Closed => 2, _ => throw new InvalidOperationException(""No state."") };
    public int Counted => _reads++ < 0 ? 0 : 1;
    public bool Closed { get { return Stored == State.Closed; } }
";

        private static CsVerify.Verifier.VerificationResult Verify(string members, bool pure = false) =>
            Harness.Verify(Account.Replace("PURE", pure ? "[Pure]" : "") + members + "}");

        [Theory]
        [InlineData(false)]
        [InlineData(true)]
        public void AGetterThatThrows_IsReadInASpecification_WhereItReturns(bool pure)
        {
            var r = Verify(@"
    public bool IsOpen() { Spec.Ensures<bool>(r => r == (Current == State.Open)); return Current == State.Open; }
    public bool Unread() { Spec.Ensures<bool>(r => r == (Current == State.Open)); return Stored == State.Open; }
    public bool Required() { Spec.Requires(Stored != null); Spec.Ensures<bool>(r => r == (Current == State.Open)); return Stored == State.Open; }
    public bool Wrong() { Spec.Ensures<bool>(r => Stored != null); return true; }
    public bool After() { Spec.Ensures<bool>(r => Stored != null); return Current == State.Closed; }
", pure);
            foreach (var ok in new[] { "IsOpen", "Required", "After", "get_Current" })
            {
                Assert.True(r.Errors(ok).Length == 0, r.Explain(ok));
            }
            // (nothing read it in code, and nothing says Stored isn't null: the postcondition has no meaning there)
            Assert.Contains("CSV1012", r.Errors("Unread"));
            Assert.Equal(new[] { "CSV1002" }, r.Errors("Wrong"));
        }

        [Fact]
        public void ACatch_SeesWhatAFunctionThrows()
        {
            var r = Verify(@"
    public int Caught() { Spec.Ensures<int>(r => r == 1 || r == 2); try { return Current == State.Open ? 1 : 1; } catch (InvalidOperationException) { return 2; } }
    public int CaughtWrong() { Spec.Ensures<int>(r => r == 1); try { return Current == State.Open ? 1 : 1; } catch (InvalidOperationException) { return 2; } }
    public bool Reads() { Spec.Ensures<bool>(r => r == (Current == State.Open)); return Current == State.Open; }
");
            Assert.True(r.Errors("Caught").Length == 0, r.Explain("Caught"));
            Assert.Equal(new[] { "CSV1002" }, r.Errors("CaughtWrong"));
        }

        [Fact]
        public void EachThrow_BoundsTheDomain()
        {
            var r = Verify(@"
    public bool IsOpenNow() { Spec.Ensures<bool>(r => r == OpenNow); return OpenNow; }
    public bool OpenNowUnread() { Spec.Ensures<bool>(r => r == OpenNow); return Stored == State.Open; }
    public int Spend() { Spec.Requires(Balance >= 10); Spec.Ensures<int>(r => r == Spendable - 10); return Spendable - 10; }
    public int SpendUnread() { Spec.Ensures<int>(r => r <= Spendable); return 0; }
    public int CodeOf() { Spec.Ensures<int>(r => r == Code && (r == 1 || r == 2)); return Code; }
    public bool Vacuous() { Spec.Ensures<bool>(r => Stored != null); return false; }
");
            foreach (var ok in new[] { "IsOpenNow", "Spend", "CodeOf", "get_OpenNow", "get_Spendable", "get_Code" })
            {
                Assert.True(r.Errors(ok).Length == 0, r.Explain(ok));
            }
            // (a function that reads one that may throw is defined where that one is)
            Assert.Contains("CSV1012", r.Errors("OpenNowUnread"));
            Assert.Contains("CSV1012", r.Errors("SpendUnread"));
            // (a domain is no fact of every object: it holds where the function was read)
            Assert.Equal(new[] { "CSV1002" }, r.Errors("Vacuous"));
        }

        [Fact]
        public void AGetter_IsAFunction_WhereItHasNoEffects()
        {
            var r = Verify(@"
    public bool IsOpened() { Spec.Ensures<bool>(r => r == Opened); return Opened; }
    public bool IsClosed() { Spec.Ensures<bool>(r => r == Closed); return Closed; }
    public int Count() { Spec.Ensures<int>(r => r == Counted); return Counted; }
");
            Assert.True(r.Errors("IsOpened").Length == 0, r.Explain("IsOpened"));
            Assert.True(r.Errors("IsClosed").Length == 0, r.Explain("IsClosed"));
            // (one that writes a field is no function, and the message says what would make it one)
            Assert.Equal(new[] { "CSV1902" }, r.Errors("Count"));
            Assert.Contains("a property whose getter is neither [Pure] nor a single expression without effects", r.Explain("Count"));
        }

        [Fact]
        public void AGetterWithNoEffects_IsKnown_WhereCodeReadsIt()
        {
            // (#136, M: such a getter can state no contract, and a struct's can't read this in one: its expression is what it is)
            var r = Harness.Verify(@"public readonly record struct Cash
{
    public Cash(decimal amount, string unit) { Spec.Ensures(Amount == amount && Unit == unit); Amount = amount; Unit = unit; }
    public decimal Amount { get; }
    public string Unit { get; }
    public bool IsZero => Amount == 0m;
    public bool IsNegative => Amount < 0m;
}
public sealed class Till
{
    private int _opened;
    public int Opened => _opened;
    public int Counted => _opened++;
    public void Open() { Spec.Requires(_opened < 100); Spec.Ensures(Opened == Spec.Old(Opened) + 1); _opened++; }
}
public static class Fees
{
    public static bool Plain(Cash fee) { Spec.Ensures<bool>(r => r == (fee.Amount == 0m)); return fee.IsZero; }
    public static int Sign(Cash fee) { Spec.Ensures<int>(r => (r < 0) == (fee.Amount < 0m)); if (fee.IsNegative) { return -1; } return 1; }
    public static bool Wrong(Cash fee) { Spec.Ensures<bool>(r => r == (fee.Amount > 0m)); return fee.IsZero; }
    public static int Read(Till t) { Spec.Ensures<int>(r => r == t.Opened); return t.Opened; }
    public static int Twice(Till t) { Spec.Ensures<int>(r => r == 0); return t.Opened - t.Opened; }
    public static int Count(Till t) { Spec.Ensures<int>(r => r == 0); return t.Counted - t.Counted; }
}");
            foreach (var ok in new[] { "Plain", "Sign", "Read", "Twice", "Open" })
            {
                Assert.True(r.Errors(ok).Length == 0, r.Explain(ok));
            }
            Assert.Equal(new[] { "CSV1002" }, r.Errors("Wrong"));
            // (one that writes a field is code: two reads of it are two calls)
            Assert.Contains("CSV1002", r.Errors("Count"));
        }

        [Fact]
        public void AThrowOfAHelpersException_IsAThrow()
        {
            // (#136, N: what a throw is handed isn't the function's value; a helper that builds it writes nothing)
            var r = Verify(@"
    public State Named => Stored ?? throw Missing(""state"");
    public State Noted => Stored ?? throw Counting(""state"");
    private InvalidOperationException Missing(string what) => new($""No {what}: {Balance}."");
    private InvalidOperationException Counting(string what) { _reads++; return new InvalidOperationException(what); }
    public bool IsNamed() { Spec.Ensures<bool>(r => r == (Named == State.Open)); return Named == State.Open; }
    public bool Unread() { Spec.Ensures<bool>(r => r == (Named == State.Open)); return Stored == State.Open; }
    public bool IsNoted() { Spec.Ensures<bool>(r => r == (Noted == State.Open)); return Noted == State.Open; }
");
            Assert.True(r.Errors("IsNamed").Length == 0, r.Explain("IsNamed"));
            Assert.Contains("CSV1012", r.Errors("Unread"));
            // (a helper that writes a field: the getter stays code)
            Assert.Equal(new[] { "CSV1902" }, r.Errors("IsNoted"));
        }

        [Fact]
        public void APostcondition_OfAFunctionThatMayThrow_HoldsWhereItReturns()
        {
            // (its postcondition is no axiom of every input: outside its domain the function has no value)
            var r = Harness.Verify(@"public static class Fns
{
    [Pure] public static int Positive(int x) { Spec.Ensures<int>(r => r > 0); return x > 0 ? x : throw new ArgumentException(""not positive""); }
    [Pure] public static int Checked(int x) { if (x < 0) { throw new ArgumentException(""negative""); } return x; }
    public static int Use(int x) { Spec.Ensures<int>(r => r == Checked(x) && x >= 0); return Checked(x); }
    public static int UseUnread(int x) { Spec.Ensures<int>(r => r == Checked(x)); return x; }
    public static void Absurd() { Spec.Assert(Positive(-1) > 0); }
    public static bool False() { Spec.Ensures<bool>(r => r); return 0 > 0; }
}");
            foreach (var ok in new[] { "Positive", "Checked", "Use" })
            {
                Assert.True(r.Errors(ok).Length == 0, r.Explain(ok));
            }
            Assert.Contains("CSV1012", r.Errors("UseUnread"));
            Assert.Contains("CSV1012", r.Errors("Absurd"));
            Assert.Equal(new[] { "CSV1002" }, r.Errors("False"));
        }

        [Fact]
        public void APostconditionThatHolds_IsDefined_ForItsCallers()
        {
            // (each return checks the postcondition well-defined: a caller's may read the same function, with no read of its own)
            var r = Verify(@"
    private bool MayClose() { Spec.Ensures<bool>(r => !r || Current == State.Open); if (Current == State.Open) { return true; } return false; }
    public bool Close(bool asked) { Spec.Ensures<bool>(r => !r || Current != State.Closed); if (!asked) { return false; } return MayClose(); }
    private bool Asked(bool asked) { Spec.Ensures<bool>(r => r == asked); return asked; }
    public bool Unread(bool asked) { Spec.Ensures<bool>(r => !r || Current != State.Closed); return Asked(asked); }
");
            foreach (var ok in new[] { "MayClose", "Close", "Asked" })
            {
                Assert.True(r.Errors(ok).Length == 0, r.Explain(ok));
            }
            // (its callee's postcondition reads nothing that may throw, and says nothing of Stored)
            Assert.Contains("CSV1012", r.Errors("Unread"));
        }

        [Fact]
        public void AFilterThatCodeEvaluated_IsDefined_WhereItHeld()
        {
            // (a lambda after a Where has the filter as its precondition: the filter returned, so what it reads was defined)
            var r = Harness.Verify(@"using System.Collections.Generic; using System.Linq;
public enum Phase { Waiting, Ready }
public sealed class Parcel
{
    public Phase? Stored { get; private set; }
    public int Weight { get; private set; }
    public Phase Current => Stored ?? throw Unset(""phase"");
    private InvalidOperationException Unset(string what) => new($""Parcel has no {what}."");
}
public static class Sorting
{
    public static IReadOnlyList<Parcel> Ready(IEnumerable<Parcel> parcels) => parcels.Where(p => p.Current == Phase.Ready).OrderBy(p => p.Weight).ToList();
    public static int ReadyCount(List<Parcel> parcels) { Spec.Ensures<int>(r => r >= 0); return parcels.Count(p => p.Current == Phase.Ready); }
    public static int Wrong(List<Parcel> parcels) { Spec.Ensures<int>(r => r > 0); return parcels.Count(p => p.Current == Phase.Ready); }
}");
            // (the lambdas verify too)
            Assert.Equal(new[] { "Sorting.Wrong" }, r.Methods.Where(m => m.Diagnostics.Any(d => d.IsError)).Select(m => m.Name).ToArray());
            Assert.Equal(new[] { "CSV1002" }, r.Errors("Wrong"));
        }

        [Fact]
        public void ALemma_MayNotReadWhatMayThrow()
        {
            var r = Verify(@"
    [Lemma, Conditional(""CSVERIFY_SPEC"")] public void Bad() { Spec.Ensures(Stored != null); var s = Current; }
    public bool Reads() { Spec.Ensures<bool>(r => r == (Current == State.Open)); return Current == State.Open; }
");
            Assert.Equal(new[] { "CSV1902" }, r.Errors("Bad"));
            Assert.Contains("which may throw, where nothing may", r.Explain("Bad"));
        }

        [Fact]
        public void AnExceptionThrown_IsNoEffect_OfAPureMember()
        {
            Assert.Empty(Harness.Analyze("static class C { [Pure] static int M(int x) { if (x < 0) { throw new ArgumentException($\"negative: {x}\"); } return x; } }"));
            Assert.Equal(new[] { "CSV0013" }, Harness.Analyze("static class C { [Pure] static int[] M(int x) { return new int[1]; } }"));
        }
    }
}
