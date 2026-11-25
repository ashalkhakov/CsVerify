using Xunit;

namespace CsVerify.Tests
{
    /// <summary>
    /// Functions that may throw (#135): defined where they don't. Code that reads one may see the exception; a
    /// specification may read it only where it is defined (CSV1012). And getters a specification reads, taken as
    /// [Pure] where their body is one expression with no effects.
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
        public void AGetterASpecificationReads_IsAFunction_WhereItHasNoEffects()
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
