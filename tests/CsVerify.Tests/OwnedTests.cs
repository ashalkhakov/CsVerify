using Xunit;

namespace CsVerify.Tests
{
    /// <summary>ATS-style ownership: [Owned] objects are written only through their linear Own&lt;T&gt; view.</summary>
    public class OwnedTests
    {
        private const string Account = @"
[Owned]
public sealed class Account
{
    public int Balance;
    [Invariant, Pure] public bool Valid() => Balance >= 0;
    public Account(int initial) { Spec.Requires(initial >= 0); Spec.Ensures(Balance == initial); Balance = initial; }
    public void Deposit(int amount) { Spec.Requires(amount >= 0); Spec.Ensures(Balance == Spec.Old(Balance) + amount); Balance += amount; }
    public void Withdraw(int amount) { Spec.Requires(0 <= amount && amount <= Balance); Spec.Ensures(Balance == Spec.Old(Balance) - amount); Balance -= amount; }
}
public interface IAudit { void Record(int amount); }
";

        private static string[] Errors(string method, string body) =>
            Harness.Verify(Account + "public static class C { " + body + " }").Errors(method);

        [Fact]
        public void Writes_NeedTheView()
        {
            Assert.Equal(new[] { "CSV1016" }, Errors("M", "static void M(Account a) { a.Balance = 1; }"));
            Assert.Equal(new[] { "CSV1016" }, Errors("M", "static void M(Account a) { a.Deposit(1); }"));
            Assert.Empty(Errors("M", "static void M(Account a, ref Own<Account> v) { Spec.Requires(v.Obj.Value == a); a.Deposit(1); }"));
            // a read-only borrow does not allow writing
            Assert.Equal(new[] { "CSV1016" }, Errors("M", "static void M(Account a, in Own<Account> v) { Spec.Requires(v.Obj.Value == a); a.Deposit(1); }"));
        }

        [Fact]
        public void Views_AreMadeOnlyForNewObjects()
        {
            Assert.Equal(new[] { "CSV1016" }, Errors("M", "static void M(Account a) { Own.New(a, out var v); Own.Drop(v); }"));
            Assert.Empty(Errors("M", "static int M() { Spec.Ensures((int r) => r == 5); var a = Own.New(new Account(5), out var v); int b = a.Balance; Own.Drop(v); return b; }"));
        }

        [Fact]
        public void TheInvariant_TravelsWithTheView()
        {
            // assumed where the view is received, proved where it is given back
            Assert.Empty(Errors("M", "static int M(Account a, ref Own<Account> v) { Spec.Requires(v.Obj.Value == a); Spec.Ensures((int r) => r >= 0); return a.Balance; }"));
            Assert.Equal(new[] { "CSV1002" }, Errors("M", "static int M(Account a) { Spec.Ensures((int r) => r >= 0); return a.Balance; }"));
            Assert.Equal(new[] { "CSV1015" }, Errors("M", "static void M(Account a, ref Own<Account> v) { Spec.Requires(v.Obj.Value == a); a.Balance = -1; }"));
            // giving the view up for good needs no invariant: nobody can write or rely on the object any more
            Assert.Empty(Errors("M", "static void M() { var a = Own.New(new Account(0), out var v); a.Balance = -1; Own.Drop(v); }"));
        }

        [Fact]
        public void OwnedInvariants_ReadOnlyTheirOwnFields()
        {
            string Check(string cls) => string.Join(",", Harness.Verify("public sealed class Cell { public int Val; }\n" + cls).Errors("V"));
            Assert.Equal("CSV1015", Check("[Owned] public sealed class A { public Cell? Peer; [Invariant, Pure] public bool V() => Peer == null || Peer.Val > 0; }"));
            Assert.Equal("CSV1015", Check("[Owned] public sealed class A { public int N; public A? Other; [Invariant, Pure] public bool V() => Other == null || Other.N >= 0; }"));
            Assert.Equal("CSV1015", Check("[Owned] public sealed class A { public int N; [Invariant, Pure] public bool V() => Ok(this); [Pure] static bool Ok(A a) => a.N >= 0; }"));
            Assert.Equal("", Check("[Owned] public sealed class A { public int N; [Invariant, Pure] public bool V() => N >= 0 && this.N < 100; }"));
        }

        [Fact]
        public void UnknownCode_CannotChangeWhatItHasNoViewOf() =>
            Assert.Empty(Errors("M", @"static void M(IAudit audit) {
                var a = Own.New(new Account(50), out var va);
                a.Withdraw(20);
                audit.Record(20);
                Spec.Assert(a.Balance == 30);
                Own.Drop(va); }"));

        [Fact]
        public void TwoViewsInHand_OwnTwoObjects() =>
            Assert.Empty(Errors("M", @"static void M(Account a, ref Own<Account> va, Account b, ref Own<Account> vb) {
                Spec.Requires(va.Obj.Value == a && vb.Obj.Value == b);
                Spec.Assert(a != b); }"));

        [Fact]
        public void MovingAView_IsNotAContradiction() =>
            Assert.Equal(new[] { "CSV1004" }, Errors("M", "static void M() { var a = Own.New(new Account(0), out var v); var w = v; Spec.Assert(false); Own.Drop(w); }"));
    }
}
