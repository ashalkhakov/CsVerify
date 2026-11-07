using System.Linq;
using Xunit;

namespace CsVerify.Tests
{
    /// <summary>A delegate type gets a contract from a [ContractClassFor] class, as an interface does: calls prove and assume it, lambdas made one are proved against it.</summary>
    public class DelegateContractTests
    {
        private const string Program = "using CsVerify; using System; using System.Threading.Tasks; " +
            "public class Cell { public int V; } " +
            "public delegate int Step(int x); " +
            "[ContractClassFor(typeof(Step))] public abstract class StepContract { public int Invoke(int x) { Spec.Requires(0 < x && x < 1000); Spec.Ensures<int>(r => r > x); return default; } } " +
            "public delegate void Fill(int[] a); " +
            "[ContractClassFor(typeof(Fill))] public abstract class FillContract { public void Invoke(int[] a) { Spec.Requires(Spec.Acc(a)); Spec.Requires(a.Length == 3); Spec.Ensures(Spec.Acc(a)); Spec.Ensures(a[0] == 1); } } " +
            "[RunsConcurrently] public delegate void Job(); public delegate void Plain(); ";

        private static string[] Ids(string code) => Harness.Verify(Program + code).Diagnostics.Where(d => d.IsError).Select(d => d.Id).ToArray();
        private static string[] All(string code) => Harness.Verify(Program + code).Diagnostics.Where(d => d.IsError).Select(d => d.Id + " " + d.Message).ToArray();

        private const string C = "public static class C { ";

        [Theory]
        // a call assumes the postcondition
        [InlineData(C + "static void M(Step g) { var z = g(1); Spec.Assert(z > 1); } }")]
        // a lambda made one is proved against it, and assumes its precondition
        [InlineData(C + "static void M() { Step s = x => x + 1; var z = s(5); Spec.Assert(z > 5); } }")]
        // one that requires no more than the type
        [InlineData(C + "static void M() { Step s = x => { Spec.Requires(x > 0 && x < 2000); return x + 1; }; } }")]
        // a method group, wrapped
        [InlineData(C + "static int F(int x) { Spec.Requires(x < 1000); Spec.Ensures<int>(r => r == x + 2); return x + 2; } static void M() { Step s = x => F(x); } }")]
        // permissions: what it's given may change, what is kept doesn't
        [InlineData(C + "static void M(Fill g) { var a = new int[3]; g(a); Spec.Assert(a[0] == 1); } }")]
        [InlineData(C + "static void M(Fill g, int[] b) { Spec.Requires(Spec.Acc(b)); Spec.Ensures(Spec.Acc(b)); Spec.Requires(b.Length == 2); var a = new int[3]; b[0] = 5; g(a); Spec.Assert(b[0] == 5); } }")]
        [InlineData(C + "static void M() { Fill f = a => { a[0] = 1; }; } }")]
        // a lambda's precondition on a type without one, but in a specification (ghost)
        [InlineData(C + "static void M(int[] a) { Spec.Requires(Spec.Forall(0, a.Length, i => a[i] >= 0) || true); } }")]
        public void Proved(string code) => Assert.Empty(All(code));

        [Theory]
        [InlineData("CSV1001", C + "static void M(Step g) { var z = g(0); } }")]
        [InlineData("CSV1002", C + "static void M() { Step s = x => x; } }")]
        [InlineData("CSV1018", C + "static void M() { Step s = x => { Spec.Requires(x > 5); return x + 1; }; } }")]
        [InlineData("CSV1004", C + "static void M(Fill g) { var a = new int[3]; a[1] = 7; g(a); Spec.Assert(a[1] == 7); } }")]
        [InlineData("CSV1002", C + "static void M() { Fill f = a => { a[0] = 2; }; } }")]
        [InlineData("CSV1016", C + "static void M() { var b = new int[3]; Fill f = a => { a[0] = 1; b[0] = 1; }; } }")]
        // a delegate's code isn't known: it may change any field
        [InlineData("CSV1004", C + "static void M(Step g, Cell c) { c.V = 1; g(1); Spec.Assert(c.V == 1); } }")]
        // checked nowhere: a precondition on a type without a contract, a method group's contract
        [InlineData("CSV1029", C + "static void M() { Func<int, int> f = x => { Spec.Requires(x > 0); return x; }; } }")]
        [InlineData("CSV1029", C + "static void M(Action<int> g) { g(1); } static void N() { M(x => { Spec.Requires(x > 0); }); } }")]
        [InlineData("CSV1029", C + "static int F(int x) => 2; static void M() { Step s = F; } }")]
        // concurrency: a lambda made a marked delegate is concurrent code; calling an unmarked one from it needs the mark
        [InlineData("CSV1027", C + "static Cell X = new Cell(); static void M() { Job j = () => { X.V = 1; }; } }")]
        [InlineData("CSV1028", C + "static async Task M(Plain p) { var t = Task.Run(() => p()); await t; } }")]
        public void Reported(string id, string code) => Assert.Contains(id, Ids(code));

        [Fact]
        public void Unmarked_IsNotConcurrent()
        {
            var ids = Ids(C + "static Cell X = new Cell(); static void M() { Plain p = () => { X.V = 1; }; } }");
            Assert.DoesNotContain("CSV1027", ids);
        }
    }
}
