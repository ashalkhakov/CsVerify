using System.Linq;
using Microsoft.CodeAnalysis.Diagnostics;
using Xunit;

namespace CsVerify.Tests
{
    /// <summary>
    /// Taint tracking (#71): [Sensitive] values never reach a log (CSV0030), and sealed values, unsealed only in an
    /// [Unseals] method (CSV0031) whose precondition is the access check (CSV0032), after DiskSec's sealed blocks.
    /// </summary>
    public class TaintTests
    {
        // (a logger of the shape Microsoft.Extensions.Logging's has, so the tests don't need the package)
        private const string Logging = @"
namespace Microsoft.Extensions.Logging
{
    public interface ILogger { void Log(string message, params object[] args); }
    public static class LoggerExtensions
    {
        public static void LogInformation(this ILogger logger, string message, params object[] args) { }
        public static void LogError(this ILogger logger, System.Exception e, string message, params object[] args) { }
    }
}
";

        /// <summary>The lines (of the test's body, from 1) with CSV0030, as "line: message".</summary>
        private static string[] Leaks(string body)
        {
            var source = Logging + "namespace T {\nusing Microsoft.Extensions.Logging;\n" + body + "\n}";
            var compilation = Harness.Compile(source);
            var errors = compilation.GetDiagnostics().Where(d => d.Severity == Microsoft.CodeAnalysis.DiagnosticSeverity.Error).ToList();
            Assert.True(errors.Count == 0, string.Join("\n", errors));
            // (Harness.Compile puts a line of usings first)
            var first = source.Split('\n').TakeWhile(l => !l.StartsWith("using Microsoft.Extensions.Logging;")).Count() + 3;
            return compilation.WithAnalyzers(System.Collections.Immutable.ImmutableArray.Create<Microsoft.CodeAnalysis.Diagnostics.DiagnosticAnalyzer>(new CsVerify.Analyzers.TaintAnalyzer()))
                .GetAnalyzerDiagnosticsAsync().Result.Where(d => d.Id == "CSV0030")
                .Select(d => $"{d.Location.GetLineSpan().StartLinePosition.Line + 1 - first + 1}: {d.GetMessage()}").OrderBy(x => x).ToArray();
        }

        private static int[] Lines(string body) => Leaks(body).Select(l => int.Parse(l.Substring(0, l.IndexOf(":")))).OrderBy(n => n).ToArray();

        [Fact]
        public void ASensitiveValue_IsFollowedToTheSinks()
        {
            var lines = Lines(@"public sealed class User
{
    [Sensitive] public string Password = """";
    public string Name = """";
}
public static class Use
{
    public static void Logs(ILogger log, User u)
    {
        log.LogInformation(""user {Name}"", u.Name);
        log.LogInformation(""password {P}"", u.Password);
        var p = u.Password;
        var shown = ""pw="" + p.Substring(1);
        Console.WriteLine(shown);
        Console.WriteLine($""{u.Name}: {p.Length}"");
        Debug.WriteLine(Hash(p));
        Console.WriteLine(p.Length > 3 ? ""long"" : ""short"");
    }
    [Declassify] public static string Hash(string s) => s.Length.ToString();
}");
            // (the name, a hash and a branch on it are not; the password, a string made of it and its length are)
            Assert.Equal(new[] { 11, 14, 15 }, lines);
        }

        [Fact]
        public void Flows_ThroughCallsFieldsCollectionsAndLambdas()
        {
            var lines = Lines(@"public sealed class Vault
{
    [Sensitive] private string _key = ""k"";
    private string _copy = """";
    public string Key() => _key;
    public void Keep() { _copy = _key; }
    public string Copy => _copy;
    public static string Same(string s) => s;
    public static void Write(string s) { Console.WriteLine(s); }
    [LogSink] public static void Audit(string message) { }
}
public static class Use
{
    public static void Leaks(Vault v, [Sensitive] string token)
    {
        Console.WriteLine(v.Key());
        Console.WriteLine(v.Copy);
        Console.WriteLine(Vault.Same(""x""));
        Vault.Write(token);
        var list = new System.Collections.Generic.List<string>();
        list.Add(token);
        Vault.Audit(list[0]);
        Vault.Audit(string.Join("","", System.Linq.Enumerable.Select(list, s => s.ToUpper())));
    }
}");
            // (Same of a constant is not; Write's sink is reached by the token it's given)
            Assert.Equal(new[] { 9, 16, 17, 22, 23 }, lines);
        }

        [Fact]
        public void WholeObjects_AndExceptions_ShowWhatTheyHold()
        {
            var lines = Lines(@"public sealed record Card([property: Sensitive] string Number, string Holder);
public sealed record Masked([property: Sensitive] string Number)
{
    public override string ToString() => ""Card ****"" + Number.Substring(Number.Length - 4);
}
public sealed class Login
{
    [Sensitive] private string _password = """";
    public string User = """";
    public override string ToString() => User;
}
public static class Use
{
    public static void Leaks(ILogger log, Card card, Masked masked, Login login)
    {
        Console.WriteLine(card);
        Console.WriteLine(masked);
        Console.WriteLine(login);
        log.LogInformation(""{@Card}"", masked);
        throw new InvalidOperationException(""bad card "" + card.Number);
    }
}");
            // (a record's ToString prints every property; one of the program's that returns a secret too; a class's
            // own that doesn't, not; a logger may destructure a public one; an exception's message is logged)
            Assert.Equal(new[] { 16, 17, 19, 20 }, lines);
        }

        [Fact]
        public void SealedValues_AreUnsealedOnlyWhereTheAccessCheckIs()
        {
            var ids = Harness.Analyze(@"public sealed class Account
{
    public readonly int Owner;
    public readonly Sealed<string> Password;
    public Account(int owner, string password) { Owner = owner; Password = Sealed.Seal(password); }
    [Unseals] public string PasswordFor(int user) { Spec.Requires(user == Owner); return Sealed.Unseal(Password); }
    [Unseals] public string Unchecked() => Sealed.Unseal(Password);
    public string Anywhere() => Sealed.Unseal(Password);
    [Unseals] public Func<string> Later(int user) { Spec.Requires(user == Owner); return () => Sealed.Unseal(Password); }
    public void Show() { Console.WriteLine(Password); }
    public void Leak(int user) { Spec.Requires(user == Owner); Console.WriteLine(PasswordFor(user)); }
}");
            // (Unchecked has no precondition; Anywhere isn't [Unseals]; a lambda may run later; the sealed value's text is a
            // redaction, what's unsealed is sensitive)
            Assert.Equal(new[] { "CSV0030", "CSV0031", "CSV0031", "CSV0032" }, ids);
        }

        [Fact]
        public void SealedValues_AreVerified()
        {
            var r = Harness.Verify(@"public sealed class Account
{
    public readonly int Owner;
    public readonly Sealed<string> Password;
    public Account(int owner, string password) { Spec.Ensures(Owner == owner && Password.Content == Ghost.Of(password)); Owner = owner; Password = Sealed.Seal(password); }
    [Unseals]
    public string PasswordFor(int user)
    {
        Spec.Requires(user == Owner);
        Spec.Ensures(Ghost.Of(Spec.Result<string>()) == Password.Content);
        return Sealed.Unseal(Password);
    }
}
public static class Use
{
    public static int Check(Account a, int user) { Spec.Requires(user == a.Owner); return a.PasswordFor(user).Length; }
    public static string RoundTrip(string s) { Spec.Ensures(Spec.Result<string>() == s); var a = new Account(1, s); return a.PasswordFor(1); }
    public static int Wrong(Account a, int user) => a.PasswordFor(user).Length;
}");
            foreach (var ok in new[] { "Account..ctor", "PasswordFor", "Check", "RoundTrip" })
            {
                Assert.True(r.Errors(ok).Length == 0, r.Explain(ok));
            }
            // (the access check, proved at the call: DiskSec's unseal safety)
            Assert.Equal(new[] { "CSV1001" }, r.Errors("Wrong"));
        }
    }
}
