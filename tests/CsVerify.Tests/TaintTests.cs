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
namespace Newtonsoft.Json
{
    public static class JsonConvert { public static string SerializeObject(object value) => """"; }
    public sealed class JsonIgnoreAttribute : System.Attribute { }
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

        /// <summary>
        /// The CSV0030 lines of a program (from its first line) that references a library compiled on its own: another
        /// project of the solution, whose bodies the analysis doesn't see.
        /// </summary>
        private static int[] LinesWith(string library, string program)
        {
            var lib = Microsoft.CodeAnalysis.CSharp.CSharpCompilation.Create("Lib",
                new[] { Microsoft.CodeAnalysis.CSharp.CSharpSyntaxTree.ParseText(Harness.Usings + library) }, Harness.References(),
                new Microsoft.CodeAnalysis.CSharp.CSharpCompilationOptions(Microsoft.CodeAnalysis.OutputKind.DynamicallyLinkedLibrary));
            var image = new System.IO.MemoryStream();
            var emit = lib.Emit(image);
            Assert.True(emit.Success, string.Join("\n", emit.Diagnostics));
            var tree = Microsoft.CodeAnalysis.CSharp.CSharpSyntaxTree.ParseText(Logging + program, path: "App.cs");
            var app = Microsoft.CodeAnalysis.CSharp.CSharpCompilation.Create("App", new[] { tree },
                Harness.References().Append(Microsoft.CodeAnalysis.MetadataReference.CreateFromImage(image.ToArray())),
                new Microsoft.CodeAnalysis.CSharp.CSharpCompilationOptions(Microsoft.CodeAnalysis.OutputKind.DynamicallyLinkedLibrary));
            var errors = app.GetDiagnostics().Where(d => d.Severity == Microsoft.CodeAnalysis.DiagnosticSeverity.Error).ToList();
            Assert.True(errors.Count == 0, string.Join("\n", errors));
            var first = Logging.Split('\n').Length - 1;
            return app.WithAnalyzers(System.Collections.Immutable.ImmutableArray.Create<Microsoft.CodeAnalysis.Diagnostics.DiagnosticAnalyzer>(new CsVerify.Analyzers.TaintAnalyzer()))
                .GetAnalyzerDiagnosticsAsync().Result.Where(d => d.Id == "CSV0030")
                .Select(d => d.Location.GetLineSpan().StartLinePosition.Line + 1 - first).OrderBy(n => n).ToArray();
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
        public void ConditionalAccessChains_AreFollowed()
        {
            // (#77: a?.b?.c's inner instance is a?.b's receiver, not the access it is in)
            var lines = Lines(@"public sealed class Order { public Customer? Customer { get; set; } }
public sealed class Customer { public string? Name { get; set; } [Sensitive] public string? Pin { get; set; } }
public static class Use
{
    public static void Logs(ILogger log, Order? o)
    {
        log.LogInformation(""name {N}"", o?.Customer?.Name);
        log.LogInformation(""name {N}"", o?.Customer?.Name?.Trim());
        log.LogInformation(""pin {P}"", o?.Customer?.Pin?.Trim());
    }
}");
            Assert.Equal(new[] { 9 }, lines);
        }

        [Fact]
        public void ASensitiveType_IsFollowedWhereverItsValuesGo()
        {
            // (#78: parameters of the type, what's read from them, records holding one, exceptions made of those)
            var lines = Lines(@"[Sensitive]
public sealed class Pin
{
    public Pin(string digits) => Digits = digits;
    public string Digits { get; }
}
[Sensitive]
public readonly record struct Card(string Number);
public sealed record Details(Pin Pin, string Name);
public sealed record Named(string Name);
public static class Use
{
    public static void A1(ILogger log, Pin p) => log.LogInformation(""pin {P}"", p);
    public static void A2(ILogger log) => log.LogInformation(""pin {P}"", new Pin(""1234""));
    public static void A3(ILogger log, Pin p) => log.LogInformation(""pin {P}"", p.Digits);
    public static void A4(ILogger log, Card c) => log.LogInformation(""card {C}"", c);
    public static void A5(ILogger log, Pin p) => log.LogInformation($""pin {p.Digits}"");
    public static void B(ILogger log, Details d) => log.LogInformation(""d {D}"", d);
    public static void F(Details d) => throw new InvalidOperationException($""bad {d}"");
    public static void G(Details d, Named n) { Console.WriteLine(""d="" + d.Name + n); Console.WriteLine(n.ToString()); }
}");
            // (a record without one, and a clean member of one that holds one, are not)
            Assert.Equal(new[] { 13, 14, 15, 16, 17, 18, 19 }, lines);
        }

        [Fact]
        public void Serializers_WriteWhatTheyAreGiven()
        {
            // (#79: a serializer writes the members, public or not, but ignored ones; through a client that takes object or T)
            var lines = Lines(@"public sealed class CreateClientRequest
{
    public string Name { get; set; } = """";
    [Sensitive] public string DateOfBirth { get; set; } = """";
}
public sealed class Wrapper { public CreateClientRequest Inner = new CreateClientRequest(); }
public sealed class Quiet { public string Name = """"; [Sensitive, Newtonsoft.Json.JsonIgnore] public string Secret = """"; }
public sealed class Client
{
    private readonly ILogger _log;
    public Client(ILogger log) { _log = log; }
    public void Direct(CreateClientRequest request, Wrapper w, Quiet q)
    {
        _log.LogInformation(""body {B}"", Newtonsoft.Json.JsonConvert.SerializeObject(request));
        _log.LogInformation(""body {B}"", Newtonsoft.Json.JsonConvert.SerializeObject(w));
        _log.LogInformation(""body {B}"", Newtonsoft.Json.JsonConvert.SerializeObject(q));
    }
    public async System.Threading.Tasks.Task<T> Send<T>(object body)
    {
        var content = new System.Net.Http.StringContent(Newtonsoft.Json.JsonConvert.SerializeObject(body));
        _log.LogInformation(""Request body: {Body}"", await content.ReadAsStringAsync());
        return default!;
    }
    public System.Threading.Tasks.Task<int> Create(CreateClientRequest r) => Send<int>(r);
    public System.Threading.Tasks.Task<int> Rename(Quiet q) => Send<int>(q);
}");
            Assert.Equal(new[] { 14, 15, 21 }, lines);
        }

        [Fact]
        public void AnObjectMadeWithASensitiveValue_HoldsItInTheMembersItIsStoredIn()
        {
            // (#80: a constructor of the program's stores its arguments; members it doesn't store them in are clean, and
            // the message names where the value was passed and stored)
            var leaks = Leaks(@"[Sensitive]
public sealed record SortCode(string Value);
public sealed class Holder
{
    public Holder(SortCode sortCode, string currency) { SortCode = sortCode; Currency = currency; }
    public SortCode SortCode { get; }
    public string Currency { get; }
    public string Label { get; } = """";
}
public sealed record Pair(string Left, string Right);
public sealed class Kept { private readonly string _note; public Kept(string note) { _note = note; } public string Note => _note; public string Other => ""x""; }
public static class Built
{
    public static void E1(ILogger log, SortCode s) => log.LogInformation(""currency {C}"", new Holder(s, ""GBP"").Currency);
    public static void E2(ILogger log, Holder h) => log.LogInformation(""currency {C}"", h.Currency);
    public static void CallsE2(ILogger log, SortCode s) => E2(log, new Holder(s, ""GBP""));
    public static void E3(ILogger log, [Sensitive] string secret)
    {
        var pair = new Pair(secret, ""clean"");
        log.LogInformation(""{L} {R}"", pair.Right, pair.Left);
        var kept = new Kept(secret);
        log.LogInformation(""{O} {N}"", kept.Other, kept.Note);
        log.LogInformation(""{H}"", (pair with { Left = """" }).Right);
    }
}");
            Assert.Equal(new[] { "20", "22" }, leaks.Select(l => l.Substring(0, l.IndexOf(':'))).ToArray());
            Assert.Contains("'pair.Left' is sensitive ([Sensitive] parameter 'secret', passed to 'Left' of 'Pair..ctor' at ", leaks[0]);
            Assert.Contains(", stored in '_note' at ", leaks[1]);
        }

        [Fact]
        public void AnHttpResponse_IsTheServersNotTheRequests()
        {
            // (#81: the response to a sensitive request, what's read from it and what's made of it are clean; the body isn't)
            var lines = Lines(@"[Sensitive]
public sealed class PartyRequest { public string Name { get; set; } = """"; }
public sealed class OrderRequest { public string Fund { get; set; } = """"; }
public sealed class OrderReply { public string Id { get; set; } = """"; }
public sealed record Answer<T>(T? Value, string? Error);
public sealed class Client(System.Net.Http.HttpClient http, ILogger log)
{
    private async System.Threading.Tasks.Task<Answer<T>> Send<T>(string url, object body)
    {
        var content = System.Net.Http.Json.JsonContent.Create(body);
        log.LogInformation(""sending {B}"", await content.ReadAsStringAsync());
        using var response = await http.PostAsync(url, content);
        return response.IsSuccessStatusCode
            ? new Answer<T>(await System.Net.Http.Json.HttpContentJsonExtensions.ReadFromJsonAsync<T>(response.Content), null)
            : new Answer<T>(default, $""{url} answered {(int)response.StatusCode}"");
    }
    public System.Threading.Tasks.Task<Answer<string>> AddParty(PartyRequest party) => Send<string>(""parties"", party);
    public async System.Threading.Tasks.Task Run(PartyRequest party)
    {
        var added = await AddParty(party);
        log.LogInformation(""party {Id}"", added.Value);
        var bank = await Send<OrderReply>($""parties/{added.Value}/bank"", new OrderRequest());
        log.LogError(new System.Exception(), ""bank details failed: {Error}"", bank.Error);
        var answer = await http.GetStringAsync(""parties/"" + party.Name);
        log.LogInformation(""{A}"", answer);
    }
}");
            Assert.Equal(new[] { 11 }, lines);
        }

        [Fact]
        public void AnotherProjectsCode_SaysWhatItHoldsByItsSensitiveMembers()
        {
            // (#85: services and entities of another project, called with a secret, don't become secrets; an interface's
            // answer is the secret only where its type could be; a value's type is metadata. The leaks stay reported)
            var lines = LinesWith(@"namespace Lib
{
    [Sensitive] public sealed record SortCode(string Value);
    public abstract record Command;
    public sealed record Link(SortCode SortCode) : Command;
    public interface ICrypto { string Encrypt(string plaintext); }
    public interface IRepository { System.Threading.Tasks.Task StageAsync(Account account); System.Threading.Tasks.Task<Account> LoadAsync(string userId); }
    public sealed class Account
    {
        public string Id { get; } = ""acc-1"";
        public bool Linked { get; private set; }
        public bool Handle(Command command) { if (command is Link) { Linked = true; return true; } return false; }
    }
}", @"namespace App
{
using System.Threading.Tasks;
using Lib;
using Microsoft.Extensions.Logging;
public sealed record Created(string? Id, string? Error);
public interface IPlatform { Task<Created> CreateAsync(Link request); Task<string> EchoAsync(Link request); }
public sealed class Steps(ILogger logger, ICrypto crypto, IPlatform platform)
{
    public void D1(SortCode sortCode, string userId)
    {
        _ = crypto.Encrypt(sortCode.Value);
        var other = crypto.Encrypt(userId);
        logger.LogInformation(""Encrypted for user {UserId}: {Other}"", userId, other);
        logger.LogInformation(""{E}"", crypto.Encrypt(sortCode.Value));
    }
    public void D2(Account account, SortCode sortCode)
    {
        account.Handle(new Link(sortCode));
        logger.LogInformation(""Linked account {AccountId}"", account.Id);
    }
    public async Task D3(SortCode sortCode)
    {
        var created = await platform.CreateAsync(new Link(sortCode));
        logger.LogInformation(""Created {Id}, error {Error}"", created.Id, created.Error);
        logger.LogInformation(""{E}"", await platform.EchoAsync(new Link(sortCode)));
    }
    public void D5(Command command, object members)
    {
        logger.LogInformation(""Could not record {Command}"", command.GetType().Name);
        foreach (var member in members.GetType().GetProperties())
        {
            logger.LogInformation(""Member {Name}"", member.Name);
        }
    }
    public void D5Call(SortCode sortCode) => D5(new Link(sortCode), new { SortCode = sortCode });
    public void Kept(SortCode sortCode)
    {
        var list = new System.Collections.Generic.List<string>();
        list.Add(sortCode.Value);
        var b = new System.Text.StringBuilder();
        b.Append(sortCode.Value);
        logger.LogInformation(""{L} {B}"", list[0], b.ToString());
    }
}
public sealed class Fields
{
    private readonly ILogger logger;
    private readonly IRepository repository;
    public Fields(ILogger logger, IRepository repository) { this.logger = logger; this.repository = repository; }
    public async Task D9(string userId)
    {
        var loaded = await repository.LoadAsync(userId);
        logger.LogInformation(""Loaded {AccountId}"", loaded.Id);
    }
    public async Task Stage(Account account, SortCode sortCode)
    {
        account.Handle(new Link(sortCode));
        await repository.StageAsync(account);
    }
    public async Task D11(string userId, SortCode sortCode)
    {
        var account = await repository.LoadAsync(userId);
        logger.LogInformation(""Setting up {AccountId}"", account.Id);
        await Record(account, new Link(sortCode));
    }
    private async Task Record(Account account, Command command)
    {
        if (!account.Handle(command))
        {
            logger.LogError(new System.Exception(), ""Could not record a command on {AccountId}"", account.Id);
            return;
        }
        await repository.StageAsync(account);
    }
}
}");
            // (Encrypt of the sort code, an interface's string answer to it, and a list and a builder that hold it)
            Assert.Equal(new[] { 15, 26, 43, 43 }, lines);
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
