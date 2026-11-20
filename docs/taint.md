# Secrets and logs

Two ways to keep a value out of the logs: **taint tracking**, which follows a `[Sensitive]` value and what is computed
from it to every sink, for code as it is; and **sealed values**, after DiskSec's sealed blocks (Ileri et al., "Proving
confidentiality in a file system using DiskSec", OSDI '18), which code can't look inside at all until an access check
the verifier proves, so nothing it does before then depends on them. `samples/Good/Secrets.cs` has both;
`samples/Buggy/SecretBugs.cs` has a bug of each kind.

## Taint tracking

```csharp
public sealed class User
{
    [Sensitive] public string Password = "";
    public string Name = "";
}

log.LogInformation("user {Name}", u.Name);        // fine
log.LogInformation("password {P}", u.Password);   // CSV0030
Console.WriteLine("pw=" + u.Password.Substring(1)); // CSV0030: made of it
Debug.WriteLine(Hash(u.Password));                // fine: Hash is [Declassify]
```

**Sources.** `[Sensitive]` on a field, a property, a parameter, a method (or its `[return:]`): its values; on a class or
a struct (or a record): every value of it, wherever it is (a parameter, a local, a field, a result), and what is read
from one. What `Sealed.Unseal` gives (below).

**Sinks.** A method marked `[LogSink]` (or one it overrides); `ILogger.Log` and the `LoggerExtensions` (`LogInformation`
and the others: the message and its arguments); `Console.Write`/`WriteLine`; `Debug` and `Trace`'s `Write`, `WriteLine`,
`Print`, `Fail`, `Assert`, `TraceError`/`Warning`/`Information`.

**Sanitizers.** A method marked `[Declassify]` gives a value that may be logged whatever it was given: a hash, a mask,
a length. It is trusted.

**What is followed** (CSV0030, at the sink, saying where the value came from):
- through assignments, operators, string concatenation and interpolation, conversions, `?:` and `??`, tuples, arrays,
  `await`, members of a sensitive value, and calls: a call given a sensitive value gives one (a library method too),
  unless it is `[Declassify]`;
- across the program's methods: a parameter that some caller passes a sensitive value is sensitive in the method (and in
  the members it overrides or implements), a method that returns one given clean arguments gives one at every call, and
  a field or property a sensitive value is stored in is a source wherever it is read;
- into what holds it: a collection a sensitive value is added to (`list.Add(token)`: any call given one taints its
  receiver), `ref` and `out` arguments, and a lambda passed alongside it (`passwords.Select(p => p.Length)`);
- whole objects: a value whose text shows a `[Sensitive]` member (or one of a `[Sensitive]` type) is reported where it
  is logged, or made into text (`$"{order}"`, `"x" + order`, `order.ToString()`): a record (its synthesized `ToString`
  prints every property), a type whose own `ToString` returns a sensitive value, and, given to a logger, which may
  destructure it (`{@Order}`), any type with a public `[Sensitive]` member. A class whose own `ToString` leaves the
  member out may be written to the console;
- serializers: what `JsonConvert.SerializeObject`, `JToken.FromObject`, `JsonSerializer.Serialize` and
  `JsonContent.Create` make of an object with a `[Sensitive]` member, public or not and not `[JsonIgnore]`, its own or
  a member's, is sensitive, and so is an HTTP body made of it (`new StringContent(json)`). A client that takes the
  object as `object`, an interface or a `T` (`Send<T>(object body)`) is reported where it logs the body, naming the
  caller that passed it;
- exceptions: an exception made with a sensitive value (`new ArgumentException("bad card " + card.Number)`) is reported
  where it is made, since exceptions' messages are logged.

**What isn't** (implicit flows): branching on a sensitive value and logging which way it went
(`if (pin[0] == '1') log("starts with 1")`, or `ok ? "accepted" : "refused"` of a password check) is not reported. That
is noninterference, a property of two runs; sealed values rule it out where it matters. Nor are reflection, other
serializers (XML, binary, a `JsonSerializer` given its type at run time), the text a response was deserialized from
(`DeserializeObject<T>` of a `T` with a `[Sensitive]` member: the members read are sensitive, the raw string isn't), or
code the analysis doesn't see (a library given a sensitive value is assumed to
hand it back, not to log it).

## Sealed values

```csharp
public sealed class Credential
{
    public readonly int Owner;
    public readonly Sealed<string> Password;            // its text is "(sealed)"

    public Credential(int owner, string password) { Owner = owner; Password = Sealed.Seal(password); }

    [Unseals]
    public string PasswordFor(int caller)
    {
        Spec.Requires(caller == Owner);                 // the access check
        return Sealed.Unseal(Password);
    }
}

int Check(Credential c, int user) { Spec.Requires(user == c.Owner); return c.PasswordFor(user).Length; }  // verified
int Wrong(Credential c, int user) => c.PasswordFor(user).Length;                                       // CSV1001
```

A `Sealed<T>` holds its value privately: code may store it, pass it and compare it by reference, but nothing reads it but
`Sealed.Unseal`, so nothing a program does with a sealed value depends on what it holds, implicit flows included.
`Sealed.Unseal` may be called only in the body of a method marked `[Unseals]` (CSV0031; not in a lambda or a local
function, which may run later), and such a method must have a precondition (CSV0032): its preconditions are the access
check, which the verifier proves at every call, as any precondition. This is DiskSec's *unseal safety*, a property of
one run, where data noninterference otherwise needs two. The permission lives where DiskSec's domains put it: in the
object that holds the sealed value (an owner, an access list), which the precondition reads.

What `Unseal` gives is a taint source: after the access check, the taint analysis keeps it out of the logs. For the
verifier, a sealed value is a reference, not null, whose content (`Content`, a ghost) is a function of it:
`Sealed.Unseal(Sealed.Seal(x)) == x` is proved. A checked build checks an `[Unseals]` method's precondition at run time
too ([the checked build](erasure.md#the-checked-build)).

An `[Unseals]` method's precondition is the policy: it is reviewed as a `[Trusted]` body would be (one that says
`Spec.Requires(true)` lets anyone in).
