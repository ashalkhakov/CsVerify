using System;
using CsVerify;

namespace Samples.Good
{
    /// <summary>
    /// Secrets kept out of the logs (taint tracking) and sealed until an access check (DiskSec's sealed blocks, Ileri et
    /// al., OSDI '18): a password only its owner can read, and a login that logs neither it nor anything made of it.
    /// </summary>
    public sealed class Credential
    {
        public readonly int Owner;
        public readonly string User;
        public readonly Sealed<string> Password;

        public Credential(int owner, string user, string password)
        {
            Spec.Ensures(Owner == owner && User == user && Password.Content == Ghost.Of(password));
            Owner = owner;
            User = user;
            Password = Sealed.Seal(password);
        }

        /// <summary>The password, for its owner only: the access check is the precondition, proved at every call.</summary>
        [Unseals]
        public string PasswordFor(int caller)
        {
            Spec.Requires(caller == Owner);
            Spec.Ensures(Ghost.Of(Spec.Result<string>()) == Password.Content);
            return Sealed.Unseal(Password);
        }

        public override string ToString() => User;
    }

    public static class Secrets
    {
        /// <summary>The last two characters, the rest starred: safe to log.</summary>
        [Declassify]
        public static string Mask(string s) => s.Length <= 2 ? "**" : "**" + s.Substring(s.Length - 2);

        public static bool Login(Credential c, int caller, string attempt)
        {
            Spec.Requires(caller == c.Owner);
            var password = c.PasswordFor(caller);
            bool ok = password == attempt;
            Console.WriteLine($"login {c.User}: {(ok ? "accepted" : "refused")}");
            Console.WriteLine("stored: " + Mask(password));
            Console.WriteLine(c);
            return ok;
        }

        /// <summary>A sealed value's text is a redaction.</summary>
        public static void Audit(Credential c) => Console.WriteLine($"{c.User} has {c.Password}");
    }
}
