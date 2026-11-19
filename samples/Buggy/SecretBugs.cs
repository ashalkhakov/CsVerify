using System;
using CsVerify;

namespace Samples.Buggy
{
    public sealed class Session
    {
        [Sensitive] public string Token = "";
        public string User = "";
    }

    public sealed record Payment([property: Sensitive] string CardNumber, int Cents);

    public static class SecretBugs
    {
        // BUG: the token reaches the console (CSV0030)
        public static void LogToken(Session s) => Console.WriteLine("session " + s.User + " " + s.Token);

        // BUG: a record's ToString prints every property, the card number too (CSV0030)
        public static void LogPayment(Payment p) => Console.WriteLine(p);

        // BUG: the card number goes in an exception's message, which logs print (CSV0030)
        public static void Reject(Payment p) => throw new ArgumentException("bad card " + p.CardNumber);
    }

    public sealed class Locker
    {
        public readonly int Owner;
        public readonly Sealed<string> Code;

        public Locker(int owner, string code)
        {
            Owner = owner;
            Code = Sealed.Seal(code);
        }

        // BUG: unseals outside an [Unseals] method, with no access check (CSV0031)
        public string Peek() => Sealed.Unseal(Code);

        // BUG: an [Unseals] method without its access check (CSV0032)
        [Unseals]
        public string Open() => Sealed.Unseal(Code);
    }
}
