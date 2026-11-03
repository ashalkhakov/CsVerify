using CsVerify;

namespace Samples.Buggy
{
    public static class NullBugs
    {
        // BUG: a nullable parameter used unchecked (CSV1013)
        public static int Unchecked(int[]? a) => a.Length;

        // BUG: '!' silences the compiler, not the verifier: null for a non-nullable parameter (CSV1014)
        public static int Forgiven() => Count(null!);
        private static int Count(string[] words) => words.Length;

        // BUG: a non-nullable return type is a promise (CSV1014)
        public static string Broken(bool ok)
        {
            if (ok) return "fine";
            return null!;
        }

        // BUG: new string[n] is all nulls, whatever its type says (CSV1013)
        public static int FreshArray()
        {
            var words = new string[2];
            return words[0].Length;
        }

        // BUG: the precondition reads a.Length before checking a (CSV1012)
        public static int SpecTooEarly(int[]? a)
        {
            Spec.Requires(a.Length > 0 && a != null);
            return a[0];
        }
    }
}
