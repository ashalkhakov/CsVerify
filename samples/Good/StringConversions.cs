// Numbers to strings and back, in any base up to 16; escaping and unescaping.
// After Dafny's standard library (Std/Strings.dfy; Copyright (c) Microsoft Corporation, MIT License).
using System.Diagnostics;
using CsVerify;

namespace Samples.Good
{
    public static class StringConversions
    {
        private const string Alphabet = "0123456789abcdef";

        /// <summary>What a digit is worth (a character that isn't a digit of the alphabet has no meaning here).</summary>
        [GhostFunction]
        private static int DigitValue(char c) => '0' <= c && c <= '9' ? c - '0' : c - 'a' + 10;

        /// <summary>c is a digit of base b.</summary>
        [GhostFunction]
        private static bool IsDigit(char c, int b) =>
            '0' <= c && c <= '9' && c - '0' < b || 'a' <= c && c <= 'f' && c - 'a' + 10 < b;

        /// <summary>The value of s's first n characters, read as digits of base b.</summary>
        [GhostFunction]
        private static int Value(string s, int n, int b)
        {
            Spec.Requires(0 <= n && n <= s.Length);
            Spec.Decreases(n);
            return n == 0 ? 0 : Value(s, n - 1, b) * b + DigitValue(s[n - 1]);
        }

        /// <summary>The value depends only on the characters it reads.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        private static void ValueOfSamePrefix(string s, string t, int n, int b)
        {
            Spec.Requires(0 <= n && n <= s.Length && n <= t.Length);
            Spec.Requires(Spec.Forall(0, n, i => s[i] == t[i]));
            Spec.Ensures(Value(s, n, b) == Value(t, n, b));
            Spec.Decreases(n);
            if (n > 0) ValueOfSamePrefix(s, t, n - 1, b);
        }

        /// <summary>n written in base b: only digits, the first one not zero (unless n is 0), and reading it gives n.</summary>
        public static string OfNat(int n, int b)
        {
            Spec.Requires(0 <= n && 2 <= b && b <= 16);
            Spec.Ensures<string>(r => r.Length > 0);
            Spec.Ensures<string>(r => Spec.Forall(0, r.Length, i => IsDigit(r[i], b)));
            Spec.Ensures<string>(r => n == 0 || r[0] != '0');
            Spec.Ensures<string>(r => Value(r, r.Length, b) == n);
            Spec.Decreases(n);
            string last = Alphabet.Substring(n % b, 1);
            Spec.Assert(DigitValue(last[0]) == n % b);
            if (n < b)
            {
                Spec.Assert(Value(last, 0, b) == 0);
                Spec.Assert(Value(last, 1, b) == n);
                return last;
            }
            string front = OfNat(n / b, b);
            string r = front + last;
            ValueOfSamePrefix(r, front, front.Length, b);
            Spec.Assert(r[front.Length] == last[0]);
            Spec.Assert(Value(r, front.Length + 1, b) == Value(r, front.Length, b) * b + DigitValue(r[front.Length]));
            return r;
        }

        /// <summary>The value of a string of digits of base b, or -1 when it holds anything else or the value doesn't fit.</summary>
        public static int ToNat(string s, int b)
        {
            Spec.Requires(2 <= b && b <= 16);
            Spec.Ensures<int>(r => r >= -1);
            Spec.Ensures<int>(r => r < 0 || Spec.Forall(0, s.Length, i => IsDigit(s[i], b)));
            Spec.Ensures<int>(r => r < 0 || r == Value(s, s.Length, b));
            int value = 0;
            for (int i = 0; i < s.Length; i++)
            {
                Spec.Invariant(0 <= i && i <= s.Length && 0 <= value);
                Spec.Invariant(Spec.Forall(0, i, k => IsDigit(s[k], b)));
                Spec.Invariant(value == Value(s, i, b));
                char c = s[i];
                int d = '0' <= c && c <= '9' ? c - '0' : 'a' <= c && c <= 'f' ? c - 'a' + 10 : 99;
                if (d >= b) return -1;
                if (value > (int.MaxValue - d) / b) return -1;
                Spec.Assert(d == DigitValue(s[i]) && IsDigit(s[i], b));
                Spec.Assert(Value(s, i + 1, b) == value * b + d);
                value = value * b + d;
            }
            return value;
        }

        /// <summary>The round trip: reading what OfNat wrote gives the number back.</summary>
        public static int RoundTrip(int n, int b)
        {
            Spec.Requires(0 <= n && 2 <= b && b <= 16);
            Spec.Ensures<int>(r => r == n || r == -1);
            return ToNat(OfNat(n, b), b);
        }
    }
}
