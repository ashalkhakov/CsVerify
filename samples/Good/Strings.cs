// Small string algorithms proved against exact specifications: what each returns is stated in terms of the characters.
using CsVerify;

namespace Samples.Good
{
    public static class Strings
    {
        /// <summary>True exactly when s reads the same both ways.</summary>
        public static bool IsPalindrome(string s)
        {
            Spec.Ensures<bool>(r => r == Spec.Forall(0, s.Length, k => s[k] == s[s.Length - 1 - k]));
            for (int i = 0; i < s.Length - 1 - i; i++)
            {
                Spec.Invariant(0 <= i && i <= s.Length);
                Spec.Invariant(Spec.Forall(0, i, k => s[k] == s[s.Length - 1 - k]));
                if (s[i] != s[s.Length - 1 - i]) return false;
            }
            return true;
        }

        /// <summary>The first place pattern occurs in text at, or -1 when it occurs nowhere.</summary>
        public static int Find(string text, string pattern)
        {
            Spec.Ensures<int>(r => -1 <= r);
            Spec.Ensures<int>(r => r < 0 || r <= text.Length - pattern.Length && OccursAt(text, pattern, r));
            Spec.Ensures<int>(r => Spec.Forall(0, text.Length - pattern.Length + 1, p => 0 <= r && r <= p || !OccursAt(text, pattern, p)));
            for (int at = 0; at <= text.Length - pattern.Length; at++)
            {
                Spec.Invariant(0 <= at && (at == 0 || at <= text.Length - pattern.Length + 1));
                Spec.Invariant(Spec.Forall(0, at, p => !OccursAt(text, pattern, p)));
                Spec.Assert(Spec.Forall(0, at, p => !OccursAt(text, pattern, p)));
                int j = 0;
                while (j < pattern.Length && text[at + j] == pattern[j])
                {
                    Spec.Invariant(0 <= j && j <= pattern.Length);
                    Spec.Invariant(Spec.Forall(0, j, k => text[at + k] == pattern[k]));
                    j++;
                }
                if (j == pattern.Length) return at;
                Spec.Assert(!OccursAt(text, pattern, at));
                Spec.Assert(Spec.Forall(0, at + 1, p => !OccursAt(text, pattern, p)));
            }
            return -1;
        }

        [GhostFunction]
        private static bool OccursAt(string text, string pattern, int at)
        {
            Spec.Requires(0 <= at && at <= text.Length - pattern.Length);
            return Spec.Forall(0, pattern.Length, k => text[at + k] == pattern[k]);
        }

        /// <summary>The value of a run of decimal digits; -1 when a character isn't a digit or the value doesn't fit.</summary>
        public static int ParseDigits(string s)
        {
            Spec.Ensures<int>(r => r < 0 || Spec.Forall(0, s.Length, k => '0' <= s[k] && s[k] <= '9'));
            Spec.Ensures<int>(r => r < 0 || r == DigitsValue(s, s.Length));
            int value = 0;
            for (int i = 0; i < s.Length; i++)
            {
                Spec.Invariant(0 <= i && i <= s.Length);
                Spec.Invariant(0 <= value);
                Spec.Invariant(Spec.Forall(0, i, k => '0' <= s[k] && s[k] <= '9'));
                Spec.Invariant(value == DigitsValue(s, i));
                char c = s[i];
                if (c < '0' || c > '9') return -1;
                int d = c - '0';
                if (value > (int.MaxValue - d) / 10) return -1;
                value = value * 10 + d;
            }
            return value;
        }

        /// <summary>The value of s's first n characters as decimal digits (a ghost function's integers don't overflow).</summary>
        [GhostFunction]
        private static int DigitsValue(string s, int n)
        {
            Spec.Requires(0 <= n && n <= s.Length);
            Spec.Decreases(n);
            return n == 0 ? 0 : DigitsValue(s, n - 1) * 10 + (s[n - 1] - '0');
        }

        /// <summary>Cutting a string in two and joining the pieces gives it back.</summary>
        public static string CutAndJoin(string s, int n)
        {
            Spec.Requires(0 <= n && n <= s.Length);
            Spec.Ensures<string>(r => r == s);
            string head = s.Substring(0, n);
            string tail = s.Substring(n);
            return head + tail;
        }

        /// <summary>Splitting at a separator: the pieces around it, with the separator back between them, are the string.</summary>
        public static string SplitAndJoin(string s, char separator)
        {
            Spec.Ensures<string>(r => r == s);
            int at = s.IndexOf(separator);
            if (at < 0) return s;
            string head = s.Substring(0, at);
            string tail = s.Substring(at + 1);
            Spec.Assert(!Contains(head, separator));
            return head + s.Substring(at, 1) + tail;
        }

        [GhostFunction]
        private static bool Contains(string s, char c) => Spec.Exists(0, s.Length, k => s[k] == c);
    }
}
