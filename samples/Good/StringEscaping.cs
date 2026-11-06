// Escaping and unescaping, after Dafny's standard library (Std/Strings.dfy; Copyright (c) Microsoft Corporation, MIT
// License). The comparison proves what the C library's strcmp promises: lexicographic order.
using System.Diagnostics;
using CsVerify;

namespace Samples.Good
{
    public static class StringEscaping
    {
        /// <summary>s, with esc before each character of must.</summary>
        [Pure]
        public static string Escape(string s, string must, string esc)
        {
            Spec.Requires(esc.Length == 1);
            Spec.Decreases(s.Length);
            if (s.Length == 0) return s;
            string rest = Escape(s.Substring(1), must, esc);
            return must.Contains(s[0]) ? esc + s.Substring(0, 1) + rest : s.Substring(0, 1) + rest;
        }

        /// <summary>s, with each esc removed and what follows it kept; null when an esc has nothing after it.</summary>
        [Pure]
        public static string? Unescape(string s, string esc)
        {
            Spec.Requires(esc.Length == 1);
            Spec.Decreases(s.Length);
            if (s.Length == 0) return s;
            if (s[0] != esc[0])
            {
                string? tail = Unescape(s.Substring(1), esc);
                return tail == null ? null : s.Substring(0, 1) + tail;
            }
            if (s.Length < 2) return null;
            string? after = Unescape(s.Substring(2), esc);
            return after == null ? null : s.Substring(1, 1) + after;
        }

        /// <summary>Unescaping undoes escaping, if the escape character is itself escaped.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        public static void UnescapeEscape(string s, string must, string esc)
        {
            Spec.Requires(esc.Length == 1 && must.Contains(esc[0]));
            Spec.Ensures(Unescape(Escape(s, must, esc), esc) == s);
            Spec.Decreases(s.Length);
            if (s.Length == 0)
            {
                Spec.Assert(Escape(s, must, esc) == s);
                return;
            }
            string rest = s.Substring(1);
            string first = s.Substring(0, 1);
            string escapedRest = Escape(rest, must, esc);
            UnescapeEscape(rest, must, esc);
            string escaped = Escape(s, must, esc);
            if (must.Contains(s[0]))
            {
                Spec.Assert(escaped == esc + first + escapedRest);
                Spec.Assert(escaped[0] == esc[0] && escaped[1] == s[0]);
                Spec.Assert(escaped.Substring(2) == escapedRest);
                Spec.Assert(escaped.Substring(1, 1) == first);
                Spec.Assert(first + rest == s);
            }
            else
            {
                Spec.Assert(s[0] != esc[0]);
                Spec.Assert(escaped == first + escapedRest);
                Spec.Assert(escaped[0] == s[0]);
                Spec.Assert(escaped.Substring(1) == escapedRest);
                Spec.Assert(escaped.Substring(0, 1) == first);
                Spec.Assert(first + rest == s);
            }
        }
    }

    public static class StringComparing
    {
        /// <summary>a and b agree on their first n characters.</summary>
        [GhostFunction]
        private static bool SamePrefix(string a, string b, int n)
        {
            Spec.Requires(0 <= n && n <= a.Length && n <= b.Length);
            return Spec.Forall(0, n, i => a[i] == b[i]);
        }

        /// <summary>a comes before b when, at the first place they differ, a has ended or has the smaller character.</summary>
        [GhostFunction]
        private static bool Before(string a, string b)
        {
            int shorter = a.Length < b.Length ? a.Length : b.Length;
            return Spec.Exists(0, shorter + 1, k => SamePrefix(a, b, k) && (k == a.Length ? k < b.Length : k < b.Length && a[k] < b[k]));
        }

        /// <summary>Where a and b first differ decides which comes first (whichever is at i, and no other k can say otherwise).</summary>
        [Lemma, Conditional(Spec.Symbol)]
        private static void DecidedAt(string a, string b, int i)
        {
            Spec.Requires(0 <= i && i <= a.Length && i <= b.Length && SamePrefix(a, b, i));
            Spec.Requires(i == a.Length || i == b.Length || a[i] != b[i]);
            Spec.Ensures(Before(a, b) == (i == a.Length ? i < b.Length : i < b.Length && a[i] < b[i]));
            bool here = i == a.Length ? i < b.Length : i < b.Length && a[i] < b[i];
            int shorter = a.Length < b.Length ? a.Length : b.Length;
            Spec.Assert(i <= shorter);
            Spec.Assert(here == (SamePrefix(a, b, i) && here));
            Spec.Assert(Spec.Forall(0, i, k => a[k] == b[k]));
            Spec.Assert(Spec.Forall(0, shorter + 1, k => k == i || !(SamePrefix(a, b, k) && (k == a.Length ? k < b.Length : k < b.Length && a[k] < b[k]))));
        }

        /// <summary>strcmp: negative, zero or positive as a comes before b, is b, or comes after it.</summary>
        public static int Compare(string a, string b)
        {
            Spec.Ensures<int>(r => (r == 0) == (a == b));
            Spec.Ensures<int>(r => (r < 0) == Before(a, b));
            Spec.Ensures<int>(r => (r > 0) == Before(b, a));
            int i = 0;
            while (i < a.Length && i < b.Length)
            {
                Spec.Invariant(0 <= i && i <= a.Length && i <= b.Length);
                Spec.Invariant(SamePrefix(a, b, i));
                if (a[i] != b[i])
                {
                    DecidedAt(a, b, i);
                    DecidedAt(b, a, i);
                    return a[i] < b[i] ? -1 : 1;
                }
                i++;
            }
            DecidedAt(a, b, i);
            DecidedAt(b, a, i);
            return a.Length < b.Length ? -1 : a.Length > b.Length ? 1 : 0;
        }
    }
}
