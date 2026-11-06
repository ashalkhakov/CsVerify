// Knuth-Morris-Pratt search, proved correct: it finds the first occurrence. (ATS's kmp.dats, by Hongwei Xi, proves memory
// safety and termination of the same algorithm; this is written afresh, with the stronger theorem.)
using System.Diagnostics;
using CsVerify;

namespace Samples.Good
{
    public static class Kmp
    {
        /// <summary>pattern occurs in text at start.</summary>
        [GhostFunction]
        public static bool Occurs(string text, string pattern, int start) =>
            0 <= start && start + pattern.Length <= text.Length && Spec.Forall(0, pattern.Length, j => text[start + j] == pattern[j]);

        /// <summary>p's first q characters end with their own first k, and k is shorter than q: a border.</summary>
        [GhostFunction]
        public static bool Border(string p, int k, int q) =>
            0 <= k && k < q && q <= p.Length && Spec.Forall(0, k, j => p[q - k + j] == p[j]);

        /// <summary>No border of p's first q characters is as long as lo.</summary>
        [GhostFunction]
        public static bool NoBorderFrom(string p, int lo, int q) => Spec.Forall(lo, q, k => !Border(p, k, q));

        /// <summary>k is the longest border of p's first q characters.</summary>
        [GhostFunction]
        public static bool Longest(string p, int k, int q) => Border(p, k, q) && NoBorderFrom(p, k + 1, q);

        // ---- borders ----------------------------------------------------------------------------------------------

        /// <summary>A border of a border is a border.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        private static void BorderOfBorder(string p, int j, int k, int q)
        {
            Spec.Requires(Border(p, j, k) && Border(p, k, q));
            Spec.Ensures(Border(p, j, q));
            Spec.Assert(Spec.Forall(0, j, i => p[k - j + i] == p[i]));
            Spec.Assert(Spec.Forall(0, k, i => p[q - k + i] == p[i]));
            Spec.Assert(Spec.Forall(0, j, i => p[q - k + (k - j + i)] == p[k - j + i]));
            Spec.Assert(Spec.Forall(0, j, i => p[q - j + i] == p[i]));
        }

        /// <summary>Of two borders, the shorter is a border of the longer.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        private static void ShorterBorder(string p, int j, int k, int q)
        {
            Spec.Requires(j < k && Border(p, j, q) && Border(p, k, q));
            Spec.Ensures(Border(p, j, k));
            Spec.Assert(Spec.Forall(0, j, i => p[q - j + i] == p[i]));
            Spec.Assert(Spec.Forall(0, k, i => p[q - k + i] == p[i]));
            Spec.Assert(Spec.Forall(0, j, i => p[q - k + (k - j + i)] == p[k - j + i]));
            Spec.Assert(Spec.Forall(0, j, i => p[k - j + i] == p[i]));
        }

        /// <summary>A border extended by a matching character.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        private static void BorderGrows(string p, int k, int q)
        {
            Spec.Requires(Border(p, k, q) && q < p.Length && p[k] == p[q]);
            Spec.Ensures(Border(p, k + 1, q + 1));
            Spec.Assert(Spec.Forall(0, k, i => p[q - k + i] == p[i]));
            Spec.Assert(Spec.Forall(0, k + 1, i => p[q + 1 - (k + 1) + i] == p[i]));
        }

        /// <summary>A non-empty border, shortened by its last character.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        private static void BorderShrinks(string p, int k, int q)
        {
            Spec.Requires(1 <= k && Border(p, k, q));
            Spec.Ensures(Border(p, k - 1, q - 1));
            Spec.Ensures(p[k - 1] == p[q - 1]);
            Spec.Assert(Spec.Forall(0, k, i => p[q - k + i] == p[i]));
            Spec.Assert(p[q - k + (k - 1)] == p[k - 1]);
            Spec.Assert(Spec.Forall(0, k - 1, i => p[q - 1 - (k - 1) + i] == p[i]));
        }

        // ---- the failure table --------------------------------------------------------------------------------------

        /// <summary>fail[q - 1] is the longest border of p's first q characters.</summary>
        public static int[] Table(string p)
        {
            Spec.Requires(p.Length > 0);
            Spec.Ensures<int[]>(f => f.Length == p.Length);
            Spec.Ensures<int[]>(f => Spec.Forall(1, p.Length + 1, r => Longest(p, f[r - 1], r)));
            var f = new int[p.Length];
            Spec.Assert(Border(p, 0, 1) && NoBorderFrom(p, 1, 1));
            Spec.Assert(Longest(p, 0, 1));
            for (int q = 1; q < p.Length; q++)
            {
                Spec.Invariant(1 <= q && q <= p.Length && f.Length == p.Length);
                Spec.Invariant(Spec.Forall(1, q + 1, r => Longest(p, f[r - 1], r)));
                f[q] = NextBorder(p, f, q);
            }
            return f;
        }

        /// <summary>The longest border of p's first q + 1 characters, from the table of those before.</summary>
        private static int NextBorder(string p, int[] f, int q)
        {
            Spec.Requires(1 <= q && q < p.Length && f.Length == p.Length);
            Spec.Requires(Spec.Forall(1, q + 1, r => Longest(p, f[r - 1], r)));
            Spec.Ensures<int>(r => Longest(p, r, q + 1));
            int k = f[q - 1];
            Spec.Assert(Longest(p, k, q));
            Spec.Assert(Border(p, k, q) && NoBorderFrom(p, k + 1, q));
            while (k > 0 && p[k] != p[q])
            {
                Spec.Invariant(0 <= k && Border(p, k, q));
                // every longer border of the first q characters fails to extend
                Spec.Invariant(Spec.Forall(k + 1, q, j => !Border(p, j, q) || p[j] != p[q]));
                Spec.Decreases(k);
                int shorter = f[k - 1];
                Spec.Assert(Longest(p, shorter, k));
                Spec.Assert(Border(p, shorter, k) && NoBorderFrom(p, shorter + 1, k));
                BorderOfBorder(p, shorter, k, q);
                OnlyLongerBorders(p, shorter + 1, k, q);
                k = shorter;
            }
            if (p[k] == p[q])
            {
                BorderGrows(p, k, q);
                LongestOfNext(p, k, q, k + 2);
                k++;
            }
            else LongestOfNext(p, k, q, 1);
            Spec.Assert(Border(p, k, q + 1));
            Spec.Assert(NoBorderFrom(p, k + 1, q + 1));
            Spec.Assert(Longest(p, k, q + 1));
            return k;
        }

        /// <summary>From lo up to k, no border of q: each would be a border of k.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        private static void OnlyLongerBorders(string p, int lo, int k, int q)
        {
            Spec.Requires(0 <= lo && lo <= k && Border(p, k, q) && NoBorderFrom(p, lo, k));
            Spec.Ensures(NoBorderFrom(p, lo, k) && Spec.Forall(lo, k, j => !Border(p, j, q)));
            Spec.Decreases(k - lo);
            if (lo == k) return;
            Spec.Assert(!Border(p, lo, k));
            if (Border(p, lo, q)) ShorterBorder(p, lo, k, q);
            Spec.Assert(Spec.Forall(lo + 1, k, j => !Border(p, j, k)));
            Spec.Assert(NoBorderFrom(p, lo + 1, k));
            OnlyLongerBorders(p, lo + 1, k, q);
        }

        /// <summary>A border of q + 1 characters comes from a border of q that extends: from none longer than the search found.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        private static void NotABorder(string p, int k, int q, int j)
        {
            Spec.Requires(0 <= k && k < q && q < p.Length && 1 <= j && (k + 1 < j || k + 1 == j && p[k] != p[q]));
            Spec.Requires(Spec.Forall(k + 1, q, i => !Border(p, i, q) || p[i] != p[q]));
            Spec.Ensures(!Border(p, j, q + 1));
            if (Border(p, j, q + 1))
            {
                BorderShrinks(p, j, q + 1);
                if (k + 1 < j) Spec.Assert(!Border(p, j - 1, q) || p[j - 1] != p[q]);
            }
        }

        /// <summary>What the search for the longest border of q + 1 characters found is the longest.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        private static void LongestOfNext(string p, int k, int q, int lo)
        {
            Spec.Requires(0 <= k && k < q && q < p.Length && 1 <= lo && lo <= q + 1 && (k + 1 < lo || k + 1 == lo && p[k] != p[q]));
            Spec.Requires(Spec.Forall(k + 1, q, i => !Border(p, i, q) || p[i] != p[q]));
            Spec.Ensures(Spec.Forall(lo, q + 1, j => !Border(p, j, q + 1)));
            Spec.Decreases(q + 1 - lo);
            if (lo == q + 1) return;
            NotABorder(p, k, q, lo);
            LongestOfNext(p, k, q, lo + 1);
        }

        // ---- the search -----------------------------------------------------------------------------------------------

        /// <summary>text's q characters before i are pattern's first q.</summary>
        [GhostFunction]
        public static bool Matched(string text, string pattern, int i, int q) =>
            0 <= q && q <= i && i <= text.Length && q <= pattern.Length && Spec.Forall(0, q, j => text[i - q + j] == pattern[j]);

        /// <summary>A later occurrence overlapping a match would be a border of it.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        private static void OverlapIsBorder(string text, string pattern, int i, int q, int s)
        {
            Spec.Requires(Matched(text, pattern, i, q) && Occurs(text, pattern, s) && i - q < s && s <= i);
            Spec.Ensures(Border(pattern, i - s, q));
            Spec.Assert(Spec.Forall(0, q, j => text[i - q + j] == pattern[j]));
            Spec.Assert(Spec.Forall(0, pattern.Length, j => text[s + j] == pattern[j]));
            Spec.Assert(Spec.Forall(0, i - s, j => text[i - q + (q - (i - s) + j)] == pattern[q - (i - s) + j]));
            Spec.Assert(Spec.Forall(0, i - s, j => pattern[q - (i - s) + j] == pattern[j]));
        }

        /// <summary>Between the match of q characters and the next shorter match, nothing occurs.</summary>
        [Lemma, Conditional(Spec.Symbol)]
        private static void NothingBetween(string text, string pattern, int i, int q, int lo, int shorter)
        {
            Spec.Requires(Matched(text, pattern, i, q) && 0 < q && q < pattern.Length && i < text.Length && text[i] != pattern[q]);
            Spec.Requires(0 <= shorter && NoBorderFrom(pattern, shorter + 1, q));
            Spec.Requires(i - q <= lo && lo <= i - shorter);
            Spec.Ensures(Spec.Forall(lo, i - shorter, s => !Occurs(text, pattern, s)));
            Spec.Decreases(i - shorter - lo);
            if (lo == i - shorter) return;
            if (Occurs(text, pattern, lo))
            {
                if (lo == i - q) Spec.Assert(text[lo + q] == pattern[q]);
                else
                {
                    OverlapIsBorder(text, pattern, i, q, lo);
                    Spec.Assert(!Border(pattern, i - lo, q));
                }
            }
            NothingBetween(text, pattern, i, q, lo + 1, shorter);
        }

        /// <summary>The first place pattern occurs in text, or -1 when it occurs nowhere.</summary>
        public static int Search(string text, string pattern)
        {
            Spec.Ensures<int>(r => -1 <= r);
            Spec.Ensures<int>(r => r < 0 || Occurs(text, pattern, r));
            Spec.Ensures<int>(r => Spec.Forall(0, text.Length + 1, s => 0 <= r && r <= s || !Occurs(text, pattern, s)));
            if (pattern.Length == 0) return 0;
            var fail = Table(pattern);
            int q = 0;
            for (int i = 0; i < text.Length; i++)
            {
                Spec.Invariant(0 <= i && i <= text.Length && 0 <= q && q < pattern.Length);
                Spec.Invariant(Matched(text, pattern, i, q));
                Spec.Invariant(Spec.Forall(0, i - q, s => !Occurs(text, pattern, s)));
                while (q > 0 && pattern[q] != text[i])
                {
                    Spec.Invariant(0 <= q && q < pattern.Length && Matched(text, pattern, i, q));
                    Spec.Invariant(Spec.Forall(0, i - q, s => !Occurs(text, pattern, s)));
                    Spec.Decreases(q);
                    int shorter = fail[q - 1];
                    Spec.Assert(Longest(pattern, shorter, q));
                    Spec.Assert(Border(pattern, shorter, q) && NoBorderFrom(pattern, shorter + 1, q));
                    NothingBetween(text, pattern, i, q, i - q, shorter);
                    Spec.Assert(Spec.Forall(0, shorter, j => pattern[q - shorter + j] == pattern[j]));
                    Spec.Assert(Spec.Forall(0, shorter, j => text[i - q + (q - shorter + j)] == pattern[q - shorter + j]));
                    q = shorter;
                    Spec.Assert(Matched(text, pattern, i, q));
                }
                if (pattern[q] == text[i])
                {
                    Spec.Assert(Matched(text, pattern, i + 1, q + 1));
                    q++;
                    if (q == pattern.Length)
                    {
                        Spec.Assert(Occurs(text, pattern, i + 1 - q));
                        return i + 1 - q;
                    }
                }
                else Spec.Assert(!Occurs(text, pattern, i));
            }
            return -1;
        }
    }
}
