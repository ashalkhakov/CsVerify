using CsVerify;

namespace Samples
{
    // A port of libatsc's strbuf (after the ATS prelude's): a C string in a buffer. strbuf_v(m, n, l) is a buffer of
    // m chars holding n non-NUL chars and a NUL after them (m > n). In ATS its shape is given by axioms
    // (strbuf_v_null, strbuf_v_cons, strbuf_v_uncons, strbuf_v_split) and the copy from a string by a __trustme;
    // here strbuf_v is a predicate over the buffer's cells, and those facts are its body: each operation proves it.
    // (A C# string's characters are not modeled, so the source of a copy is a char array without NULs, which is what
    // ATS's string(n) is.)
    public static class AtsStrBuf
    {
        /// <summary>strbuf_v(m, n, l): n non-NUL chars, then a NUL, in a buffer of m = buf.Length chars.</summary>
        [Predicate]
        public static bool StrBuf(char[] buf, int n) =>
            buf != null && 0 <= n && n < buf.Length && Spec.Acc(buf) &&
            Spec.Forall(0, n, i => buf[i] != '\0') && buf[n] == '\0';

        /// <summary>strbuf_of_bytes: an empty string in fresh bytes (strbuf_v_null).</summary>
        public static void OfBytes(char[] buf)
        {
            Spec.Requires(buf.Length > 0 && Spec.Acc(buf));
            Spec.Ensures(StrBuf(buf, 0));
            buf[0] = '\0';
            Spec.Fold(StrBuf(buf, 0));
        }

        /// <summary>strbuf_of_substring: str[st..st+ln) copied into the buffer, and a NUL after it (memcpy).</summary>
        public static void OfSubstring(char[] buf, char[] str, int st, int ln)
        {
            Spec.Requires(0 <= st && 0 <= ln && st + ln <= str.Length && ln < buf.Length && buf != str && Spec.Acc(buf));
            Spec.Requires(Spec.Forall(st, st + ln, i => str[i] != '\0'));
            Spec.Ensures(StrBuf(buf, ln) && Spec.Forall(0, ln, i => buf[i] == str[st + i]));
            for (int i = 0; i < ln; i++)
            {
                Spec.Invariant(0 <= i && i <= ln && Spec.Forall(0, i, j => buf[j] == str[st + j]));
                buf[i] = str[st + i];
            }
            buf[ln] = '\0';
            Spec.Fold(StrBuf(buf, ln));
        }

        /// <summary>strbuf_of_string.</summary>
        public static void OfString(char[] buf, char[] str)
        {
            Spec.Requires(str.Length < buf.Length && buf != str && Spec.Acc(buf) && Spec.Forall(0, str.Length, i => str[i] != '\0'));
            Spec.Ensures(StrBuf(buf, str.Length) && Spec.Forall(0, str.Length, i => buf[i] == str[i]));
            OfSubstring(buf, str, 0, str.Length);
        }

        /// <summary>strbuf_get_char_at: a char of the string, never the NUL.</summary>
        public static char GetCharAt(char[] buf, int n, int i)
        {
            Spec.Requires(0 <= i && i < n && 0 <= n && n < buf.Length && StrBuf(buf, n));
            Spec.Ensures((char c) => c != '\0' && c == buf[i] && 0 <= n && n < buf.Length && StrBuf(buf, n));
            Spec.Ensures(Spec.Forall(0, n, j => buf[j] == Spec.Old(buf[j])));
            Spec.Unfold(StrBuf(buf, n));
            char c = buf[i];
            Spec.Fold(StrBuf(buf, n));
            return c;
        }

        /// <summary>strbuf_set_char_at: a non-NUL char in place of another; the length stays.</summary>
        public static void SetCharAt(char[] buf, int n, int i, char c)
        {
            Spec.Requires(0 <= i && i < n && c != '\0' && 0 <= n && n < buf.Length && StrBuf(buf, n));
            Spec.Ensures(StrBuf(buf, n) && buf[i] == c && Spec.Forall(0, n, j => j != i ? buf[j] == Spec.Old(buf[j]) : true));
            Spec.Unfold(StrBuf(buf, n));
            buf[i] = c;
            Spec.Fold(StrBuf(buf, n));
        }

        /// <summary>strbuf_test_char_at_size: the char at i, which is NUL exactly at the end.</summary>
        public static char TestCharAt(char[] buf, int n, int i)
        {
            Spec.Requires(0 <= i && i <= n && 0 <= n && n < buf.Length && StrBuf(buf, n));
            Spec.Ensures((char c) => (c == '\0') == (i == n) && 0 <= n && n < buf.Length && StrBuf(buf, n));
            Spec.Ensures(Spec.Forall(0, n, j => buf[j] == Spec.Old(buf[j])));
            Spec.Unfold(StrBuf(buf, n));
            char c = buf[i];
            Spec.Fold(StrBuf(buf, n));
            return c;
        }

        /// <summary>strlen: scans for the NUL; it is at n, so the scan finds the length.</summary>
        public static int Length(char[] buf, int n)
        {
            Spec.Requires(0 <= n && n < buf.Length && StrBuf(buf, n));
            Spec.Ensures((int r) => r == n && StrBuf(buf, n));
            Spec.Ensures(Spec.Forall(0, n, j => buf[j] == Spec.Old(buf[j])));
            int i = 0;
            while (TestCharAt(buf, n, i) != '\0')
            {
                Spec.Invariant(0 <= i && i <= n && StrBuf(buf, n) && Spec.Forall(0, n, j => buf[j] == Spec.Old(buf[j])));
                Spec.Decreases(n - i);
                i++;
            }
            return i;
        }

        /// <summary>strbuf_strchr: the first c in the string (strchr_v_unsome), or -1 (strchr_v_unnone).</summary>
        public static int IndexOf(char[] buf, int n, char c)
        {
            Spec.Requires(c != '\0' && 0 <= n && n < buf.Length && StrBuf(buf, n));
            Spec.Ensures((int r) => StrBuf(buf, n) && -1 <= r && r < n);
            Spec.Ensures(Spec.Forall(0, n, j => buf[j] == Spec.Old(buf[j])));
            Spec.Ensures((int r) => r >= 0 ? buf[r] == c && Spec.Forall(0, r, j => buf[j] != c) : Spec.Forall(0, n, j => buf[j] != c));
            Spec.Unfold(StrBuf(buf, n));
            int i = 0;
            while (buf[i] != '\0')
            {
                Spec.Invariant(0 <= i && i <= n && Spec.Forall(0, i, j => buf[j] != c));
                Spec.Decreases(n - i);
                if (buf[i] == c)
                {
                    Spec.Fold(StrBuf(buf, n));
                    return i;
                }
                i++;
            }
            Spec.Fold(StrBuf(buf, n));
            return -1;
        }

        /// <summary>"abc" into a buffer of 8: length 3, 'c' at 2, then "axc" and no more 'b'.</summary>
        public static bool Demo()
        {
            Spec.Ensures((bool r) => r);
            var buf = new char[8];
            OfString(buf, new[] { 'a', 'b', 'c' });
            int len = Length(buf, 3);
            int at = IndexOf(buf, 3, 'c');
            SetCharAt(buf, 3, 1, 'x');
            char x = GetCharAt(buf, 3, 1);
            int none = IndexOf(buf, 3, 'b');
            return len == 3 && at == 2 && x == 'x' && none == -1;
        }
    }
}
