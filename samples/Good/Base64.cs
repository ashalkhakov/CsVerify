// Base64, written with shifts and masks and specified by plain arithmetic: the round trip of a byte array.
// After Dafny's standard library (Std/Base64.dfy; Copyright (c) Microsoft Corporation, MIT License).
using CsVerify;

namespace Samples.Good
{
    public static class Base64
    {
        /// <summary>The value of a Base64 character, or -1 for any other.</summary>
        [GhostFunction]
        public static int V(int c) =>
            'A' <= c && c <= 'Z' ? c - 'A' : 'a' <= c && c <= 'z' ? c - 'a' + 26 : '0' <= c && c <= '9' ? c - '0' + 52 : c == '+' ? 62 : c == '/' ? 63 : -1;

        /// <summary>Four characters say what three bytes do.</summary>
        [GhostFunction]
        public static bool Block(int c0, int c1, int c2, int c3, int b0, int b1, int b2) =>
            V(c0) >= 0 && V(c1) >= 0 && V(c2) >= 0 && V(c3) >= 0 &&
            V(c0) * 262144 + V(c1) * 4096 + V(c2) * 64 + V(c3) == b0 * 65536 + b1 * 256 + b2;

        private static char Symbol(int i)
        {
            Spec.Requires(0 <= i && i < 64);
            Spec.Ensures<char>(r => V(r) == i);
            if (i < 26) return (char)('A' + i);
            if (i < 52) return (char)('a' + i - 26);
            if (i < 62) return (char)('0' + i - 52);
            return i == 62 ? '+' : '/';
        }

        private static int Value(char c)
        {
            Spec.Ensures<int>(r => r == V(c));
            if ('A' <= c && c <= 'Z') return c - 'A';
            if ('a' <= c && c <= 'z') return c - 'a' + 26;
            if ('0' <= c && c <= '9') return c - '0' + 52;
            return c == '+' ? 62 : c == '/' ? 63 : -1;
        }

        private static int Pack(int b0, int b1, int b2)
        {
            Spec.Requires(0 <= b0 && b0 < 256 && 0 <= b1 && b1 < 256 && 0 <= b2 && b2 < 256);
            Spec.Ensures<int>(r => r == b0 * 65536 + b1 * 256 + b2);
            return (b0 << 16) | (b1 << 8) | b2;
        }

        private static int Join(int i0, int i1, int i2, int i3)
        {
            Spec.Requires(0 <= i0 && i0 < 64 && 0 <= i1 && i1 < 64 && 0 <= i2 && i2 < 64 && 0 <= i3 && i3 < 64);
            Spec.Ensures<int>(r => r == i0 * 262144 + i1 * 4096 + i2 * 64 + i3);
            return (i0 << 18) | (i1 << 12) | (i2 << 6) | i3;
        }

        /// <summary>Two characters and padding say what one byte does (the unused bits are zero: one text for one byte).</summary>
        [GhostFunction]
        public static bool Tail1(int c0, int c1, int p0, int p1, int b0) =>
            V(c0) >= 0 && V(c1) >= 0 && V(c1) % 16 == 0 && p0 == '=' && p1 == '=' && V(c0) * 4 + V(c1) / 16 == b0;

        /// <summary>Three characters and padding say what two bytes do.</summary>
        [GhostFunction]
        public static bool Tail2(int c0, int c1, int c2, int p0, int b0, int b1) =>
            V(c0) >= 0 && V(c1) >= 0 && V(c2) >= 0 && V(c2) % 4 == 0 && p0 == '=' && V(c0) * 1024 + V(c1) * 16 + V(c2) / 4 == b0 * 256 + b1;

        /// <summary>How many padding characters end text.</summary>
        [GhostFunction]
        public static int Pad(char[] t) => t.Length < 2 || t[t.Length - 1] != '=' ? 0 : t[t.Length - 2] != '=' ? 1 : 2;

        /// <summary>
        /// Canonical Base64: blocks of four characters, the last perhaps padded, with the unused bits of its last character zero.
        /// </summary>
        [GhostFunction]
        public static bool WellFormed(char[] t) =>
            t.Length % 4 == 0 && (t.Length == 0 ||
                Spec.Forall(0, t.Length - 4, i => V(t[i]) >= 0) && V(t[t.Length - 4]) >= 0 && V(t[t.Length - 3]) >= 0 &&
                (Pad(t) == 2 ? V(t[t.Length - 3]) % 16 == 0
                : V(t[t.Length - 2]) >= 0 && (Pad(t) == 1 ? V(t[t.Length - 2]) % 4 == 0 : V(t[t.Length - 1]) >= 0)));

        /// <summary>The text for data: its whole blocks, and what is left, padded.</summary>
        public static char[] Encode(byte[] data)
        {
            Spec.Requires(data.Length <= 1000000000);
            Spec.Modifies(ObjSet.Empty); // (only the array it makes)
            Spec.Ensures<char[]>(r => Spec.Fresh(r));
            Spec.Ensures<char[]>(r => r.Length == (data.Length + 2) / 3 * 4);
            Spec.Ensures<char[]>(r => WellFormed(r) && Pad(r) == (3 - data.Length % 3) % 3);
            Spec.Ensures<char[]>(r => Spec.Forall(0, data.Length / 3, k =>
                Block(r[4 * k], r[4 * k + 1], r[4 * k + 2], r[4 * k + 3], data[3 * k], data[3 * k + 1], data[3 * k + 2])));
            Spec.Ensures<char[]>(r => data.Length % 3 != 1 || Tail1(r[r.Length - 4], r[r.Length - 3], r[r.Length - 2], r[r.Length - 1], data[data.Length - 1]));
            Spec.Ensures<char[]>(r => data.Length % 3 != 2 || Tail2(r[r.Length - 4], r[r.Length - 3], r[r.Length - 2], r[r.Length - 1], data[data.Length - 2], data[data.Length - 1]));
            int blocks = data.Length / 3, left = data.Length % 3;
            var text = new char[(data.Length + 2) / 3 * 4];
            for (int k = 0; k < blocks; k++)
            {
                Spec.Invariant(0 <= k && k <= blocks);
                Spec.Invariant(Spec.Forall(0, 4 * k, i => V(text[i]) >= 0));
                Spec.Invariant(Spec.Forall(0, k, j =>
                    Block(text[4 * j], text[4 * j + 1], text[4 * j + 2], text[4 * j + 3], data[3 * j], data[3 * j + 1], data[3 * j + 2])));
                int n = Pack(data[3 * k], data[3 * k + 1], data[3 * k + 2]);
                int i0 = (n >> 18) & 63, i1 = (n >> 12) & 63, i2 = (n >> 6) & 63, i3 = n & 63;
                Spec.Assert(n == (n >> 6) * 64 + i3);
                Spec.Assert((n >> 6) == (n >> 12) * 64 + i2);
                Spec.Assert((n >> 12) == (n >> 18) * 64 + i1);
                Spec.Assert((n >> 18) == i0);
                text[4 * k] = Symbol(i0);
                text[4 * k + 1] = Symbol(i1);
                text[4 * k + 2] = Symbol(i2);
                text[4 * k + 3] = Symbol(i3);
                Spec.Assert(Block(text[4 * k], text[4 * k + 1], text[4 * k + 2], text[4 * k + 3], data[3 * k], data[3 * k + 1], data[3 * k + 2]));
            }
            if (left == 1)
            {
                int b0 = data[data.Length - 1];
                text[text.Length - 4] = Symbol(b0 >> 2);
                text[text.Length - 3] = Symbol((b0 & 3) << 4);
                text[text.Length - 2] = '=';
                text[text.Length - 1] = '=';
                Spec.Assert(Tail1(text[text.Length - 4], text[text.Length - 3], text[text.Length - 2], text[text.Length - 1], data[data.Length - 1]));
            }
            else if (left == 2)
            {
                int b0 = data[data.Length - 2], b1 = data[data.Length - 1];
                text[text.Length - 4] = Symbol(b0 >> 2);
                text[text.Length - 3] = Symbol(((b0 & 3) << 4) | (b1 >> 4));
                text[text.Length - 2] = Symbol((b1 & 15) << 2);
                text[text.Length - 1] = '=';
                Spec.Assert(Tail2(text[text.Length - 4], text[text.Length - 3], text[text.Length - 2], text[text.Length - 1], data[data.Length - 2], data[data.Length - 1]));
            }
            Spec.Assert(Spec.Forall(0, 4 * blocks, i => V(text[i]) >= 0));
            Spec.Assert(Pad(text) == (3 - left) % 3);
            Spec.Assert(WellFormed(text));
            return text;
        }

        /// <summary>The bytes text says, or null when it isn't canonical Base64.</summary>
        public static byte[]? Decode(char[] text)
        {
            Spec.Modifies(ObjSet.Empty); // (only the array it makes)
            Spec.Ensures<byte[]?>(r => r == null || Spec.Fresh(r));
            Spec.Ensures<byte[]?>(r => r == null || WellFormed(text) && r.Length == text.Length / 4 * 3 - Pad(text));
            Spec.Ensures<byte[]?>(r => r == null || Spec.Forall(0, r.Length / 3, k =>
                Block(text[4 * k], text[4 * k + 1], text[4 * k + 2], text[4 * k + 3], r[3 * k], r[3 * k + 1], r[3 * k + 2])));
            Spec.Ensures<byte[]?>(r => r == null || r.Length % 3 != 1 || Tail1(text[text.Length - 4], text[text.Length - 3], text[text.Length - 2], text[text.Length - 1], r[r.Length - 1]));
            Spec.Ensures<byte[]?>(r => r == null || r.Length % 3 != 2 || Tail2(text[text.Length - 4], text[text.Length - 3], text[text.Length - 2], text[text.Length - 1], r[r.Length - 2], r[r.Length - 1]));
            // and it refuses only what isn't
            Spec.Ensures<byte[]?>(r => r != null || !WellFormed(text));
            if (text.Length % 4 != 0) return null;
            if (text.Length == 0) return new byte[0];
            int pad = text[text.Length - 1] != '=' ? 0 : text[text.Length - 2] != '=' ? 1 : 2;
            Spec.Assert(pad == Pad(text));
            int whole = pad == 0 ? text.Length / 4 : text.Length / 4 - 1;
            var data = new byte[text.Length / 4 * 3 - pad];
            for (int k = 0; k < whole; k++)
            {
                Spec.Invariant(0 <= k && k <= whole);
                Spec.Invariant(Spec.Forall(0, 4 * k, i => V(text[i]) >= 0));
                Spec.Invariant(Spec.Forall(0, k, j =>
                    Block(text[4 * j], text[4 * j + 1], text[4 * j + 2], text[4 * j + 3], data[3 * j], data[3 * j + 1], data[3 * j + 2])));
                int i0 = Value(text[4 * k]), i1 = Value(text[4 * k + 1]), i2 = Value(text[4 * k + 2]), i3 = Value(text[4 * k + 3]);
                if (i0 < 0 || i1 < 0 || i2 < 0 || i3 < 0) return null;
                int n = Join(i0, i1, i2, i3);
                data[3 * k] = (byte)(n >> 16);
                data[3 * k + 1] = (byte)((n >> 8) & 255);
                data[3 * k + 2] = (byte)(n & 255);
                Spec.Assert(Block(text[4 * k], text[4 * k + 1], text[4 * k + 2], text[4 * k + 3], data[3 * k], data[3 * k + 1], data[3 * k + 2]));
            }
            if (pad == 0)
            {
                Spec.Assert(Spec.Forall(0, text.Length, i => V(text[i]) >= 0));
                Spec.Assert(WellFormed(text));
                return data;
            }
            int a = Value(text[text.Length - 4]), b = Value(text[text.Length - 3]);
            if (a < 0 || b < 0) return null;
            if (pad == 2)
            {
                if ((b & 15) != 0) return null;
                data[data.Length - 1] = (byte)((a << 2) | (b >> 4));
                Spec.Assert(Tail1(text[text.Length - 4], text[text.Length - 3], text[text.Length - 2], text[text.Length - 1], data[data.Length - 1]));
            }
            else
            {
                int c = Value(text[text.Length - 2]);
                if (c < 0 || (c & 3) != 0) return null;
                data[data.Length - 2] = (byte)((a << 2) | (b >> 4));
                data[data.Length - 1] = (byte)(((b & 15) << 4) | (c >> 2));
                Spec.Assert(Tail2(text[text.Length - 4], text[text.Length - 3], text[text.Length - 2], text[text.Length - 1], data[data.Length - 2], data[data.Length - 1]));
            }
            Spec.Assert(WellFormed(text));
            return data;
        }

        /// <summary>Encoding and decoding give the bytes back, whatever their number.</summary>
        public static void RoundTrip(byte[] data)
        {
            Spec.Requires(data.Length <= 1000000000);
            var text = Encode(data);
            var back = Decode(text);
            Spec.Assert(back != null);
            Spec.Assert(back.Length == data.Length);
            for (int k = 0; k < data.Length / 3; k++)
            {
                Spec.Invariant(0 <= k && k <= data.Length / 3);
                Spec.Invariant(Spec.Forall(0, 3 * k, i => back[i] == data[i]));
                Spec.Assert(Block(text[4 * k], text[4 * k + 1], text[4 * k + 2], text[4 * k + 3], data[3 * k], data[3 * k + 1], data[3 * k + 2]));
                Spec.Assert(Block(text[4 * k], text[4 * k + 1], text[4 * k + 2], text[4 * k + 3], back[3 * k], back[3 * k + 1], back[3 * k + 2]));
                Spec.Assert(data[3 * k] * 65536 + data[3 * k + 1] * 256 + data[3 * k + 2] == back[3 * k] * 65536 + back[3 * k + 1] * 256 + back[3 * k + 2]);
            }
            if (data.Length % 3 == 1)
                Spec.Assert(back[data.Length - 1] == data[data.Length - 1]);
            if (data.Length % 3 == 2)
                Spec.Assert(back[data.Length - 2] == data[data.Length - 2] && back[data.Length - 1] == data[data.Length - 1]);
            Spec.Assert(Spec.Forall(0, data.Length, i => back[i] == data[i]));
        }
    }
}
