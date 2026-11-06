// UTF-8: a scalar value to bytes and back, written with shifts and masks and specified by plain arithmetic.
// After Dafny's standard library (Std/Unicode/Utf8EncodingForm.dfy; Copyright (c) Microsoft Corporation, MIT License).
using CsVerify;

namespace Samples.Good
{
    public static class Utf8
    {
        /// <summary>A Unicode scalar value: any code point but a surrogate.</summary>
        [GhostFunction]
        public static bool IsScalar(int cp) => 0 <= cp && cp <= 0x10FFFF && !(0xD800 <= cp && cp <= 0xDFFF);

        /// <summary>How many bytes a scalar value takes.</summary>
        [GhostFunction]
        public static int ByteCount(int cp) => cp < 0x80 ? 1 : cp < 0x800 ? 2 : cp < 0x10000 ? 3 : 4;

        /// <summary>b holds at at the encoding of cp, as the standard's table has it.</summary>
        [GhostFunction]
        public static bool EncodedAt(byte[] b, int at, int cp) =>
            0 <= at &&
            (cp < 0x80 ? at < b.Length && b[at] == cp
            : cp < 0x800 ? b.Length - at >= 2 && b[at] == 0xC0 + cp / 64 && b[at + 1] == 0x80 + cp % 64
            : cp < 0x10000 ? b.Length - at >= 3 && b[at] == 0xE0 + cp / 4096 && b[at + 1] == 0x80 + cp / 64 % 64 && b[at + 2] == 0x80 + cp % 64
            : b.Length - at >= 4 && b[at] == 0xF0 + cp / 262144 && b[at + 1] == 0x80 + cp / 4096 % 64 && b[at + 2] == 0x80 + cp / 64 % 64 && b[at + 3] == 0x80 + cp % 64);

        public static byte[] Encode(int cp)
        {
            Spec.Requires(IsScalar(cp));
            Spec.Ensures<byte[]>(r => r.Length == ByteCount(cp) && EncodedAt(r, 0, cp));
            if (cp < 0x80) return new byte[] { (byte)cp };
            if (cp < 0x800) return new byte[] { (byte)(0xC0 | (cp >> 6)), (byte)(0x80 | (cp & 0x3F)) };
            if (cp < 0x10000) return new byte[] { (byte)(0xE0 | (cp >> 12)), (byte)(0x80 | ((cp >> 6) & 0x3F)), (byte)(0x80 | (cp & 0x3F)) };
            return new byte[] { (byte)(0xF0 | (cp >> 18)), (byte)(0x80 | ((cp >> 12) & 0x3F)), (byte)(0x80 | ((cp >> 6) & 0x3F)), (byte)(0x80 | (cp & 0x3F)) };
        }

        // the bits of each form, as plain arithmetic: the rest of the proof reasons about these

        private static int Two(int b0, int b1)
        {
            Spec.Requires(0xC0 <= b0 && b0 <= 0xDF && 0x80 <= b1 && b1 <= 0xBF);
            Spec.Ensures<int>(r => r == (b0 - 0xC0) * 64 + (b1 - 0x80));
            return ((b0 & 0x1F) << 6) | (b1 & 0x3F);
        }

        private static int Three(int b0, int b1, int b2)
        {
            Spec.Requires(0xE0 <= b0 && b0 <= 0xEF && 0x80 <= b1 && b1 <= 0xBF && 0x80 <= b2 && b2 <= 0xBF);
            Spec.Ensures<int>(r => r == (b0 - 0xE0) * 4096 + (b1 - 0x80) * 64 + (b2 - 0x80));
            return ((b0 & 0x0F) << 12) | ((b1 & 0x3F) << 6) | (b2 & 0x3F);
        }

        private static int Four(int b0, int b1, int b2, int b3)
        {
            Spec.Requires(0xF0 <= b0 && b0 <= 0xF7 && 0x80 <= b1 && b1 <= 0xBF && 0x80 <= b2 && b2 <= 0xBF && 0x80 <= b3 && b3 <= 0xBF);
            Spec.Ensures<int>(r => r == (b0 - 0xF0) * 262144 + (b1 - 0x80) * 4096 + (b2 - 0x80) * 64 + (b3 - 0x80));
            return ((b0 & 0x07) << 18) | ((b1 & 0x3F) << 12) | ((b2 & 0x3F) << 6) | (b3 & 0x3F);
        }

        /// <summary>An encoding says which bytes it has, so two scalar values can't share one.</summary>
        [Lemma, System.Diagnostics.Conditional(Spec.Symbol)]
        private static void OneEncoding(byte[] b, int at, int x, int y)
        {
            Spec.Requires(IsScalar(x) && IsScalar(y) && EncodedAt(b, at, x) && EncodedAt(b, at, y));
            Spec.Ensures(x == y);
        }

        /// <summary>The scalar value encoded at at, or -1: truncated, a stray byte, overlong, a surrogate or out of range.</summary>
        public static int Decode(byte[] b, int at)
        {
            Spec.Requires(0 <= at && at < b.Length);
            Spec.Ensures<int>(r => r >= -1);
            // what it accepts is exactly the encoding: so no overlong form, and nothing else, gets through
            Spec.Ensures<int>(r => r < 0 || IsScalar(r) && EncodedAt(b, at, r));
            // and it rejects nothing the standard allows
            Spec.Ensures<int>(r => Spec.Forall(0, 0x110000, cp => !(IsScalar(cp) && EncodedAt(b, at, cp)) || r == cp));
            int b0 = b[at];
            if (b0 < 0x80)
            {
                Spec.Assert(EncodedAt(b, at, b0));
                return b0;
            }
            if ((b0 & 0xE0) == 0xC0)
            {
                if (b.Length - at < 2) return -1;
                int b1 = b[at + 1];
                if ((b1 & 0xC0) != 0x80) return -1;
                int cp = Two(b0, b1);
                if (cp < 0x80) return -1;
                Spec.Assert(EncodedAt(b, at, cp));
                return cp;
            }
            if ((b0 & 0xF0) == 0xE0)
            {
                if (b.Length - at < 3) return -1;
                int b1 = b[at + 1], b2 = b[at + 2];
                if ((b1 & 0xC0) != 0x80 || (b2 & 0xC0) != 0x80) return -1;
                int cp = Three(b0, b1, b2);
                if (cp < 0x800 || 0xD800 <= cp && cp <= 0xDFFF) return -1;
                Spec.Assert(EncodedAt(b, at, cp));
                return cp;
            }
            if ((b0 & 0xF8) == 0xF0)
            {
                if (b.Length - at < 4) return -1;
                int b1 = b[at + 1], b2 = b[at + 2], b3 = b[at + 3];
                if ((b1 & 0xC0) != 0x80 || (b2 & 0xC0) != 0x80 || (b3 & 0xC0) != 0x80) return -1;
                int cp = Four(b0, b1, b2, b3);
                if (cp < 0x10000 || cp > 0x10FFFF) return -1;
                Spec.Assert(EncodedAt(b, at, cp));
                return cp;
            }
            return -1;
        }

        /// <summary>The round trip: what Encode wrote, Decode reads back.</summary>
        public static void RoundTrip(int cp)
        {
            Spec.Requires(IsScalar(cp));
            var bytes = Encode(cp);
            int back = Decode(bytes, 0);
            Spec.Assert(back == cp);
        }
    }
}
