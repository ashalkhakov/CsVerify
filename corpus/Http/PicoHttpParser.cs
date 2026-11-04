// A C# port of picohttpparser (https://github.com/h2o/picohttpparser), a tiny HTTP/1.x request, response and header
// parser, with its chunked transfer-encoding decoder. The SSE4.2 fast paths are left out (the C has a portable path
// for each). It is ported as it is, without specifications: part of the corpus CsVerify is measured on (see
// corpus/README.md). The input is a span of bytes; pointers into it are offsets, and a parsed string is an offset and
// a length (-1 for the C's NULL). The C's "const char *buf" cursor is an index into the span, and its
// "*ret = ...; return NULL" pair is a negative return value.
//
// Copyright (c) 2009-2014 Kazuho Oku, Tokuhiro Matsuno, Daisuke Murase, Shigeo Mitsunari
//
// The software is licensed under either the MIT License (below) or the Perl license.
//
// Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated
// documentation files (the "Software"), to deal in the Software without restriction, including without limitation
// the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to
// permit persons to whom the Software is furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in all copies or substantial portions of
// the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE
// WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
// COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR
// OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

using System;

namespace Corpus.Http
{
    /// <summary>struct phr_header: a header's name and value, as offsets into the buffer. A continuation line has no
    /// name (NameStart is -1).</summary>
    public struct PhrHeader
    {
        public int NameStart;
        public int NameLen;
        public int ValueStart;
        public int ValueLen;
    }

    /// <summary>struct phr_chunked_decoder: the state of <see cref="PicoHttpParser.DecodeChunked"/> between calls.
    /// Zero-filled (new) to start.</summary>
    public sealed class PhrChunkedDecoder
    {
        /// <summary>number of bytes left in current chunk</summary>
        public long BytesLeftInChunk;
        /// <summary>if trailing headers should be consumed</summary>
        public bool ConsumeTrailer;
        internal int HexCount;
        internal int State;
        internal long TotalRead;
        internal long TotalOverhead;
    }

    public static class PicoHttpParser
    {
        // the results of the parsers: the C's -1 and -2
        public const int Error = -1;
        public const int Incomplete = -2;

        private static bool IsPrintableAscii(byte c) => (uint)(c - 32) < 95u;

        // token_char_map: the characters of a token (RFC 7230's tchar)
        private static readonly bool[] TokenCharMap = BuildTokenCharMap();

        private static bool[] BuildTokenCharMap()
        {
            var map = new bool[256];
            for (int c = '0'; c <= '9'; c++) map[c] = true;
            for (int c = 'A'; c <= 'Z'; c++) map[c] = true;
            for (int c = 'a'; c <= 'z'; c++) map[c] = true;
            foreach (char c in "!#$%&'*+-.^_`|~") map[c] = true;
            return map;
        }

        /// <summary>get_token_to_eol: the text up to the end of the line (CRLF or LF), and the offset after it.</summary>
        private static int GetTokenToEol(ReadOnlySpan<byte> buf, int pos, out int token, out int tokenLen)
        {
            int tokenStart = pos;
            token = -1;
            tokenLen = 0;

            for (; ; ++pos)
            {
                if (pos == buf.Length) return Incomplete;
                byte c = buf[pos];
                if (!IsPrintableAscii(c))
                {
                    if ((c < 32 && c != 9) || c == 127)
                    {
                        break;  // FOUND_CTL
                    }
                }
            }

            if (buf[pos] == '\r')
            {
                ++pos;
                if (pos == buf.Length) return Incomplete;
                if (buf[pos++] != '\n') return Error;
                tokenLen = pos - 2 - tokenStart;
            }
            else if (buf[pos] == '\n')
            {
                tokenLen = pos - tokenStart;
                ++pos;
            }
            else
            {
                return Error;
            }
            token = tokenStart;
            return pos;
        }

        /// <summary>is_complete: the offset after the blank line that ends the headers, looking from near where the
        /// last call left off.</summary>
        private static int IsComplete(ReadOnlySpan<byte> buf, int lastLen)
        {
            int retCnt = 0;
            int pos = lastLen < 3 ? 0 : lastLen - 3;

            while (true)
            {
                if (pos == buf.Length) return Incomplete;
                if (buf[pos] == '\r')
                {
                    ++pos;
                    if (pos == buf.Length) return Incomplete;
                    if (buf[pos++] != '\n') return Error;
                    ++retCnt;
                }
                else if (buf[pos] == '\n')
                {
                    ++pos;
                    ++retCnt;
                }
                else
                {
                    ++pos;
                    retCnt = 0;
                }
                if (retCnt == 2)
                {
                    return pos;
                }
            }
        }

        /// <summary>parse_token: a token ending at <paramref name="nextChar"/>, and the offset of that character.</summary>
        private static int ParseToken(ReadOnlySpan<byte> buf, int pos, out int token, out int tokenLen, byte nextChar)
        {
            int bufStart = pos;
            token = -1;
            tokenLen = 0;
            if (pos == buf.Length) return Incomplete;
            while (true)
            {
                if (buf[pos] == nextChar)
                {
                    break;
                }
                else if (!TokenCharMap[buf[pos]])
                {
                    return Error;
                }
                ++pos;
                if (pos == buf.Length) return Incomplete;
            }
            token = bufStart;
            tokenLen = pos - bufStart;
            return pos;
        }

        /// <summary>parse_http_version: "HTTP/1.x"; the returned offset is always within the buffer.</summary>
        private static int ParseHttpVersion(ReadOnlySpan<byte> buf, int pos, out int minorVersion)
        {
            minorVersion = -1;
            // we want at least [HTTP/1.<two chars>] to try to parse
            if (buf.Length - pos < 9)
            {
                return Incomplete;
            }
            if (buf[pos++] != 'H') return Error;
            if (buf[pos++] != 'T') return Error;
            if (buf[pos++] != 'T') return Error;
            if (buf[pos++] != 'P') return Error;
            if (buf[pos++] != '/') return Error;
            if (buf[pos++] != '1') return Error;
            if (buf[pos++] != '.') return Error;
            // PARSE_INT(minor_version, 1)
            if (buf[pos] < '0' || '9' < buf[pos])
            {
                return Error;
            }
            minorVersion = buf[pos++] - '0';
            return pos;
        }

        /// <summary>parse_headers: header lines up to the blank line; <paramref name="numHeaders"/> counts them.</summary>
        private static int ParseHeadersCore(ReadOnlySpan<byte> buf, int pos, PhrHeader[] headers, ref int numHeaders, int maxHeaders)
        {
            for (; ; ++numHeaders)
            {
                if (pos == buf.Length) return Incomplete;
                if (buf[pos] == '\r')
                {
                    ++pos;
                    if (pos == buf.Length) return Incomplete;
                    if (buf[pos++] != '\n') return Error;
                    break;
                }
                else if (buf[pos] == '\n')
                {
                    ++pos;
                    break;
                }
                if (numHeaders == maxHeaders)
                {
                    return Error;
                }
                if (!(numHeaders != 0 && (buf[pos] == ' ' || buf[pos] == '\t')))
                {
                    // parsing name, but do not discard SP before colon, see
                    // http://www.mozilla.org/security/announce/2006/mfsa2006-33.html
                    pos = ParseToken(buf, pos, out headers[numHeaders].NameStart, out headers[numHeaders].NameLen, (byte)':');
                    if (pos < 0)
                    {
                        return pos;
                    }
                    if (headers[numHeaders].NameLen == 0)
                    {
                        return Error;
                    }
                    ++pos;
                    for (; ; ++pos)
                    {
                        if (pos == buf.Length) return Incomplete;
                        if (!(buf[pos] == ' ' || buf[pos] == '\t'))
                        {
                            break;
                        }
                    }
                }
                else
                {
                    headers[numHeaders].NameStart = -1;
                    headers[numHeaders].NameLen = 0;
                }
                pos = GetTokenToEol(buf, pos, out int value, out int valueLen);
                if (pos < 0)
                {
                    return pos;
                }
                // remove trailing SPs and HTABs
                int valueEnd = value + valueLen;
                for (; valueEnd != value; --valueEnd)
                {
                    byte c = buf[valueEnd - 1];
                    if (!(c == ' ' || c == '\t'))
                    {
                        break;
                    }
                }
                headers[numHeaders].ValueStart = value;
                headers[numHeaders].ValueLen = valueEnd - value;
            }
            return pos;
        }

        private static int ParseRequestCore(ReadOnlySpan<byte> buf, out int method, out int methodLen, out int path, out int pathLen,
                                        out int minorVersion, PhrHeader[] headers, ref int numHeaders, int maxHeaders)
        {
            int pos = 0;
            method = path = -1;
            methodLen = pathLen = 0;
            minorVersion = -1;

            // skip first empty line (some clients add CRLF after POST content)
            if (pos == buf.Length) return Incomplete;
            if (buf[pos] == '\r')
            {
                ++pos;
                if (pos == buf.Length) return Incomplete;
                if (buf[pos++] != '\n') return Error;
            }
            else if (buf[pos] == '\n')
            {
                ++pos;
            }

            // parse request line
            pos = ParseToken(buf, pos, out method, out methodLen, (byte)' ');
            if (pos < 0)
            {
                return pos;
            }
            do
            {
                ++pos;
                if (pos == buf.Length) return Incomplete;
            } while (buf[pos] == ' ');

            // ADVANCE_TOKEN(path, path_len)
            int tokStart = pos;
            if (pos == buf.Length) return Incomplete;
            while (true)
            {
                byte c = buf[pos];
                if (c == ' ')
                {
                    break;
                }
                else if (!IsPrintableAscii(c))
                {
                    if (c < 32 || c == 127)
                    {
                        return Error;
                    }
                }
                ++pos;
                if (pos == buf.Length) return Incomplete;
            }
            path = tokStart;
            pathLen = pos - tokStart;

            do
            {
                ++pos;
                if (pos == buf.Length) return Incomplete;
            } while (buf[pos] == ' ');
            if (methodLen == 0 || pathLen == 0)
            {
                return Error;
            }
            pos = ParseHttpVersion(buf, pos, out minorVersion);
            if (pos < 0)
            {
                return pos;
            }
            if (buf[pos] == '\r')
            {
                ++pos;
                if (pos == buf.Length) return Incomplete;
                if (buf[pos++] != '\n') return Error;
            }
            else if (buf[pos] == '\n')
            {
                ++pos;
            }
            else
            {
                return Error;
            }

            return ParseHeadersCore(buf, pos, headers, ref numHeaders, maxHeaders);
        }

        /// <summary>
        /// phr_parse_request: parses a request's line and headers. Returns the number of bytes consumed if successful,
        /// <see cref="Incomplete"/> if the request is partial, or <see cref="Error"/> if it failed. On entry
        /// <paramref name="numHeaders"/> is the capacity of <paramref name="headers"/>; on return, the number of
        /// headers parsed. <paramref name="lastLen"/> is the length of the buffer at the previous call (0 the first
        /// time).
        /// </summary>
        public static int ParseRequest(ReadOnlySpan<byte> buf, out int method, out int methodLen, out int path, out int pathLen,
                                       out int minorVersion, PhrHeader[] headers, ref int numHeaders, int lastLen)
        {
            int maxHeaders = numHeaders;
            method = path = -1;
            methodLen = pathLen = 0;
            minorVersion = -1;
            numHeaders = 0;

            // if last_len != 0, check if the request is complete (a fast countermeasure againt slowloris
            if (lastLen != 0)
            {
                int r = IsComplete(buf, lastLen);
                if (r < 0)
                {
                    return r;
                }
            }

            return ParseRequestCore(buf, out method, out methodLen, out path, out pathLen, out minorVersion, headers, ref numHeaders, maxHeaders);
        }

        private static int ParseResponseCore(ReadOnlySpan<byte> buf, out int minorVersion, out int status, out int msg, out int msgLen,
                                         PhrHeader[] headers, ref int numHeaders, int maxHeaders)
        {
            status = 0;
            msg = -1;
            msgLen = 0;

            // parse "HTTP/1.x"
            int pos = ParseHttpVersion(buf, 0, out minorVersion);
            if (pos < 0)
            {
                return pos;
            }
            // skip space
            if (buf[pos] != ' ')
            {
                return Error;
            }
            do
            {
                ++pos;
                if (pos == buf.Length) return Incomplete;
            } while (buf[pos] == ' ');
            // parse status code, we want at least [:digit:][:digit:][:digit:]<other char> to try to parse
            if (buf.Length - pos < 4)
            {
                return Incomplete;
            }
            // PARSE_INT_3(status)
            for (int mul = 100; mul >= 1; mul /= 10)
            {
                if (buf[pos] < '0' || '9' < buf[pos])
                {
                    return Error;
                }
                status += mul * (buf[pos++] - '0');
            }

            // get message including preceding space
            pos = GetTokenToEol(buf, pos, out msg, out msgLen);
            if (pos < 0)
            {
                return pos;
            }
            if (msgLen == 0)
            {
                // ok
            }
            else if (buf[msg] == ' ')
            {
                // Remove preceding space. Successful return from GetTokenToEol guarantees that we would hit something
                // other than SP before running past the end of the given buffer.
                do
                {
                    ++msg;
                    --msgLen;
                } while (buf[msg] == ' ');
            }
            else
            {
                // garbage found after status code
                return Error;
            }

            return ParseHeadersCore(buf, pos, headers, ref numHeaders, maxHeaders);
        }

        /// <summary>phr_parse_response: as <see cref="ParseRequest(ReadOnlySpan{byte}, out int, out int, out int, out int, out int, PhrHeader[], ref int, int)"/>,
        /// for a response's status line and headers.</summary>
        public static int ParseResponse(ReadOnlySpan<byte> buf, out int minorVersion, out int status, out int msg, out int msgLen,
                                        PhrHeader[] headers, ref int numHeaders, int lastLen)
        {
            int maxHeaders = numHeaders;
            minorVersion = -1;
            status = 0;
            msg = -1;
            msgLen = 0;
            numHeaders = 0;

            // if last_len != 0, check if the response is complete (a fast countermeasure against slowloris
            if (lastLen != 0)
            {
                int r = IsComplete(buf, lastLen);
                if (r < 0)
                {
                    return r;
                }
            }

            return ParseResponseCore(buf, out minorVersion, out status, out msg, out msgLen, headers, ref numHeaders, maxHeaders);
        }

        /// <summary>phr_parse_headers: header lines alone, up to the blank line.</summary>
        public static int ParseHeaders(ReadOnlySpan<byte> buf, PhrHeader[] headers, ref int numHeaders, int lastLen)
        {
            int maxHeaders = numHeaders;
            numHeaders = 0;

            // if last_len != 0, check if the response is complete (a fast countermeasure against slowloris
            if (lastLen != 0)
            {
                int r = IsComplete(buf, lastLen);
                if (r < 0)
                {
                    return r;
                }
            }

            return ParseHeadersCore(buf, 0, headers, ref numHeaders, maxHeaders);
        }

        private const int ChunkedInChunkSize = 0;
        private const int ChunkedInChunkExt = 1;
        private const int ChunkedInChunkData = 2;
        private const int ChunkedInChunkCrlf = 3;
        private const int ChunkedInTrailersLineHead = 4;
        private const int ChunkedInTrailersLineMiddle = 5;

        private static int DecodeHex(int ch)
        {
            if ('0' <= ch && ch <= '9')
            {
                return ch - '0';
            }
            else if ('A' <= ch && ch <= 'F')
            {
                return ch - 'A' + 0xa;
            }
            else if ('a' <= ch && ch <= 'f')
            {
                return ch - 'a' + 0xa;
            }
            else
            {
                return -1;
            }
        }

        /// <summary>
        /// phr_decode_chunked: decodes chunked data in place. On return <paramref name="bufSize"/> is the length of the
        /// decoded data at the start of <paramref name="buf"/>. Returns the number of undecoded bytes left after the
        /// chunked data if it is complete (they follow the decoded data), <see cref="Incomplete"/> if more is needed,
        /// or <see cref="Error"/>.
        /// </summary>
        public static long DecodeChunked(PhrChunkedDecoder decoder, Span<byte> buf, ref int bufSize)
        {
            int dst = 0, src = 0, bufsz = bufSize;
            long ret = Incomplete;  // incomplete
            bool complete = false;

            decoder.TotalRead += bufsz;

            while (!complete)
            {
                switch (decoder.State)
                {
                    case ChunkedInChunkSize:
                        for (; ; ++src)
                        {
                            int v;
                            if (src == bufsz)
                            {
                                goto Exit;
                            }
                            if ((v = DecodeHex(buf[src])) == -1)
                            {
                                if (decoder.HexCount == 0)
                                {
                                    ret = Error;
                                    goto Exit;
                                }
                                // the only characters that may appear after the chunk size are BWS, semicolon, or CRLF
                                switch (buf[src])
                                {
                                    case (byte)' ':
                                    case (byte)'\t':
                                    case (byte)';':
                                    case (byte)'\n':
                                    case (byte)'\r':
                                        break;
                                    default:
                                        ret = Error;
                                        goto Exit;
                                }
                                break;
                            }
                            if (decoder.HexCount == sizeof(long) * 2)
                            {
                                ret = Error;
                                goto Exit;
                            }
                            decoder.BytesLeftInChunk = decoder.BytesLeftInChunk * 16 + v;
                            ++decoder.HexCount;
                        }
                        decoder.HexCount = 0;
                        decoder.State = ChunkedInChunkExt;
                        goto case ChunkedInChunkExt;
                    case ChunkedInChunkExt:
                        // RFC 7230 A.2 "Line folding in chunk extensions is disallowed"
                        for (; ; ++src)
                        {
                            if (src == bufsz)
                            {
                                goto Exit;
                            }
                            if (buf[src] == '\n')
                            {
                                break;
                            }
                        }
                        ++src;
                        if (decoder.BytesLeftInChunk == 0)
                        {
                            if (decoder.ConsumeTrailer)
                            {
                                decoder.State = ChunkedInTrailersLineHead;
                                break;
                            }
                            else
                            {
                                complete = true;
                                break;
                            }
                        }
                        decoder.State = ChunkedInChunkData;
                        goto case ChunkedInChunkData;
                    case ChunkedInChunkData:
                        {
                            int avail = bufsz - src;
                            if (avail < decoder.BytesLeftInChunk)
                            {
                                if (dst != src)
                                {
                                    buf.Slice(src, avail).CopyTo(buf.Slice(dst));
                                }
                                src += avail;
                                dst += avail;
                                decoder.BytesLeftInChunk -= avail;
                                goto Exit;
                            }
                            int n = (int)decoder.BytesLeftInChunk;
                            if (dst != src)
                            {
                                buf.Slice(src, n).CopyTo(buf.Slice(dst));
                            }
                            src += n;
                            dst += n;
                            decoder.BytesLeftInChunk = 0;
                            decoder.State = ChunkedInChunkCrlf;
                        }
                        goto case ChunkedInChunkCrlf;
                    case ChunkedInChunkCrlf:
                        for (; ; ++src)
                        {
                            if (src == bufsz)
                            {
                                goto Exit;
                            }
                            if (buf[src] != '\r')
                            {
                                break;
                            }
                        }
                        if (buf[src] != '\n')
                        {
                            ret = Error;
                            goto Exit;
                        }
                        ++src;
                        decoder.State = ChunkedInChunkSize;
                        break;
                    case ChunkedInTrailersLineHead:
                        for (; ; ++src)
                        {
                            if (src == bufsz)
                            {
                                goto Exit;
                            }
                            if (buf[src] != '\r')
                            {
                                break;
                            }
                        }
                        if (buf[src++] == '\n')
                        {
                            complete = true;
                            break;
                        }
                        decoder.State = ChunkedInTrailersLineMiddle;
                        goto case ChunkedInTrailersLineMiddle;
                    case ChunkedInTrailersLineMiddle:
                        for (; ; ++src)
                        {
                            if (src == bufsz)
                            {
                                goto Exit;
                            }
                            if (buf[src] == '\n')
                            {
                                break;
                            }
                        }
                        ++src;
                        decoder.State = ChunkedInTrailersLineHead;
                        break;
                    default:
                        throw new InvalidOperationException("decoder is corrupt");
                }
            }

            // Complete:
            ret = bufsz - src;
        Exit:
            if (dst != src)
            {
                buf.Slice(src, bufsz - src).CopyTo(buf.Slice(dst));
            }
            bufSize = dst;
            // if incomplete but the overhead of the chunked encoding is >=100KB and >80%, return error
            if (ret == Incomplete)
            {
                decoder.TotalOverhead += bufsz - dst;
                if (decoder.TotalOverhead >= 100 * 1024 && decoder.TotalRead - decoder.TotalOverhead < decoder.TotalRead / 4)
                {
                    ret = Error;
                }
            }
            return ret;
        }

        /// <summary>phr_decode_chunked_is_in_data: whether the decoder is in the middle of chunked data.</summary>
        public static bool DecodeChunkedIsInData(PhrChunkedDecoder decoder) => decoder.State == ChunkedInChunkData;
    }
}
