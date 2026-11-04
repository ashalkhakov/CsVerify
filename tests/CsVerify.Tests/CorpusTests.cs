using System;
using System.Text;
using Corpus.Http;
using Corpus.Json;
using Xunit;

namespace CsVerify.Tests
{
    /// <summary>
    /// The corpus's ports behave as their C originals: cases after jsmn's and picohttpparser's own tests. (What the
    /// verifier makes of them is the library report's business, not these tests'.)
    /// </summary>
    public class CorpusTests
    {
        // ---------------------------------------------------------------------------------------------- jsmn

        private static (int r, JsmnToken[] t) Json(string js, int numTokens = 64)
        {
            var tokens = new JsmnToken[numTokens];
            return (Jsmn.Parse(new JsmnParser(), js, js.Length, tokens, numTokens), tokens);
        }

        private static void Token(string js, JsmnToken t, JsmnType type, string text, int size)
        {
            Assert.Equal(type, t.Type);
            Assert.Equal(text, js.Substring(t.Start, t.End - t.Start));
            Assert.Equal(size, t.Size);
        }

        [Fact]
        public void Jsmn_TokenizesObjectsArraysStringsAndPrimitives()
        {
            const string js = "{\"a\": [1, true, \"x\\u00e9\"], \"b\": {}}";
            var (r, t) = Json(js);
            Assert.Equal(8, r);
            Token(js, t[0], JsmnType.Object, js, 2);
            Token(js, t[1], JsmnType.String, "a", 1);
            Token(js, t[2], JsmnType.Array, "[1, true, \"x\\u00e9\"]", 3);
            Token(js, t[3], JsmnType.Primitive, "1", 0);
            Token(js, t[4], JsmnType.Primitive, "true", 0);
            Token(js, t[5], JsmnType.String, "x\\u00e9", 0);
            Token(js, t[6], JsmnType.String, "b", 1);
            Token(js, t[7], JsmnType.Object, "{}", 0);
        }

        [Fact]
        public void Jsmn_CountsWithoutTokens()
        {
            const string js = "[1, [2, 3], {\"k\": null}]";
            Assert.Equal(8, Jsmn.Parse(new JsmnParser(), js, js.Length, null, 0));
        }

        [Theory]
        [InlineData("]", JsmnError.Inval)]
        [InlineData("{\"a\": 1]", JsmnError.Inval)]
        [InlineData("\"\\q\"", JsmnError.Inval)]
        [InlineData("\"\\u12g4\"", JsmnError.Inval)]
        [InlineData("{\"a\"", JsmnError.Part)]
        [InlineData("[1, 2", JsmnError.Part)]
        [InlineData("\"abc", JsmnError.Part)]
        public void Jsmn_ReportsErrors(string js, int error) => Assert.Equal(error, Json(js).r);

        [Fact]
        public void Jsmn_RunsOutOfTokens_AndResumesWithMore()
        {
            const string js = "[1, 2, 3]";
            var parser = new JsmnParser();
            var tokens = new JsmnToken[4];
            Assert.Equal(JsmnError.NoMem, Jsmn.Parse(parser, js, js.Length, tokens, 2));
            Assert.Equal(4, Jsmn.Parse(parser, js, js.Length, tokens, 4));
            Token(js, tokens[3], JsmnType.Primitive, "3", 0);
        }

        // ------------------------------------------------------------------------------------ picohttpparser

        private static byte[] B(string s) => Encoding.Latin1.GetBytes(s);
        private static string S(byte[] buf, int start, int len) => start < 0 ? null : Encoding.Latin1.GetString(buf, start, len);

        private static int Request(string text, out string method, out string path, out int minor, out (string name, string value)[] hs, int lastLen = 0)
        {
            var buf = B(text);
            var headers = new PhrHeader[4];
            int n = headers.Length;
            int r = PicoHttpParser.ParseRequest(buf, out int m, out int ml, out int p, out int pl, out minor, headers, ref n, lastLen);
            method = S(buf, m, ml);
            path = S(buf, p, pl);
            hs = new (string, string)[Math.Max(n, 0)];
            for (int i = 0; i < hs.Length; i++)
                hs[i] = (S(buf, headers[i].NameStart, headers[i].NameLen), S(buf, headers[i].ValueStart, headers[i].ValueLen));
            return r;
        }

        [Fact]
        public void Pico_ParsesRequests()
        {
            Assert.Equal(18, Request("GET / HTTP/1.0\r\n\r\n", out var m, out var p, out int minor, out var hs));
            Assert.Equal(("GET", "/", 0), (m, p, minor));
            Assert.Empty(hs);

            const string req = "GET /hoge HTTP/1.1\r\nHost: example.com\r\nCookie: \r\n\r\n";
            Assert.Equal(req.Length, Request(req, out m, out p, out minor, out hs));
            Assert.Equal(("GET", "/hoge", 1), (m, p, minor));
            Assert.Equal(new[] { ("Host", "example.com"), ("Cookie", "") }, hs);

            const string multiline = "GET / HTTP/1.0\r\nfoo: \r\nfoo: b\r\n  \tc\r\n\r\n";
            Assert.Equal(multiline.Length, Request(multiline, out _, out _, out _, out hs));
            Assert.Equal(new[] { ("foo", ""), ("foo", "b"), (null, "  \tc") }, hs);

            Assert.Equal(16, Request("GET / HTTP/1.0\n\n", out _, out _, out _, out _));       // bare LFs
            Assert.Equal(20, Request("\r\nGET / HTTP/1.0\r\n\r\n", out m, out _, out _, out _));  // a leading empty line
            Assert.Equal("GET", m);
            const string trailing = "GET / HTTP/1.0\r\nx: a \t\r\n\r\n";            // trailing space trimmed
            Assert.Equal(trailing.Length, Request(trailing, out _, out _, out _, out hs));
            Assert.Equal(("x", "a"), hs[0]);
        }

        [Theory]
        [InlineData("GET / HTTP/1.0\r\n\r")]
        [InlineData("GET / HTTP/1.0\r\n")]
        [InlineData("GET / HTTP/1.0")]
        [InlineData("GET / ")]
        [InlineData("GET")]
        [InlineData("")]
        [InlineData("GET / HTTP/1.0\r\nHost: a")]
        public void Pico_PartialRequests_AreIncomplete(string text) => Assert.Equal(PicoHttpParser.Incomplete, Request(text, out _, out _, out _, out _));

        [Theory]
        [InlineData(" GET / HTTP/1.0\r\n\r\n")]          // empty method
        [InlineData("GET / HTTP/1.0\r\n:a\r\n\r\n")]      // empty header name
        [InlineData("GET / HTTP/1.0\r\nab: c\0d\r\n\r\n")] // NUL in a value
        [InlineData("GET /\x7fhello HTTP/1.0\r\n\r\n")]  // DEL in the path
        [InlineData("G\0T / HTTP/1.0\r\n\r\n")]           // not a token character
        [InlineData("GET / HTTP/2.0\r\n\r\n")]            // not HTTP/1.x
        [InlineData("GET / HTTP/1.x\r\n\r\n")]
        [InlineData("GET / HTTP/1.0\r\na: b\r\nc: d\r\ne: f\r\ng: h\r\ni: j\r\n\r\n")] // more headers than room
        public void Pico_BadRequests_AreErrors(string text) => Assert.Equal(PicoHttpParser.Error, Request(text, out _, out _, out _, out _));

        [Fact]
        public void Pico_LastLen_ChecksCompletenessFirst()
        {
            const string req = "GET / HTTP/1.0\r\nHost: a\r\n\r\n";
            Assert.Equal(PicoHttpParser.Incomplete, Request(req.Substring(0, req.Length - 1), out _, out _, out _, out _, lastLen: 10));
            Assert.Equal(req.Length, Request(req, out _, out _, out _, out _, lastLen: req.Length - 1));
        }

        private static int Response(string text, out int minor, out int status, out string msg, out int numHeaders)
        {
            var buf = B(text);
            var headers = new PhrHeader[4];
            numHeaders = headers.Length;
            int r = PicoHttpParser.ParseResponse(buf, out minor, out status, out int m, out int ml, headers, ref numHeaders, 0);
            msg = S(buf, m, ml);
            return r;
        }

        [Fact]
        public void Pico_ParsesResponses()
        {
            Assert.Equal(19, Response("HTTP/1.0 200 OK\r\n\r\n", out int minor, out int status, out var msg, out int n));
            Assert.Equal((0, 200, "OK", 0), (minor, status, msg, n));
            const string long_ = "HTTP/1.1 500 Internal Server Error\r\nA: b\r\n\r\n";
            Assert.Equal(long_.Length, Response(long_, out minor, out status, out msg, out n));
            Assert.Equal((1, 500, "Internal Server Error", 1), (minor, status, msg, n));
            Assert.Equal(16, Response("HTTP/1.1 200\r\n\r\n ", out _, out status, out msg, out _)); // what follows is left
            Assert.Equal((200, ""), (status, msg));
            Assert.Equal(PicoHttpParser.Incomplete, Response("HTTP/1.1 200 OK\r\n", out _, out _, out _, out _));
            Assert.Equal(PicoHttpParser.Error, Response("HTTP/1.1 2x0 OK\r\n\r\n", out _, out _, out _, out _));
            Assert.Equal(PicoHttpParser.Error, Response("HTTP/1.1 200X\r\n\r\n", out _, out _, out _, out _));
            Assert.Equal(PicoHttpParser.Error, Response("HTTP/1.1200 OK\r\n\r\n", out _, out _, out _, out _));
        }

        private static (long ret, string decoded) Chunked(string text, bool consumeTrailer, int step = 0)
        {
            var decoder = new PhrChunkedDecoder { ConsumeTrailer = consumeTrailer };
            var all = B(text);
            if (step == 0)
            {
                int size = all.Length;
                long r = PicoHttpParser.DecodeChunked(decoder, all, ref size);
                return (r, Encoding.Latin1.GetString(all, 0, size));
            }
            // fed a few bytes at a time, the way a reader would
            var output = new StringBuilder();
            long ret = PicoHttpParser.Incomplete;
            for (int i = 0; i < all.Length && ret == PicoHttpParser.Incomplete; i += step)
            {
                var piece = all.AsSpan(i, Math.Min(step, all.Length - i)).ToArray();
                int size = piece.Length;
                ret = PicoHttpParser.DecodeChunked(decoder, piece, ref size);
                output.Append(Encoding.Latin1.GetString(piece, 0, size));
            }
            return (ret, output.ToString());
        }

        [Theory]
        [InlineData(0)]
        [InlineData(1)]
        [InlineData(3)]
        public void Pico_DecodesChunked(int step)
        {
            Assert.Equal((0L, "hello world"), Chunked("b\r\nhello world\r\n0\r\n", false, step));
            Assert.Equal((0L, "hello world"), Chunked("6\r\nhello \r\n5\r\nworld\r\n0\r\n", false, step));
            Assert.Equal((0L, "hello world"), Chunked("6;ext=1\r\nhello \r\n5\r\nworld\r\n0\r\na: b\r\nc: d\r\n\r\n", true, step));
            Assert.Equal((PicoHttpParser.Incomplete, "hello"), Chunked("b\r\nhello", false, step));
        }

        [Fact]
        public void Pico_Chunked_LeavesWhatFollows_AndRejectsGarbage()
        {
            Assert.Equal((3L, "hello"), Chunked("5\r\nhello\r\n0\r\n\r\nabc", true));
            Assert.Equal(PicoHttpParser.Error, Chunked("z\r\nhello\r\n0\r\n", false).ret);
            Assert.Equal(PicoHttpParser.Error, Chunked("5x\r\nhello\r\n0\r\n", false).ret);
            Assert.Equal(PicoHttpParser.Error, Chunked("5\r\nhelloX\r\n0\r\n", false).ret);
            Assert.Equal(PicoHttpParser.Error, Chunked("11111111111111111\r\n", false).ret);
        }
    }
}
