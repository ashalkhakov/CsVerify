// A C# port of jsmn (https://github.com/zserge/jsmn), a minimalistic JSON tokenizer, in its default
// configuration: not JSMN_STRICT, without JSMN_PARENT_LINKS. It is ported as it is, without specifications: part of
// the corpus CsVerify is measured on (see corpus/README.md). Pointers into the token array are indices; the parser is
// a class, as the C passes it by pointer.
//
// MIT License
//
// Copyright (c) 2010 Serge Zaitsev
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

namespace Corpus.Json
{
    /// <summary>jsmntype_t: the kind of a token.</summary>
    public enum JsmnType
    {
        Undefined = 0,
        Object = 1,
        Array = 2,
        String = 4,
        Primitive = 8,
    }

    /// <summary>enum jsmnerr: the negative results of <see cref="Jsmn.Parse"/>.</summary>
    public static class JsmnError
    {
        /// <summary>Not enough tokens were provided.</summary>
        public const int NoMem = -1;
        /// <summary>Invalid character inside the JSON string.</summary>
        public const int Inval = -2;
        /// <summary>The string is not a full JSON packet, more bytes expected.</summary>
        public const int Part = -3;
    }

    /// <summary>jsmntok_t: a token, as the start and end of its text in the input, and its number of children.</summary>
    public struct JsmnToken
    {
        public JsmnType Type;
        public int Start;
        public int End;
        public int Size;
    }

    /// <summary>jsmn_parser: the position in the input, the next free token, and the current parent token.</summary>
    public sealed class JsmnParser
    {
        public int Pos;
        public int TokNext;
        public int TokSuper;

        /// <summary>jsmn_init.</summary>
        public JsmnParser()
        {
            Pos = 0;
            TokNext = 0;
            TokSuper = -1;
        }
    }

    public static class Jsmn
    {
        /// <summary>Allocates a fresh unused token from the token pool; -1 if there is none.</summary>
        private static int AllocToken(JsmnParser parser, JsmnToken[] tokens, int numTokens)
        {
            if (parser.TokNext >= numTokens)
            {
                return -1;
            }
            int tok = parser.TokNext++;
            tokens[tok].Start = tokens[tok].End = -1;
            tokens[tok].Size = 0;
            return tok;
        }

        /// <summary>Fills token type and boundaries.</summary>
        private static void FillToken(ref JsmnToken token, JsmnType type, int start, int end)
        {
            token.Type = type;
            token.Start = start;
            token.End = end;
            token.Size = 0;
        }

        /// <summary>Fills next available token with JSON primitive.</summary>
        private static int ParsePrimitive(JsmnParser parser, string js, int len, JsmnToken[]? tokens, int numTokens)
        {
            int start = parser.Pos;
            bool found = false;
            for (; parser.Pos < len && js[parser.Pos] != '\0'; parser.Pos++)
            {
                switch (js[parser.Pos])
                {
                    // In strict mode primitive must be followed by "," or "}" or "]"
                    case ':':
                    case '\t':
                    case '\r':
                    case '\n':
                    case ' ':
                    case ',':
                    case ']':
                    case '}':
                        found = true;
                        break;
                }
                if (found)
                {
                    break;
                }
                if (js[parser.Pos] < 32 || js[parser.Pos] >= 127)
                {
                    parser.Pos = start;
                    return JsmnError.Inval;
                }
            }

            // found:
            if (tokens == null)
            {
                parser.Pos--;
                return 0;
            }
            int token = AllocToken(parser, tokens, numTokens);
            if (token == -1)
            {
                parser.Pos = start;
                return JsmnError.NoMem;
            }
            FillToken(ref tokens[token], JsmnType.Primitive, start, parser.Pos);
            parser.Pos--;
            return 0;
        }

        /// <summary>Fills next token with JSON string.</summary>
        private static int ParseString(JsmnParser parser, string js, int len, JsmnToken[]? tokens, int numTokens)
        {
            int start = parser.Pos;

            // Skip starting quote
            parser.Pos++;

            for (; parser.Pos < len && js[parser.Pos] != '\0'; parser.Pos++)
            {
                char c = js[parser.Pos];

                // Quote: end of string
                if (c == '"')
                {
                    if (tokens == null)
                    {
                        return 0;
                    }
                    int token = AllocToken(parser, tokens, numTokens);
                    if (token == -1)
                    {
                        parser.Pos = start;
                        return JsmnError.NoMem;
                    }
                    FillToken(ref tokens[token], JsmnType.String, start + 1, parser.Pos);
                    return 0;
                }

                // Backslash: Quoted symbol expected
                if (c == '\\' && parser.Pos + 1 < len)
                {
                    parser.Pos++;
                    switch (js[parser.Pos])
                    {
                        // Allowed escaped symbols
                        case '"':
                        case '/':
                        case '\\':
                        case 'b':
                        case 'f':
                        case 'r':
                        case 'n':
                        case 't':
                            break;
                        // Allows escaped symbol \uXXXX
                        case 'u':
                            parser.Pos++;
                            for (int i = 0; i < 4 && parser.Pos < len && js[parser.Pos] != '\0'; i++)
                            {
                                // If it isn't a hex character we have an error
                                char h = js[parser.Pos];
                                if (!((h >= 48 && h <= 57) ||   // 0-9
                                      (h >= 65 && h <= 70) ||   // A-F
                                      (h >= 97 && h <= 102)))   // a-f
                                {
                                    parser.Pos = start;
                                    return JsmnError.Inval;
                                }
                                parser.Pos++;
                            }
                            parser.Pos--;
                            break;
                        // Unexpected symbol
                        default:
                            parser.Pos = start;
                            return JsmnError.Inval;
                    }
                }
            }
            parser.Pos = start;
            return JsmnError.Part;
        }

        /// <summary>
        /// jsmn_parse: parses the first <paramref name="len"/> characters of <paramref name="js"/> into
        /// <paramref name="tokens"/>, and returns the number of tokens (a negative <see cref="JsmnError"/> on an
        /// error). With no token array, it only counts the tokens. It may be called again on the same parser with more
        /// input.
        /// </summary>
        public static int Parse(JsmnParser parser, string js, int len, JsmnToken[]? tokens, int numTokens)
        {
            int r;
            int i;
            int token;
            int count = parser.TokNext;

            for (; parser.Pos < len && js[parser.Pos] != '\0'; parser.Pos++)
            {
                char c = js[parser.Pos];
                JsmnType type;
                switch (c)
                {
                    case '{':
                    case '[':
                        count++;
                        if (tokens == null)
                        {
                            break;
                        }
                        token = AllocToken(parser, tokens, numTokens);
                        if (token == -1)
                        {
                            return JsmnError.NoMem;
                        }
                        if (parser.TokSuper != -1)
                        {
                            tokens[parser.TokSuper].Size++;
                        }
                        tokens[token].Type = c == '{' ? JsmnType.Object : JsmnType.Array;
                        tokens[token].Start = parser.Pos;
                        parser.TokSuper = parser.TokNext - 1;
                        break;
                    case '}':
                    case ']':
                        if (tokens == null)
                        {
                            break;
                        }
                        type = c == '}' ? JsmnType.Object : JsmnType.Array;
                        for (i = parser.TokNext - 1; i >= 0; i--)
                        {
                            if (tokens[i].Start != -1 && tokens[i].End == -1)
                            {
                                if (tokens[i].Type != type)
                                {
                                    return JsmnError.Inval;
                                }
                                parser.TokSuper = -1;
                                tokens[i].End = parser.Pos + 1;
                                break;
                            }
                        }
                        // Error if unmatched closing bracket
                        if (i == -1)
                        {
                            return JsmnError.Inval;
                        }
                        for (; i >= 0; i--)
                        {
                            if (tokens[i].Start != -1 && tokens[i].End == -1)
                            {
                                parser.TokSuper = i;
                                break;
                            }
                        }
                        break;
                    case '"':
                        r = ParseString(parser, js, len, tokens, numTokens);
                        if (r < 0)
                        {
                            return r;
                        }
                        count++;
                        if (parser.TokSuper != -1 && tokens != null)
                        {
                            tokens[parser.TokSuper].Size++;
                        }
                        break;
                    case '\t':
                    case '\r':
                    case '\n':
                    case ' ':
                        break;
                    case ':':
                        parser.TokSuper = parser.TokNext - 1;
                        break;
                    case ',':
                        if (tokens != null && parser.TokSuper != -1 &&
                            tokens[parser.TokSuper].Type != JsmnType.Array &&
                            tokens[parser.TokSuper].Type != JsmnType.Object)
                        {
                            for (i = parser.TokNext - 1; i >= 0; i--)
                            {
                                if (tokens[i].Type == JsmnType.Array || tokens[i].Type == JsmnType.Object)
                                {
                                    if (tokens[i].Start != -1 && tokens[i].End == -1)
                                    {
                                        parser.TokSuper = i;
                                        break;
                                    }
                                }
                            }
                        }
                        break;
                    default:
                        // In non-strict mode every unquoted value is a primitive
                        r = ParsePrimitive(parser, js, len, tokens, numTokens);
                        if (r < 0)
                        {
                            return r;
                        }
                        count++;
                        if (parser.TokSuper != -1 && tokens != null)
                        {
                            tokens[parser.TokSuper].Size++;
                        }
                        break;
                }
            }

            if (tokens != null)
            {
                for (i = parser.TokNext - 1; i >= 0; i--)
                {
                    // Unmatched opened object or array
                    if (tokens[i].Start != -1 && tokens[i].End == -1)
                    {
                        return JsmnError.Part;
                    }
                }
            }

            return count;
        }
    }
}
