using System.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Composite format strings: <c>string.Format</c>, <c>StringBuilder.AppendFormat</c>, and <c>Console</c>'s and
    /// <c>TextWriter</c>'s <c>Write</c>/<c>WriteLine</c> with a format throw FormatException when the format is not
    /// well-formed, or names an argument that is not there. With a constant format and arguments that can be counted
    /// (written out, or a params array written out), that is a precondition of the call (CSV1001). A format that is not
    /// a constant, or an array of arguments passed as one, is not checked.
    /// </summary>
    internal sealed partial class StaticChecks
    {

        /// <summary>Where and why a call with a constant composite format would throw FormatException (CSV1001); null if it wouldn't, or can't be told.</summary>
        internal static (SyntaxNode at, string message)? FormatProblem(IInvocationOperation inv)
        {
            var m = inv.TargetMethod;
            if (!IsFormatMethod(m)) return null;
            var format = inv.Arguments.FirstOrDefault(a => a.Parameter?.Name == "format");
            if (format == null || format.Parameter.Type.SpecialType != SpecialType.System_String ||
                !(format.Value.ConstantValue is { HasValue: true, Value: string text })) return null;
            int given = 0;
            foreach (var a in inv.Arguments.Where(a => a.Parameter != null && a.Parameter.Ordinal > format.Parameter.Ordinal))
            {
                if (a.ArgumentKind == ArgumentKind.ParamArray || a.ArgumentKind == ArgumentKind.ParamCollection)
                {
                    switch (a.Value)
                    {
                        case IArrayCreationOperation ac when ac.Initializer != null: given += ac.Initializer.ElementValues.Length; break;
                        case ICollectionExpressionOperation ce: given += ce.Elements.Length; break;
                        default: return null; // (an array or span of arguments: how many is not counted)
                    }
                }
                else if (a.Parameter.IsParams) return null; // (an array passed as the params array)
                else given++;
            }
            int needed = FormatStrings.Arity(text);
            var call = $"{m.ContainingType.Name}.{m.Name}";
            if (needed < 0)
                return (format.Value.Syntax, $"'{format.Value.Syntax}' is not a well-formed format string: {call} would throw FormatException");
            if (needed > given)
                return (inv.Syntax, $"the format string names {needed} argument(s), and {given} {(given == 1 ? "is" : "are")} given: {call} would throw FormatException");
            return null;
        }

        private static bool IsFormatMethod(IMethodSymbol m)
        {
            var type = m.ContainingType;
            if (type == null || type.DeclaringSyntaxReferences.Length > 0) return false;
            switch (type.ToDisplayString())
            {
                case "string": return m.Name == "Format";
                case "System.Text.StringBuilder": return m.Name == "AppendFormat";
                case "System.Console": return m.Name == "Write" || m.Name == "WriteLine";
            }
            for (var t = type; t != null; t = t.BaseType)
                if (t.ToDisplayString() == "System.IO.TextWriter") return m.Name == "Write" || m.Name == "WriteLine";
            return false;
        }
    }

    /// <summary>.NET's composite format strings.</summary>
    public static class FormatStrings
    {
        /// <summary>
        /// How many arguments a composite format string names (its highest index plus one), or -1 when it is not
        /// well-formed (.NET's grammar: <c>{index[,alignment][:formatString]}</c>, with <c>{{</c> and <c>}}</c> for braces).
        /// </summary>
        public static int Arity(string s)
        {
            int arity = 0, i = 0;
            while (i < s.Length)
            {
                char c = s[i++];
                if (c == '}')
                {
                    if (i < s.Length && s[i] == '}') { i++; continue; }
                    return -1;
                }
                if (c != '{') continue;
                if (i < s.Length && s[i] == '{') { i++; continue; }
                // an item: the index
                int start = i, index = 0;
                while (i < s.Length && char.IsDigit(s[i]) && s[i] <= '9') { index = index * 10 + (s[i] - '0'); i++; if (index >= 1000000) return -1; }
                if (i == start) return -1;
                while (i < s.Length && s[i] == ' ') i++;
                if (i < s.Length && s[i] == ',')
                {
                    i++;
                    while (i < s.Length && s[i] == ' ') i++;
                    if (i < s.Length && s[i] == '-') i++;
                    int digits = i;
                    while (i < s.Length && s[i] >= '0' && s[i] <= '9') i++;
                    if (i == digits) return -1;
                    while (i < s.Length && s[i] == ' ') i++;
                }
                if (i < s.Length && s[i] == ':')
                {
                    i++;
                    while (i < s.Length && s[i] != '}')
                    {
                        if (s[i] == '{') return -1;
                        i++;
                    }
                }
                if (i >= s.Length || s[i] != '}') return -1;
                i++;
                arity = System.Math.Max(arity, index + 1);
            }
            return arity;
        }
    }
}
