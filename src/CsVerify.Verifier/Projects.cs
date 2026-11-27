using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Runtime.CompilerServices;
using Microsoft.CodeAnalysis;

namespace CsVerify.Verifier
{
    /// <summary>
    /// A referenced project, as its build describes it (the file its CsVerifyGetProject target writes, in csverify's
    /// arguments): what its compilation is made of. The program's compilation references it as a compilation
    /// (Roslyn's CompilationReference, as the IDE's workspace does), so its types and members are source symbols.
    /// </summary>
    public sealed class ProjectReference
    {
        public string AssemblyName;
        public NullableContextOptions Nullable = NullableContextOptions.Disable;
        public readonly List<string> Sources = new List<string>();
        public readonly List<string> References = new List<string>();
        public readonly List<string> Analyzers = new List<string>();
        public readonly List<string> AnalyzerConfigs = new List<string>();
        /// <summary>The native libraries its packages bring (what a provider loads to build EF's model).</summary>
        public readonly List<string> NativeLibraries = new List<string>();

        public static ProjectReference Read(string path)
        {
            var p = new ProjectReference();
            var args = ResponseFile.Expand(new[] { "@" + path }).ToList();
            for (int i = 0; i < args.Count; i++)
            {
                switch (args[i])
                {
                    case "--assembly-name": p.AssemblyName = args[++i]; break;
                    case "--nullable": p.Nullable = ParseNullable(args[++i]); break;
                    case "-r": p.References.Add(args[++i]); break;
                    case "--native": p.NativeLibraries.Add(args[++i]); break;
                    case "-a": p.Analyzers.Add(args[++i]); break;
                    case "--analyzer-config": p.AnalyzerConfigs.Add(args[++i]); break;
                    default:
                        if (args[i].StartsWith("-"))
                        {
                            throw new ArgumentException($"{path}: unknown option {args[i]}");
                        }
                        p.Sources.Add(args[i]);
                        break;
                }
            }
            if (p.AssemblyName == null)
            {
                throw new ArgumentException(path + ": no --assembly-name");
            }
            return p;
        }

        /// <summary>A project's &lt;Nullable&gt;: enable, disable, warnings, annotations (unset is disable).</summary>
        public static NullableContextOptions ParseNullable(string context) =>
            context.Length == 0 ? NullableContextOptions.Disable : (NullableContextOptions)Enum.Parse(typeof(NullableContextOptions), context, ignoreCase: true);
    }

    /// <summary>Response files (@file.rsp): one argument per line; a line "-r path" is an option and its value.</summary>
    public static class ResponseFile
    {
        public static IEnumerable<string> Expand(IEnumerable<string> args)
        {
            foreach (var a in args)
            {
                if (!a.StartsWith("@"))
                {
                    yield return a;
                    continue;
                }
                foreach (var line in File.ReadAllLines(a.Substring(1)).Select(l => l.Trim()).Where(l => l.Length > 0))
                {
                    int space = line.IndexOf(' ');
                    if (line.StartsWith("-") && space > 0)
                    {
                        yield return line.Substring(0, space);
                        yield return line.Substring(space + 1).Trim();
                    }
                    else
                    {
                        yield return line;
                    }
                }
            }
        }
    }
}
