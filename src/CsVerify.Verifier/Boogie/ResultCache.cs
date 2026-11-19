using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Security.Cryptography;
using System.Text;
using Microsoft.Boogie;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>
    /// The methods proved before, each by a key of what its proof depends on (--cache): a method whose key is in the cache
    /// is proved, and not given to the solver again. The key is a hash of the method's procedures and of every declaration
    /// of the Boogie program they reach: the contracts of the procedures they call, the functions, constants and variables
    /// they name, the axioms that name any of those (and so on from those), the types; and of the options a proof depends
    /// on and the verifier's and the solver's builds. Only proved methods are kept: a failure is always found again.
    /// </summary>
    internal sealed class ResultCache
    {
        private readonly string _path;
        private readonly HashSet<string> _proved;

        private ResultCache(string path, HashSet<string> proved)
        {
            _path = path;
            _proved = proved;
        }

        /// <summary>The cache in this file; empty if there is none, or it can't be read.</summary>
        public static ResultCache Load(string path)
        {
            var proved = new HashSet<string>(StringComparer.Ordinal);
            try
            {
                if (File.Exists(path))
                {
                    proved.UnionWith(File.ReadAllLines(path).Where(l => l.Length > 0));
                }
            }
            catch (IOException)
            {
            }
            catch (UnauthorizedAccessException)
            {
            }
            return new ResultCache(path, proved);
        }

        public bool Proved(string key) => _proved.Contains(key);

        /// <summary>Keeps these keys: with the others too (a run of some methods, --only), or only these (a run of all).</summary>
        public void Save(IEnumerable<string> proved, bool keepOthers)
        {
            var all = keepOthers ? new HashSet<string>(_proved.Concat(proved), StringComparer.Ordinal) : new HashSet<string>(proved, StringComparer.Ordinal);
            try
            {
                var dir = Path.GetDirectoryName(Path.GetFullPath(_path));
                if (!string.IsNullOrEmpty(dir))
                {
                    Directory.CreateDirectory(dir);
                }
                // (written whole, then moved: a run stopped halfway leaves the old cache, not half of one)
                var temp = _path + ".tmp";
                File.WriteAllLines(temp, all.OrderBy(k => k, StringComparer.Ordinal));
                File.Move(temp, _path, overwrite: true);
            }
            catch (IOException)
            {
            }
            catch (UnauthorizedAccessException)
            {
            }
        }

        /// <summary>
        /// Each procedure's key, of those named that the program has: a hash of its own declaration and implementation, and
        /// of the declarations its proof reaches, with the salt (the options and builds).
        /// </summary>
        public static Dictionary<string, string> Keys(string text, IEnumerable<string> procedures, string salt)
        {
            var keys = new Dictionary<string, string>(StringComparer.Ordinal);
            if (Parser.Parse(text, "csverify.bpl", out Microsoft.Boogie.Program program, false) != 0 || program == null)
            {
                return keys;
            }
            var options = new CommandLineOptions(new StringWriter(), new ConsolePrinter());
            options.Parse(new string[0]);
            var resolution = new ResolutionContext(new Sink(), options);
            program.Resolve(resolution);
            if (resolution.ErrorCount > 0)
            {
                return keys;
            }
            var lines = text.Split('\n');
            // (each top-level declaration's text: its lines, to the next declaration's)
            var starts = program.TopLevelDeclarations.Select(d => d.tok.line).Where(l => l > 0).Distinct().OrderBy(l => l).ToList();
            string TextOf(Declaration d, bool contractOnly)
            {
                int k = starts.BinarySearch(d.tok.line);
                if (k < 0)
                {
                    return d.ToString();
                }
                int end = k + 1 < starts.Count ? starts[k + 1] - 1 : lines.Length;
                var segment = lines.Skip(d.tok.line - 1).Take(end - d.tok.line + 1);
                // (a procedure called: its contract, not its body, which its own proof is about)
                if (contractOnly)
                {
                    segment = segment.TakeWhile(l => l.TrimEnd() != "{");
                }
                return string.Join("\n", segment);
            }
            var axioms = program.TopLevelDeclarations.OfType<Axiom>().Select(a => (axiom: a, names: Names.Of(a.Expr))).ToList();
            var types = string.Join("\n", program.TopLevelDeclarations.Where(d => d is TypeCtorDecl || d is TypeSynonymDecl).Select(d => TextOf(d, false)).OrderBy(t => t, StringComparer.Ordinal));
            var byName = program.Implementations.GroupBy(i => i.Name).ToDictionary(g => g.Key, g => g.First(), StringComparer.Ordinal);
            foreach (var name in procedures.Distinct())
            {
                if (!byName.TryGetValue(name, out var impl))
                {
                    continue;
                }
                var seen = new HashSet<Declaration>();
                var texts = new List<string> { TextOf(impl.Proc, false) };
                var work = new Stack<Declaration>(Names.Of(impl).Concat(Names.Of(impl.Proc)));
                var usedAxioms = new HashSet<Axiom>();
                while (true)
                {
                    while (work.Count > 0)
                    {
                        var d = work.Pop();
                        if (d == impl.Proc || !seen.Add(d))
                        {
                            continue;
                        }
                        texts.Add(TextOf(d, d is Procedure));
                        foreach (var n in d is Procedure p ? Names.Of(p) : d is Function f ? Names.Of(f) : Enumerable.Empty<Declaration>())
                        {
                            work.Push(n);
                        }
                    }
                    // (the axioms that name what's reached: they are what the solver knows of it)
                    foreach (var (axiom, names) in axioms.Where(a => !usedAxioms.Contains(a.axiom) && a.names.Any(n => seen.Contains(n))).ToList())
                    {
                        usedAxioms.Add(axiom);
                        texts.Add(TextOf(axiom, false));
                        foreach (var n in names)
                        {
                            work.Push(n);
                        }
                    }
                    if (work.Count == 0)
                    {
                        break;
                    }
                }
                texts.Sort(StringComparer.Ordinal);
                keys[name] = Hash(salt + "\n" + types + "\n" + string.Join("\n", texts));
            }
            return keys;
        }

        public static string Hash(string s) => Convert.ToHexString(SHA256.HashData(Encoding.UTF8.GetBytes(s)));

        private sealed class Sink : IErrorSink
        {
            public void Error(IToken tok, string msg)
            {
            }
        }

        /// <summary>The global declarations an expression, a contract or a body names: functions, constants, variables, procedures.</summary>
        private sealed class Names : ReadOnlyVisitor
        {
            private readonly HashSet<Declaration> _found = new HashSet<Declaration>();

            public static HashSet<Declaration> Of(Absy node)
            {
                var v = new Names();
                switch (node)
                {
                    case Procedure p:
                        // (its contract: what its callers assume)
                        foreach (var r in p.Requires)
                        {
                            v.Visit(r.Condition);
                        }
                        foreach (var e in p.Ensures)
                        {
                            v.Visit(e.Condition);
                        }
                        foreach (var m in p.Modifies)
                        {
                            v.Visit(m);
                        }
                        break;
                    case Function f:
                        if (f.Body != null)
                        {
                            v.Visit(f.Body);
                        }
                        break;
                    default:
                        v.Visit(node);
                        break;
                }
                return v._found;
            }

            public override Expr VisitIdentifierExpr(IdentifierExpr node)
            {
                if (node.Decl is GlobalVariable || node.Decl is Constant)
                {
                    _found.Add(node.Decl);
                }
                return base.VisitIdentifierExpr(node);
            }

            public override Expr VisitNAryExpr(NAryExpr node)
            {
                if (node.Fun is FunctionCall fc && fc.Func != null)
                {
                    _found.Add(fc.Func);
                }
                return base.VisitNAryExpr(node);
            }

            public override Cmd VisitCallCmd(CallCmd node)
            {
                if (node.Proc != null)
                {
                    _found.Add(node.Proc);
                }
                return base.VisitCallCmd(node);
            }
        }
    }
}
