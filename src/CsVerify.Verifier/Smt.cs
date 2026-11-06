using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Text;

namespace CsVerify.Verifier
{
    public enum Sort { Int, Bool, Heap, Row, Perm, PermHeap, F32, F64 }

    /// <summary>An SMT-LIB2 term with its sort.</summary>
    public sealed class Term
    {
        public readonly string S;
        public readonly Sort Sort;
        public Term(string s, Sort sort) { S = s; Sort = sort; }
        public override string ToString() => S;
    }

    /// <summary>Builders for SMT-LIB2 terms over integers, booleans and the array heap.</summary>
    public static class T
    {
        public static readonly Term True = new Term("true", Sort.Bool);
        public static readonly Term False = new Term("false", Sort.Bool);

        public static string SortName(Sort s) => s switch
        {
            Sort.Int => "Int",
            Sort.Bool => "Bool",
            Sort.Row => "(Array Int Int)",
            Sort.Perm => "(Array Int Real)",
            Sort.PermHeap => "(Array Int (Array Int Real))",
            Sort.F32 => "(_ FloatingPoint 8 24)",
            Sort.F64 => "(_ FloatingPoint 11 53)",
            _ => "(Array Int (Array Int Int))",
        };

        public static Term Int(long v) => new Term(v < 0 ? $"(- {-(System.Numerics.BigInteger)v})" : v.ToString(), Sort.Int);
        public static Term Int(System.Numerics.BigInteger v) => new Term(v < 0 ? $"(- {-v})" : v.ToString(), Sort.Int);
        public static Term Bool(bool b) => b ? True : False;

        private static Term App(string f, Sort sort, params Term[] args) =>
            new Term("(" + f + " " + string.Join(" ", args.Select(a => a.S)) + ")", sort);

        public static Term Add(Term a, Term b) => App("+", Sort.Int, a, b);
        public static Term Sub(Term a, Term b) => App("-", Sort.Int, a, b);
        public static Term Mul(Term a, Term b) => App("*", Sort.Int, a, b);
        public static Term Neg(Term a) => App("-", Sort.Int, a);
        public static Term Lt(Term a, Term b) => App("<", Sort.Bool, a, b);
        public static Term Le(Term a, Term b) => App("<=", Sort.Bool, a, b);
        public static Term Gt(Term a, Term b) => App(">", Sort.Bool, a, b);
        public static Term Ge(Term a, Term b) => App(">=", Sort.Bool, a, b);
        public static Term Eq(Term a, Term b) => App("=", Sort.Bool, a, Coerce(b, a.Sort));
        public static Term Not(Term a) => a == True ? False : a == False ? True : App("not", Sort.Bool, a);
        public static Term Implies(Term a, Term b) => App("=>", Sort.Bool, a, b);
        public static Term Xor(Term a, Term b) => App("xor", Sort.Bool, a, b);
        public static Term Ite(Term c, Term a, Term b) => App("ite", a.Sort, c, a, Coerce(b, a.Sort));

        public static Term And(params Term[] xs)
        {
            var ys = xs.Where(x => x != True).ToArray();
            return ys.Length == 0 ? True : ys.Length == 1 ? ys[0] : App("and", Sort.Bool, ys);
        }

        public static Term Or(params Term[] xs)
        {
            var ys = xs.Where(x => x != False).ToArray();
            return ys.Length == 0 ? False : ys.Length == 1 ? ys[0] : App("or", Sort.Bool, ys);
        }

        public static Term InRange(Term x, System.Numerics.BigInteger lo, System.Numerics.BigInteger hi) =>
            And(Le(Int(lo), x), Le(x, Int(hi)));

        /// <summary>
        /// C# integer division truncates toward zero; SMT-LIB <c>div</c> is Euclidean. Division, remainder and absolute
        /// value repeat their operands when written out, so of compound operands they are macros of the background
        /// theory (<see cref="IntTheory"/>), applied once: nested ones would otherwise grow exponentially (a term of a
        /// few divisions deep passed 2^31 characters). Of short operands they are written out.
        /// </summary>
        public static Term Div(Term a, Term b)
        {
            if (!(Atom(a) && Atom(b))) return App("cv_div", Sort.Int, a, b);
            var q = App("div", Sort.Int, Abs(a), Abs(b));
            return Ite(Eq(Ge(a, Int(0)), Ge(b, Int(0))), q, Neg(q));
        }

        public static Term Rem(Term a, Term b) => Atom(a) && Atom(b) ? Sub(a, Mul(b, Div(a, b))) : App("cv_rem", Sort.Int, a, b);
        public static Term Abs(Term a) => Atom(a) ? Ite(Ge(a, Int(0)), a, Neg(a)) : App("cv_abs", Sort.Int, a);

        // (an operand short enough to repeat: written out, as the solver searches best on those; a longer one, which
        // nesting would multiply, through the macro)
        private static bool Atom(Term t) => t.S.Length <= 400;

        /// <summary>The macros for <see cref="Div"/>, <see cref="Rem"/> and <see cref="Abs"/>: Z3 expands them itself.</summary>
        public const string IntTheory =
            "(define-fun cv_abs ((x Int)) Int (ite (>= x 0) x (- x)))\n" +
            "(define-fun cv_div ((x Int) (y Int)) Int (ite (= (>= x 0) (>= y 0)) (div (cv_abs x) (cv_abs y)) (- (div (cv_abs x) (cv_abs y)))))\n" +
            "(define-fun cv_rem ((x Int) (y Int)) Int (- x (* y (cv_div x y))))";

        /// <summary>
        /// Strings' characters: <c>cv_at</c> is a string's code unit at an index, and <c>cv_diff</c> an index at which two
        /// strings of a length differ, if they do (see MethodVerifier.Equal). Plain functions and quantified facts, not Z3's
        /// sequence theory: that one's answers swing between a second and a timeout on how a query was asserted, and it can
        /// run on for hours past the timeout.
        /// </summary>
        public const string StringDeclarations = "(declare-fun cv_at (Int Int) Int)\n(declare-fun cv_diff (Int Int) Int)";

        public static Term Select(Term array, Term index, Sort sort) => App("select", sort, array, index);
        public static Term Store(Term array, Term index, Term value) => App("store", array.Sort, array, index, value);
        public static Term ZeroRow() => ConstRow(Int(0));
        public static Term ConstRow(Term value) => new Term($"((as const (Array Int Int)) {value.S})", Sort.Row);

        /// <summary>Converts between Int and Bool where a generic contract met a concrete sort.</summary>
        public static Term Coerce(Term t, Sort to)
        {
            if (t.Sort == to) return t;
            if (to == Sort.Bool && t.Sort == Sort.Int) return Not(Eq(t, Int(0)));
            if (to == Sort.Int && t.Sort == Sort.Bool) return Ite(t, Int(1), Int(0));
            // a float in the heap (a field, an array cell) is stored through an injective encoding
            if (to == Sort.Int && (t.Sort == Sort.F32 || t.Sort == Sort.F64)) return new Term($"({(t.Sort == Sort.F32 ? "cv_enc32" : "cv_enc64")} {t.S})", Sort.Int);
            if ((to == Sort.F32 || to == Sort.F64) && t.Sort == Sort.Int) return new Term($"({(to == Sort.F32 ? "cv_dec32" : "cv_dec64")} {t.S})", to);
            throw new InvalidOperationException($"cannot coerce {t.Sort} to {to}");
        }

        public static Term Quant(string q, string var, Term body) =>
            new Term($"({q} (({var} Int)) {body.S})", Sort.Bool);

        public static string Quote(string name) => "|" + name.Replace("|", "_").Replace("\\", "_") + "|";
    }

    /// <summary>
    /// Talks SMT-LIB2 to a Z3 process. Z3 lives out of process so neither the analyzer nor the build loads native
    /// code; any Z3 4.8+ on PATH (or <c>CSVERIFY_Z3</c>) works on every OS and CPU.
    /// </summary>
    public sealed class SmtSolver : IDisposable
    {
        private Process _z3;
        private StreamWriter _in;
        private StreamReader _out;
        private readonly HashSet<string> _declared = new HashSet<string>();
        private readonly List<string> _preamble = new List<string>();
        private readonly int _timeoutMs;
        private int _fresh;
        private int _defined;
        public int Depth { get; private set; }
        public readonly List<string> Errors = new List<string>();
        /// <summary>Queries Z3 never answered: not a fault of the verifier's, and what they asked is simply not proved.</summary>
        public readonly List<string> Hangs = new List<string>();
        public StringBuilder Log; // set to capture the whole SMT-LIB2 conversation

        public SmtSolver(string z3Path, int timeoutMs)
        {
            _z3Path = z3Path;
            _timeoutMs = timeoutMs;
            HangMs = Math.Max(timeoutMs * 10, 60000);
            Launch();
            Start();
        }

        private void Launch()
        {
            var psi = new ProcessStartInfo(_z3Path, "-in -smt2")
            {
                RedirectStandardInput = true,
                RedirectStandardOutput = true,
                RedirectStandardError = true,
                UseShellExecute = false,
            };
            _z3 = Process.Start(psi) ?? throw new InvalidOperationException("could not start " + _z3Path);
            _in = _z3.StandardInput;
            _out = _z3.StandardOutput;
        }

        private readonly string _z3Path;
        /// <summary>Z3 stopped answering and was killed: until the next <see cref="Reset"/>, nothing is proved.</summary>
        private bool _hung;
        /// <summary>
        /// How long a query may go unanswered. Z3's own timeout is checked only where its search looks at the clock, and
        /// some theory code runs on without looking (seen in its sequence solver, for hours), so the wait must end here too.
        /// </summary>
        public int HangMs { get; set; }

        private void Start()
        {
            Send("(set-option :global-declarations true)");
            Send($"(set-option :timeout {_timeoutMs})");
            Send("(set-logic ALL)");
            // Quantifiers are instantiated by e-matching only. Model-based instantiation can search for a
            // counterexample until the timeout (notably with array lambdas); without it Z3 answers "unknown" at once,
            // which CsVerify reports exactly like "sat": the obligation is not proved.
            Send("(set-option :smt.mbqi false)");
        }

        /// <summary>Adds background declarations and axioms (at the outermost scope).</summary>
        public void Preamble(string smtLib)
        {
            foreach (var line in smtLib.Split('\n')) { _preamble.Add(line); Send(line); }
        }

        /// <summary>
        /// Starts over: no declarations or assertions, as in a fresh process. Each method is verified from this state,
        /// so a result never depends on which methods were verified before it (Z3's search is history-dependent).
        /// </summary>
        public void Reset()
        {
            if (_hung) { _hung = false; _z3.Dispose(); Launch(); }
            Send("(reset)");
            _kept.Clear();
            _recording = 0;
            _log.Clear();
            _macros = false;
            _stringsDeclared = false;
            _declared.Clear();
            _defines.Clear();
            Causes.Clear();
            Origins.Clear();
            _defined = 0;
            _fresh = 0; // the same names for the same method, whatever was verified before: Z3's search depends on them
            Depth = 0;
            Scope = ++_scopes;
            Start();
            foreach (var line in _preamble) Send(line);
        }

        public static string FindZ3(string explicitPath)
        {
            if (!string.IsNullOrEmpty(explicitPath)) return explicitPath;
            var env = Environment.GetEnvironmentVariable("CSVERIFY_Z3");
            if (!string.IsNullOrEmpty(env)) return env;
            var exe = OperatingSystem.IsWindows() ? "z3.exe" : "z3";
            var dirs = (Environment.GetEnvironmentVariable("PATH") ?? "").Split(Path.PathSeparator)
                .Concat(new[] { "/opt/homebrew/bin", "/usr/local/bin", "/usr/bin" });
            foreach (var d in dirs)
            {
                if (string.IsNullOrEmpty(d)) continue;
                var p = Path.Combine(d, exe);
                if (File.Exists(p)) return p;
            }
            throw new FileNotFoundException("Z3 not found: install it (brew install z3 / apt install z3 / winget install z3) or set CSVERIFY_Z3.");
        }

        private void Send(string cmd)
        {
            // (T.IntTheory's macros, defined where a command first uses them: declaring them always would change
            // Z3's search on queries that do not, which some proofs are sensitive to. Declarations are global, so
            // once until the next reset.)
            if (!_macros && cmd.Contains("cv_") && (cmd.Contains("cv_div") || cmd.Contains("cv_rem") || cmd.Contains("cv_abs")))
            {
                _macros = true;
                foreach (var line in T.IntTheory.Split('\n')) Write(line);
            }
            Write(cmd);
        }

        private bool _macros;
        private bool _stringsDeclared;

        /// <summary>
        /// Strings' characters, from the first use on, in a method that looks at them: like the macros, declaring them
        /// would change Z3's search on queries that do not.
        /// </summary>
        public void UseStrings()
        {
            if (!_stringsDeclared)
            {
                _stringsDeclared = true;
                foreach (var line in T.StringDeclarations.Split('\n')) Write(line);
            }
        }

        private void Write(string cmd)
        {
            Log?.AppendLine(cmd);
            if (!_hung) _in.WriteLine(cmd);
        }

        public Term Fresh(string hint, Sort sort)
        {
            var name = T.Quote(hint + "!" + (_fresh++));
            Send($"(declare-const {name} {T.SortName(sort)})");
            if (Cause != null) Causes[name] = Cause;
            if (Origin != null) Origins[name] = Origin;
            return new Term(name, sort);
        }

        /// <summary>
        /// Where the unknown values made now come from (a library call, a loop without invariants), for the library
        /// report: a fresh constant declared while it is set is charged to it. Null for none.
        /// </summary>
        public string Cause;
        /// <summary>The fresh constants made while <see cref="Cause"/> was set, and their causes.</summary>
        public readonly Dictionary<string, string> Causes = new Dictionary<string, string>(StringComparer.Ordinal);
        private readonly Dictionary<string, string> _defines = new Dictionary<string, string>(StringComparer.Ordinal);
        private static readonly System.Text.RegularExpressions.Regex Symbol = new System.Text.RegularExpressions.Regex(@"\|[^|]*\|");

        /// <summary>
        /// Where the values made now come from, in words with a line, for the reasons of a failed null check
        /// ("'Find' may return null (line 12)"). Null for none. Set like <see cref="Cause"/>, or after the fact.
        /// </summary>
        public string Origin;
        public readonly Dictionary<string, string> Origins = new Dictionary<string, string>(StringComparer.Ordinal);

        /// <summary>The causes of the fresh constants a term mentions, through the names <see cref="Define"/> gave.</summary>
        public SortedSet<string> CausesIn(Term t) => new SortedSet<string>(Lookup(t, Causes), StringComparer.Ordinal);

        /// <summary>The origins of the fresh constants a term mentions, in the order they were made.</summary>
        public List<string> OriginsIn(Term t) => Lookup(t, Origins).Distinct().ToList();

        private IEnumerable<string> Lookup(Term t, Dictionary<string, string> notes)
        {
            if (notes.Count == 0) yield break;
            var seen = new HashSet<string>(StringComparer.Ordinal);
            var todo = new Stack<string>();
            todo.Push(t.S);
            while (todo.Count > 0)
                foreach (System.Text.RegularExpressions.Match m in Symbol.Matches(todo.Pop()))
                {
                    if (!seen.Add(m.Value)) continue;
                    if (notes.TryGetValue(m.Value, out var note)) yield return note;
                    else if (_defines.TryGetValue(m.Value, out var body)) todo.Push(body);
                }
        }

        /// <summary>
        /// Names a long term (define-fun), so that a state built from it, which mentions it more than once, is written
        /// with the name: chains of updates (masks, ownership maps) stay linear in size instead of doubling.
        /// </summary>
        public Term Define(string hint, Term t)
        {
            if (t.S.Length < 4000) return t; // (only where it matters: a name changes Z3's search a little)
            // (a counter of its own: the fresh constants keep their names, and Z3's search, which depends on them)
            var name = T.Quote(hint + "#" + (_defined++));
            Send($"(define-fun {name} () {T.SortName(t.Sort)} {t.S})");
            if (Causes.Count > 0 || Origins.Count > 0) _defines[name] = t.S;
            return new Term(name, t.Sort);
        }

        public string FreshName(string hint) => T.Quote(hint + "!" + (_fresh++));

        public Term Apply(string function, Sort range, IReadOnlyList<Term> args)
        {
            var name = T.Quote(function + "/" + args.Count + ":" + string.Join(",", args.Select(a => a.Sort)) + "->" + range);
            if (_declared.Add(name))
                Send($"(declare-fun {name} ({string.Join(" ", args.Select(a => T.SortName(a.Sort)))}) {T.SortName(range)})");
            return args.Count == 0 ? new Term(name, range) : new Term("(" + name + " " + string.Join(" ", args.Select(a => a.S)) + ")", range);
        }

        public void Assume(Term t)
        {
            if (t == T.True) return;
            if (_recording > 0) _log[Depth].Add(t);
            Send($"(assert {t.S})");
        }

        // ---- a log of what is assumed, per scope, while some try collects its raises (state merging)
        private int _recording;
        private readonly List<List<Term>> _log = new List<List<Term>>();

        /// <summary>Starts logging assumptions, from this scope (just pushed) on.</summary>
        public void StartRecording()
        {
            while (_log.Count <= Depth) _log.Add(new List<Term>());
            if (_recording++ == 0) _log[Depth] = new List<Term>();
        }

        public void StopRecording() => _recording--;

        /// <summary>What has been assumed in the scopes from <paramref name="baseDepth"/> to the current one.</summary>
        public List<Term> Recorded(int baseDepth)
        {
            var all = new List<Term>();
            for (int d = baseDepth; d <= Depth && d < _log.Count; d++) all.AddRange(_log[d]);
            return all;
        }

        public void Push()
        {
            Depth++; Scope = ++_scopes; Send("(push 1)");
            while (_frames.Count <= Depth) _frames.Add(0);
            _frames[Depth] = Scope;
            if (_recording > 0)
            {
                while (_log.Count <= Depth) _log.Add(new List<Term>());
                _log[Depth] = new List<Term>();
            }
        }

        // the scope open at each depth (a fact asserted there lasts while that one is)
        private readonly List<long> _frames = new List<long> { 0 };
        private readonly Dictionary<string, (int depth, long frame)> _kept = new Dictionary<string, (int, long)>();

        /// <summary>A background fact, asserted once for its key: again only if the scope it was asserted in was left.</summary>
        public void AssumeOnce(string key, Func<Term> fact)
        {
            if (_kept.TryGetValue(key, out var at) && at.depth <= Depth && _frames[at.depth] == at.frame) return;
            Assume(fact());
            _kept[key] = (Depth, _frames[Depth]);
        }
        public void Pop() { Depth--; Scope = ++_scopes; Send("(pop 1)"); }

        /// <summary>Changes whenever an assertion scope is entered or left: a fact asserted under one Scope value is still there.</summary>
        public long Scope { get; private set; }
        private long _scopes;

        /// <summary>Is <paramref name="t"/> satisfiable together with everything assumed so far?</summary>
        public string Check(Term t)
        {
            Push();
            Assume(t);
            Send("(check-sat)");
            if (_hung) { Pop(); return "unknown"; }
            _in.Flush();
            string result;
            var clock = Stopwatch.StartNew();
            while (true)
            {
                var read = _out.ReadLineAsync();
                var left = HangMs - (int)clock.ElapsedMilliseconds;
                if (left <= 0 || !read.Wait(left))
                {
                    // (the rest of the method's obligations come back unknown: they are not proved, which is sound)
                    _hung = true;
                    try { _z3.Kill(); } catch (InvalidOperationException) { }
                    result = "unknown";
                    Hangs.Add($"z3 did not answer within {HangMs} ms and was stopped; the rest of this method is not verified");
                    break;
                }
                var line = read.Result;
                if (line == null) { result = "unknown"; Errors.Add("z3 exited"); break; }
                Log?.AppendLine("; " + line);
                line = line.Trim();
                if (line == "sat" || line == "unsat" || line == "unknown" || line == "timeout") { result = line; break; }
                if (line.Length > 0) Errors.Add(line);
            }
            Pop();
            return result;
        }

        public void Dispose()
        {
            try { if (!_hung) { _in.WriteLine("(exit)"); _in.Flush(); } if (!_z3.WaitForExit(2000)) _z3.Kill(); } catch { }
            _z3.Dispose();
        }
    }
}
