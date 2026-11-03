using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Text;

namespace CsVerify.Verifier
{
    public enum Sort { Int, Bool, Heap, Row }

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

        /// <summary>C# integer division truncates toward zero; SMT-LIB <c>div</c> is Euclidean.</summary>
        public static Term Div(Term a, Term b)
        {
            var q = App("div", Sort.Int, Abs(a), Abs(b));
            return Ite(Eq(Ge(a, Int(0)), Ge(b, Int(0))), q, Neg(q));
        }

        public static Term Rem(Term a, Term b) => Sub(a, Mul(b, Div(a, b)));
        public static Term Abs(Term a) => Ite(Ge(a, Int(0)), a, Neg(a));

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
        private readonly Process _z3;
        private readonly StreamWriter _in;
        private readonly StreamReader _out;
        private readonly HashSet<string> _declared = new HashSet<string>();
        private readonly List<string> _preamble = new List<string>();
        private readonly int _timeoutMs;
        private int _fresh;
        public int Depth { get; private set; }
        public readonly List<string> Errors = new List<string>();
        public StringBuilder Log; // set to capture the whole SMT-LIB2 conversation

        public SmtSolver(string z3Path, int timeoutMs)
        {
            var psi = new ProcessStartInfo(z3Path, "-in -smt2")
            {
                RedirectStandardInput = true,
                RedirectStandardOutput = true,
                RedirectStandardError = true,
                UseShellExecute = false,
            };
            _z3 = Process.Start(psi) ?? throw new InvalidOperationException("could not start " + z3Path);
            _in = _z3.StandardInput;
            _out = _z3.StandardOutput;
            _timeoutMs = timeoutMs;
            Start();
        }

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
            Send("(reset)");
            _declared.Clear();
            Depth = 0;
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
            Log?.AppendLine(cmd);
            _in.WriteLine(cmd);
        }

        public Term Fresh(string hint, Sort sort)
        {
            var name = T.Quote(hint + "!" + (_fresh++));
            Send($"(declare-const {name} {T.SortName(sort)})");
            return new Term(name, sort);
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
            Send($"(assert {t.S})");
        }

        public void Push() { Depth++; Send("(push 1)"); }
        public void Pop() { Depth--; Send("(pop 1)"); }

        /// <summary>Is <paramref name="t"/> satisfiable together with everything assumed so far?</summary>
        public string Check(Term t)
        {
            Push();
            Assume(t);
            Send("(check-sat)");
            _in.Flush();
            string result;
            while (true)
            {
                var line = _out.ReadLine();
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
            try { _in.WriteLine("(exit)"); _in.Flush(); if (!_z3.WaitForExit(2000)) _z3.Kill(); } catch { }
            _z3.Dispose();
        }
    }
}
