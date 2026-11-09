using System;
using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using static CsVerify.Verifier.Boogie.KernelTypes;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>What a line of the Boogie program checks: the diagnostic it is, and where in the C# source.</summary>
    internal sealed class Check
    {
        public string Id;
        public string Message;
        public FileLinePositionSpan Span;
        public MethodResult Method;
        /// <summary>For a requires or an ensures (Id Aux): the diagnostic a failure of it is (CSV1001 or CSV1014; CSV1002 or CSV1014).</summary>
        public string ReportAs;
    }

    /// <summary>A construct outside the subset the Boogie translation covers: the method is verified the other way.</summary>
    internal sealed class NotTranslated : Exception
    {
        public NotTranslated(string why) : base(why) { }
    }

    /// <summary>
    /// C# to Boogie (docs/boogie.md), in passes over a kernel language (Kernel.cs): <see cref="Lowering"/> (Roslyn's
    /// control-flow graph to kernel blocks), <see cref="Checks"/> (C#'s meaning made mathematics, each obligation an
    /// assert), <see cref="Heap"/> (arrays as Dafny encodes them), <see cref="BoogiePrinter"/> (the text, and which line
    /// is which check). This class holds the program together: which methods are procedures and functions, their
    /// recursion groups, and what each modifies, closed over calls.
    /// </summary>
    internal sealed class BoogieTranslator : IProgramFacts
    {
        private readonly BoogiePrinter _printer = new BoogiePrinter();

        /// <summary>The check each line of the program is (1-based, as Boogie reports).</summary>
        public Dictionary<int, Check> Lines => _printer.Lines;

        /// <summary>How many obligations each procedure has.</summary>
        public readonly Dictionary<MethodResult, int> Obligations = new Dictionary<MethodResult, int>();

        /// <summary>A line that says what a failure is about (a requires, an ensures, a return), not a check of its own.</summary>
        internal const string Aux = "aux";

        private readonly HashSet<IMethodSymbol> _procedures = new HashSet<IMethodSymbol>(SymbolEqualityComparer.Default);
        private readonly bool _checkOverflow;

        /// <summary>The procedures translated, written when all are (their modifies need what each calls).</summary>
        private readonly List<KProcedure> _pending = new List<KProcedure>();

        public BoogieTranslator(bool checkOverflow) { _checkOverflow = checkOverflow; }

        public string Text => _printer.Text;

        // ------------------------------------------------------------------ the subset

        /// <summary>Could this method be a procedure (before its body is looked at)?</summary>
        public static bool Candidate(IMethodSymbol m, Contract c) =>
            m.IsStatic && !m.IsAsync && !m.IsGenericMethod && m.MethodKind == MethodKind.Ordinary &&
            (m.ReturnsVoid || InSubset(m.ReturnType)) && m.Parameters.All(p => p.RefKind == RefKind.None && InSubset(p.Type)) &&
            c.Modifies == null && c.Reads == null && c.ThrowEnsures.Count == 0 && !c.IsTrusted &&
            c.Ensures.All(e => e.Guard == null) && c.Bases.Count == 0;

        /// <summary>Why a method isn't a candidate (for CSVERIFY_TRACE).</summary>
        public static string WhyNot(IMethodSymbol m, Contract c) =>
            !m.IsStatic ? "an instance member" : m.IsAsync ? "async" : m.IsGenericMethod ? "generic" : m.MethodKind != MethodKind.Ordinary ? m.MethodKind.ToString() :
            !(m.ReturnsVoid || InSubset(m.ReturnType)) ? "returns " + m.ReturnType :
            m.Parameters.FirstOrDefault(p => p.RefKind != RefKind.None || !InSubset(p.Type)) is IParameterSymbol bad ? $"a parameter of {(bad.RefKind != RefKind.None ? bad.RefKind + " " : "")}{bad.Type}" :
            c.Modifies != null ? "Spec.Modifies" : c.Reads != null ? "Spec.Reads" : c.ThrowEnsures.Count > 0 ? "Spec.EnsuresOnThrow" :
            c.IsTrusted ? "[Trusted]" : "an inherited contract";

        /// <summary>Each method's contract (CsVerify's reading of its Spec statements).</summary>
        public Func<IMethodSymbol, Contract> ContractOf;

        /// <summary>What each procedure calls, directly or not (its recursion groups: each other's).</summary>
        private readonly Dictionary<IMethodSymbol, HashSet<IMethodSymbol>> _reaches = new Dictionary<IMethodSymbol, HashSet<IMethodSymbol>>(SymbolEqualityComparer.Default);

        /// <summary>The procedures in the program (each candidate whose body translates): calls of them are calls.</summary>
        public void Declare(IEnumerable<(IMethodSymbol method, SyntaxNode decl, SemanticModel model)> procedures)
        {
            var list = procedures.ToList();
            foreach (var p in list) _procedures.Add(p.method.OriginalDefinition);
            var calls = new Dictionary<IMethodSymbol, HashSet<IMethodSymbol>>(SymbolEqualityComparer.Default);
            foreach (var (m, decl, model) in list)
                calls[m.OriginalDefinition] = new HashSet<IMethodSymbol>(decl.DescendantNodes().OfType<InvocationExpressionSyntax>()
                    .Select(i => (model.GetSymbolInfo(i).Symbol as IMethodSymbol)?.OriginalDefinition).Where(x => x != null && _procedures.Contains(x)), SymbolEqualityComparer.Default);
            foreach (var m in calls.Keys)
            {
                var seen = new HashSet<IMethodSymbol>(SymbolEqualityComparer.Default);
                var work = new Stack<IMethodSymbol>(calls[m]);
                while (work.Count > 0)
                {
                    var x = work.Pop();
                    if (!seen.Add(x)) continue;
                    if (calls.TryGetValue(x, out var next)) foreach (var y in next) work.Push(y);
                }
                _reaches[m] = seen;
            }
        }

        public bool Recursive(IMethodSymbol a, IMethodSymbol b) =>
            _reaches.TryGetValue(b, out var fromB) && fromB.Contains(a) && _reaches.TryGetValue(a, out var fromA) && fromA.Contains(b);

        /// <summary>
        /// A [Pure] or [GhostFunction] method with a single expression for its body: a Boogie function too, which
        /// specifications call (as Dafny's functions, with fuel: one unfolding per use, as CsVerify's engine).
        /// </summary>
        private bool IsFunction(IMethodSymbol m) => _procedures.Contains(m.OriginalDefinition) && ContractOf?.Invoke(m) is Contract c && c.IsPure && c.PureBody != null;

        bool IProgramFacts.CheckOverflow => _checkOverflow;

        Contract IProgramFacts.ContractOf(IMethodSymbol m) => ContractOf(m);

        private readonly Dictionary<IMethodSymbol, KProcedure> _signatures = new Dictionary<IMethodSymbol, KProcedure>(SymbolEqualityComparer.Default);

        KProcedure IProgramFacts.Signature(IMethodSymbol m)
        {
            m = m.OriginalDefinition;
            if (!_signatures.TryGetValue(m, out var sig)) _signatures[m] = sig = Lowering.Signature(m, ContractOf(m), IsFunction);
            return sig;
        }

        // ------------------------------------------------------------------ the program

        /// <summary>What every program has: C#'s division, fuel, and the heap of arrays (Dafny's encoding).</summary>
        public void Prelude() => _printer.Prelude();

        /// <summary>The method as a procedure; throws <see cref="NotTranslated"/> for one outside the subset (then nothing is kept).</summary>
        public void Procedure(IMethodSymbol m, Contract contract, SyntaxNode decl, SemanticModel model, MethodResult result)
        {
            var p = Lowering.Lower(m, contract, decl, model, result, x => _procedures.Contains(x.OriginalDefinition), IsFunction);
            Checks.Run(p, this);
            Heap.Run(p);
            _pending.Add(p);
        }

        /// <summary>Writes the functions and the procedures: each modifies what it writes, and what what it calls does.</summary>
        public void Finish()
        {
            foreach (var p in _pending.Where(p => p.FunctionBody != null)) _printer.Function(p);
            var writes = _pending.ToDictionary(p => p.Method, p => new HashSet<string>(p.Modifies), SymbolEqualityComparer.Default);
            for (bool grew = true; grew;)
            {
                grew = false;
                foreach (var p in _pending)
                    foreach (var c in p.Calls)
                        if (writes.TryGetValue(c, out var w))
                            foreach (var g in w.ToList())
                                if (writes[p.Method].Add(g)) grew = true;
            }
            foreach (var p in _pending)
            {
                _printer.Procedure(p, writes[p.Method], p.FunctionBody != null);
                Obligations[p.Result] = p.Obligations;
            }
            _pending.Clear();
        }
    }
}
