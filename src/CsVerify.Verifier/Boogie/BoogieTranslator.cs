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

        /// <summary>A procedure's own line: what Boogie reports there (a timeout, running out of resources) isn't a check's failure.</summary>
        internal const string Undecided = "undecided";

        private readonly HashSet<IMethodSymbol> _procedures = new HashSet<IMethodSymbol>(SymbolEqualityComparer.Default);
        private readonly bool _checkOverflow;

        /// <summary>The procedures translated, written when all are (their modifies need what each calls).</summary>
        private readonly List<KProcedure> _pending = new List<KProcedure>();

        public BoogieTranslator(bool checkOverflow) { _checkOverflow = checkOverflow; }

        public string Text => _printer.Text;

        // ------------------------------------------------------------------ the subset

        /// <summary>Could this method be a procedure (before its body is looked at)?</summary>
        public static bool Candidate(IMethodSymbol m, Contract c) =>
            (m.IsStatic ? m.MethodKind == MethodKind.Ordinary
                        : IsClass(m.ContainingType) && (m.MethodKind == MethodKind.Ordinary || m.MethodKind == MethodKind.Constructor) && !m.IsVirtual && !m.IsAbstract && !m.IsOverride) &&
            !m.IsAsync && !m.IsGenericMethod &&
            (m.ReturnsVoid || InSubset(m.ReturnType)) && m.Parameters.All(p => p.RefKind != RefKind.In && p.RefKind != RefKind.RefReadOnlyParameter && InSubset(p.Type)) &&
            c.Modifies == null && c.Reads == null && c.ThrowEnsures.Count == 0 && !c.IsTrusted &&
            c.Ensures.All(e => e.Guard == null) && c.Bases.Count == 0;

        /// <summary>Why a method isn't a candidate (for CSVERIFY_TRACE).</summary>
        public static string WhyNot(IMethodSymbol m, Contract c) =>
            !m.IsStatic && !IsClass(m.ContainingType) ? "a member of " + m.ContainingType.Name + ", a class outside the subset" :
            !m.IsStatic && (m.IsVirtual || m.IsAbstract || m.IsOverride) ? "virtual" :
            m.IsAsync ? "async" : m.IsGenericMethod ? "generic" : m.MethodKind != MethodKind.Ordinary && !(m.MethodKind == MethodKind.Constructor && !m.IsStatic) ? m.MethodKind.ToString() :
            !(m.ReturnsVoid || InSubset(m.ReturnType)) ? "returns " + m.ReturnType :
            m.Parameters.FirstOrDefault(p => p.RefKind == RefKind.In || p.RefKind == RefKind.RefReadOnlyParameter || !InSubset(p.Type)) is IParameterSymbol bad ? $"a parameter of {(bad.RefKind != RefKind.None ? bad.RefKind + " " : "")}{bad.Type}" :
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
            {
                calls[m.OriginalDefinition] = new HashSet<IMethodSymbol>(decl.DescendantNodes().Where(n => n is InvocationExpressionSyntax || n is BaseObjectCreationExpressionSyntax)
                    .Select(i => (model.GetSymbolInfo(i).Symbol as IMethodSymbol)?.OriginalDefinition).Where(x => x != null && _procedures.Contains(x)), SymbolEqualityComparer.Default);
                _fieldsRead[m.OriginalDefinition] = new HashSet<ISymbol>(decl.DescendantNodes().OfType<SimpleNameSyntax>()
                    .Select(n => model.GetSymbolInfo(n).Symbol).Where(IsField).Select(x => x.OriginalDefinition), SymbolEqualityComparer.Default);
            }
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
        private bool IsFunction(IMethodSymbol m) => _procedures.Contains(m.OriginalDefinition) && !SpecSymbols.IsPredicate(m.OriginalDefinition) &&
                                                     ContractOf?.Invoke(m) is Contract c && c.IsPure && c.PureBody != null;

        /// <summary>The fields each procedure's declaration names.</summary>
        private readonly Dictionary<IMethodSymbol, HashSet<ISymbol>> _fieldsRead = new Dictionary<IMethodSymbol, HashSet<ISymbol>>(SymbolEqualityComparer.Default);

        /// <summary>The fields a function may read: those it, or what it calls, names.</summary>
        private HashSet<ISymbol> FieldsOf(IMethodSymbol m)
        {
            m = m.OriginalDefinition;
            var all = new HashSet<ISymbol>(SymbolEqualityComparer.Default);
            foreach (var x in new[] { m }.Concat(_reaches.TryGetValue(m, out var r) ? r : Enumerable.Empty<IMethodSymbol>()))
                if (_fieldsRead.TryGetValue(x, out var f)) all.UnionWith(f);
            return all;
        }

        public List<string> FunctionFields(IMethodSymbol m) => FieldsOf(m).Select(FieldMap).Distinct().OrderBy(x => x, StringComparer.Ordinal).ToList();

        bool IProgramFacts.CheckOverflow => _checkOverflow;

        bool IProgramFacts.IsFunction(IMethodSymbol m) => IsFunction(m);

        /// <summary>Does the program use permissions at all (Spec.Acc, Spec.AccRead: CsVerify's engine checks array writes against cells then)?</summary>
        public bool UsesPermissions { get; set; }

        public bool UsesFieldPermissions { get; set; }

        private readonly Dictionary<IMethodSymbol, (IMethodSymbol pred, int[] arg)?> _over = new Dictionary<IMethodSymbol, (IMethodSymbol, int[])?>(SymbolEqualityComparer.Default);

        public (IMethodSymbol pred, int[] arg)? OverPredicate(IMethodSymbol f)
        {
            f = f.OriginalDefinition;
            if (_over.TryGetValue(f, out var known)) return known;
            (IMethodSymbol, int[])? over = null;
            try
            {
                // (static, its precondition holding one instance, whose arguments are its parameters, each once)
                if (f.IsStatic && IsFunction(f) && ContractOf(f).Requires.Any(Lowering.HasAtoms))
                {
                    var sig = ((IProgramFacts)this).Signature(f);
                    var atoms = sig.Requires.SelectMany(r => AtomsOf(r.Expr)).ToList();
                    if (atoms.Count == 1 && atoms[0] is KInst q && q.Args.All(a => a is KVar) && q.Args.Length == f.Parameters.Length)
                    {
                        var names = q.Args.Select(a => ((KVar)a).Name).ToList();
                        var map = f.Parameters.Select(x => names.IndexOf(Local(x))).ToArray();
                        if (map.All(j => j >= 0) && map.Distinct().Count() == map.Length) over = (q.Pred, map);
                    }
                    if (over == null) throw new NotTranslated("a function over a predicate, of other than one instance of its parameters");
                }
            }
            catch (NotTranslated) { _over[f] = null; throw; }
            return _over[f] = over;
        }

        private static IEnumerable<KExpr> AtomsOf(KExpr e) => e switch
        {
            KCells _ or KAcc _ or KInst _ or KFieldAcc _ => new[] { e },
            KOp op => op.Args.SelectMany(AtomsOf),
            _ => Enumerable.Empty<KExpr>(),
        };

        public IEnumerable<IMethodSymbol> FunctionsOver(IMethodSymbol pred)
        {
            foreach (var f in _procedures)
            {
                (IMethodSymbol pred, int[] arg)? over;
                try { over = OverPredicate(f); }
                catch (NotTranslated) { continue; }
                if (over is (IMethodSymbol p, _) && SymbolEqualityComparer.Default.Equals(p, pred.OriginalDefinition)) yield return f;
            }
        }

        private readonly Dictionary<ISymbol, int> _fieldIds = new Dictionary<ISymbol, int>(SymbolEqualityComparer.Default);

        public int FieldId(ISymbol field)
        {
            field = field.OriginalDefinition;
            if (!_fieldIds.TryGetValue(field, out var id)) _fieldIds[field] = id = _fieldIds.Count + 1;
            return id;
        }

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
            var fields = new HashSet<ISymbol>(_pending.SelectMany(p => p.Fields), SymbolEqualityComparer.Default);
            foreach (var p in _pending.Where(p => p.FunctionBody != null)) fields.UnionWith(FieldsOf(p.Method));
            // the predicates named, and those their bodies name
            var preds = new HashSet<IMethodSymbol>(_pending.SelectMany(p => p.Preds), SymbolEqualityComparer.Default);
            for (var work = new Stack<IMethodSymbol>(preds); work.Count > 0;)
            {
                var pred = work.Pop();
                // (a predicate whose body isn't translated: its procedure was refused, and so were those that name it)
                IEnumerable<IMethodSymbol> inner;
                try { inner = ((IProgramFacts)this).Signature(pred).Preds; }
                catch (NotTranslated) { inner = Enumerable.Empty<IMethodSymbol>(); }
                foreach (var q in inner)
                    if (preds.Add(q)) work.Push(q);
            }
            if (_pending.Any(p => p.UsesPerm)) _printer.Instances(preds);
            _printer.Fields(fields);
            _printer.OwnedMaps = fields.Where(IsOwnedField).Select(FieldMap).ToHashSet();
            OwnArrays();
            foreach (var p in _pending.Where(p => p.FunctionBody != null && !p.IsPredicate))
                if (OverPredicate(p.Method) != null) _printer.FunctionOverPredicate(p);
                else _printer.Function(p, FunctionFields(p.Method), fields);
            var writes = Closed(p => p.Modifies);
            var any = Closed(p => p.AnyWrites);
            // around each call that exchanges permissions: the [Owned] maps it may write, kept where the caller holds them
            foreach (var p in _pending)
                foreach (var frame in p.Blocks.SelectMany(b => b.Stmts).OfType<KCallFrame>().Where(f => !f.After))
                {
                    frame.Maps.AddRange((writes.TryGetValue(frame.Callee.OriginalDefinition, out var w) ? w : new HashSet<string>())
                        .Where(_printer.OwnedMaps.Contains).OrderBy(x => x, StringComparer.Ordinal));
                    p.Locals.Add(new KLocal { Name = $"s{frame.Id}$perm", Raw = "[Ref]bool" });
                    p.Locals.Add(new KLocal { Name = $"s{frame.Id}$pinst", Raw = "[Inst]int" });
                    p.Locals.Add(new KLocal { Name = $"s{frame.Id}$owner", Raw = "[Ref]Inst" });
                    p.Locals.Add(new KLocal { Name = $"s{frame.Id}$psnap", Raw = "[Inst]int" });
                    p.Locals.Add(new KLocal { Name = $"s{frame.Id}$Alloc", Raw = "[Ref]bool" });
                    foreach (var map in frame.Maps)
                        p.Locals.Add(new KLocal { Name = $"s{frame.Id}{map}", Raw = $"[Ref]{TypeOf(FieldType(fields.First(f => FieldMap(f) == map)))}" });
                    foreach (var map in frame.Maps) frame.FieldIds[map] = FieldId(fields.First(f => FieldMap(f) == map));
                    if (frame.Fields)
                    {
                        p.Locals.Add(new KLocal { Name = $"s{frame.Id}$fperm", Raw = "[Ref][int]bool" });
                        p.Locals.Add(new KLocal { Name = $"s{frame.Id}$fowner", Raw = "[Ref][int]Inst" });
                    }
                    if (frame.Cells)
                    {
                        frame.ElementMaps.AddRange((w ?? new HashSet<string>()).Where(x => x.StartsWith("$E.")).OrderBy(x => x, StringComparer.Ordinal));
                        p.Locals.Add(new KLocal { Name = $"s{frame.Id}$cells", Raw = "[Ref][int]real" });
                        p.Locals.Add(new KLocal { Name = $"s{frame.Id}$cowner", Raw = "[Ref][int]Inst" });
                        foreach (var map in frame.ElementMaps)
                            p.Locals.Add(new KLocal { Name = $"s{frame.Id}{map}", Raw = map == ElementMap(SpecialType.System_Boolean) ? "[Ref][int]bool" : "[Ref][int]int" });
                    }
                    // (and the globals its postconditions read as they were)
                    foreach (var g in frame.OldGlobals.Where(g => !p.Locals.Any(l => l.Name == $"s{frame.Id}{g}")).ToList())
                    {
                        var raw = g.StartsWith("$E.") ? (g == ElementMap(SpecialType.System_Boolean) ? "[Ref][int]bool" : "[Ref][int]int")
                                : fields.FirstOrDefault(f => FieldMap(f) == g) is ISymbol fs ? $"[Ref]{TypeOf(FieldType(fs))}" : null;
                        if (raw != null) p.Locals.Add(new KLocal { Name = $"s{frame.Id}{g}", Raw = raw });
                    }
                }
            // (a call, in array mode, that may write any array: reported only if it may)
            foreach (var a in _pending.SelectMany(p => p.Blocks).SelectMany(b => b.Stmts).OfType<KAssert>().Where(a => a.UnlessWritesArrays != null))
                if (!(writes.TryGetValue(a.UnlessWritesArrays.OriginalDefinition, out var cw) && cw.Any(x => x.StartsWith("$E.")))) a.Cond = new KLit("true");
            // each loop frame keeps the element maps, unless the loop calls what writes arrays
            foreach (var p in _pending)
                foreach (var frame in p.Blocks.SelectMany(b => b.Stmts).OfType<KLoopFrame>())
                {
                    if (frame.Callees.Any(c => writes.TryGetValue(c, out var w) && w.Any(x => x.StartsWith("$E.")))) continue;
                    frame.Maps = writes[p.Method].Where(x => x.StartsWith("$E.")).OrderBy(x => x, StringComparer.Ordinal).ToList();
                    if (frame.Maps.Count == 0) continue;
                    p.Locals.Add(new KLocal { Name = $"s${frame.Head}$Alloc", Raw = "[Ref]bool" });
                    foreach (var map in frame.Maps)
                        p.Locals.Add(new KLocal { Name = $"s${frame.Head}{map}", Raw = map == ElementMap(SpecialType.System_Boolean) ? "[Ref][int]bool" : "[Ref][int]int" });
                }
            foreach (var p in _pending)
            {
                _printer.Procedure(p, writes[p.Method], any[p.Method], p.FunctionBody != null && !p.IsPredicate && OverPredicate(p.Method) == null ? FunctionFields(p.Method) : null);
                Obligations[p.Result] = p.Obligations;
            }
            _pending.Clear();
        }

        /// <summary>
        /// Which functions read arrays only through their own array parameters (and call only such functions, on
        /// them): their value depends on those arrays' elements alone, as in CsVerify's engine, so a write of another
        /// array leaves it as it was. The others depend on the element maps whole.
        /// </summary>
        private void OwnArrays()
        {
            var functions = _pending.Where(p => p.FunctionBody != null && !p.IsPredicate && OverPredicate(p.Method) == null).ToDictionary(p => p.Method, p => p, (IEqualityComparer<IMethodSymbol>)SymbolEqualityComparer.Default);
            var own = functions.Keys.ToHashSet<IMethodSymbol>(SymbolEqualityComparer.Default);
            List<(int arg, string param, string map)> Of(IMethodSymbol m) =>
                m.Parameters.Where(x => IsArray(x.Type)).Select(x => (x.Ordinal + (m.IsStatic ? 0 : 1), Local(x), Elements(x.Type))).ToList();
            bool Reads(KExpr e, HashSet<string> mine) => e switch
            {
                KOp { Op: "sel" } s when s.Args.Length == 3 && s.Args[0] is KVar map && map.Name.StartsWith("$E.") =>
                    s.Args[1] is KVar a && mine.Contains(a.Name) && Reads(s.Args[2], mine),
                KOp op => op.Args.All(x => Reads(x, mine)),
                KQuant q => (q.Range == null || Reads(q.Range, mine)) && Reads(q.Body, mine),
                KFnApp f => own.Contains(f.Callee) && Of(f.Callee).All(o => f.Args[o.arg] is KVar a && mine.Contains(a.Name)) && f.Args.All(x => Reads(x, mine)),
                _ => true,
            };
            for (bool shrank = true; shrank;)
            {
                shrank = false;
                foreach (var p in functions.Values.Where(p => own.Contains(p.Method)).ToList())
                {
                    var mine = Of(p.Method).Select(o => o.param).ToHashSet();
                    if (!new[] { p.FunctionBody }.Concat(p.Requires.Select(r => r.Expr)).Concat(p.Ensures.Select(x => x.Expr)).All(x => Reads(x, mine)))
                    {
                        own.Remove(p.Method);
                        shrank = true;
                    }
                }
            }
            _printer.OwnArrays = m => own.Contains(m.OriginalDefinition) ? Of(m.OriginalDefinition) : null;
        }

        /// <summary>A set of globals of each procedure's, with those of everything it calls.</summary>
        private Dictionary<IMethodSymbol, HashSet<string>> Closed(Func<KProcedure, HashSet<string>> own)
        {
            var sets = _pending.ToDictionary(p => p.Method, p => new HashSet<string>(own(p)), (IEqualityComparer<IMethodSymbol>)SymbolEqualityComparer.Default);
            for (bool grew = true; grew;)
            {
                grew = false;
                foreach (var p in _pending)
                    foreach (var c in p.Calls)
                        if (sets.TryGetValue(c, out var w))
                            foreach (var g in w.ToList())
                                if (sets[p.Method].Add(g)) grew = true;
            }
            return sets;
        }
    }
}
