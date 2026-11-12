using System;
using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.FlowAnalysis;
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
        /// <summary>What the unknown values its conditions read come from (the library report's causes).</summary>
        public readonly HashSet<string> Causes = new HashSet<string>();
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

        /// <summary>The lines of loop facts left out (see BoogieRunner).</summary>
        public HashSet<int> Disabled => _printer.Disabled;

        /// <summary>How many obligations each procedure has.</summary>
        public readonly Dictionary<MethodResult, int> Obligations = new Dictionary<MethodResult, int>();

        /// <summary>The warnings of a method's procedure (none if it isn't one).</summary>
        public IEnumerable<VerificationDiagnostic> Warnings(MethodResult r) => _warnings.TryGetValue(r, out var w) ? w : Enumerable.Empty<VerificationDiagnostic>();

        private readonly Dictionary<MethodResult, List<VerificationDiagnostic>> _warnings = new Dictionary<MethodResult, List<VerificationDiagnostic>>();

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
        public static bool Candidate(IMethodSymbol m, Contract c) => EmptyDataConstructor(m) ||
            (m.MethodKind == MethodKind.DelegateInvoke ? c.OfDelegate && IsDelegate(m.ContainingType) :
             // (a lambda or a local function: a unit of its own, in a class's member or a static one)
             IsNested(m) ? StaticContext(m) || IsClass(m.ContainingType) :
             m.IsStatic ? m.MethodKind is MethodKind.Ordinary or MethodKind.StaticConstructor or MethodKind.PropertyGet or MethodKind.PropertySet
                        : (IsClass(m.ContainingType) || IsInterface(m.ContainingType) && m.IsAbstract ||
                           IsData(m.ContainingType) && m.MethodKind == MethodKind.Ordinary && !m.IsVirtual && !m.IsAbstract && !m.IsOverride) &&
                          (m.MethodKind is MethodKind.Ordinary or MethodKind.PropertyGet or MethodKind.PropertySet || m.MethodKind == MethodKind.Constructor && IsClass(m.ContainingType)) ||
                          m.MethodKind == MethodKind.Constructor && IsStruct(m.ContainingType) ||
                          // (a struct's member that reads it: this, a value; one that writes it is CsVerify's engine's to refuse)
                          IsStruct(m.ContainingType) && m.MethodKind is MethodKind.Ordinary or MethodKind.PropertyGet && !m.IsVirtual && !m.IsOverride) &&
            (!m.IsAsync || IsTaskLike(m.ReturnType) && !c.IsPure && !c.IsLemma) && (!m.IsGenericMethod || !m.IsVirtual && !m.IsAbstract && !m.IsOverride && m.TypeParameters.All(IsGenericParameter)) && KnownAttributes(m) &&
            (Returns(m) == null || InSubset(Returns(m))) && m.Parameters.All(p => (p.RefKind != RefKind.In || HoldsShare(p) || IsMemView(p.Type) || InValue(p)) && p.RefKind != RefKind.RefReadOnlyParameter && InSubset(p.Type) && (!IsShare(p.Type) || HoldsShare(p))) &&
            (c.Reads == null || c.IsPure || m.MethodKind == MethodKind.PropertyGet || IsNested(m)) && !c.IsTrusted &&
            // (a base of the library's, IDisposable.Dispose say, with no contract: nothing inherited)
            c.Bases.All(b => b.Method.DeclaringSyntaxReferences.Length > 0 || b.Requires.Count == 0 && b.Ensures.Count == 0 && b.ThrowEnsures.Count == 0 && b.Modifies == null);

        /// <summary>A data type's constructor that does nothing (a closed base's private Avl() { }): nothing to verify.</summary>
        public static bool EmptyDataConstructor(IMethodSymbol m) =>
            m.MethodKind == MethodKind.Constructor && !m.IsStatic && IsData(m.ContainingType) && m.Parameters.Length == 0 &&
            m.DeclaringSyntaxReferences.Length == 1 && m.DeclaringSyntaxReferences[0].GetSyntax() is Microsoft.CodeAnalysis.CSharp.Syntax.ConstructorDeclarationSyntax
                { Initializer: null, ExpressionBody: null, Body: { Statements.Count: 0 } };

        /// <summary>CsVerify's attributes that the translation knows; any other (an atomic step, a lock's) is CsVerify's engine's to check.</summary>
        private static readonly HashSet<string> Known = new HashSet<string>
        {
            "PureAttribute", "GhostFunctionAttribute", "LemmaAttribute", "PredicateAttribute", "InvariantAttribute", "GuardedByAttribute", "LockInvariantAttribute",
            "RunsConcurrentlyAttribute", "TakesNoLocksAttribute",
        };

        private static bool KnownAttributes(IMethodSymbol m) =>
            m.GetAttributes().All(a => a.AttributeClass?.ContainingNamespace?.ToDisplayString() != SpecSymbols.Namespace || Known.Contains(a.AttributeClass.Name)) &&
            // (nor one another member's attribute names: an atomic field's step, a lock's invariant)
            !m.ContainingType.GetMembers().SelectMany(x => x.GetAttributes())
                .Where(a => a.AttributeClass?.ContainingNamespace?.ToDisplayString() == SpecSymbols.Namespace && a.AttributeClass.Name != "AtomicAttribute")
                .Any(a => a.ConstructorArguments.Concat(a.NamedArguments.Select(n => n.Value)).Any(v => v.Value is string name && name == m.Name));

        /// <summary>Why a method isn't a candidate (for CSVERIFY_TRACE).</summary>
        public static string WhyNot(IMethodSymbol m, Contract c) =>
            !StaticContext(m) && !IsClass(m.ContainingType) && !IsInterface(m.ContainingType) && !EmptyDataConstructor(m) ? "a member of " + m.ContainingType.Name + ", a type outside the subset" :
            m.IsAsync && !IsTaskLike(m.ReturnType) ? "async void" : m.IsGenericMethod && !(!m.IsVirtual && !m.IsAbstract && !m.IsOverride && m.TypeParameters.All(IsGenericParameter)) ? "generic" : !KnownAttributes(m) ? "an attribute of CsVerify's the translation doesn't know" : m.MethodKind != MethodKind.Ordinary && !IsNested(m) && !(m.MethodKind == MethodKind.Constructor && !m.IsStatic) && m.MethodKind != MethodKind.StaticConstructor && !(m.MethodKind is MethodKind.PropertyGet or MethodKind.PropertySet) ? m.MethodKind.ToString() :
            !(Returns(m) == null || InSubset(Returns(m))) ? "returns " + m.ReturnType :
            m.Parameters.FirstOrDefault(p => p.RefKind == RefKind.In && !HoldsShare(p) && !IsMemView(p.Type) && !InValue(p) || p.RefKind == RefKind.RefReadOnlyParameter || !InSubset(p.Type) || IsShare(p.Type) && !HoldsShare(p)) is IParameterSymbol bad ? $"a parameter of {(bad.RefKind != RefKind.None ? bad.RefKind + " " : "")}{bad.Type}" :
            c.Reads != null ? "Spec.Reads of what isn't [Pure]" : c.ThrowEnsures.Count > 0 ? "Spec.EnsuresOnThrow" :
            c.IsTrusted ? "[Trusted]" : "an inherited contract";

        /// <summary>Each method's contract (CsVerify's reading of its Spec statements).</summary>
        public Func<IMethodSymbol, Contract> ContractOf;

        /// <summary>What each procedure calls, directly or not (its recursion groups: each other's).</summary>
        private readonly Dictionary<IMethodSymbol, HashSet<IMethodSymbol>> _reaches = new Dictionary<IMethodSymbol, HashSet<IMethodSymbol>>(SymbolEqualityComparer.Default);

        /// <summary>The procedures in the program (each candidate whose body translates): calls of them are calls.</summary>
        public void Declare(IEnumerable<(IMethodSymbol method, SyntaxNode decl, SemanticModel model)> procedures)
        {
            var list = procedures.ToList();
            // (a lambda: nothing calls it as a procedure; a local function's calls do)
            foreach (var p in list.Where(x => x.method.MethodKind != MethodKind.AnonymousFunction)) _procedures.Add(p.method.OriginalDefinition);
            var calls = new Dictionary<IMethodSymbol, HashSet<IMethodSymbol>>(SymbolEqualityComparer.Default);
            foreach (var (m, decl, model) in list)
            {
                calls[m.OriginalDefinition] = new HashSet<IMethodSymbol>(decl.DescendantNodes().Where(n => n is InvocationExpressionSyntax || n is BaseObjectCreationExpressionSyntax)
                    .Select(i => (model.GetSymbolInfo(i).Symbol as IMethodSymbol)?.OriginalDefinition)
                    // (and the getters of the properties it reads)
                    .Concat(decl.DescendantNodes().OfType<SimpleNameSyntax>().Select(n => (model.GetSymbolInfo(n).Symbol as IPropertySymbol)?.GetMethod?.OriginalDefinition))
                    .Where(x => x != null && _procedures.Contains(x)), SymbolEqualityComparer.Default);
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
        /// <summary>
        /// (an abstract [Pure] member too, of its contract alone; and a virtual one, which an override may answer: of its
        /// contract alone; and one whose body is more than an expression, of its contract alone, as CsVerify's engine has
        /// it: its procedure proves the contract, and gives the function's value)
        /// </summary>
        private bool IsFunction(IMethodSymbol m) => _procedures.Contains(m.OriginalDefinition) && !SpecSymbols.IsPredicate(m.OriginalDefinition) &&
                                                     ContractOf?.Invoke(m) is Contract c && Pure(m, c) && (c.PureBody != null || m.IsAbstract || !m.ReturnsVoid && m.DeclaringSyntaxReferences.Length > 0);

        /// <summary>[Pure]: the method, or (a getter) its property.</summary>
        private static bool Pure(IMethodSymbol m, Contract c) => c.IsPure || m.MethodKind == MethodKind.PropertyGet && m.AssociatedSymbol != null && SpecSymbols.IsPure(m.AssociatedSymbol);

        /// <summary>The fields each procedure's declaration names.</summary>
        private readonly Dictionary<IMethodSymbol, HashSet<ISymbol>> _fieldsRead = new Dictionary<IMethodSymbol, HashSet<ISymbol>>(SymbolEqualityComparer.Default);

        /// <summary>The fields a function may read: those it, or what it calls, names.</summary>
        private HashSet<ISymbol> FieldsOf(IMethodSymbol m)
        {
            m = m.OriginalDefinition;
            var all = new HashSet<ISymbol>(SymbolEqualityComparer.Default);
            // (one an override may answer reads what any of them might: every field the program names)
            if (Engine.IsOverridable(m)) { foreach (var f in _fieldsRead.Values) all.UnionWith(f); return all; }
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

        /// <summary>The overrides of a virtual member, in the program: a call of it may run any of them.</summary>
        public Func<IMethodSymbol, IEnumerable<IMethodSymbol>> OverridesOf = _ => Enumerable.Empty<IMethodSymbol>();

        /// <summary>The string literals: one constant per contents.</summary>
        private readonly Dictionary<string, string> _literals = new Dictionary<string, string>(StringComparer.Ordinal);

        private string Literal(string s)
        {
            if (!_literals.TryGetValue(s, out var name)) _literals[s] = name = "s#" + _literals.Count;
            return name;
        }

        private readonly Dictionary<IMethodSymbol, (IMethodSymbol pred, int[] arg)?> _over = new Dictionary<IMethodSymbol, (IMethodSymbol, int[])?>(SymbolEqualityComparer.Default);

        public (IMethodSymbol pred, int[] arg)? OverPredicate(IMethodSymbol f)
        {
            f = f.OriginalDefinition;
            if (_over.TryGetValue(f, out var known)) return known;
            (IMethodSymbol, int[])? over = null;
            try
            {
                // (static, its precondition holding one instance, whose arguments are its parameters, each once; its
                // other parameters (an index) not of the instance: -1)
                if (f.IsStatic && IsFunction(f) && ContractOf(f).Requires.Any(Lowering.HasAtoms))
                {
                    var sig = ((IProgramFacts)this).Signature(f);
                    var atoms = sig.Requires.SelectMany(r => AtomsOf(r.Expr)).ToList();
                    if (atoms.Count == 1 && atoms[0] is KInst q && q.Args.All(a => a is KVar))
                    {
                        var names = q.Args.Select(a => ((KVar)a).Name).ToList();
                        var map = f.Parameters.Select(x => names.IndexOf(Local(x))).ToArray();
                        var used = map.Where(j => j >= 0).ToList();
                        if (used.Distinct().Count() == used.Count && used.Count == names.Count && names.Distinct().Count() == names.Count) over = (q.Pred, map);
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
            if (!IsCollection(m.ContainingType)) m = m.OriginalDefinition;
            if (!_signatures.TryGetValue(m, out var sig)) _signatures[m] = sig = Lowering.Signature(m, ContractOf(m), IsFunction, Literal, ContractOf);
            return sig;
        }

        // ------------------------------------------------------------------ the program

        /// <summary>What every program has: C#'s division, fuel, and the heap of arrays (Dafny's encoding).</summary>
        public void Prelude() => _printer.Prelude();

        /// <summary>The method as a procedure; throws <see cref="NotTranslated"/> for one outside the subset (then nothing is kept).</summary>
        public void Procedure(IMethodSymbol m, Contract contract, SyntaxNode decl, SemanticModel model, MethodResult result, ControlFlowGraph graph = null)
        {
            var p = Lowering.Lower(m, contract, decl, model, result, x => _procedures.Contains(x.OriginalDefinition), IsFunction, Literal, ContractOf, graph: graph);
            Checks.Run(p, this);
            Heap.Run(p);
            // (the library members it calls: each a procedure of its stub's contract, once; one that doesn't translate refuses this)
            var lib = new List<KProcedure>();
            foreach (var callee in p.LibCalls.Where(c => !_libraries.Contains(c)))
            {
                try
                {
                    var lp = Lowering.Lower(callee, ContractOf(callee), null, null, new MethodResult(), x => _procedures.Contains(x.OriginalDefinition), IsFunction, Literal, ContractOf);
                    Checks.Run(lp, this);
                    Heap.Run(lp);
                    lib.Add(lp);
                }
                catch (NotTranslated why) { throw new NotTranslated("a call of List's " + callee.Name + ": " + why.Message); }
            }
            foreach (var lp in lib) { _libraries.Add(lp.Method); _pending.Add(lp); }
            _pending.Add(p);
        }

        private readonly HashSet<IMethodSymbol> _libraries = new HashSet<IMethodSymbol>(SymbolEqualityComparer.Default);

        /// <summary>
        /// A method whose body doesn't translate, as its callers see it: a procedure of its contract alone (nothing of it
        /// verified here). It may write what CsVerify's effects analysis says it may: the fields it and its callees write
        /// (any, where that says so), every array unless it writes none. Throws <see cref="NotTranslated"/> where the
        /// contract doesn't translate either.
        /// </summary>
        public void ContractOnly(IMethodSymbol m, Contract contract, SyntaxNode decl, SemanticModel model, MethodResult result, ControlFlowGraph graph = null)
        {
            var p = Lowering.Lower(m, contract, decl, model, result, x => _procedures.Contains(x.OriginalDefinition), IsFunction, Literal, ContractOf, contractOnly: true, graph: graph);
            Checks.Run(p, this);
            Heap.Run(p);
            _pending.Add(p);
        }

        /// <summary>Writes the functions and the procedures: each modifies what it writes, and what what it calls does.</summary>
        public void Finish()
        {
            var fields = new HashSet<ISymbol>(_pending.SelectMany(p => p.Fields), SymbolEqualityComparer.Default);
            foreach (var p in _pending.Where(p => IsFunction(p.Method))) fields.UnionWith(FieldsOf(p.Method));
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
            // the library stubs used (a string's [Pure] members): functions their contracts describe
            // (and the stubs those stubs' contracts call)
            var stubs = new HashSet<IMethodSymbol>(_pending.SelectMany(p => p.Stubs).Concat(_signatures.Values.SelectMany(s => s.Stubs)), SymbolEqualityComparer.Default);
            var stubMath = new Dictionary<IMethodSymbol, (List<KExpr> requires, List<KExpr> ensures)>(SymbolEqualityComparer.Default);
            for (var work = new Stack<IMethodSymbol>(stubs); work.Count > 0;)
            {
                var s = work.Pop();
                var sig = ((IProgramFacts)this).Signature(s);
                stubMath[s] = (sig.Requires.Select(r => Checks.MathOf(r.Expr, this, s)).ToList(), sig.Ensures.Select(e => Checks.MathOf(e.Expr, this, s)).ToList());
                foreach (var t in sig.Stubs.Concat(_signatures.Values.SelectMany(x => x.Stubs)))
                    if (stubs.Add(t)) work.Push(t);
            }
            foreach (var s in stubs.OrderBy(x => x.ToDisplayString(), StringComparer.Ordinal))
                _printer.Stub(s, ContractOf(s), stubMath[s].requires, stubMath[s].ensures);
            // (the literals last: the stubs' contracts may have some)
            _printer.Literals(_literals);
            _printer.Fields(fields);
            // (before the data types: their invariants may call functions, which read no arrays)
            OwnArrays();
            DataTypes();
            // (the lists' models: maps as fields are)
            var models = _pending.SelectMany(p => p.Models.Values).Concat(_signatures.Values.SelectMany(s => s.Models.Values))
                .GroupBy(m => m.Name).Select(g => g.First()).OrderBy(m => m.Name, StringComparer.Ordinal).ToList();
            _printer.Models(models, _pending.SelectMany(p => p.Pairs).Concat(_signatures.Values.SelectMany(s => s.Pairs)).Distinct().ToList());
            _printer.OwnedMaps = fields.Where(IsOwnedField).Select(FieldMap).ToHashSet();
            _printer.Recursive = (a, b) => Recursive(a.OriginalDefinition, b.OriginalDefinition);
            foreach (var p in _pending.Where(p => IsFunction(p.Method) && !p.IsPredicate))
                if (OverPredicate(p.Method) != null) _printer.FunctionOverPredicate(p);
                else _printer.Function(p, FunctionFields(p.Method), fields);
            // (a [Pure] override, of an object whose dynamic type is exactly its class: the base member's value is its)
            foreach (var p in _pending.Where(p => IsFunction(p.Method) && !p.IsPredicate && OverPredicate(p.Method) == null && p.Method.IsOverride))
                for (var b = p.Method.OverriddenMethod?.OriginalDefinition; b != null; b = b.OverriddenMethod?.OriginalDefinition)
                    if (IsFunction(b) && OverPredicate(b) == null && IsModeledClass(p.Method.ContainingType))
                        _printer.Dispatch(b, FunctionFields(b), p.Method, FunctionFields(p.Method), fields);
            // (the atomic fields' steps, kept wherever the fields are forgotten)
            foreach (var f in fields.Where(f => Atomics.IsAtomic(f) && Atomics.StepOf(f) != null && IsFunction(Atomics.StepOf(f).OriginalDefinition)))
            {
                var step = Atomics.StepOf(f).OriginalDefinition;
                var a = new KVar("x$old");
                var b = new KVar("x$now");
                _printer.AtomicSteps[FieldMap(f)] = new KOp("||", new KOp("==", a, b), Checks.MathOf(new KFnCall { Callee = step, Args = new KExpr[] { a, b } }, this, step));
            }
            _allMaps = new[] { "$Alloc" }.Concat(ElementTypes.Select(ElementMap)).Concat(fields.Select(FieldMap))
                .Concat(models.Select(m => m.Name)).Concat(KernelTypes.Trees ? new[] { "$root" } : new string[0]).ToHashSet();
            var writes = Closed(p => p.CallsDelegates ? new HashSet<string>(p.Modifies.Concat(_allMaps)) : p.Modifies);
            var any = Closed(p => p.CallsDelegates ? new HashSet<string>(p.AnyWrites.Concat(_allMaps)) : p.AnyWrites);
            _printer.UsesState |= _pending.Any(p => p.UsesState);
            _printer.Delegates(_pending.SelectMany(p => p.DelegateKeys).Concat(_signatures.Values.SelectMany(s => s.DelegateKeys)), _allMaps);
            if (_pending.Any(p => p.HavocsAll)) _printer.Havoc(_allMaps);
            if (_pending.Any(p => p.Awaits)) _printer.Await(_allMaps);
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
                    if (KernelTypes.Trees) p.Locals.Add(new KLocal { Name = $"s{frame.Id}$root", Raw = "[Ref]Ref" });
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
                            p.Locals.Add(new KLocal { Name = $"s{frame.Id}{map}", Raw = "[Ref][int]" + ElementValue(map) });
                    }
                    // (and the globals its postconditions read as they were)
                    foreach (var g in frame.OldGlobals.Where(g => !p.Locals.Any(l => l.Name == $"s{frame.Id}{g}")).ToList())
                    {
                        var raw = g.StartsWith("$E.") ? ("[Ref][int]" + ElementValue(g))
                                : fields.FirstOrDefault(f => FieldMap(f) == g) is ISymbol fs ? $"[Ref]{TypeOf(FieldType(fs))}" : null;
                        if (raw != null) p.Locals.Add(new KLocal { Name = $"s{frame.Id}{g}", Raw = raw });
                    }
                }
            // (a call, in array mode, that may write any array: reported only if it may)
            foreach (var a in _pending.SelectMany(p => p.Blocks).SelectMany(b => b.Stmts).OfType<KAssert>().Where(a => a.UnlessWritesArrays != null))
            {
                var cw = writes.TryGetValue(a.UnlessWritesArrays, out var w) || writes.TryGetValue(a.UnlessWritesArrays.OriginalDefinition, out w) ? w : new HashSet<string>();
                bool arrays = cw.Any(x => x.StartsWith("$E.")), writesFields = cw.Any(x => x.StartsWith("$F.") && !_printer.OwnedMaps.Contains(x));
                // (a callee of the program's that writes only arrays it makes, as CsVerify's engine infers it: none of ours)
                var uw = a.UnlessWritesArrays;
                if (arrays && uw.DeclaringSyntaxReferences.Length > 0 && KernelTypes.MayWriteHeap != null && !KernelTypes.MayWriteHeap(uw)) arrays = false;
                bool stands = a.UnlessKind switch { "fields" => writesFields && !arrays, "any" => writesFields || arrays, _ => arrays };
                if (!stands) a.Cond = new KLit("true");
            }
            // (around a call of an async method: a copy of each map, for the confined objects it can't reach)
            foreach (var p in _pending)
                foreach (var keep in p.Blocks.SelectMany(b => b.Stmts).OfType<KKeep>().Where(k => !k.After))
                    foreach (var (name, type) in _printer.StateMaps)
                        p.Locals.Add(new KLocal { Name = $"k${keep.Id}{name}", Raw = type });
            // (each confined frame's snapshot of every state map)
            foreach (var p in _pending)
                foreach (var cf in p.Blocks.SelectMany(b => b.Stmts).OfType<KConfinedFrame>())
                    foreach (var (name, type) in _printer.StateMaps)
                        p.Locals.Add(new KLocal { Name = $"c${cf.Head}{name}", Raw = type });
            // each loop frame keeps the element maps, unless the loop calls what writes arrays
            foreach (var p in _pending)
                foreach (var frame in p.Blocks.SelectMany(b => b.Stmts).OfType<KLoopFrame>())
                {
                    if (frame.Callees.Any(c => writes.TryGetValue(c, out var w) && w.Any(x => x.StartsWith("$E.")))) continue;
                    frame.Maps = writes[p.Method].Where(x => x.StartsWith("$E.")).OrderBy(x => x, StringComparer.Ordinal).ToList();
                    if (frame.Maps.Count == 0) continue;
                    p.Locals.Add(new KLocal { Name = $"s${frame.Head}$Alloc", Raw = "[Ref]bool" });
                    foreach (var map in frame.Maps)
                        p.Locals.Add(new KLocal { Name = $"s${frame.Head}{map}", Raw = "[Ref][int]" + ElementValue(map) });
                }
            // the exception types named, and how they derive
            var exceptions = new HashSet<ITypeSymbol>(_pending.SelectMany(p => p.ExceptionTypes).Concat(_signatures.Values.SelectMany(s => s.ExceptionTypes)), SymbolEqualityComparer.Default);
            bool throws = _pending.Any(p => p.Blocks.SelectMany(b => b.Stmts).Any(s => s is KFork || s is KThrow || s is KNewExc || s is KThrowExit));
            var classes = new HashSet<ITypeSymbol>(_pending.SelectMany(p => p.ClassTypes).Concat(_signatures.Values.SelectMany(s => s.ClassTypes)), SymbolEqualityComparer.Default);
            foreach (var p in _pending.Where(p => IsFunction(p.Method) && !p.IsPredicate && OverPredicate(p.Method) == null && p.Method.IsOverride && IsModeledClass(p.Method.ContainingType)))
                if (p.Method.OverriddenMethod is IMethodSymbol ob && IsFunction(ob.OriginalDefinition)) classes.Add(p.Method.ContainingType.OriginalDefinition);
            if (_compilationException != null && (exceptions.Count > 0 || throws) || classes.Count > 0)
                _printer.ExceptionTypes(exceptions, _compilationException != null && (exceptions.Count > 0 || throws) ? _compilationException : null, classes);
            foreach (var p in _pending)
            {
                // (the function's value is its body's: not where an override may answer the call)
                _printer.Procedure(p, writes[p.Method], any[p.Method], IsFunction(p.Method) && !p.IsPredicate && OverPredicate(p.Method) == null && !Engine.IsOverridable(p.Method) ? FunctionFields(p.Method) : null);
                Obligations[p.Result] = p.Obligations;
            }
            // the twins of what throws, for the ways calls of them throw
            foreach (var callee in _printer.Throwing.OrderBy(x => x.ToDisplayString(), StringComparer.Ordinal).ToList())
            {
                var sig = ((IProgramFacts)this).Signature(callee);
                var clauses = sig.ThrowEnsures.Select(t => (t.type, Checks.MathOf(t.cond, this, callee))).ToList();
                _printer.Throws(sig, writes.TryGetValue(callee, out var w) || writes.TryGetValue(callee.OriginalDefinition, out w) ? w : _allMaps, clauses);
            }
            _printer.Throwing.Clear();
            // the twins of what's started as a task or a thread: its preconditions free, as its start checked them
            foreach (var callee in _printer.Started.ToList())
            {
                var p = _pending.FirstOrDefault(x => SymbolEqualityComparer.Default.Equals(x.Method, callee.OriginalDefinition));
                if (p == null) continue;
                var twin = p.Clone();
                twin.Name = p.Name + "$started";
                twin.Abstract = true;
                twin.FreeRequires = true;
                _printer.Procedure(twin, writes[p.Method], any[p.Method], null);
            }
            _printer.Started.Clear();
            _printer.Tuples();
            foreach (var p in _pending.Where(p => p.Result != null && p.Warnings.Count > 0))
                (_warnings.TryGetValue(p.Result, out var w) ? w : _warnings[p.Result] = new List<VerificationDiagnostic>()).AddRange(p.Warnings);
            _pending.Clear();
        }

        /// <summary>The data types named, their cases and the data types of their fields: Dafny's datatypes.</summary>
        private void DataTypes()
        {
            var defs = new HashSet<INamedTypeSymbol>(_pending.SelectMany(p => p.DataTypes).Concat(_signatures.Values.SelectMany(s => s.DataTypes)), SymbolEqualityComparer.Default);
            // (the types of the procedures' parameters and results: their facts name them, a body or none)
            foreach (var t in _pending.Concat(_signatures.Values).SelectMany(p => p.Method.Parameters.Select(x => x.Type).Append(Returns(p.Method))).Where(t => t != null && IsData(t)))
                defs.Add(Verifier.DataTypes.Def(t));
            if (defs.Count == 0) return;
            var cases = new HashSet<INamedTypeSymbol>(SymbolEqualityComparer.Default);
            for (var work = new Stack<INamedTypeSymbol>(defs); work.Count > 0;)
            {
                var d = work.Pop();
                foreach (var c in Data.Cases(Verifier.DataTypes.Def(d)) ?? new INamedTypeSymbol[0])
                    if (cases.Add(c))
                        foreach (var f in Data.Fields(c).Where(f => IsData(f.Type)))
                            work.Push(Verifier.DataTypes.Def(f.Type));
            }
            var list = new List<BoogiePrinter.DataCase>();
            var fields = new Dictionary<string, (string type, KExpr fact)>();
            foreach (var c in cases.OrderBy(x => Data.TagOf(x)))
            {
                var ctor = Verifier.DataTypes.PrimaryConstructor(c) ?? throw new NotTranslated("a data case without its primary constructor: " + c.Name);
                var dc = new BoogiePrinter.DataCase { Type = c, Name = CaseName(c), Tag = Data.TagOf(c) };
                foreach (var p in ctor.Parameters)
                {
                    var prop = Verifier.DataTypes.PositionalProperty(c, p.Ordinal);
                    dc.Params.Add((Local(p), TypeOf(p.Type), IsData(p.Type), FieldFunction(prop)));
                }
                foreach (var prop in Data.Fields(c))
                {
                    var fn = FieldFunction(prop);
                    KExpr value = SymbolEqualityComparer.Default.Equals(prop.ContainingType.OriginalDefinition, c.OriginalDefinition)
                        ? new KVar(Local(ctor.Parameters.First(x => x.Name == prop.Name)))
                        : Checks.MathOf(Lowering.BaseArgument(c, prop, IsFunction, Literal, ContractOf), this, ctor);
                    dc.Fields.Add((fn, value));
                    // (a field of data type: one of its cases, and not null where its type says so, as each construction is checked;
                    // an integer one in its type's range)
                    if (!fields.ContainsKey(fn))
                        fields[fn] = (TypeOf(prop.OriginalDefinition.Type), IsData(prop.Type)
                            ? NotNullable(prop.OriginalDefinition.Type) ? IsCase(new KOp(fn, new KVar("d")), prop.Type)
                              : new KOp("||", new KOp("==", new KOp(fn, new KVar("d")), new KLit("null")), IsCase(new KOp(fn, new KVar("d")), prop.Type))
                            : IsIntegral(prop.OriginalDefinition.Type) ? InRange(new KOp(fn, new KVar("d")), prop.OriginalDefinition.Type) : null);
                }
                list.Add(dc);
            }
            _printer.Data(list, fields.OrderBy(kv => kv.Key, StringComparer.Ordinal).Select(kv => (kv.Key, kv.Value.type, kv.Value.fact)).ToList());
            // (valid values: their invariants hold, and their parts with invariants are valid, case by case)
            var valid = new HashSet<INamedTypeSymbol>(_pending.SelectMany(p => p.Valid).Concat(_signatures.Values.SelectMany(s => s.Valid)), SymbolEqualityComparer.Default);
            for (var work = new Stack<INamedTypeSymbol>(valid); work.Count > 0;)
                foreach (var c in Data.Cases(work.Pop()) ?? new INamedTypeSymbol[0])
                {
                    // (a base's value is valid as the case it is)
                    if (HasInvariants(c) && valid.Add(c)) work.Push(c);
                    foreach (var f in Data.Fields(c).Where(f => HasInvariants(f.Type)))
                        if (valid.Add(Verifier.DataTypes.Def(f.Type))) work.Push(Verifier.DataTypes.Def(f.Type));
                }
            var dv = new KVar("d");
            var validity = new List<(string name, KExpr invariant, List<(string isCase, KExpr part)> parts)>();
            foreach (var t in valid.OrderBy(x => x.ToDisplayString(), StringComparer.Ordinal))
            {
                var invs = Verifier.DataTypes.Invariants(t).Select(inv => Checks.Rename(Checks.MathOf(Lowering.InvariantBody(inv.OriginalDefinition, IsFunction, Literal, ContractOf), this, inv.OriginalDefinition), "this", dv)).ToList();
                var parts = new List<(string, KExpr)>();
                foreach (var c in Data.Cases(t).Where(c => !SymbolEqualityComparer.Default.Equals(c, t) && HasInvariants(c)))
                    parts.Add(("$is." + CaseName(c).Substring(3), new KOp(ValidName(c), dv)));
                foreach (var c in Data.Cases(t))
                    foreach (var f in Data.Fields(c).Where(f => HasInvariants(f.Type)))
                        parts.Add(("$is." + CaseName(c).Substring(3), new KOp("||", new KOp("==", new KOp(FieldFunction(f), dv), new KLit("null")), new KOp(ValidName(f.Type), new KOp(FieldFunction(f), dv)))));
                validity.Add((ValidName(t), invs.Count == 0 ? new KLit("true") : invs.Aggregate((a, b) => new KOp("&&", a, b)), parts));
            }
            _printer.Valid(validity);
        }

        /// <summary>System.Exception, of the program's compilation (what every exception is).</summary>
        public ITypeSymbol ExceptionType { set => _compilationException = value; }
        private ITypeSymbol _compilationException;

        /// <summary>
        /// Which functions read arrays only through their own array parameters (and call only such functions, on
        /// them): their value depends on those arrays' elements alone, as in CsVerify's engine, so a write of another
        /// array leaves it as it was. The others depend on the element maps whole.
        /// </summary>
        private void OwnArrays()
        {
            // (and a function of its contract alone whose body reads nothing of the memory: no array, no field, calling only
            // such functions or mathematics; its procedure's value is then of its arguments alone too)
            bool ReadsNothing(IMethodSymbol m) => m.IsStatic && !m.IsAbstract && !Engine.IsOverridable(m) && m.Parameters.All(x => Scalar(x.Type)) && FieldsOf(m).Count == 0 &&
                m.DeclaringSyntaxReferences.Select(r => r.GetSyntax()).All(d => !d.DescendantNodes().Any(n => n is ElementAccessExpressionSyntax || n is ObjectCreationExpressionSyntax ||
                    n is InvocationExpressionSyntax inv && !(inv.Expression.ToString().StartsWith("Spec.") || inv.Expression.ToString().StartsWith("Math."))));
            var functions = _pending.Where(p => (p.FunctionBody != null || IsFunction(p.Method) && ReadsNothing(p.Method)) && !p.IsPredicate && OverPredicate(p.Method) == null).ToDictionary(p => p.Method, p => p, (IEqualityComparer<IMethodSymbol>)SymbolEqualityComparer.Default);
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
                    if (!new[] { p.FunctionBody }.Where(x => x != null).Concat(p.Requires.Select(r => r.Expr)).Concat(p.Ensures.Select(x => x.Expr)).All(x => Reads(x, mine)))
                    {
                        own.Remove(p.Method);
                        shrank = true;
                    }
                }
            }
            _printer.OwnArrays = m => own.Contains(m.OriginalDefinition) ? Of(m.OriginalDefinition) : null;
        }

        private HashSet<string> _allMaps = new HashSet<string>();

        /// <summary>A set of globals of each procedure's, with those of everything it calls.</summary>
        private Dictionary<IMethodSymbol, HashSet<string>> Closed(Func<KProcedure, HashSet<string>> own)
        {
            var sets = _pending.ToDictionary(p => p.Method, p => new HashSet<string>(own(p)), (IEqualityComparer<IMethodSymbol>)SymbolEqualityComparer.Default);
            // (a virtual member's call may run any override: what each does, it does; one of them not here, anything)
            var edges = _pending.ToDictionary(p => p.Method, p => p.Calls.ToList(), (IEqualityComparer<IMethodSymbol>)SymbolEqualityComparer.Default);
            foreach (var p in _pending.Where(p => p.Method.IsVirtual || p.Method.IsAbstract || p.Method.IsOverride))
            {
                // (a [Pure] member whose every override is [Pure] too: no call of it writes anything, whichever runs)
                if (IsFunction(p.Method) && OverridesOf(p.Method).All(o => ContractOf(o.OriginalDefinition) is Contract oc && oc.IsPure)) continue;
                foreach (var o in OverridesOf(p.Method).Select(o => o.OriginalDefinition))
                    if (sets.ContainsKey(o)) edges[p.Method].Add(o);
                    else sets[p.Method].UnionWith(_allMaps);
                // (as CsVerify's engine says: a call that may run an override changes what the member's Spec.Modifies
                // allows, and without one, anything)
                // (a library member's stub: what it says, unless it may run the program's code, as CsVerify's engine has it)
                bool library = p.Method.DeclaringSyntaxReferences.Length == 0 && ContractOf(p.Method) is Contract pc && pc.IsStub;
                if (Engine.IsOverridable(p.Method) && p.Frame == null && !(library && KernelTypes.RunsUserCode != null && !KernelTypes.RunsUserCode(p.Method))) sets[p.Method].UnionWith(_allMaps);
            }
            // (a body not translated: what CsVerify's effects analysis says it writes, which is anything but the fields it doesn't)
            foreach (var p in _pending.Where(p => p.Opaque))
            {
                var (written, all) = KernelTypes.FieldEffectsOf?.Invoke(p.Method) ?? (null, true);
                var kept = all ? new HashSet<string>() : new HashSet<string>(_allMaps.Where(x => x.StartsWith("$F.")));
                if (!all) foreach (var f in written) kept.Remove(FieldMap(f));
                sets[p.Method].UnionWith(_allMaps.Where(x => !kept.Contains(x)));
            }
            // (a delegate's call runs whichever body it was made of: anything)
            foreach (var p in _pending.Where(p => p.Method.MethodKind == MethodKind.DelegateInvoke)) sets[p.Method].UnionWith(_allMaps);
            for (bool grew = true; grew;)
            {
                grew = false;
                foreach (var p in _pending)
                    foreach (var c in edges[p.Method])
                        if (sets.TryGetValue(c, out var w))
                            foreach (var g in w.ToList())
                                if (sets[p.Method].Add(g)) grew = true;
            }
            return sets;
        }
    }
}
