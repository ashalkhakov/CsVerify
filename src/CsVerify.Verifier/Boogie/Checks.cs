using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.CodeAnalysis;
using static CsVerify.Verifier.Boogie.KernelTypes;
using static CsVerify.Verifier.Boogie.MOp;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>What Checks needs to know of the rest of the program.</summary>
    internal interface IProgramFacts
    {
        bool CheckOverflow { get; }
        /// <summary>Is a call of b from a recursive (b calls a back, or is a)?</summary>
        bool Recursive(IMethodSymbol a, IMethodSymbol b);
        Contract ContractOf(IMethodSymbol m);
        /// <summary>A callee's requires and measure, lowered over its parameters.</summary>
        KProcedure Signature(IMethodSymbol m);
        /// <summary>The field maps a function reads (it, or the functions it calls).</summary>
        List<string> FunctionFields(IMethodSymbol m);
        /// <summary>The fields a function reads (its own and its callees'), as symbols.</summary>
        IEnumerable<ISymbol> FunctionFieldSymbols(IMethodSymbol m);
        /// <summary>Is the method a function too (so its value can be named)?</summary>
        bool IsFunction(IMethodSymbol m);
        /// <summary>Does the program use permissions (Spec.Acc, Spec.AccRead) at all? Then array writes are checked against cells.</summary>
        bool UsesPermissions { get; }
        /// <summary>Does the program use single-field permissions (Spec.Acc(o, nameof(C.F)))?</summary>
        bool UsesFieldPermissions { get; }
        /// <summary>A field's id, for its single-field permission.</summary>
        int FieldId(ISymbol field);
        /// <summary>
        /// A function over a predicate (its precondition holds one instance, of its parameters): the predicate, and
        /// for each of the function's parameters, the instance's argument it is. Null for any other.
        /// </summary>
        (IMethodSymbol pred, int[] arg)? OverPredicate(IMethodSymbol f);
        /// <summary>The functions over a predicate.</summary>
        IEnumerable<IMethodSymbol> FunctionsOver(IMethodSymbol pred);
    }

    /// <summary>
    /// Pass 2, level 1 to level 2 (a KProcedure in, an MProcedure out; the kernel's is never changed but for what it
    /// names and declares): C#'s meaning made mathematics, and each obligation an assert, in the order C# evaluates. In code: an
    /// array's element or length checked not null and in bounds; arithmetic and conversions in their context (an
    /// obligation, the path's end, wrap-around, or mathematics in ghost code); division checked by zero; a call's
    /// non-null arguments, its termination in its recursion group, its precondition (the call's). In specifications:
    /// what makes them well-defined (CSV1012), under the guards of &amp;&amp;, || and ?: and the quantifiers' ranges, as
    /// Dafny's. And where the contract is checked: the requires well-defined at entry; invariants (and each loop's
    /// measure taken) at its head; the measure gone down on each back edge; at each return, the result not null and
    /// each postcondition well-defined and holding. After it, only Heap's array writes and allocations are left.
    /// This file: the pass's state, asserting and assuming, the facts on a path, and Run. The rest, a file per
    /// obligation: Statements, Calls, Code, Specs, Termination, Permissions, Snapshots, Cells, Predicates,
    /// Ownership, Invariants.
    /// </summary>
    internal sealed partial class Checks
    {
        /// <summary>The method as Lowering made it (level 1), and what Checks makes of it (level 2).</summary>
        private readonly KProcedure _p;
        private readonly MProcedure _m;
        private readonly IProgramFacts _program;
        private List<MStmt> _out;

        private Checks(KProcedure p, IProgramFacts program)
        {
            _p = p;
            _m = new MProcedure { Source = p };
            _program = program;
        }

        public static MProcedure Run(KProcedure p, IProgramFacts facts)
        {
            var c = new Checks(p, facts);
            c.Run();
            return c._m;
        }

        private Check At(string id, SyntaxNode at, string message, string reportAs = null) =>
            new Check
            {
                Id = id,
                Message = message,
                Span = at.GetLocation().GetLineSpan(),
                Method = _p.Result,
                ReportAs = reportAs,
            };

        /// <summary>A null check of what <paramref name="what"/> is, saying where the null may come from.</summary>
        private Check NullAt(SyntaxNode at, SyntaxNode what, string message) => At("CSV1013", at, message + NullReasons(what));

        private static int LineOf(SyntaxNode n) => n.GetLocation().GetLineSpan().StartLinePosition.Line + 1;

        /// <summary>
        /// Why a value might be null, from the source (StaticChecks.NullReasons): a parameter
        /// declared nullable, a call that may return null (or a local made of one), a call between a check of it and its use
        /// (with the usual fix). Empty if nothing is known.
        /// </summary>
        internal static string NullReasons(SyntaxNode what)
        {
            if (what == null || KernelTypes.Compilation == null || what.SyntaxTree == null || !KernelTypes.Compilation.SyntaxTrees.Contains(what.SyntaxTree))
            {
                return "";
            }
            var model = KernelTypes.Compilation.GetSemanticModel(what.SyntaxTree);
            while (what is Microsoft.CodeAnalysis.CSharp.Syntax.ParenthesizedExpressionSyntax pe)
            {
                what = pe.Expression;
            }
            var symbol = model.GetSymbolInfo(what).Symbol;
            var origins = new List<string>();
            if (NullOrigin(what, symbol, model) is string origin)
            {
                origins.Add(origin);
            }
            if (ChangedSinceChecked(what, symbol, model) is string changed)
            {
                origins.Add(changed);
            }
            if (origins.Count == 0)
            {
                return "";
            }
            var reasons = ": " + string.Join("; ", origins.Take(3));
            if (origins.Any(o => o.Contains(" may change ")))
            {
                reasons += " (a check made before a call does not hold after it: copy the value to a local, check that, and use the local)";
            }
            return reasons;
        }

        /// <summary>Where a null may come from: a parameter declared nullable, a call that may return null (or a local made of one).</summary>
        private static string NullOrigin(SyntaxNode what, ISymbol symbol, SemanticModel model)
        {
            string Note(ITypeSymbol t) => t.ToDisplayString(SymbolDisplayFormat.MinimallyQualifiedFormat.WithMiscellaneousOptions(SymbolDisplayMiscellaneousOptions.UseSpecialTypes | SymbolDisplayMiscellaneousOptions.IncludeNullableReferenceTypeModifier));
            bool MayReturnNull(IMethodSymbol m) => !m.ReturnsVoid && (m.ReturnType.NullableAnnotation == NullableAnnotation.Annotated || m.ReturnType.IsReferenceType && m.ReturnType.NullableAnnotation == NullableAnnotation.None ||
                                                                      m.GetReturnTypeAttributes().Any(a => a.AttributeClass?.Name == "MaybeNullAttribute"));
            string FromCall(Microsoft.CodeAnalysis.CSharp.Syntax.InvocationExpressionSyntax inv) =>
                model.GetSymbolInfo(inv).Symbol is IMethodSymbol m && MayReturnNull(m) ? $"'{m.Name}' may return null (line {LineOf(inv)})" : null;
            if (symbol is IParameterSymbol p && (p.Type.NullableAnnotation == NullableAnnotation.Annotated || p.Type.OriginalDefinition.SpecialType == SpecialType.System_Nullable_T))
            {
                return $"parameter '{p.Name}' is declared '{Note(p.Type)}'";
            }
            if (what is Microsoft.CodeAnalysis.CSharp.Syntax.InvocationExpressionSyntax call)
            {
                return FromCall(call);
            }
            if (symbol is ILocalSymbol l && l.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() is Microsoft.CodeAnalysis.CSharp.Syntax.VariableDeclaratorSyntax d &&
                d.Initializer?.Value is Microsoft.CodeAnalysis.CSharp.Syntax.InvocationExpressionSyntax made)
            {
                return FromCall(made);
            }
            return null;
        }

        /// <summary>A field or property checked before a call, and read again after it: the call may have changed it.</summary>
        private static string ChangedSinceChecked(SyntaxNode what, ISymbol symbol, SemanticModel model)
        {
            if (!(what is Microsoft.CodeAnalysis.CSharp.Syntax.MemberAccessExpressionSyntax read && symbol is IFieldSymbol or IPropertySymbol))
            {
                return null;
            }
            var text = read.ToString();
            var check = what.Ancestors().OfType<Microsoft.CodeAnalysis.CSharp.Syntax.IfStatementSyntax>()
                .FirstOrDefault(i => i.Condition.DescendantNodesAndSelf().OfType<Microsoft.CodeAnalysis.CSharp.Syntax.BinaryExpressionSyntax>().Any(b => b.Left.ToString() == text || b.Right.ToString() == text));
            if (check == null)
            {
                return null;
            }
            var between = check.Statement.DescendantNodes().OfType<Microsoft.CodeAnalysis.CSharp.Syntax.InvocationExpressionSyntax>()
                .Where(i => i.SpanStart < what.SpanStart && !i.Span.Contains(what.Span)).Select(i => model.GetSymbolInfo(i).Symbol as IMethodSymbol)
                .FirstOrDefault(m => m != null && !CsVerify.Analyzers.SpecSymbols.IsSpecClass(m.ContainingType));
            var at = check.Statement.DescendantNodes().OfType<Microsoft.CodeAnalysis.CSharp.Syntax.InvocationExpressionSyntax>().FirstOrDefault(i => i.SpanStart < what.SpanStart && model.GetSymbolInfo(i).Symbol is IMethodSymbol bm && SymbolEqualityComparer.Default.Equals(bm, between));
            return between != null && at != null ? $"the call to '{between.Name}' (line {LineOf(at)}) may change what was checked before it" : null;
        }

        private void Emit(MStmt s)
        {
            _out.Add(s);
            if (_headInto != null && _inQuantifier == 0 && s is MAssume { Always: true } always)
            {
                foreach (var into in _headInto)
                {
                    into.Stmts.Add(MAssume.Of(always.Cond, always: true));
                }
            }
        }

        /// <summary>The blocks into a loop's head from before it, while its statements are checked.</summary>
        private List<MBlock> _headInto;
        private int _inQuantifier;

        /// <summary>The id of a loop's inferred fact, a candidate of Houdini's: never reported.</summary>
        public const string Candidate = "HOUDINI";

        private int _unfoldingAssert;
        private readonly List<MExpr> _unfoldedFacts = new List<MExpr>();


        /// <summary>
        /// A condition with each function application among its conjuncts (a static function of the program's with a body
        /// and no precondition, of the memory now) replaced by its body, once (the functions it applies stay applications);
        /// the same object where there is none. Its definition says the two are equal, at every argument.
        /// </summary>
        private MExpr UnfoldOnce(MExpr e)
        {
            switch (e)
            {
                case MOp { Op: "&&", Args: { Length: 2 } a }:
                {
                    var l = UnfoldOnce(a[0]);
                    var r = UnfoldOnce(a[1]);
                    return ReferenceEquals(l, a[0]) && ReferenceEquals(r, a[1]) ? e : AndAlso(l, r);
                }
                case MFnApp app when app.Snap == null && !app.Plain && app.MapsAt == null && app.Callee.IsStatic:
                {
                    var sig = _program.Signature(app.Callee);
                    if (sig.FunctionBody == null || sig.Requires.Count > 0 || app.Args.Length != app.Callee.Parameters.Length)
                    {
                        return e;
                    }
                    var given = app.Callee.Parameters.Select((x, k) => (x, k)).ToDictionary(x => Local(x.x), x => app.Args[x.k]);
                    var saved = _facts.ToList();
                    _facts.Clear();
                    try
                    {
                        var body = Spec(sig.FunctionBody, out _).Substitute(given);
                        // (what reading the body lets one assume, a field's array allocated: known where it's asserted)
                        _unfoldedFacts.AddRange(_facts.Select(f => f.Substitute(given)));
                        return body;
                    }
                    catch (NotTranslated)
                    {
                        return e;
                    }
                    finally
                    {
                        _facts.Clear();
                        _facts.AddRange(saved);
                    }
                }
                default: return e;
            }
        }

        private void Assert(MExpr cond, Check check, bool notAssumedAfter = false)
        {
            // (a postcondition or a loop invariant that is a function, Wf(p), of no precondition: its body asserted
            // first, unfolded once, a conjunct at a time, as Dafny does. The function's definition, an equation, holds its
            // quantifiers where the solver can't use them to prove it; its body proved, the equation gives it)
            if (!notAssumedAfter && check?.Id is "CSV1002" or "CSV1005" or "CSV1006" && _unfoldingAssert == 0)
            {
                _unfoldedFacts.Clear();
                var unfolded = UnfoldOnce(cond);
                if (!ReferenceEquals(unfolded, cond))
                {
                    foreach (var f in _unfoldedFacts)
                    {
                        Assume(f);
                    }
                    _unfoldedFacts.Clear();
                    _unfoldingAssert++;
                    try
                    {
                        foreach (var c in unfolded.Conjuncts())
                        {
                            Assert(c, check);
                        }
                    }
                    finally
                    {
                        _unfoldingAssert--;
                    }
                }
            }
            // (an assertion of a conjunction, one conjunct at a time, each known for the next: as Dafny splits them, so
            // that Z3 needn't find what the first says while it proves the second)
            if (!notAssumedAfter && check?.Id == "CSV1004" && cond is MOp { Op: "&&", Args: { Length: 2 } and_ })
            {
                Assert(and_[0], check);
                Assert(and_[1], check);
                return;
            }
            if (check != null)
            {
                check.Causes.UnionWith(CausesOf(cond));
            }
            Emit(MAssert.Of(cond, check, notAssumedAfter: notAssumedAfter));
        }

        /// <summary>The causes of a condition's unknown values: its variables', and those they were made from.</summary>
        private HashSet<string> CausesOf(MExpr cond)
        {
            var seen = new HashSet<string>();
            var causes = new HashSet<string>();
            var todo = new Stack<string>(cond.Subterms().OfType<MVar>().Select(v => v.Name));
            while (todo.Count > 0)
            {
                var v = todo.Pop();
                if (!seen.Add(v))
                {
                    continue;
                }
                if (_p.Causes.TryGetValue(v, out var c))
                {
                    causes.UnionWith(c);
                }
                if (_p.Deps.TryGetValue(v, out var d))
                {
                    foreach (var x in d)
                    {
                        todo.Push(x);
                    }
                }
            }
            return causes;
        }

        private void Assume(MExpr cond) => Emit(MAssume.Of(cond));

        /// <summary>
        /// What reading a specification lets one assume (a non-nullable field of a built object isn't null), where
        /// it reads one; quantified ones are left out.
        /// </summary>
        private readonly List<MExpr> _facts = new List<MExpr>();
        private readonly HashSet<string> _bound = new HashSet<string>();

        private void Facts()
        {
            foreach (var f in _facts)
            {
                Assume(f);
            }
            _facts.Clear();
        }

        private int _fresh;

        /// <summary>A new local of this Boogie type, havocked: a value nothing is known of.</summary>
        private MVar Fresh(string type)
        {
            var name = "f$" + _fresh++;
            _p.Locals.Add(KLocal.Of(name, type));
            Emit(MHavoc.Of(name));
            return new MVar(name);
        }

        private static MExpr Allocated(MExpr o, MExpr v) =>
            Implies(AndAlso(Sel("$Alloc", o), NotNull(v)), Sel("$Alloc", v));

        /// <summary>A field whose value, once its object is built, is never null.</summary>
        private static bool NonNullField(ISymbol field) => (!field.IsStatic || StaticStartsWithObject(field)) && IsNullable(FieldType(field)) && NotNullable(FieldType(field));

        private static MExpr And(IEnumerable<MExpr> xs)
        {
            var list = xs.ToList();
            return list.Count == 0 ? MLit.True : AndAll(list);
        }

        /// <summary>A clause of the contract as mathematics: the clause, its value, what makes it well-defined, what reading it gives.</summary>
        private sealed record Clause(KSpec Source, MExpr Math, List<MExpr> Wf, List<MExpr> Facts);

        /// <summary>The contract as mathematics: its clauses, its measure (of entry), each loop's invariants and measure.</summary>
        private sealed class ContractMath
        {
            public List<Clause> Requires, Ensures;
            public List<MExpr> Decreases;
            public Dictionary<int, List<Clause>> Invariants;
            public Dictionary<int, List<MExpr>> Measures;
        }

        /// <summary>
        /// The method: its contract as mathematics; at entry, its preconditions well-defined and what it overrides kept to;
        /// then each block, in order: what holds at entry, at a loop's head, its statements' obligations, its jump's.
        /// </summary>
        private void Run()
        {
            if (_p.IsPredicate)
            {
                RunPredicate();
                return;
            }
            // (what the contract gives and takes: its permissions, read from the specifications as written)
            _rawRequires = _p.Requires.Select(r => r.Expr).ToList();
            _rawEnsures = _p.Ensures.Select(e => e.Expr).ToList();
            _rawInvariants = _p.Invariants.ToDictionary(kv => kv.Key, kv => kv.Value.Select(i => (i.Expr, i.At)).ToList());
            Frames();
            DecideCellModes();
            var contract = ContractAsMath();

            // at entry: the requires well-defined, in order (each under those before it)
            _out = _m.Entry;
            // (the preconditions are well-defined given what entry gives: the views received hold their invariants)
            if (_p.UsesPerm)
            {
                ViewsAtEntry(grant: false);
            }
            // (an abstract member: nothing of its own to check, its contract is what calls of it use)
            if (_p.Abstract)
            {
                _m.Entry.Clear();
                _m.Obligations = 0;
                return;
            }
            var before = new List<MExpr>();
            foreach (var r in contract.Requires)
            {
                foreach (var f in r.Facts)
                {
                    Assume(f);
                }
                WellDefined(r.Wf, r.Source.At, before);
                before.Add(r.Math);
            }
            KeepsToWhatItOverrides();

            // (each block's statements, made into level 2's in a block of its own, the same label and jump)
            _bodies = _p.Blocks;
            _m.Blocks = _p.Blocks.Select(b => MBlock.Of(b.Label, b.Ordinal, jump: b.Jump)).ToList();
            foreach (var (b, mb) in _p.Blocks.Zip(_m.Blocks))
            {
                _out = mb.Stmts;
                if (b == _p.Blocks[0])
                {
                    AtEntry(contract);
                }
                bool head = b.Label == $"b{b.Ordinal}";
                if (head)
                {
                    AtLoopHead(b, contract);
                }
                // (a loop's head: what the code there assumes that holds in every state (a non-nullable field read not
                // null) is assumed on the way in too, as Boogie takes the assumes at a head's start for free invariants)
                _headInto = head ? _m.Blocks.Where(x => x.Ordinal < b.Ordinal && x.Jump is KGoto hg && hg.Targets.Contains(b.Label)).ToList() : null;
                if (_headInto != null && !_p.Blocks.Any(x => x.Ordinal >= b.Ordinal && x.Jump is KGoto lg && lg.Targets.Contains(b.Label)))
                {
                    _headInto = null;
                }
                foreach (var s in b.Stmts)
                {
                    Statement(s, contract.Decreases);
                }
                _headInto = null;
                switch (b.Jump)
                {
                    case KReturn ret:
                        Return(ret, contract.Ensures);
                        break;
                    case KGoto g:
                        Goto(b, g, contract);
                        break;
                }
            }
            _m.Obligations = _m.Entry.Concat(_m.Blocks.SelectMany(b => b.Stmts)).Count(s => s is MAssert a && a.Check != null || s is MCall)
                             + _p.Contract.Ensures.Count;
        }

        /// <summary>A function's Spec.Reads, a method's Spec.Modifies, as mathematics, and the locals that keep them as of entry.</summary>
        private void Frames()
        {
            if (_p.ReadsFrame != null)
            {
                _m.ReadsFrame = Spec(_p.ReadsFrame, out _);
                _facts.Clear();
                _p.Locals.Add(KLocal.Of("r$entry", "[Ref]bool"));
            }
            if (_p.Frame != null)
            {
                _m.Frame = Spec(_p.Frame, out _);
                _facts.Clear();
                _p.Locals.Add(KLocal.Of("w$entry", "[Ref]bool"));
                _p.Locals.Add(KLocal.Of("alloc$entry", "[Ref]bool"));
            }
        }

        /// <summary>The contract as mathematics (each clause with what makes it well-defined), the level 2 procedure's.</summary>
        private ContractMath ContractAsMath()
        {
            var m = _p.Method;
            var requires = _p.Requires.Select(r => new Clause(r, Spec(r.Expr, out var wf), wf, Take())).ToList();
            var ensures = _p.Ensures.Select(e =>
            {
                var math = OldAtEntry(Spec(e.Expr, out var wf));
                return new Clause(e, math, wf.Select(OldAtEntry).ToList(), Take().Select(OldAtEntry).ToList());
            }).ToList();
            _m.Requires = requires.Select(r => new MSpec
            {
                Expr = r.Math,
                At = r.Source.At,
                Check = At(BoogieTranslator.Aux, r.Source.At, $"precondition '{r.Source.At}' of '{m.Name}'", "CSV1001"),
            }).ToList();
            _m.Ensures = ensures.Select(e => new MSpec
            {
                Expr = e.Math,
                At = e.Source.At,
            }).ToList();
            // (the caller's measure is as it was at entry, as Dafny's is: what the body writes before the call doesn't count)
            var decreases = _p.Decreases?.Select(d => (MExpr)Old(Spec(d, out _))).ToList();
            if (_p.FunctionBody != null)
            {
                _m.FunctionBody = Spec(_p.FunctionBody, out _);
            }
            if (_m.FunctionBody != null && _m.ReadsFrame == null)
            {
                _m.InferredReads = InferReads(_m.FunctionBody);
            }
            // (a function's axioms are about every state: what they say can't be of a procedure's snapshots. One whose body
            // reads them is a function of its contract alone: its procedure proves the contract, its calls give it)
            if (_m.FunctionBody != null && _program.OverPredicate(m) == null && _m.FunctionBody.Mentions(Snaps))
            {
                _m.FunctionBody = null;
                _m.InferredReads = null;
            }
            if (_program.OverPredicate(m) == null && _program.IsFunction(m) &&
                requires.Select(r => r.Math).Concat(ensures.Select(e => e.Math)).Any(x => x.Mentions(Snaps)))
            {
                throw new NotTranslated("a function whose contract reads a function over a predicate");
            }
            var invariants = _p.Invariants.ToDictionary(kv => kv.Key, kv => kv.Value.Select(i =>
            {
                var math = OldAtEntry(Spec(i.Expr, out var wf));
                return new Clause(i, math, wf.Select(OldAtEntry).ToList(), Take().Select(OldAtEntry).ToList());
            }).ToList());
            var measures = _p.Measures.ToDictionary(kv => kv.Key, kv => kv.Value.Select(x => Spec(x.Expr, out _)).ToList());
            _facts.Clear();
            return new ContractMath
            {
                Requires = requires,
                Ensures = ensures,
                Decreases = decreases,
                Invariants = invariants,
                Measures = measures,
            };
        }

        /// <summary>
        /// Behavioural subtyping: an override requires no more than what it overrides promises its callers, and changes no
        /// more than that allows (CSV1018); checked at entry, where its own precondition isn't assumed.
        /// </summary>
        private void KeepsToWhatItOverrides()
        {
            var m = _p.Method;
            var decl = m.DeclaringSyntaxReferences[0].GetSyntax();
            MExpr Conjunction(IEnumerable<KExpr> xs)
            {
                MExpr all = MLit.True;
                foreach (var x in xs)
                {
                    var v = Spec(x, out _);
                    _facts.Clear();
                    all = Conj(all, v);
                }
                return all;
            }
            foreach (var (b, reqs) in _p.BaseRequires)
            {
                Assert(Implies(Conjunction(reqs), Conjunction(_p.OwnRequires)),
                    At("CSV1018", decl, $"'{m.Name}' requires more than {b.ContainingType.Name}.{b.Name}, which it overrides, promises its callers"), true);
            }
            foreach (var (b, frame) in _p.BaseFrames.Where(_ => _p.Frame != null))
            {
                var allowed = Conjunction(new[] { frame });
                var r = new MVar("r$");
                Assert(MQuant.ForAll("r$", "Ref", Implies(Sel(_m.Frame, r), Sel(allowed, r))),
                    At("CSV1018", decl, $"Spec.Modifies of '{m.Name}' might not be within that of {b.ContainingType.Name}.{b.Name}, which it overrides"), true);
            }
        }

        /// <summary>
        /// At the first block: the permissions the preconditions give in hand; the frames as of entry; the preconditions
        /// that are functions unfolded once; the immutable objects received holding their invariants.
        /// </summary>
        private void AtEntry(ContractMath contract)
        {
            if (_p.UsesPerm)
            {
                EnterOwned();
                foreach (var r in _rawRequires)
                {
                    Inhale(r, null, null);
                }
                // (what the preconditions say of snapshots: Boogie's requires can't name them)
                Emit(MAssign.Of("psnap$entry", new MVar("psnap")));
                foreach (var r in contract.Requires.Where(r => r.Math.Mentions(Snaps)))
                {
                    Assume(r.Math);
                }
            }
            if (_m.ReadsFrame != null)
            {
                Emit(MAssign.Of("r$entry", _m.ReadsFrame));
            }
            // (a precondition that is a function, Wf(p), of no precondition: its body too, unfolded once, so
            // that its quantifiers are facts the solver uses as they are, not inside the function's equation)
            foreach (var r in contract.Requires)
            {
                _unfoldedFacts.Clear();
                var unfolded = UnfoldOnce(r.Math);
                if (!ReferenceEquals(unfolded, r.Math))
                {
                    foreach (var f in _unfoldedFacts)
                    {
                        Assume(f);
                    }
                    foreach (var c in unfolded.Conjuncts())
                    {
                        Assume(c);
                    }
                }
                _unfoldedFacts.Clear();
            }
            // (immutable objects received hold their invariants: not this, in its constructor or its invariant)
            foreach (var param in _p.Method.Parameters.Where(x => x.RefKind != RefKind.Out))
            {
                ObjectInvariant(new MVar(Local(param)), param.Type);
            }
            if (_p.HasThis && !_p.IsCtor && !DefinesInvariant(_p.Method))
            {
                ObjectInvariant(new MVar("this"), _p.Method.ContainingType);
            }
            if (_m.Frame != null)
            {
                // (the frame as it is on entry, and what was allocated then)
                Emit(MAssign.Of("w$entry", _m.Frame));
                // (a constructor's object was allocated just before it ran: new, as far as its frame is concerned)
                Emit(MAssign.Of("alloc$entry", _p.IsCtor ? Store("$Alloc", new MVar("this"), MLit.False) : new MVar("$Alloc")));
            }
        }

        /// <summary>
        /// At a loop's head: its inferred facts, each a candidate invariant; its invariants well-defined and holding; its
        /// measure taken; where it exchanges permissions, what was held outside it and its invariants' permissions in hand.
        /// </summary>
        private void AtLoopHead(KBlock b, ContractMath contract)
        {
            // (a loop's inferred facts: each an invariant, left out and verified again without where it doesn't hold)
            if (_p.Candidates.TryGetValue(b.Ordinal, out var candidates))
            {
                for (int k = 0; k < candidates.Count; k++)
                {
                    var math = Spec(candidates[k].Expr, out _);
                    _facts.Clear();
                    Emit(MAssert.Of(math, At(Candidate, candidates[k].At, "a loop's inferred fact")));
                }
            }
            if (contract.Invariants.TryGetValue(b.Ordinal, out var invs))
            {
                foreach (var inv in invs)
                {
                    // (what reading the invariant lets one assume, a non-nullable field not null, holds in every state:
                    // assumed on the way in too, as Boogie takes an assume at a loop's head for a free invariant, only
                    // after its havoc, and the invariant's checks on entry need it)
                    foreach (var into in _m.Blocks.Where(x => x.Ordinal < b.Ordinal && x.Jump is KGoto g && g.Targets.Contains(b.Label)))
                    {
                        foreach (var f in inv.Facts)
                        {
                            into.Stmts.Add(MAssume.Of(f));
                        }
                    }
                    foreach (var f in inv.Facts)
                    {
                        Assume(f);
                    }
                    WellDefined(inv.Wf, inv.Source.At, null);
                    Assert(inv.Math, At("CSV1005", inv.Source.At, $"loop invariant '{inv.Source.At}'"));
                }
            }
            if (contract.Measures.TryGetValue(b.Ordinal, out var measure))
            {
                for (int k = 0; k < measure.Count; k++)
                {
                    Emit(MAssign.Of($"m${b.Ordinal}${k}", measure[k]));
                }
            }
            if (Exchanges(b.Ordinal))
            {
                PermissionsAtLoopHead(b.Ordinal);
            }
        }

        /// <summary>A loop that exchanges permissions: what it holds at its head is what was held outside it, and its invariants'.</summary>
        private void PermissionsAtLoopHead(int head)
        {
            Emit(MAssign.Of("perm", new MVar($"l${head}$perm")));
            Emit(MAssign.Of("pinst", new MVar($"l${head}$pinst")));
            Emit(MHavoc.Of("owner"));
            if (_p.UsesFields)
            {
                Emit(MAssign.Of("fperm", new MVar($"l${head}$fperm")));
                Emit(MHavoc.Of("fowner"));
            }
            if (_p.UsesCells)
            {
                Emit(MAssign.Of("cells", new MVar($"l${head}$cells")));
                Emit(MHavoc.Of("cowner"));
            }
            // (the loop havocs the snapshots it changes: an instance's at the head is new already, and the
            // invariants' facts, assumed by Boogie at the head, are of it)
            _atLoopHead = true;
            try
            {
                foreach (var (inv, _) in _rawInvariants.GetValueOrDefault(head) ?? new List<(KExpr, SyntaxNode)>())
                {
                    Inhale(inv, null, null);
                }
            }
            finally
            {
                _atLoopHead = false;
            }
        }

        /// <summary>
        /// A jump: into a loop's head that exchanges permissions, its invariants' permissions given up, and what is held
        /// carried in (or, on a back edge, none used up); on a back edge, the loop's measure gone down.
        /// </summary>
        private void Goto(KBlock b, KGoto g, ContractMath contract)
        {
            foreach (var target in g.Targets)
            {
                if (target.StartsWith("b") && int.TryParse(target.Substring(1), out var into) && Exchanges(into))
                {
                    // the invariant's permissions go round the loop: given up on each way into its head
                    foreach (var (inv, at) in _rawInvariants.GetValueOrDefault(into) ?? new List<(KExpr, SyntaxNode)>())
                    {
                        Exhale(inv, null, at, null);
                    }
                    if (into > b.Ordinal)
                    {
                        Emit(MAssign.Of($"l${into}$perm", new MVar("perm")));
                        Emit(MAssign.Of($"l${into}$pinst", new MVar("pinst")));
                        if (_p.UsesCells)
                        {
                            Emit(MAssign.Of($"l${into}$cells", new MVar("cells")));
                        }
                        if (_p.UsesFields)
                        {
                            Emit(MAssign.Of($"l${into}$fperm", new MVar("fperm")));
                        }
                    }
                    else
                    {
                        Assert(new MLit($"(forall y: Ref :: l${into}$perm[y] ==> perm[y]) && (forall q: Inst :: pinst[q] >= l${into}$pinst[q])" +
                                        (_p.UsesCells ? $" && (forall x$: Ref, i$: int :: cells[x$][i$] >= l${into}$cells[x$][i$])" : "") +
                                        (_p.UsesFields ? $" && (forall y$: Ref, k$: int :: l${into}$fperm[y$][k$] ==> fperm[y$][k$])" : "")),
                            At("CSV1016", _p.LoopSyntax.GetValueOrDefault(into) ?? _p.Method.DeclaringSyntaxReferences[0].GetSyntax(), "the loop body might use up permissions held outside it (only its invariant's go round the loop)"));
                    }
                }
            }
            foreach (var target in g.Targets)
            {
                if (target.StartsWith("b") && int.TryParse(target.Substring(1), out var to) && to <= b.Ordinal && contract.Measures.TryGetValue(to, out var now))
                {
                    var spec = _p.Measures[to];
                    var then = Enumerable.Range(0, now.Count).Select(k => (MExpr)new MVar($"m${to}${k}")).ToList();
                    // (not assumed after: the loop's invariant is checked on this edge whether or not the measure went down)
                    Assert(Lexicographic(now, then), At("CSV1007", spec[0].At.Parent?.Parent ?? spec[0].At,
                        $"loop measure '{string.Join(", ", spec.Select(x => x.At))}' might not decrease or might be negative"), true);
                }
            }
        }
    }
}
