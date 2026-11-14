using System.Collections.Generic;
using System.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Operations;
using static CsVerify.Verifier.Boogie.KernelTypes;
using static CsVerify.Verifier.Boogie.KOp;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>
    /// What code started here may race on (StaticChecks.Async): the fields and arrays
    /// each of two things running at once uses, from their source and their callees' (what's under a lock left out), on
    /// the objects they're given as far as can be told (this, a parameter or a local that stays the same). Where one
    /// writes what the other uses, on what may be one object, that could race (CSV1900, a warning): "may be one object"
    /// is a check of Boogie's whose failure is the warning, of the objects' values where the second starts.
    /// </summary>
    internal sealed partial class Lowering
    {
        private sealed class Effects
        {
            public string Name;
            public readonly List<(ISymbol field, KExpr on)> Writes = new List<(ISymbol, KExpr)>();
            public readonly List<(ISymbol field, KExpr on)> Reads = new List<(ISymbol, KExpr)>();
            public readonly List<KExpr> WrittenArrays = new List<KExpr>();
            public readonly List<KExpr> UsedArrays = new List<KExpr>();
            /// <summary>It has permissions for all it does to arrays, as is proved: so it stays out of what others hold.</summary>
            public bool Covered;
        }

        private sealed class EffectScope
        {
            public System.Func<ISymbol, KExpr> Of = _ => null;
            public KExpr This;
        }

        /// <summary>The objects in this method's variables, those that stay the same (a variable of a loop's body is another object next round, but to what captured it).</summary>
        private EffectScope ScopeHere(bool capturing) => new EffectScope
        {
            This = _p.HasThis ? new KVar("this") : null,
            Of = s =>
            {
                if (!StartedDelegates.StaysTheSame(s, _decl, _model) || !capturing && DeclaredInALoop(s))
                {
                    return null;
                }
                if (s is IParameterSymbol p && p.ContainingSymbol is IMethodSymbol pm && SymbolEqualityComparer.Default.Equals(pm.OriginalDefinition, _m.OriginalDefinition) && IsRef(p.Type) && p.RefKind == RefKind.None)
                {
                    return new KVar(Local(_m.Parameters[p.Ordinal]));
                }
                if (s is ILocalSymbol l && IsRef(l.Type) && l.RefKind == RefKind.None && _decl.Span.Contains(l.DeclaringSyntaxReferences.FirstOrDefault()?.Span ?? default))
                {
                    return new KVar(Declare(Local(l), l.Type));
                }
                return null;
            },
        };

        private static bool DeclaredInALoop(ISymbol s) =>
            s.DeclaringSyntaxReferences.Any(r => r.GetSyntax().AncestorsAndSelf().TakeWhile(a => !(a is MemberDeclarationSyntax)).Any(a => a is ForStatementSyntax || a is WhileStatementSyntax || a is DoStatementSyntax || a is CommonForEachStatementSyntax));

        private static string KeyOf(KExpr o) => (o as KVar)?.Name ?? "";

        private Effects EffectsOfMethod(IMethodSymbol m)
        {
            var e = new Effects { Name = m.Name };
            AddEffects(m, e, new HashSet<string>(), new EffectScope());
            return e;
        }

        /// <summary>What a call does, on the objects it's given.</summary>
        private Effects EffectsOfCall(IInvocationOperation call, bool capturing = false)
        {
            var e = new Effects { Name = call.TargetMethod.Name };
            var seen = new HashSet<string>();
            if (call.Syntax is InvocationExpressionSyntax syntax)
            {
                AddCallEffects(call.TargetMethod, syntax, _model, ScopeHere(capturing), e, seen);
            }
            else
            {
                AddEffects(call.TargetMethod, e, seen, new EffectScope());
            }
            return e;
        }

        /// <summary>What a piece of this method's source uses, itself and through its calls.</summary>
        private Effects EffectsOfCode(SyntaxNode code, bool capturing, SyntaxNode except = null)
        {
            var e = new Effects { Name = "this method" };
            AddEffects(code, _model, e, new HashSet<string>(), except, ScopeHere(capturing));
            return e;
        }

        /// <summary>What a delegate handed to a task or a thread may use; null if it can't be told which code it is.</summary>
        private Effects EffectsOfDelegate(SyntaxNode d)
        {
            if (d is AnonymousFunctionExpressionSyntax)
            {
                var e = EffectsOfCode(d, capturing: true);
                e.Name = "the delegate";
                return e;
            }
            if (d != null && _model.GetOperation(d) is IOperation op)
            {
                var u = Unconverted(op);
                if (u is IDelegateCreationOperation dc)
                {
                    u = Unconverted(dc.Target);
                }
                if (u is IMethodReferenceOperation mr && mr.Method.DeclaringSyntaxReferences.Length > 0)
                {
                    return EffectsOfMethod(mr.Method);
                }
            }
            return null;
        }

        /// <summary>What this method does while what it started goes on: from there to where it is awaited or joined, as far as can be told.</summary>
        private Effects EffectsAlongside(SyntaxNode start, string task, SyntaxNode except, bool covered)
        {
            var e = new Effects
            {
                Name = "this method",
                Covered = covered,
            };
            var seen = new HashSet<string>();
            var scope = ScopeHere(capturing: false);
            foreach (var code in StartedDelegates.CodeAlongside(start, task, _decl, _model))
            {
                AddEffects(code, _model, e, seen, except, scope);
            }
            return e;
        }

        private static bool MentionsCells(Contract c) =>
            c.Requires.Concat(c.Ensures.Select(x => x.Expr)).Any(x => x != null && x.DescendantsAndSelf().Any(CellAcc));

        private static bool CellAcc(IOperation o) =>
            o is IInvocationOperation inv && CsVerify.Analyzers.SpecSymbols.IsSpecClass(inv.TargetMethod.ContainingType) && (inv.TargetMethod.Name == "Acc" || inv.TargetMethod.Name == "AccRead") &&
            inv.Arguments.Length > 0 && Unconverted(inv.Arguments[0].Value).Type is IArrayTypeSymbol;

        private void AddEffects(IMethodSymbol m, Effects e, HashSet<string> seen, EffectScope scope)
        {
            var c = _contractOf?.Invoke(m.OriginalDefinition);
            if (m.OriginalDefinition.DeclaringSyntaxReferences.Length > 0 && c != null && c.HasSource && MentionsCells(c))
            {
                e.Covered = true;
            }
            if (!seen.Add(m.OriginalDefinition.ToDisplayString() + "/" + KeyOf(scope.This) + "/" + string.Join(",", m.OriginalDefinition.Parameters.Select(p => KeyOf(scope.Of(p))))))
            {
                return;
            }
            var refs = m.OriginalDefinition.DeclaringSyntaxReferences;
            if (refs.Length == 0)
            {
                // (the library's: what a contract says it does; for the rest there's nothing to go on)
                if (m.Name == "Run" && m.ContainingType?.ToDisplayString() == "System.Threading.Tasks.Task" || c == null || !c.IsStub)
                {
                    return;
                }
                if (KernelTypes.FieldWrites != null)
                {
                    e.Writes.AddRange(KernelTypes.FieldWrites(m).Select(x => (x, (KExpr)null)));
                }
                if (KernelTypes.FieldReads != null)
                {
                    e.Reads.AddRange(KernelTypes.FieldReads(m).Select(x => (x, (KExpr)null)));
                }
                if (KernelTypes.MayWriteHeap?.Invoke(m) == true)
                {
                    e.WrittenArrays.Add(null);
                }
                if (KernelTypes.MayTouchArrays?.Invoke(m) == true)
                {
                    e.UsedArrays.Add(null);
                }
                return;
            }
            foreach (var r in refs)
            {
                AddEffects(r.GetSyntax(), KernelTypes.Compilation.GetSemanticModel(r.SyntaxTree), e, seen, null, scope);
            }
        }

        /// <summary>The object an expression is, where it can be told.</summary>
        private static KExpr ObjectOf(ExpressionSyntax x, SemanticModel model, EffectScope scope)
        {
            while (x is ParenthesizedExpressionSyntax p)
            {
                x = p.Expression;
            }
            if (x == null || x is ThisExpressionSyntax)
            {
                return scope.This;
            }
            return x is IdentifierNameSyntax && (model.GetSymbolInfo(x).Symbol is ILocalSymbol || model.GetSymbolInfo(x).Symbol is IParameterSymbol) ? scope.Of(model.GetSymbolInfo(x).Symbol) : null;
        }

        private void AddCallEffects(IMethodSymbol callee, InvocationExpressionSyntax call, SemanticModel model, EffectScope scope, Effects e, HashSet<string> seen)
        {
            var given = new Dictionary<ISymbol, KExpr>(SymbolEqualityComparer.Default);
            var definition = callee.OriginalDefinition;
            if (model.GetOperation(call) is IInvocationOperation operation)
            {
                foreach (var a in operation.Arguments)
                {
                    if (a.Parameter != null && a.Syntax is ArgumentSyntax arg && a.Parameter.RefKind == RefKind.None &&
                        definition.Parameters.ElementAtOrDefault(a.Parameter.Ordinal) is IParameterSymbol p && ObjectOf(arg.Expression, model, scope) is KExpr t &&
                        definition.DeclaringSyntaxReferences.All(r => StartedDelegates.StaysTheSame(p, r.GetSyntax(), KernelTypes.Compilation.GetSemanticModel(r.SyntaxTree))))
                    {
                        given[p] = t;
                    }
                }
            }
            var receiver = definition.IsStatic ? null : call.Expression is MemberAccessExpressionSyntax ma ? ObjectOf(ma.Expression, model, scope) : scope.This;
            AddEffects(callee, e, seen, new EffectScope
            {
                This = receiver,
                Of = s => given.TryGetValue(s, out var t) ? t : null,
            });
        }

        /// <summary>What's done under a lock doesn't count, even to what isn't a field (a dictionary's contents): that is what a lock is for.</summary>
        private void AddEffects(SyntaxNode code, SemanticModel model, Effects e, HashSet<string> seen, SyntaxNode except, EffectScope scope)
        {
            var locks = KernelTypes.Locks;
            bool Enter(SyntaxNode x) => x != except && !(x is LockStatementSyntax) && !(x is TryStatementSyntax t && locks?.GateOfTry(t, model) != null) &&
                                        !(x is UsingStatementSyntax u && locks?.GateOfUsing(u, model) != null) && !(x is StatementSyntax st && st.Parent is BlockSyntax b && locks != null && locks.UsingsBefore(st, b, model).Any());
            if (code == except)
            {
                return;
            }
            foreach (var n in code.DescendantNodes(Enter))
            {
                switch (n)
                {
                    case InvocationExpressionSyntax call when model.GetSymbolInfo(call).Symbol is IMethodSymbol callee:
                        AddCallEffects(callee, call, model, scope, e, seen);
                        break;
                    case SimpleNameSyntax name when !(name.Parent is NameColonSyntax) && !(name.Parent is NameEqualsSyntax):
                    {
                        var symbol = model.GetSymbolInfo(name).Symbol;
                        if (symbol is IPropertySymbol stubbed && stubbed.DeclaringSyntaxReferences.Length == 0)
                        {
                            symbol = LockGuards.IsWriteTarget(name) ? stubbed.SetMethod : stubbed.GetMethod;
                        }
                        if (symbol is IMethodSymbol accessed)
                        {
                            if (!(name.Parent is InvocationExpressionSyntax) && !(name.Parent is MemberAccessExpressionSyntax m0 && m0.Name == name && m0.Parent is InvocationExpressionSyntax))
                            {
                                AddEffects(accessed, e, seen, new EffectScope());
                            }
                        }
                        else if (symbol != null && FieldEffects.IsHeapField(symbol))
                        {
                            ExpressionSyntax whole = name.Parent is MemberAccessExpressionSyntax ma && ma.Name == name ? ma : name;
                            var on = symbol.IsStatic ? null : whole is MemberAccessExpressionSyntax owner ? ObjectOf(owner.Expression, model, scope) : scope.This;
                            (LockGuards.IsWriteTarget(whole) ? e.Writes : e.Reads).Add((FieldEffects.Key(symbol), on));
                        }
                        break;
                    }
                    case ElementAccessExpressionSyntax ea when model.GetTypeInfo(ea.Expression).Type is IArrayTypeSymbol:
                    {
                        var array = ObjectOf(ea.Expression, model, scope);
                        e.UsedArrays.Add(array);
                        if (LockGuards.IsWriteTarget(ea))
                        {
                            e.WrittenArrays.Add(array);
                        }
                        break;
                    }
                    case ElementAccessExpressionSyntax ea when model.GetSymbolInfo(ea).Symbol is IPropertySymbol ix:
                        // (d[k] = v: a library's indexer)
                        if ((LockGuards.IsWriteTarget(ea) ? ix.SetMethod : ix.GetMethod) is IMethodSymbol accessor)
                        {
                            AddEffects(accessor, e, seen, new EffectScope());
                        }
                        break;
                }
            }
        }

        /// <summary>Two objects told apart: both known, and not equal (a condition, false where either isn't known).</summary>
        private static KExpr Apart(KExpr x, KExpr y) => x == null || y == null ? KLit.False : KeyOf(x) == KeyOf(y) && KeyOf(x) != "" ? KLit.False : Ne(x, y);

        private static KExpr All(IEnumerable<KExpr> parts) => parts.DefaultIfEmpty(KLit.True).Aggregate((a, b) => AndAlso(a, b));

        /// <summary>The unguarded fields one writes and the other uses, with the condition that each such pair is on two objects.</summary>
        private static List<(ISymbol field, KExpr apart)> FieldRaces(Effects writer, Effects other)
        {
            var found = new List<(ISymbol, KExpr)>();
            var locks = KernelTypes.Locks;
            foreach (var (field, on) in writer.Writes)
            {
                if (locks?.GuardOf(field) == null && !Atomics.IsAtomic(field) && !(locks?.IsFlag(field) ?? false))
                {
                    foreach (var x in other.Writes.Concat(other.Reads).Where(x => SymbolEqualityComparer.Default.Equals(x.field, field)))
                    {
                        found.Add((field, Apart(on, x.on)));
                    }
                }
            }
            return found;
        }

        private static KExpr ArraysApart(Effects writer, Effects other) =>
            All(writer.WrittenArrays.SelectMany(w => other.UsedArrays.Select(u => Apart(w, u))));

        /// <summary>
        /// Two things running at once, where one writes what the other uses, on what may be one object: a warning (each is
        /// proved as if alone). Unless <paramref name="unless"/> holds there (the other was awaited by then).
        /// </summary>
        private void WarnIfMayRace(SyntaxNode at, Effects a, Effects b, KExpr unless = null)
        {
            if (a == null || b == null || at == null)
            {
                return;
            }
            var fields = FieldRaces(a, b).Concat(FieldRaces(b, a)).ToList();
            var fieldsApart = All(fields.Select(f => f.apart));
            KExpr Or(KExpr c) => unless == null ? c : OrElse(unless, c);
            if (fields.Count > 0)
            {
                Emit(KCheck.Of(
                    Or(fieldsApart),
                    Warning,
                    at,
                    notAssumedAfter: true,
                    message: $"'{a.Name}' and '{b.Name}' run at once, and '{fields[0].field.Name}' is written by one and used by the other: on one object, that could race, and each is proved as if alone"));
            }
            if (a.Covered && b.Covered)
            {
                return;
            }
            if (!a.WrittenArrays.Any(w => b.UsedArrays.Any()) && !b.WrittenArrays.Any(w => a.UsedArrays.Any()))
            {
                return;
            }
            // (as an else of the fields': warned of only where those are apart)
            Emit(KCheck.Of(
                Or(OrElse(Not(fieldsApart), AndAlso(ArraysApart(a, b), ArraysApart(b, a)))),
                Warning,
                at,
                notAssumedAfter: true,
                message: $"'{a.Name}' and '{b.Name}' run at once, and one writes arrays the other may use: on one array, that could race, and each is proved as if alone"));
        }

        /// <summary>The id of a check whose failure is a warning (CSV1900, not an error), never assumed after.</summary>
        public const string Warning = "WARN";

        /// <summary>What goes on running after this method (a thread never joined): a warning of what it writes.</summary>
        private void Detached(SyntaxNode at, Effects effects)
        {
            if (at == null)
            {
                return;
            }
            string message = null;
            var locks = KernelTypes.Locks;
            if (effects == null)
            {
                message = "this runs a delegate that can't be told, and keeps running after this method: what it does to state no lock guards isn't looked at";
            }
            else if (effects.Writes.Select(x => x.field).FirstOrDefault(x => locks?.GuardOf(x) == null && !Atomics.IsAtomic(x) && !(locks?.IsFlag(x) ?? false)) is ISymbol unguarded)
            {
                message = $"this keeps running after this method, and writes '{unguarded.Name}', which no lock guards: it could race with whatever uses it, and every method is proved as if nothing did";
            }
            else if (effects.WrittenArrays.Count > 0 && !effects.Covered)
            {
                message = "this keeps running after this method, and writes arrays: it could race with whatever uses them, and every method is proved as if nothing did";
            }
            if (message != null)
            {
                _p.Warnings.Add(new VerificationDiagnostic("CSV1900", false, message, at.GetLocation().GetLineSpan()));
            }
        }

        /// <summary>What a task or thread started here may race on: against those started before and not yet awaited, and against this method alongside it.</summary>
        private void RacesAtStart(SyntaxNode at, Effects effects, string task, SyntaxNode except, bool alongside)
        {
            foreach (var other in _tasks.Values.Where(t => t.Effects != null && t.At != at))
            {
                WarnIfMayRace(at, effects, other.Effects, new KVar(other.Awaited));
            }
            if (alongside)
            {
                WarnIfMayRace(at, effects, EffectsAlongside(at, task, except, effects?.Covered ?? false));
            }
        }
    }
}
