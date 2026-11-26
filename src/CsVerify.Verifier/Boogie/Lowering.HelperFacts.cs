using System.Collections.Generic;
using System.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.FlowAnalysis;
using Microsoft.CodeAnalysis.Operations;
using static CsVerify.Verifier.Boogie.KernelTypes;
using static CsVerify.Verifier.Boogie.KOp;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>
    /// Inferred postconditions of methods that take a query. Such a method is verified once, whatever its body does; of
    /// each query parameter q it is given a ghost input, "q has one row at most" (which holds of every reading of q, and
    /// of what filters, orders and maps it), and a candidate postcondition, proved in its body like a loop's inferred
    /// fact: if so, its result (a list, an array) has one element at most, and is new, no one else's. A caller whose
    /// argument's relational type says one row at most (Lowering.Relations) assumes the result's; where the candidate
    /// doesn't hold, the caller is verified again without it.
    /// </summary>
    internal sealed partial class Lowering
    {
        /// <summary>A method that takes a query and returns a list or an array: its result's type, else null.</summary>
        private static ITypeSymbol SummarizedResult(IMethodSymbol m)
        {
            if (KernelTypes.Ef == null || m.MethodKind != MethodKind.Ordinary || m.IsVirtual || m.IsAbstract || m.IsOverride || m.IsExtern ||
                m.DeclaringSyntaxReferences.Length == 0 || !m.Parameters.Any(p => IsQueryHandle(p.Type)) || m.Parameters.Any(p => p.RefKind != RefKind.None))
            {
                return null;
            }
            var t = m.ReturnType is INamedTypeSymbol { Name: "Task" or "ValueTask", Arity: 1 } task ? task.TypeArguments[0] : m.ReturnType;
            return ElementOf(t) is ITypeSymbol e && InSubset(e) && (IsArray(t) || IsList(t) || IsCollectionInterface(t)) ? t : null;
        }

        private static string FactKey(IMethodSymbol m, IParameterSymbol p) => FactPrefix(m) + p.Ordinal;

        /// <summary>What every fact of a method's query parameters is named by.</summary>
        internal static string FactPrefix(IMethodSymbol m) => "rows:" + m.OriginalDefinition.ToDisplayString(SymbolDisplayFormat.FullyQualifiedFormat) + "#";

        /// <summary>The ghost input of a query parameter of this method: has the query one row at most?</summary>
        private string OneRow(IParameterSymbol p) => Declare("q$one$" + p.Name, KernelTypes.Compilation.GetSpecialType(SpecialType.System_Boolean));

        /// <summary>How many elements a list or an array has.</summary>
        private KExpr CountOf(KExpr x, ITypeSymbol t)
        {
            if (IsArray(t))
            {
                return Length(x);
            }
            var list = IsList(t) ? (INamedTypeSymbol)t : (INamedTypeSymbol)KernelTypes.Compilation.GetTypeByMetadataName("System.Collections.Generic.List`1").Construct(ElementOf(t));
            foreach (var m in ModelsOf(list))
            {
                _p.Models[m.Name] = m;
            }
            if (IsList(t))
            {
                return Sel(SizeMap, x);
            }
            _p.UsesState = true;
            return IfcRead(x, null, ElementOf(t));
        }

        /// <summary>
        /// At a return of a method that takes queries: of each, the candidate that, where it has one row at most, so has
        /// the result; none holds of a result that isn't new here (a list other code may reach can change at an await).
        /// </summary>
        private void HelperCandidates(IOperation returned)
        {
            if (_m == null || SummarizedResult(_m) is not ITypeSymbol t)
            {
                return;
            }
            bool isNew = Unconverted(returned) is ILocalReferenceOperation l && Confined().Contains(l.Local, SymbolEqualityComparer.Default) ||
                         returned.Syntax is ExpressionSyntax made && Fresh(made);
            foreach (var p in _m.Parameters.Where(p => IsQueryHandle(p.Type)))
            {
                KExpr fact = isNew ? Implies(new KVar(OneRow(p)), AndAlso(NotNull(new KVar("result")), Le(CountOf(new KVar("result"), t), KLit.One))) : KLit.False;
                var check = KCheck.Of(fact, Checks.Candidate, returned.Syntax, "a query helper's inferred fact");
                check.Key = FactKey(_m, p);
                Emit(check);
            }
        }

        /// <summary>
        /// After a call of a method that takes queries (its value, once it has returned): its result has one element at
        /// most where an argument has one row at most, by its relational type, or by this method's own ghost input for
        /// a query it was given and passes on.
        /// </summary>
        private void HelperFacts(IInvocationOperation call, KExpr value)
        {
            var m = call.TargetMethod;
            if (value == null || SummarizedResult(m) is not ITypeSymbol t)
            {
                return;
            }
            foreach (var a in call.Arguments.Where(a => a.Parameter != null && IsQueryHandle(a.Parameter.Type) && a.ArgumentKind == ArgumentKind.Explicit))
            {
                KExpr when = RelOf(a.Value) is { AtMostOne: true } ? KLit.True
                    : _m != null && SummarizedResult(_m) != null && GivenRows(a.Value) is IParameterSymbol given ? new KVar(OneRow(given)) : null;
                if (when == null)
                {
                    continue;
                }
                Emit(new KFactUse
                {
                    Cond = Implies(when, AndAlso(NotNull(value), Le(CountOf(value, t), KLit.One))),
                    Key = FactKey(m, a.Parameter.OriginalDefinition),
                    At = call.Syntax,
                });
            }
        }

        // ------------------------------------------------------------------ a computed list's count

        /// <summary>A list, an array or a list through an interface, of the subset's elements.</summary>
        private static bool Listed(ITypeSymbol t) => t != null && ElementOf(t) is ITypeSymbol e && InSubset(e) && (IsArray(t) || IsList(t) || IsCollectionInterface(t));

        private static readonly System.Runtime.CompilerServices.ConditionalWeakTable<IMethodSymbol, List<ISymbol>> _countSources =
            new System.Runtime.CompilerServices.ConditionalWeakTable<IMethodSymbol, List<ISymbol>>();

        /// <summary>
        /// A member of one expression that returns a list (public IReadOnlyList&lt;Guid&gt; Items => lines.Select(l => l.Item).ToList()):
        /// it can state no contract, and where it makes the list it is no function. The collections its expression
        /// names, a field of its object or a parameter: of each, a candidate postcondition, that the result has as many
        /// elements, proved in its body as a loop's inferred fact is and assumed where it is called while it holds.
        /// </summary>
        private static List<ISymbol> CountSources(IMethodSymbol m) => _countSources.GetValue(m.OriginalDefinition, def =>
        {
            var none = new List<ISymbol>();
            if (def.MethodKind is not (MethodKind.Ordinary or MethodKind.PropertyGet) || def.IsAbstract || def.IsVirtual || def.IsOverride || def.IsExtern || def.IsAsync ||
                def.IsGenericMethod || def.ContainingType.IsGenericType || def.Parameters.Any(p => p.RefKind != RefKind.None) || !Listed(def.ReturnType) ||
                (def.AssociatedSymbol ?? def).DeclaringSyntaxReferences.Length != 1)
            {
                return none;
            }
            var body = (def.AssociatedSymbol ?? def).DeclaringSyntaxReferences[0].GetSyntax() switch
            {
                PropertyDeclarationSyntax p => p.ExpressionBody?.Expression ?? p.AccessorList?.Accessors.FirstOrDefault(a => a.Keyword.Text == "get")?.ExpressionBody?.Expression,
                MethodDeclarationSyntax d => d.ExpressionBody?.Expression,
                _ => null,
            };
            if (body == null || KernelTypes.Compilation == null)
            {
                return none;
            }
            var model = CsVerify.Analyzers.Compilations.ModelOf(KernelTypes.Compilation, body.SyntaxTree);
            return body.DescendantNodesAndSelf().OfType<SimpleNameSyntax>()
                // (a field of this: named alone, or this.f)
                .Where(n => !(n.Parent is MemberAccessExpressionSyntax ma && ma.Name == n && !(ma.Expression is ThisExpressionSyntax)))
                .Select(n => model.GetSymbolInfo(n).Symbol?.OriginalDefinition)
                .Where(s => s is IParameterSymbol p && SymbolEqualityComparer.Default.Equals(p.ContainingSymbol, def) && Listed(p.Type) ||
                            (s is IFieldSymbol || s is IPropertySymbol) && !s.IsStatic && IsField(s) && SymbolEqualityComparer.Default.Equals(s.ContainingType, def.ContainingType) && Listed(FieldType(s)))
                .Distinct(SymbolEqualityComparer.Default).ToList();
        });

        private static string CountKey(IMethodSymbol m, ISymbol source) => FactPrefix(m) + "count:" + source.Name;

        /// <summary>The result has as many elements as the collection, where that isn't null.</summary>
        private KExpr SameCount(KExpr result, ITypeSymbol resultType, KExpr source, ITypeSymbol sourceType) =>
            Implies(NotNull(source), AndAlso(NotNull(result), Eq(CountOf(result, resultType), CountOf(source, sourceType))));

        /// <summary>At the return of such a member: of each collection it names, the candidate that its result has as many elements.</summary>
        private void CountCandidates(IOperation returned)
        {
            if (_m == null || _contract.IsPure || _contract.Ensures.Count > 0)
            {
                return;
            }
            foreach (var s in CountSources(_m))
            {
                KExpr source = s is IParameterSymbol p ? new KVar(Local(p)) : new KField { Field = s, Instance = new KVar("this"), OnThis = true, At = returned.Syntax };
                var check = KCheck.Of(SameCount(new KVar("result"), _m.ReturnType, source, s is IParameterSymbol sp ? sp.Type : FieldType(s)),
                    Checks.Candidate, returned.Syntax, "a computed list's inferred count");
                check.Key = CountKey(_m, s);
                Emit(check);
            }
        }

        /// <summary>After a call of such a member: its result has as many elements as each collection whose candidate holds.</summary>
        private void CountFacts(IMethodSymbol callee, KExpr receiver, bool onThis, KExpr[] args, string result, SyntaxNode at)
        {
            if (result == null || _awaiting || _contractOf?.Invoke(callee) is not Contract c || c.IsPure || c.Ensures.Count > 0)
            {
                return;
            }
            foreach (var s in CountSources(callee))
            {
                KExpr source = s is IParameterSymbol p ? (p.Ordinal < args.Length ? args[p.Ordinal] : null)
                    : receiver == null ? null : new KField { Field = s, Instance = receiver, OnThis = onThis, NoNull = true, At = at };
                if (source == null)
                {
                    continue;
                }
                Emit(new KFactUse
                {
                    Cond = SameCount(new KVar(result), callee.OriginalDefinition.ReturnType, source, s is IParameterSymbol sp ? sp.Type : FieldType(s)),
                    Key = CountKey(callee, s),
                    At = at,
                });
            }
        }

        /// <summary>The query parameter of this method a query reads, through operators that keep, drop or map its rows one to one; else null.</summary>
        private IParameterSymbol GivenRows(IOperation op)
        {
            for (int depth = 0; depth < 64 && op != null; depth++)
            {
                op = Unconverted(op);
                switch (op)
                {
                    case IParameterReferenceOperation p when IsQueryHandle(p.Type) && SymbolEqualityComparer.Default.Equals(p.Parameter.ContainingSymbol, _m) && !_assigned.ContainsKey(p.Parameter):
                        return p.Parameter;
                    case ILocalReferenceOperation l when Initializer(l) is IOperation init:
                        op = init;
                        continue;
                    case IFlowCaptureReferenceOperation c when _captured.TryGetValue(c.Id, out var cv):
                        op = cv;
                        continue;
                    case IInvocationOperation c when (IsQueryableMethod(c.TargetMethod) || IsEfMethod(c.TargetMethod)) && c.Arguments.Length > 0 &&
                                                     c.TargetMethod.Name is "Where" or "OrderBy" or "OrderByDescending" or "ThenBy" or "ThenByDescending" or "Select" or "Distinct" or "Skip" or "Take" or
                                                         "AsNoTracking" or "AsNoTrackingWithIdentityResolution" or "AsTracking" or "Include" or "ThenInclude" or "AsSplitQuery" or "AsSingleQuery" or
                                                         "IgnoreQueryFilters" or "IgnoreAutoIncludes" or "TagWith" or "TagWithCallSite":
                        op = c.Arguments.OrderBy(a => a.Parameter.Ordinal).First().Value;
                        continue;
                    default:
                        return null;
                }
            }
            return null;
        }
    }
}
