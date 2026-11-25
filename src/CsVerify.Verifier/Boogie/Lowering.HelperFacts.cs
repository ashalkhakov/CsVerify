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

        private static string FactKey(IMethodSymbol m, IParameterSymbol p) =>
            "rows:" + m.OriginalDefinition.ToDisplayString(SymbolDisplayFormat.FullyQualifiedFormat) + "#" + p.Ordinal;

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
