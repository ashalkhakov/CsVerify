using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>
    /// What a failure's unknown values come from, for the library report: a library member
    /// without a contract ("library M"), a method of the program without postconditions ("source M"), a loop without
    /// invariants. Each variable has the causes of the unknown values it was made from (a call's result, what such a
    /// loop assigns), and those of the variables its values were computed from; a check, those of its condition's.
    /// </summary>
    internal sealed partial class Lowering
    {
        /// <summary>What the values made now are charged to (a call being lowered), if anything.</summary>
        private string _cause;

        /// <summary>The loop heads with invariants the program wrote (not the kernel's own).</summary>
        private readonly HashSet<int> _writtenInvariants = new HashSet<int>();

        /// <summary>The variables in an expression (its KVars), by walking its parts.</summary>
        public static IEnumerable<string> VarsIn(KExpr e)
        {
            switch (e)
            {
                case null: yield break;
                case KVar v:
                    yield return v.Name;
                    yield break;
                case KExpr x:
                    foreach (var f in Parts(x.GetType()))
                    {
                        switch (f.GetValue(x))
                        {
                            case KExpr k:
                                foreach (var n in VarsIn(k))
                                {
                                    yield return n;
                                }
                                break;
                            case IEnumerable<KExpr> ks:
                                foreach (var k in ks)
                                {
                                    foreach (var n in VarsIn(k))
                                    {
                                        yield return n;
                                    }
                                }
                                break;
                        }
                    }
                    yield break;
            }
        }

        private static readonly Dictionary<System.Type, FieldInfo[]> _parts = new Dictionary<System.Type, FieldInfo[]>();

        private static FieldInfo[] Parts(System.Type t)
        {
            lock (_parts)
            {
                if (_parts.TryGetValue(t, out var known))
                {
                    return known;
                }
                return _parts[t] = t.GetFields(BindingFlags.Public | BindingFlags.Instance)
                    .Where(f => typeof(KExpr).IsAssignableFrom(f.FieldType) || typeof(IEnumerable<KExpr>).IsAssignableFrom(f.FieldType)).ToArray();
            }
        }

        private void Cause(string var, string cause)
        {
            if (var == null || cause == null)
            {
                return;
            }
            if (!_p.Causes.TryGetValue(var, out var set))
            {
                _p.Causes[var] = set = new HashSet<string>();
            }
            set.Add(cause);
        }

        /// <summary>A statement emitted: what its variables are made from.</summary>
        private void Track(KStmt s)
        {
            switch (s)
            {
                case KAssign a:
                    if (!_p.Deps.TryGetValue(a.Var, out var deps))
                    {
                        _p.Deps[a.Var] = deps = new HashSet<string>();
                    }
                    deps.UnionWith(VarsIn(a.Value));
                    break;
                case KHavoc h:
                    Cause(h.Var, _cause);
                    break;
                case KCall c when c.Result != null:
                    Cause(c.Result, _cause);
                    break;
            }
        }

        /// <summary>What a call's unknown values are charged to: null where nothing is.</summary>
        private string CallCause(IMethodSymbol m)
        {
            if (SpecSymbols.IsSpecClass(m.ContainingType) || m.ContainingNamespace?.ToDisplayString()?.StartsWith("CsVerify") == true)
            {
                return null;
            }
            if (m.MethodKind == MethodKind.Constructor && m.ContainingType.SpecialType == SpecialType.System_Object)
            {
                return null;
            }
            if (m.IsImplicitlyDeclared && m.ContainingType.Locations.Any(l => l.IsInSource))
            {
                return null;
            }
            var c = _contractOf?.Invoke(m.OriginalDefinition);
            if (m.DeclaringSyntaxReferences.Length == 0 && !(c?.OfDelegate ?? false))
            {
                return "library " + m.OriginalDefinition.ToDisplayString();
            }
            if (c == null || c.IsStub || c.IsPure || c.IsLemma || c.Ensures.Count > 0 || c.ThrowEnsures.Count > 0)
            {
                return null;
            }
            return "source " + m.OriginalDefinition.ToDisplayString();
        }

        /// <summary>The library's members the method's code calls, for the report.</summary>
        private void LibraryCalls()
        {
            if (_p.Result == null || _decl == null || _model == null || !(_model.GetOperation(_decl) is IOperation root))
            {
                return;
            }
            foreach (var call in root.DescendantsAndSelf().OfType<Microsoft.CodeAnalysis.Operations.IInvocationOperation>())
            {
                if (!InSpec(call.Syntax) && CallCause(call.TargetMethod) is string lib && lib.StartsWith("library "))
                {
                    lock (_p.Result.LibraryCalls) _p.Result.LibraryCalls.Add((lib.Substring("library ".Length), call.Syntax.SyntaxTree.FilePath + ":" + call.Syntax.SpanStart));
                }
            }
        }

        /// <summary>At the end: what a loop without invariants assigns is charged to it.</summary>
        private void LoopCauses()
        {
            foreach (var (h, last) in _p.LoopBodies)
            {
                if (_writtenInvariants.Contains(h))
                {
                    continue;
                }
                foreach (var b in _p.Blocks.Where(x => x.Ordinal >= h && x.Ordinal <= last))
                {
                    foreach (var a in b.Stmts.OfType<KAssign>())
                    {
                        Cause(a.Var, "a loop without invariants");
                    }
                }
            }
        }
    }
}
