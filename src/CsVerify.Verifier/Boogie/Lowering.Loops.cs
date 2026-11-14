using System.Collections.Generic;
using System.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.FlowAnalysis;
using Microsoft.CodeAnalysis.Operations;
using static CsVerify.Verifier.Boogie.KernelTypes;
using static CsVerify.Verifier.Boogie.KOp;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>Loops: their heads, invariants and measures, and the facts inferred for loops without invariants.</summary>
    internal sealed partial class Lowering
    {
        /// <summary>The blocks a loop is entered at other than its head (from before it).</summary>
        private readonly HashSet<int> _secondEntries = new HashSet<int>();

        // ------------------------------------------------------------------ loops

        /// <summary>The blocks a later block goes back to: loop heads.</summary>
        private static HashSet<int> LoopHeads(ControlFlowGraph cfg)
        {
            var heads = new HashSet<int>();
            foreach (var b in cfg.Blocks)
            {
                foreach (var s in new[] { b.FallThroughSuccessor, b.ConditionalSuccessor })
                {
                    if (s?.Destination != null && s.Destination.Ordinal <= b.Ordinal)
                    {
                        heads.Add(s.Destination.Ordinal);
                    }
                }
            }
            return heads;
        }

        /// <summary>The innermost loop a block is in: the latest head before it whose back edge comes from it or after it; -1 if none.</summary>
        private static int HeadOf(ControlFlowGraph cfg, HashSet<int> heads, BasicBlock b) =>
            heads.Where(h => h <= b.Ordinal && cfg.Blocks.Any(x => x.Ordinal >= b.Ordinal &&
                new[] { x.FallThroughSuccessor, x.ConditionalSuccessor }.Any(s => s?.Destination?.Ordinal == h))).DefaultIfEmpty(-1).Max();

        private readonly List<(int head, string var, KExpr value)> _entryValues = new List<(int, string, KExpr)>();

        /// <summary>
        /// A for, while or do loop without invariants: the facts inferred for it (StaticChecks.LoopFacts),
        /// as Houdini's candidates: from its condition (i &lt; n suggests i &lt;= n at the head), and for each integer in it,
        /// that it never goes below, or above, its value on entry. Those that hold on entry and at every back edge are kept.
        /// </summary>
        private void LoopFacts(HashSet<int> heads)
        {
            foreach (var h in heads.OrderBy(x => x))
            {
                if (_p.Invariants.ContainsKey(h) || !_p.LoopSyntax.TryGetValue(h, out var loop))
                {
                    continue;
                }
                var condition = loop switch { ForStatementSyntax f => f.Condition, WhileStatementSyntax w => w.Condition, DoStatementSyntax d => d.Condition, _ => null };
                if (condition == null || !(_model.GetOperation(condition) is IOperation cond))
                {
                    continue;
                }
                var comparisons = new List<IBinaryOperation>();
                void Conjuncts(IOperation o)
                {
                    o = Unconverted(o);
                    if (o is IBinaryOperation { OperatorKind: BinaryOperatorKind.ConditionalAnd } and)
                    {
                        Conjuncts(and.LeftOperand);
                        Conjuncts(and.RightOperand);
                    }
                    else if (o is IBinaryOperation b && b.OperatorMethod == null && IsIntegral(Unconverted(b.LeftOperand).Type) && IsIntegral(Unconverted(b.RightOperand).Type))
                    {
                        comparisons.Add(b);
                    }
                }
                Conjuncts(cond);
                var facts = new List<KSpec>();
                var paths = new List<IOperation>();
                try
                {
                    foreach (var b in comparisons)
                    {
                        var (l, r) = (Unconverted(b.LeftOperand), Unconverted(b.RightOperand));
                        foreach (var side in new[] { l, r })
                        {
                            if (!side.ConstantValue.HasValue && !paths.Any(p => p.Syntax.IsEquivalentTo(side.Syntax)))
                            {
                                paths.Add(side);
                            }
                        }
                        var (lv, rv) = (Spec(l, null), Spec(r, null));
                        KExpr Offset(int k) => k == 0 ? rv : Plus(rv, new KLit(k < 0 ? $"(-{-k})" : k.ToString()));
                        var made = b.OperatorKind switch
                        {
                            BinaryOperatorKind.LessThan => new[] { Le(lv, Offset(0)) },
                            BinaryOperatorKind.LessThanOrEqual => new[] { Le(lv, Offset(1)) },
                            BinaryOperatorKind.GreaterThan => new[] { Ge(lv, Offset(0)) },
                            BinaryOperatorKind.GreaterThanOrEqual => new[] { Ge(lv, Offset(-1)) },
                            BinaryOperatorKind.NotEquals => new[] { Le(lv, Offset(0)), Ge(lv, Offset(0)) },
                            _ => new KOp[0],
                        };
                        facts.AddRange(made.Select(x => KSpec.Of(x, loop)));
                    }
                    // (what the loop changes: an integer that moves one way)
                    foreach (var path in paths.Where(p => !(p is ILiteralOperation)))
                    {
                        var v = Spec(path, null);
                        var entry = Declare($"lf${h}${_entryValues.Count}", _model.Compilation.GetSpecialType(SpecialType.System_Int64));
                        _entryValues.Add((h, entry, v));
                        facts.Add(KSpec.Of(Ge(v, new KVar(entry)), loop));
                        facts.Add(KSpec.Of(Le(v, new KVar(entry)), loop));
                    }
                }
                catch (NotTranslated)
                {
                    continue;
                }
                if (facts.Count > 0)
                {
                    _p.Candidates[h] = facts;
                }
            }
        }

        /// <summary>Each Spec.Invariant and loop Spec.Decreases, at the head of the innermost loop it is in.</summary>
        private void ReadLoopSpecs(ControlFlowGraph cfg, HashSet<int> heads)
        {
            foreach (var b in cfg.Blocks)
            {
                foreach (var op in b.Operations)
                {
                    if (SpecCall(op, "Decreases") is IInvocationOperation dec && HeadOf(cfg, heads, b) is int h && h >= 0)
                    {
                        var whole = _model.GetOperation(dec.Syntax) as IInvocationOperation ?? throw new NotTranslated("a measure without its operation");
                        var measure = new List<KSpec>();
                        for (int k = 0; k < whole.Arguments.Length; k++)
                        {
                            measure.Add(KSpec.Of(Measure(whole.Arguments[k].Value), whole.Arguments[k].Value.Syntax));
                            Declare($"m${h}${k}", IsData(whole.Arguments[k].Value.Type) ? _model.Compilation.GetSpecialType(SpecialType.System_Int32) : whole.Arguments[k].Value.Type);
                        }
                        _p.Measures[h] = measure;
                    }
                    if (SpecCall(op, "Invariant") is IInvocationOperation inv)
                    {
                        var head = HeadOf(cfg, heads, b);
                        if (head < 0)
                        {
                            throw new NotTranslated("an invariant outside a loop");
                        }
                        if (!_p.Invariants.TryGetValue(head, out var list))
                        {
                            _p.Invariants[head] = list = new List<KSpec>();
                        }
                        _writtenInvariants.Add(head);
                        var arg = SpecArgument(inv);
                        list.Add(KSpec.Of(Spec(arg, null), arg.Syntax));
                    }
                }
            }
        }
    }
}
