using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Facts about loops without invariants, inferred as Houdini does. Candidates come from the loop's condition
    /// (<c>i &lt; n</c> suggests <c>i &lt;= n</c> at the head) and from the integers it changes (each may never go below,
    /// or never above, its value on entry). A candidate that holds on entry is assumed at the head. Each back edge
    /// checks it again; if it might not hold there, the method is verified again without it, until every candidate
    /// assumed is one that held at every back edge (<see cref="FailedLoopFacts"/>, Engine's reruns). Loops with
    /// invariants of their own are left as they are.
    /// </summary>
    internal sealed partial class MethodVerifier
    {
        private sealed class LoopFact
        {
            public string Key;
            /// <summary>The fact in a frame: of the loop's head, or at a back edge.</summary>
            public Func<Frame, Term> Make;
            /// <summary>For "never below/above its value on entry": the value, taken on entry.</summary>
            public Func<Frame, Term> Path;
            public bool AtLeast;
        }

        /// <summary>The facts that might not hold at some back edge: the next run leaves them out.</summary>
        public readonly HashSet<string> FailedLoopFacts = new HashSet<string>(StringComparer.Ordinal);

        private readonly ISet<string> _excludedFacts;

        /// <summary>Infer nothing: the last run, after too many rounds.</summary>
        public bool InferNoLoopFacts;

        /// <summary>The candidates for a for or while loop without invariants.</summary>
        private void InferLoopFacts(Loop loop, ExpressionSyntax condition)
        {
            if (loop.Invariants.Count > 0 || condition == null || InferNoLoopFacts) return;
            if (!(_model.GetOperation(condition) is IOperation cond)) return;
            Term Value(Frame f, IOperation op) => T.Coerce(EvalForeignSpec(op, f, new SpecEnv { Old = _entry }), Sort.Int);
            var comparisons = new List<IBinaryOperation>();
            Conjuncts(cond, comparisons);
            var paths = new List<IOperation>();
            int n = 0;
            string Key() => loop.Id + ":" + n++;
            foreach (var b in comparisons)
            {
                var (l, r) = (b.LeftOperand, b.RightOperand);
                foreach (var side in new[] { l, r })
                    if (!(side.ConstantValue.HasValue) && !paths.Any(p => p.Syntax.IsEquivalentTo(side.Syntax))) paths.Add(side);
                // at the head, before the test: within one step of the condition
                var offsets = b.OperatorKind switch
                {
                    BinaryOperatorKind.LessThan => new[] { (le: true, k: 0) },
                    BinaryOperatorKind.LessThanOrEqual => new[] { (le: true, k: 1) },
                    BinaryOperatorKind.GreaterThan => new[] { (le: false, k: 0) },
                    BinaryOperatorKind.GreaterThanOrEqual => new[] { (le: false, k: -1) },
                    BinaryOperatorKind.NotEquals => new[] { (le: true, k: 0), (le: false, k: 0) },
                    _ => Array.Empty<(bool, int)>(),
                };
                foreach (var (le, k) in offsets)
                    loop.Facts.Add(new LoopFact
                    {
                        Key = Key(),
                        Make = f => le ? T.Le(Value(f, l), T.Add(Value(f, r), T.Int(k))) : T.Ge(Value(f, l), T.Add(Value(f, r), T.Int(k))),
                    });
            }
            // what the loop changes: an integer that moves one way
            foreach (var p in paths.Where(p => !(Unwrap(p) is ILiteralOperation)))
            {
                var path = p;
                loop.Facts.Add(new LoopFact { Key = Key(), Path = f => Value(f, path), AtLeast = true });
                loop.Facts.Add(new LoopFact { Key = Key(), Path = f => Value(f, path), AtLeast = false });
            }
        }

        private static IOperation Unwrap(IOperation op)
        {
            while (op is IConversionOperation c && c.IsImplicit) op = c.Operand;
            return op;
        }

        /// <summary>The integer comparisons a condition is a conjunction of, between operands that read state only.</summary>
        private void Conjuncts(IOperation cond, List<IBinaryOperation> into)
        {
            switch (cond)
            {
                case IBinaryOperation both when both.OperatorKind == BinaryOperatorKind.ConditionalAnd:
                    Conjuncts(both.LeftOperand, into);
                    Conjuncts(both.RightOperand, into);
                    break;
                case IBinaryOperation b when b.OperatorMethod == null && !b.IsLifted && IsIntegral(b.LeftOperand.Type) && IsIntegral(b.RightOperand.Type) &&
                                             Simple(b.LeftOperand) && Simple(b.RightOperand):
                    into.Add(b);
                    break;
            }
        }

        /// <summary>Reads only: locals, parameters, constants, fields and auto-properties of those, lengths, + and -.</summary>
        private bool Simple(IOperation op)
        {
            switch (op)
            {
                case ILocalReferenceOperation l: return l.Local.RefKind == RefKind.None;
                case IParameterReferenceOperation _:
                case ILiteralOperation _:
                    return true;
                case IConversionOperation c: return c.IsImplicit && c.OperatorMethod == null && Simple(c.Operand);
                case IParenthesizedOperation p: return Simple(p.Operand);
                case IFieldReferenceOperation fr: return !fr.Field.IsVolatile && !Atomics.IsAtomic(fr.Field) && (fr.Instance == null || Simple(fr.Instance));
                case IPropertyReferenceOperation pr when pr.Instance != null && IsSequence(pr.Instance.Type) && pr.Property.Name == "Length":
                    return Simple(pr.Instance);
                case IPropertyReferenceOperation pr when pr.Arguments.Length == 0 && pr.Instance != null &&
                                                         (FieldEffects.IsHeapField(pr.Property) || IsStructMember(pr.Property)):
                    return Simple(pr.Instance);
                case IBinaryOperation b when (b.OperatorKind == BinaryOperatorKind.Add || b.OperatorKind == BinaryOperatorKind.Subtract) && b.OperatorMethod == null:
                    return Simple(b.LeftOperand) && Simple(b.RightOperand);
                default: return op.ConstantValue.HasValue;
            }
        }

        /// <summary>On entry: which candidates hold, and the entry values of the integers; they are assumed after the havoc.</summary>
        private void LoopFactsEntry(Loop loop, Frame f)
        {
            if (loop.Facts.Count == 0) return;
            var active = new List<string>();
            for (int i = 0; i < loop.Facts.Count; i++)
            {
                var fact = loop.Facts[i];
                if (_excludedFacts != null && _excludedFacts.Contains(fact.Key)) continue;
                if (fact.Path != null) f.LoopFactEntry[fact.Key] = fact.Path(f);
                else if (_z3.Check(T.Not(fact.Make(f))) != "unsat") continue;
                active.Add(fact.Key);
            }
            f.LoopFacts[loop.Id] = active;
        }

        /// <summary>A fact in a frame: a candidate's own, or "never below/above" its value on entry.</summary>
        private Term LoopFactIn(Loop loop, string key, Frame f)
        {
            var fact = loop.Facts.First(x => x.Key == key);
            if (fact.Make != null) return fact.Make(f);
            var entry = f.LoopFactEntry[key];
            var now = fact.Path(f);
            return fact.AtLeast ? T.Ge(now, entry) : T.Le(now, entry);
        }

        private void LoopFactsHead(Loop loop, Frame f)
        {
            if (!f.LoopFacts.TryGetValue(loop.Id, out var active)) return;
            foreach (var key in active) _z3.Assume(LoopFactIn(loop, key, f));
        }

        private void LoopFactsBackEdge(Loop loop, Frame f)
        {
            if (!f.LoopFacts.TryGetValue(loop.Id, out var active)) return;
            foreach (var key in active)
                if (!FailedLoopFacts.Contains(key) && _z3.Check(T.Not(LoopFactIn(loop, key, f))) != "unsat") FailedLoopFacts.Add(key);
        }
    }
}
