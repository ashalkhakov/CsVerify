// Semantic values for the parsers CsLemon generates in C#: the verified interpreter gives the parse tree, and this walks
// it in the order an LR parser reduces (children left to right, then the node), giving each leaf the next token's
// value and each node what its rule's action makes of its children's values.
using System.Collections.Generic;
using CsVerify;

namespace CsLemon.Lr
{
    public static class Evaluator
    {
        /// <summary>A node being evaluated: its rule, the children still to do, and the values of those done.</summary>
        private sealed class Frame
        {
            public readonly int Rule;
            public Forest Rest;
            public readonly List<object?> Values = new List<object?>();

            public Frame(int rule, Forest rest)
            {
                Rule = rule;
                Rest = rest;
            }
        }

        /// <summary>
        /// The value of t: leaves take values[0], values[1], ... in order (null past the end), and a node of rule r
        /// takes reduce(r, its children's values). Iterative, so a long list (a deep tree) needs no deep recursion.
        /// </summary>
        public static object? Evaluate(Tree t, object?[] values, System.Func<int, object?[], object?> reduce)
        {
            Spec.Requires(Spec.Total(reduce));
            int next = 0;
            return Evaluate(t, values, ref next, reduce);
        }

        /// <summary>
        /// The trees of a stack, bottom to top (the reductions a parser has made, in order), each evaluated for what its
        /// actions do; the leaves take the values in order across them.
        /// </summary>
        public static void EvaluateStack(Stack s, object?[] values, System.Func<int, object?[], object?> reduce)
        {
            Spec.Requires(Spec.Total(reduce));
            var trees = new List<Tree>();
            Stack cur = s;
            while (cur is Stack.Cell)
            {
                var c = (Stack.Cell)cur;
                trees.Add(c.T);
                cur = c.Below;
            }
            // (an array: reduce may run any code, but an array's length stays as it is)
            Tree[] bottomUp = trees.ToArray();
            int next = 0;
            int i = bottomUp.Length;
            while (i > 0)
            {
                Spec.Invariant(0 <= next && i <= bottomUp.Length);
                i--;
                if (bottomUp[i] is Tree t) Evaluate(t, values, ref next, reduce);
            }
        }

        /// <summary>Evaluate, with the leaves taking values[next], values[next + 1], ...; next moves past them.</summary>
        public static object? Evaluate(Tree t, object?[] values, ref int next, System.Func<int, object?[], object?> reduce)
        {
            Spec.Requires(Spec.Total(reduce));
            Spec.Requires(0 <= next);
            Spec.Ensures(0 <= next);
            if (t is Tree.Leaf)
            {
                object? leaf = next < values.Length ? values[next] : null;
                next = checked(next + 1);
                return leaf;
            }
            if (!(t is Tree.Node root)) return null;
            var frames = new List<Frame> { new Frame(root.Rule, root.Kids) };
            while (true)
            {
                Spec.Invariant(0 <= next);
                int depth = frames.Count;
                if (depth <= 0) return null;
                Frame top = frames[depth - 1];
                if (top.Rest is Forest.Cons c)
                {
                    top.Rest = c.Tail;
                    if (c.Head is Tree.Node n) frames.Add(new Frame(n.Rule, n.Kids));
                    else
                    {
                        top.Values.Add(next < values.Length ? values[next] : null);
                        next = checked(next + 1);
                    }
                }
                else
                {
                    frames.RemoveAt(depth - 1);
                    object? v = reduce(top.Rule, top.Values.ToArray());
                    int left = frames.Count;
                    if (left <= 0) return v;
                    frames[left - 1].Values.Add(v);
                }
            }
        }
    }
}
