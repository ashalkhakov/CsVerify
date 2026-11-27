using System.Collections.Generic;
using System.Linq;
using System.Runtime.CompilerServices;
using Microsoft.CodeAnalysis;

namespace CsVerify.Analyzers
{
    /// <summary>
    /// The program as compilations: the project's, which references its projects' and the Spec library's
    /// (CompilationReference). A tree's semantic model is its own compilation's.
    /// </summary>
    public static class Compilations
    {
        private static readonly ConditionalWeakTable<Compilation, Dictionary<SyntaxTree, Compilation>> _owners =
            new ConditionalWeakTable<Compilation, Dictionary<SyntaxTree, Compilation>>();

        /// <summary>The compilations of the program: this one and those it references, transitively.</summary>
        public static IEnumerable<Compilation> Referenced(this Compilation c)
        {
            var seen = new HashSet<Compilation>();
            var work = new Stack<Compilation>();
            work.Push(c);
            while (work.Count > 0)
            {
                var x = work.Pop();
                if (!seen.Add(x))
                {
                    continue;
                }
                yield return x;
                foreach (var r in x.References.OfType<CompilationReference>())
                {
                    work.Push(r.Compilation);
                }
            }
        }

        private static Dictionary<SyntaxTree, Compilation> Owners(Compilation c) =>
            _owners.GetValue(c, x => x.Referenced().SelectMany(r => r.SyntaxTrees.Select(t => (t, r))).GroupBy(p => p.t).ToDictionary(g => g.Key, g => g.First().r));

        /// <summary>The semantic model of a tree of the program, from the compilation that holds it.</summary>
        public static SemanticModel ModelOf(this Compilation c, SyntaxTree tree) =>
            (c.ContainsSyntaxTree(tree) ? c : Owners(c).TryGetValue(tree, out var owner) ? owner : c).GetSemanticModel(tree);

        /// <summary>The trees of the program: this compilation's and its referenced compilations'.</summary>
        public static IEnumerable<SyntaxTree> ProgramTrees(this Compilation c) => Owners(c).Keys;

        /// <summary>Is the tree one of the program's?</summary>
        public static bool HoldsTree(this Compilation c, SyntaxTree tree) => c.ContainsSyntaxTree(tree) || Owners(c).ContainsKey(tree);
    }
}
