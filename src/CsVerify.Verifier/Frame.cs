using System.Collections.Generic;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.FlowAnalysis;

namespace CsVerify.Verifier
{
    /// <summary>Symbolic program state along one path.</summary>
    public sealed class Frame
    {
        public Dictionary<ISymbol, Term> Vars = new Dictionary<ISymbol, Term>(SymbolEqualityComparer.Default);
        public Term This;
        /// <summary>
        /// Array contents: reference -> (index -> element). Arrays are outside dynamic frames, so a change to them
        /// ends the <see cref="Link"/> chain: a [Pure] function's value then follows only from its arguments.
        /// </summary>
        public Term Heap { get => _heap; set { _heap = value; Link = null; } }
        private Term _heap;
        /// <summary>Heap fields changed on this path: field -> (object -> value). Others are as of the last FieldEpoch.</summary>
        public Dictionary<ISymbol, Term> Fields = new Dictionary<ISymbol, Term>(SymbolEqualityComparer.Default);
        /// <summary>0 for the method's entry state; a new number each time every heap field may have changed.</summary>
        public int FieldEpoch;
        /// <summary>Dynamic frames: the set of objects allocated so far (null when the program uses no dynamic frames).</summary>
        public Term Alloc;
        /// <summary>How the heap fields came to be: the state before the last change and what it may have touched.</summary>
        public StateLink Link;
        /// <summary>The Own&lt;T&gt; view variables in hand (not consumed, not read-only borrows).</summary>
        public HashSet<ISymbol> LiveViews = new HashSet<ISymbol>(SymbolEqualityComparer.Default);
        public Dictionary<CaptureId, Term> Captures = new Dictionary<CaptureId, Term>();
        public HashSet<int> ActiveLoops = new HashSet<int>();
        public Dictionary<int, Term[]> LoopMeasures = new Dictionary<int, Term[]>();
        public Term Result;
        public SyntaxNode ReturnSyntax;

        public Frame Clone() => new Frame
        {
            Vars = new Dictionary<ISymbol, Term>(Vars, SymbolEqualityComparer.Default),
            This = This,
            Heap = Heap,
            Fields = new Dictionary<ISymbol, Term>(Fields, SymbolEqualityComparer.Default),
            FieldEpoch = FieldEpoch,
            LiveViews = new HashSet<ISymbol>(LiveViews, SymbolEqualityComparer.Default),
            Alloc = Alloc,
            Link = Link,
            Captures = new Dictionary<CaptureId, Term>(Captures),
            ActiveLoops = new HashSet<int>(ActiveLoops),
            LoopMeasures = new Dictionary<int, Term[]>(LoopMeasures),
            Result = Result,
            ReturnSyntax = ReturnSyntax,
        };
    }

    /// <summary>
    /// A change of heap fields that touched only the objects in <see cref="Changed"/> (a set): a [Pure] function
    /// with a Spec.Reads frame disjoint from it has the same value as in <see cref="Before"/>.
    /// </summary>
    public sealed class StateLink
    {
        public Frame Before;
        public Term Changed;
    }

    /// <summary>
    /// Evaluation context of a specification expression: entry state for <c>Spec.Old</c>, the return value for
    /// <c>Spec.Result</c> / the <c>r =&gt;</c> parameter of <c>Ensures</c>.
    /// </summary>
    public sealed class SpecEnv
    {
        public Frame Old;
        public Term Result;
        public IParameterSymbol ResultParameter;
    }
}
