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
        /// <summary>Array contents: reference -> (index -> element).</summary>
        public Term Heap;
        /// <summary>Heap fields changed on this path: field -> (object -> value). Others are as of the last FieldEpoch.</summary>
        public Dictionary<ISymbol, Term> Fields = new Dictionary<ISymbol, Term>(SymbolEqualityComparer.Default);
        /// <summary>0 for the method's entry state; a new number each time every heap field may have changed.</summary>
        public int FieldEpoch;
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
            Captures = new Dictionary<CaptureId, Term>(Captures),
            ActiveLoops = new HashSet<int>(ActiveLoops),
            LoopMeasures = new Dictionary<int, Term[]>(LoopMeasures),
            Result = Result,
            ReturnSyntax = ReturnSyntax,
        };
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
