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
        /// <summary>
        /// Ownership trees: each [Owned] object's tree root (the object whose view is in someone's hand); null when
        /// the program has no [Owned] classes.
        /// </summary>
        public Term Root;
        /// <summary>Dynamic frames: the set of objects allocated so far (null when the program uses no dynamic frames).</summary>
        public Term Alloc;
        /// <summary>How the heap fields came to be: the state before the last change and what it may have touched.</summary>
        public StateLink Link;
        /// <summary>
        /// Permissions to [Owned] objects: object -> fraction (1 lets the holder write it; step 2 adds fractions in
        /// between for shared reading). Granted by a view in hand, <c>this</c> in the class's methods, or a frame lent
        /// through Spec.Modifies; revoked when the view goes. Null when the program has no [Owned] classes.
        /// </summary>
        public Term Perm;
        /// <summary>Predicate instances held: instance -> amount (1 per copy). Null when the program has no [Owned] classes.</summary>
        public Term Inst;
        /// <summary>
        /// The predicate instance whose (folded) footprint each object is in: object -> instance, 0 for none. An
        /// ownership tree is in the footprint its root is in.
        /// </summary>
        public Term Owner;
        /// <summary>
        /// Permissions to array cells: array -> (index -> amount). In a method whose contract gives it array
        /// permissions, writes need them; elsewhere every cell is held (arrays are not checked there). Null when the
        /// program has no Spec.Acc.
        /// </summary>
        public Term ArrPerm;
        /// <summary>The predicate instance an array cell is folded into: array -> index -> instance, 0 for none.</summary>
        public Term COwner;
        /// <summary>Permissions to single fields of owned objects: object -> field -> amount (the whole object's are in Perm).</summary>
        public Term FPerm;
        /// <summary>The predicate instance a single field is folded into: object -> field -> instance, 0 for none.</summary>
        public Term FOwner;
        /// <summary>Loops whose body exchanges permissions: the permissions held outside them (not their invariants'), on entry.</summary>
        public Dictionary<int, (Term perm, Term inst, Term arr, Term fperm)> LoopPermFrames = new Dictionary<int, (Term, Term, Term, Term)>();
        /// <summary>The Own&lt;T&gt; view variables in hand (not consumed, not read-only borrows).</summary>
        public HashSet<ISymbol> LiveViews = new HashSet<ISymbol>(SymbolEqualityComparer.Default);
        /// <summary>The variables holding packages of views ([Linear] record structs) not yet given away or taken apart.</summary>
        public HashSet<ISymbol> LivePackages = new HashSet<ISymbol>(SymbolEqualityComparer.Default);
        /// <summary>The variables holding views of memory cells (PointsTo, ArrayView, ArrayHole) in hand.</summary>
        public HashSet<ISymbol> LiveMemViews = new HashSet<ISymbol>(SymbolEqualityComparer.Default);
        public Dictionary<CaptureId, Term> Captures = new Dictionary<CaptureId, Term>();
        public HashSet<int> ActiveLoops = new HashSet<int>();
        /// <summary>What each ref local names: a variable, or an array cell.</summary>
        public Dictionary<ISymbol, RefTarget> Refs = new Dictionary<ISymbol, RefTarget>(SymbolEqualityComparer.Default);
        /// <summary>The foreach loops over arrays: the array, and the index of the element the iteration is at.</summary>
        public Dictionary<int, (Term arr, Term idx)> ForEach = new Dictionary<int, (Term, Term)>();
        public Dictionary<int, Term[]> LoopMeasures = new Dictionary<int, Term[]>();
        /// <summary>The inferred loop facts assumed at each loop's head on this path, and the entry values they compare with.</summary>
        public Dictionary<int, List<string>> LoopFacts = new Dictionary<int, List<string>>();
        public Dictionary<string, Term> LoopFactEntry = new Dictionary<string, Term>();
        /// <summary>A foreach over a LINQ view: the view as it was read when the loop began (MethodVerifier.Linq).</summary>
        public Dictionary<int, object> ViewSequences = new Dictionary<int, object>();
        public Term Result;
        /// <summary>The exception being handled (in a catch or filter), or thrown (in a finally run by it).</summary>
        public Term Exception;
        /// <summary>
        /// What runs when the innermost finally (or filter) on this path ends: the branch it interrupted, or the
        /// search for a handler, which goes on.
        /// </summary>
        public System.Collections.Immutable.ImmutableStack<System.Action<Frame>> Pending = System.Collections.Immutable.ImmutableStack<System.Action<Frame>>.Empty;
        public SyntaxNode ReturnSyntax;

        public Frame Clone() => new Frame
        {
            Vars = new Dictionary<ISymbol, Term>(Vars, SymbolEqualityComparer.Default),
            This = This,
            Heap = Heap,
            Fields = new Dictionary<ISymbol, Term>(Fields, SymbolEqualityComparer.Default),
            FieldEpoch = FieldEpoch,
            LiveViews = new HashSet<ISymbol>(LiveViews, SymbolEqualityComparer.Default),
            LivePackages = new HashSet<ISymbol>(LivePackages, SymbolEqualityComparer.Default),
            LiveMemViews = new HashSet<ISymbol>(LiveMemViews, SymbolEqualityComparer.Default),
            Alloc = Alloc,
            Root = Root,
            Perm = Perm,
            Inst = Inst,
            Owner = Owner,
            ArrPerm = ArrPerm,
            COwner = COwner,
            FPerm = FPerm,
            FOwner = FOwner,
            LoopPermFrames = new Dictionary<int, (Term, Term, Term, Term)>(LoopPermFrames),
            Link = Link,
            Captures = new Dictionary<CaptureId, Term>(Captures),
            ActiveLoops = new HashSet<int>(ActiveLoops),
            ForEach = new Dictionary<int, (Term, Term)>(ForEach),
            Refs = new Dictionary<ISymbol, RefTarget>(Refs, SymbolEqualityComparer.Default),
            LoopMeasures = new Dictionary<int, Term[]>(LoopMeasures),
            LoopFacts = new Dictionary<int, List<string>>(LoopFacts),
            LoopFactEntry = new Dictionary<string, Term>(LoopFactEntry),
            ViewSequences = new Dictionary<int, object>(ViewSequences),
            Result = Result,
            Exception = Exception,
            Pending = Pending,
            ReturnSyntax = ReturnSyntax,
        };
    }

    /// <summary>The location a ref local names: a variable, or the cell Idx of array Arr.</summary>
    public sealed class RefTarget
    {
        public ISymbol Variable;
        public Term Arr, Idx;
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
