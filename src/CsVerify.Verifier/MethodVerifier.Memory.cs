using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// ATS's manual memory (<c>Mem</c>, <c>Ptr&lt;T&gt;</c>) on the same model as C# arrays: its cells are a row of the
    /// heap, the one at null (array code never reads or writes there: it proves its arrays non-null first), and the
    /// views <c>PointsTo&lt;T&gt;</c> (<c>T @ l</c>), <c>ArrayView&lt;T&gt;</c> (<c>array_v</c>) and <c>ArrayHole&lt;T&gt;</c>
    /// hold permissions to cells of it, like Spec.Acc to an array's cells:
    /// <list type="bullet">
    /// <item>a view in hand holds its cells (Frame.ArrPerm at row 0): two views in hand are of disjoint cells;</item>
    /// <item>what a view says (<c>Elems</c>, <c>Value</c>) is what its cells hold: a view's contents are its own ghost
    /// value, as in ATS, tied to the heap whenever it comes into hand (nobody changes cells held, so it stays true);</item>
    /// <item>a call changes only the cells it may: none of those whose views stay in hand, and anything else (the
    /// views it got, memory it allocates or frees); the proof functions (Split, Join, TakeOut, PutBack, Get, Read) none.</item>
    /// </list>
    /// </summary>
    internal sealed partial class MethodVerifier
    {
        private static readonly Term MemRow = T.Int(0);

        internal static bool IsMemView(ITypeSymbol t) =>
            SpecSymbols.IsCsVerifyType(t, "PointsTo`1") || SpecSymbols.IsCsVerifyType(t, "ArrayView`1") || SpecSymbols.IsCsVerifyType(t, "ArrayHole`1");

        /// <summary>A ghost property of a view (Addr, Length, Index): the function EvalProperty applies to it.</summary>
        private Term ViewGhost(Term view, ITypeSymbol type, string name)
        {
            var p = ((INamedTypeSymbol)type).OriginalDefinition.GetMembers(name).OfType<IPropertySymbol>().First();
            return _z3.Apply(p.ToDisplayString(), SortOf(p.Type), new[] { T.Coerce(view, Sort.Int) });
        }

        private Term ViewLength(Term view, ITypeSymbol type) =>
            SpecSymbols.IsCsVerifyType(type, "PointsTo`1") ? T.Int(1) : ViewGhost(view, type, "Length");

        /// <summary>Is memory cell <paramref name="i"/> one of the view's? (A hole's are all but its index.)</summary>
        private string InView(Term view, ITypeSymbol type, string i)
        {
            var addr = ViewGhost(view, type, "Addr");
            var cond = $"(and (<= {addr} {i}) (< {i} (+ {addr} {ViewLength(view, type)})))";
            return SpecSymbols.IsCsVerifyType(type, "ArrayHole`1") ? $"(and {cond} (distinct {i} (+ {addr} {ViewGhost(view, type, "Index")})))" : cond;
        }

        private void ChangeView(Frame f, Term view, ITypeSymbol type, string op)
        {
            if (f.ArrPerm == null) return;
            f.ArrPerm = _z3.Define("cells", new Term(
                $"(lambda ((x Int)) (lambda ((i Int)) (ite (and (= x {MemRow}) {InView(view, type, "i")}) ({op} (select (select {f.ArrPerm} x) i) 1.0) (select (select {f.ArrPerm} x) i))))", Sort.PermHeap));
        }

        /// <summary>A view comes into hand: its cells are held, by nobody else (no other view in hand has them).</summary>
        private void GrantView(Frame f, Term view, ITypeSymbol type)
        {
            if (f.ArrPerm == null) return;
            var mem = $"(select {f.ArrPerm} {MemRow})";
            _z3.Assume(new Term($"(forall ((i Int)) (=> {InView(view, type, "i")} (< (select {mem} i) 1.0)))", Sort.Bool));
            var addr = ViewGhost(view, type, "Addr");
            _z3.Assume(new Term($"(=> {InView(view, type, addr.S)} (< (select {mem} {addr}) 1.0))", Sort.Bool));
            // (two intervals overlap only if one starts inside the other: at the other views' first cells too)
            foreach (var other in f.LiveMemViews.Where(f.Vars.ContainsKey).ToList())
            {
                var start = ViewGhost(f.Vars[other], TypeOf(other), "Addr");
                _z3.Assume(new Term($"(=> {InView(view, type, start.S)} (< (select {mem} {start}) 1.0))", Sort.Bool));
            }
            ChangeView(f, view, type, "+");
            // and what it says is what those cells hold (for a view a call gives back: once the call's changes are in)
            if (_pendingTies != null) _pendingTies.Add((view, type));
            else TieView(f, view, type);
        }

        private List<(Term view, ITypeSymbol type)> _pendingTies;

        /// <summary>Views given back by a call or reassigned by a loop are tied to the heap after it changes, not before.</summary>
        private void DeferTies() => _pendingTies = new List<(Term, ITypeSymbol)>();

        private void FlushTies(Frame f)
        {
            var ties = _pendingTies;
            _pendingTies = null;
            if (ties != null) foreach (var (view, type) in ties) TieView(f, view, type);
        }

        private void TieView(Frame f, Term view, ITypeSymbol type)
        {
            var addr = ViewGhost(view, type, "Addr");
            var row = $"(select {f.Heap} {MemRow})";
            if (SpecSymbols.IsCsVerifyType(type, "PointsTo`1"))
                _z3.Assume(new Term($"(= (select {row} {addr}) {T.Coerce(ViewGhost(view, type, "Value"), Sort.Int)})", Sort.Bool));
            else
            {
                var elems = ViewGhost(view, type, "Elems");
                _z3.Assume(new Term($"(forall ((i Int)) (! (=> {InView(view, type, $"(+ {addr} i)")} (= (select {row} (+ {addr} i)) (select {elems} i))) :pattern ((select {elems} i))))", Sort.Bool));
            }
        }

        private void RevokeView(Frame f, Term view, ITypeSymbol type) => ChangeView(f, view, type, "-");

        /// <summary>A view variable gets a view: its cells come into hand.</summary>
        private void MemViewAlive(Frame f, ISymbol variable, Term view)
        {
            GrantView(f, view, TypeOf(variable));
            f.LiveMemViews.Add(variable);
        }

        /// <summary>A view variable gives its view up (moved, given to a call by value or by ref, packed): so do its cells.</summary>
        private void ReleaseMemView(Frame f, ISymbol variable)
        {
            if (f.LiveMemViews.Remove(variable) && f.Vars.TryGetValue(variable, out var view)) RevokeView(f, view, TypeOf(variable));
        }

        /// <summary>Calls that change no memory: the proof functions of views, and reads.</summary>
        private static bool IsMemoryNeutral(Contract callee)
        {
            var m = callee.Method;
            if (callee.IsPure || callee.IsLemma) return true;
            return SpecSymbols.IsCsVerifyType(m.ContainingType, "Mem") &&
                   (m.Name == "Split" || m.Name == "Join" || m.Name == "TakeOut" || m.Name == "PutBack" || m.Name == "Get" || m.Name == "Read");
        }

        /// <summary>
        /// After a call: memory cells still held (their views were not given to it) are as they were; every other
        /// cell may have changed: the call got its view, or allocated it (perhaps where freed memory was).
        /// </summary>
        private Term KeepHeldMemory(Term heapAfter, Term heapBefore, Term held)
        {
            if (held == null || !_engine.UsesMemory) return heapAfter;
            var fresh = _z3.Fresh("mem", Sort.Row);
            return CellwiseHeap($"(ite (= x {MemRow}) (ite (>= (select (select {held} {MemRow}) i) 1.0) (select (select {heapBefore} {MemRow}) i) (select {fresh} i)) (select (select {heapAfter} x) i))");
        }

        /// <summary>
        /// A heap defined cell by cell (x, i): a constant of its own and an axiom, not a lambda term, so quantified
        /// facts about cells (postconditions over arrays, [Pure] applications) are instantiated through it.
        /// </summary>
        private Term CellwiseHeap(string cell)
        {
            var heap = _z3.Fresh("heap", Sort.Heap);
            _z3.Assume(new Term($"(forall ((x Int) (i Int)) (! (= (select (select {heap} x) i) {cell}) :pattern ((select (select {heap} x) i))))", Sort.Bool));
            return heap;
        }

        /// <summary>A loop that changes memory: only cells of views not touched in it keep their contents.</summary>
        private void LoopMemory(Frame f, IReadOnlyCollection<ISymbol> havocked, Term heapBefore)
        {
            if (!_engine.UsesMemory || f.ArrPerm == null) return;
            var kept = f.LiveMemViews.Where(v => !havocked.Contains(v, SymbolEqualityComparer.Default) && f.Vars.ContainsKey(v))
                .Select(v => InView(f.Vars[v], TypeOf(v), "i")).ToList();
            var fresh = _z3.Fresh("mem", Sort.Row);
            var keep = kept.Count == 0 ? "false" : $"(or {string.Join(" ", kept)})";
            f.Heap = CellwiseHeap($"(ite (= x {MemRow}) (ite {keep} (select (select {heapBefore} {MemRow}) i) (select {fresh} i)) (select (select {f.Heap} x) i))");
        }
    }
}
