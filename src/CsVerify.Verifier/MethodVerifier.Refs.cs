using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// References to variables and array cells:
    /// <list type="bullet">
    /// <item>an array element passed by <c>ref</c>/<c>out</c>/<c>in</c> is copied in and out of the callee's parameter.
    /// That is exactly what happens when nothing else looks at the cell during the call: so a callee given one by
    /// ref or out must not touch array contents at all (Engine.MayTouchArrays), and one given one by in must not
    /// write them. Two arguments by reference, one of them ref or out, must not be the same cell or variable
    /// (CSV1020): the callee's parameters are variables of their own.</item>
    /// <item>a ref local is bound to a location, a variable or an array cell (the array and the index as they were
    /// when it was bound); reading and writing it read and write the location. A loop that writes through one
    /// havocs every location it is ever bound to.</item>
    /// </list>
    /// </summary>
    internal sealed partial class MethodVerifier
    {
        /// <summary>The cell an argument passed by reference names: an array element, or a ref local bound to one.</summary>
        private (Term arr, Term idx)? RefCell(IOperation value, Frame f, SpecEnv spec)
        {
            switch (value)
            {
                case IArrayElementReferenceOperation ae:
                {
                    var arr = Eval(ae.ArrayReference, f, spec);
                    return (arr, CellOf(ae, arr, f, spec));
                }
                case ILocalReferenceOperation l when l.Local.RefKind != RefKind.None && f.Refs.TryGetValue(l.Local, out var target) && target.Variable == null:
                    return (target.Arr, target.Idx);
                default:
                    return null;
            }
        }

        private Term ReadCell((Term arr, Term idx) cell, ITypeSymbol type, Frame f, SyntaxNode at)
        {
            CheckCellFraming(cell.arr, cell.idx, f, at);
            return InRangeOf(T.Coerce(T.Select(T.Select(f.Heap, cell.arr, Sort.Row), cell.idx, Sort.Int), SortOf(type)), type);
        }

        private void WriteCell((Term arr, Term idx) cell, Term v, Frame f, SyntaxNode at)
        {
            CheckCellWrite(cell.arr, cell.idx, f, at);
            f.Heap = T.Store(f.Heap, cell.arr, T.Store(T.Select(f.Heap, cell.arr, Sort.Row), cell.idx, T.Coerce(v, Sort.Int)));
        }

        /// <summary>Array cells lent to a callee: it must leave arrays alone while it has them, and get each once.</summary>
        private void LendCells(IInvocationOperation inv, Dictionary<IArgumentOperation, (Term arr, Term idx)> cells)
        {
            var m = inv.TargetMethod;
            bool writable = cells.Keys.Any(a => a.Parameter.RefKind != RefKind.In && a.Parameter.RefKind != RefKind.RefReadOnlyParameter);
            if (writable ? _engine.MayTouchArrays(m) : _engine.MayWriteHeap(m))
            {
                var a = cells.Keys.First();
                NotModeled(a.Syntax, $"passing '{a.Value.Syntax}' by reference to '{m.Name}', which may {(writable ? "read or write" : "write")} array contents itself, is not supported: " +
                                     "the cell and the parameter would disagree (copy the element into a local)");
            }
        }

        /// <summary>
        /// The variable or cell each argument passed by reference names: two of them, one written by the callee, must
        /// not be the same (the callee's parameters are distinct variables).
        /// </summary>
        private void CheckRefAliasing(IInvocationOperation inv, Dictionary<IArgumentOperation, (Term arr, Term idx)> cells, Frame f)
        {
            var byRef = inv.Arguments.Where(a => a.Parameter != null && a.Parameter.RefKind != RefKind.None && a.ArgumentKind == ArgumentKind.Explicit &&
                                                 !(a.Value is IDiscardOperation)).ToList();
            for (int i = 0; i < byRef.Count; i++)
                for (int j = i + 1; j < byRef.Count; j++)
                {
                    var (a, b) = (byRef[i], byRef[j]);
                    if (a.Parameter.RefKind == RefKind.In && b.Parameter.RefKind == RefKind.In) continue;
                    var message = $"'{a.Value.Syntax}' and '{b.Value.Syntax}' might be the same {{0}}, passed by reference to two parameters of '{inv.TargetMethod.Name}'";
                    if (cells.TryGetValue(a, out var ca) && cells.TryGetValue(b, out var cb))
                        Prove(T.Or(T.Not(T.Eq(ca.arr, cb.arr)), T.Not(T.Eq(ca.idx, cb.idx))), "CSV1020", inv.Syntax, string.Format(message, "array cell"));
                    // (a linear value passed twice is CSV0007, the analyzer's)
                    else if (RefVariable(a.Value, f) is ISymbol va && SymbolEqualityComparer.Default.Equals(va, RefVariable(b.Value, f)) &&
                             !IsViewVariable(va) && !IsMemView(TypeOf(va)) && !SpecSymbols.IsLinearPackage(TypeOf(va)))
                        Report("CSV1020", inv.Syntax, string.Format(message, "variable"), isError: true);
                }
        }

        /// <summary>The variable an argument by reference names (through a ref local), or null for a cell or anything else.</summary>
        private ISymbol RefVariable(IOperation value, Frame f)
        {
            switch (value)
            {
                case ILocalReferenceOperation l when l.Local.RefKind != RefKind.None:
                    return f.Refs.TryGetValue(l.Local, out var t) ? t.Variable : null;
                case ILocalReferenceOperation l: return l.Local;
                case IParameterReferenceOperation p: return p.Parameter;
                default: return null;
            }
        }

        // ================================================================================== ref locals

        /// <summary><c>ref T r = ref e</c> or <c>r = ref e</c>: r names e's location from now on.</summary>
        private Term BindRef(ILocalSymbol r, IOperation value, Frame f, SpecEnv spec, SyntaxNode at)
        {
            if (IsViewVariable(r) || IsMemView(r.Type) || SpecSymbols.IsLinearPackage(r.Type))
            {
                NotModeled(at, $"ref local '{r.Name}' of a linear type is not supported");
                return Unknown(r.Type);
            }
            switch (value)
            {
                case ILocalReferenceOperation l when l.Local.RefKind != RefKind.None:
                    if (!f.Refs.TryGetValue(l.Local, out var other)) break;
                    f.Refs[r] = other;
                    return ReadRef(r, f, at);
                case ILocalReferenceOperation l:
                    f.Refs[r] = new RefTarget { Variable = l.Local };
                    return ReadRef(r, f, at);
                case IParameterReferenceOperation p:
                    f.Refs[r] = new RefTarget { Variable = p.Parameter };
                    return ReadRef(r, f, at);
                case IArrayElementReferenceOperation ae:
                {
                    var arr = Eval(ae.ArrayReference, f, spec);
                    var idx = CellOf(ae, arr, f, spec);
                    f.Refs[r] = new RefTarget { Arr = arr, Idx = idx };
                    return ReadRef(r, f, at);
                }
            }
            f.Refs.Remove(r);
            NotModeled(at, $"ref local '{r.Name}' bound to '{value.Syntax}' is not supported: only to locals, parameters and array elements");
            return Unknown(r.Type);
        }

        private Term ReadRef(ILocalSymbol r, Frame f, SyntaxNode at)
        {
            if (!f.Refs.TryGetValue(r, out var t))
            {
                NotModeled(at, $"ref local '{r.Name}' is rebound in a loop: which location it names at the loop's head is not known");
                return Unknown(r.Type);
            }
            return t.Variable != null ? Read(f, t.Variable) : ReadCell((t.Arr, t.Idx), r.Type, f, at);
        }

        private void WriteRef(ILocalSymbol r, Term v, Frame f, SyntaxNode at)
        {
            if (!f.Refs.TryGetValue(r, out var t))
            {
                NotModeled(at, $"ref local '{r.Name}' is rebound in a loop: which location it names at the loop's head is not known");
                return;
            }
            if (t.Variable == null) { WriteCell((t.Arr, t.Idx), v, f, at); return; }
            CheckNonNullVariable(t.Variable, v, at);
            f.Vars[t.Variable] = v;
        }

        /// <summary>The expressions a ref local is ever bound to (ref e in its declaration, r = ref e).</summary>
        private IEnumerable<ExpressionSyntax> RefBindings(ILocalSymbol r)
        {
            foreach (var n in _contract.Declaration.DescendantNodes())
            {
                if (n is VariableDeclaratorSyntax vd && vd.Initializer?.Value is RefExpressionSyntax init &&
                    SymbolEqualityComparer.Default.Equals(_model.GetDeclaredSymbol(vd), r))
                    yield return init.Expression;
                if (n is AssignmentExpressionSyntax asg && asg.Right is RefExpressionSyntax re &&
                    SymbolEqualityComparer.Default.Equals(_model.GetSymbolInfo(asg.Left).Symbol, r))
                    yield return re.Expression;
            }
        }
    }
}
