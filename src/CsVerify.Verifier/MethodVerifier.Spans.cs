using System.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Spans (<c>Span&lt;T&gt;</c>, <c>ReadOnlySpan&lt;T&gt;</c>) are views of memory: a base (an array, or memory the
    /// verifier knows only as some array's cells), an offset into it, and a length. <c>s[i]</c> is the base's cell at
    /// offset + i, read from and written to the heap like an array's, so what code writes through one span (or the
    /// array) a span over the same cells sees. A span made from an array (a conversion, <c>new Span&lt;T&gt;(a, start,
    /// length)</c>, <c>a.AsSpan(...)</c>) has the array as its base. <c>Slice</c> keeps the base and moves the offset;
    /// <c>CopyTo</c>, <c>Fill</c> and <c>Clear</c> write cells; <c>stackalloc</c> makes a new base. A span from
    /// elsewhere (a parameter, a library call) has some base and offset, its cells within the base's length.
    /// Under array permissions (Spec.Acc), spans are as before: their reads unknown, their writes refused.
    /// </summary>
    internal sealed partial class MethodVerifier
    {
        private Term SpanBase(Term s) => _z3.Apply("span.base", Sort.Int, new[] { s });
        private Term SpanOffset(Term s) => _z3.Apply("span.offset", Sort.Int, new[] { s });

        /// <summary>A span (from a parameter, a library call) whose base and offset are not known: its cells are some array's.</summary>
        private void SomeSpan(Term s) => AssumeSide(T.And(T.Le(T.Int(0), SpanOffset(s)), T.Le(T.Add(SpanOffset(s), Len(s)), Len(SpanBase(s)))));

        /// <summary>The span over a whole array (the array converted): the array itself, as its own base at 0.</summary>
        private Term SpanOfArray(Term arr)
        {
            AssumeSide(T.And(T.Eq(SpanBase(arr), arr), T.Eq(SpanOffset(arr), T.Int(0))));
            return arr;
        }

        private Term NewSpan(Term @base, Term offset, Term length)
        {
            var s = _z3.Fresh("span", Sort.Int);
            AssumeSide(T.And(T.Eq(SpanBase(s), @base), T.Eq(SpanOffset(s), offset), T.Eq(Len(s), length)));
            return s;
        }

        private Term SpanRead(Term s, Term i, ITypeSymbol type, Frame f) =>
            InRangeOf(T.Coerce(T.Select(T.Select(f.Heap, SpanBase(s), Sort.Row), T.Add(SpanOffset(s), i), Sort.Int), SortOf(type)), type);

        private void SpanWrite(Term s, Term i, Term v, Frame f)
        {
            var b = SpanBase(s);
            f.Heap = T.Store(f.Heap, b, T.Store(T.Select(f.Heap, b, Sort.Row), T.Add(SpanOffset(s), i), T.Coerce(v, Sort.Int)));
        }

        /// <summary>The cells of [start, start + length) of span s, as a range of its base, checked like C#'s.</summary>
        private Term Subspan(Term s, Term start, Term length, SyntaxNode at, string what)
        {
            Require(T.And(T.Le(T.Int(0), start), T.Le(T.Int(0), length), T.Le(T.Add(start, length), Len(s))), "CSV1001", at,
                $"{what}: the range might not be within the span (it would throw ArgumentOutOfRangeException)");
            return NewSpan(SpanBase(s), T.Add(SpanOffset(s), start), length);
        }

        /// <summary>The span methods and constructors modeled here; null for others.</summary>
        private Term SpanInvocation(IInvocationOperation inv, Frame f, SpecEnv spec)
        {
            var m = inv.TargetMethod;
            Term Arg(int ordinal) => T.Coerce(Eval(inv.Arguments.First(a => a.Parameter.Ordinal == ordinal).Value, f, spec), Sort.Int);
            // a.AsSpan(), a.AsSpan(start), a.AsSpan(start, length) on an array (or a string: its characters)
            if (m.ContainingType?.ToDisplayString() == "System.MemoryExtensions" && m.Name == "AsSpan" && m.Parameters.Length >= 1 &&
                (m.Parameters[0].Type is IArrayTypeSymbol || m.Parameters[0].Type.SpecialType == SpecialType.System_String) &&
                m.Parameters.Skip(1).All(p => p.Type.SpecialType == SpecialType.System_Int32))
            {
                var a = Arg(0);
                Deref(inv.Arguments[0].Value, a, inv.Syntax);
                var whole = m.Parameters[0].Type is IArrayTypeSymbol ? SpanOfArray(a) : NewSpan(a, T.Int(0), Len(a));
                if (m.Parameters.Length == 1) return whole;
                var start = Arg(1);
                return Subspan(whole, start, m.Parameters.Length == 3 ? Arg(2) : T.Sub(Len(a), start), inv.Syntax, $"'{inv.Syntax}'");
            }
            if (!IsSpan(m.ContainingType) || inv.Instance == null) return null;
            if (_arrayMode) return null;
            var s = T.Coerce(Eval(inv.Instance, f, spec), Sort.Int);
            switch (m.Name)
            {
                case "Slice" when m.Parameters.Length == 1:
                {
                    var start = Arg(0);
                    return Subspan(s, start, T.Sub(Len(s), start), inv.Syntax, $"'{inv.Syntax}'");
                }
                case "Slice" when m.Parameters.Length == 2:
                    return Subspan(s, Arg(0), Arg(1), inv.Syntax, $"'{inv.Syntax}'");
                case "CopyTo" when m.Parameters.Length == 1 && IsSpan(m.Parameters[0].Type):
                {
                    var d = Arg(0);
                    if (!_codeMode) return null;
                    Require(T.Le(Len(s), Len(d)), "CSV1001", inv.Syntax, $"'{inv.Syntax}': the destination might be shorter than the source (it would throw ArgumentException)");
                    CopyCells(s, d, f, inv.Syntax);
                    return T.True;
                }
                case "TryCopyTo" when m.Parameters.Length == 1 && IsSpan(m.Parameters[0].Type):
                {
                    var d = Arg(0);
                    if (!_codeMode) return null;
                    var fits = T.Le(Len(s), Len(d));
                    var before = f.Heap;
                    CopyCells(s, d, f, inv.Syntax);
                    f.Heap = new Term($"(ite {fits} {f.Heap} {before})", Sort.Heap);
                    return fits;
                }
                case "Fill" when m.Parameters.Length == 1:
                {
                    var v = T.Coerce(Eval(inv.Arguments[0].Value, f, spec), Sort.Int);
                    if (!_codeMode) return null;
                    SetCells(s, f, inv.Syntax, _ => v.S);
                    return T.True;
                }
                case "Clear" when m.Parameters.Length == 0:
                    if (!_codeMode) return null;
                    SetCells(s, f, inv.Syntax, _ => "0");
                    return T.True;
                case "ToArray" when m.Parameters.Length == 0:
                {
                    if (!_codeMode) return null;
                    var arr = Unknown(inv.Type, "toArray");
                    AssumeSide(T.And(NotNull(arr), T.Eq(Len(arr), Len(s))));
                    NewArrayIsDistinct(arr, f);
                    var src = T.Select(f.Heap, SpanBase(s), Sort.Row);
                    var row = Pointwise("toArray", Sort.Row, $"(select {src} (+ {SpanOffset(s)} y))");
                    f.Heap = T.Store(f.Heap, arr, row);
                    return arr;
                }
            }
            return null;
        }

        /// <summary>
        /// Copies s's cells to the start of d, as memmove does (the source read before anything is written, so
        /// overlapping spans copy right).
        /// </summary>
        private void CopyCells(Term s, Term d, Frame f, SyntaxNode at)
        {
            CheckWrite(SpanBase(d), at);
            var heap = f.Heap;
            var db = SpanBase(d);
            var src = T.Select(heap, SpanBase(s), Sort.Row);
            var dst = T.Select(heap, db, Sort.Row);
            var lo = SpanOffset(d);
            var hi = T.Add(SpanOffset(d), Len(s));
            var row = Pointwise("copyTo", Sort.Row,
                $"(ite (and (<= {lo} y) (< y {hi})) (select {src} (+ {SpanOffset(s)} (- y {lo}))) (select {dst} y))");
            f.Heap = T.Store(heap, db, row);
        }

        private void SetCells(Term s, Frame f, SyntaxNode at, System.Func<string, string> value)
        {
            CheckWrite(SpanBase(s), at);
            var b = SpanBase(s);
            var old = T.Select(f.Heap, b, Sort.Row);
            var lo = SpanOffset(s);
            var hi = T.Add(SpanOffset(s), Len(s));
            var row = Pointwise("fill", Sort.Row, $"(ite (and (<= {lo} y) (< y {hi})) {value("y")} (select {old} y))");
            f.Heap = T.Store(f.Heap, b, row);
        }

        /// <summary><c>new Span&lt;T&gt;(a)</c>, <c>new Span&lt;T&gt;(a, start, length)</c>; null for other constructors.</summary>
        private Term SpanConstruction(IObjectCreationOperation oc, Frame f, SpecEnv spec)
        {
            var ctor = oc.Constructor;
            if (ctor == null || !IsSpan(oc.Type) || ctor.Parameters.Length == 0 || !(ctor.Parameters[0].Type is IArrayTypeSymbol) ||
                ctor.Parameters.Skip(1).Any(p => p.Type.SpecialType != SpecialType.System_Int32) || ctor.Parameters.Length == 2) return null;
            var args = oc.Arguments.OrderBy(a => a.Parameter.Ordinal).Select(a => T.Coerce(Eval(a.Value, f, spec), Sort.Int)).ToArray();
            // (a null array makes an empty span)
            var a0 = args[0];
            var whole = T.Ite(T.Eq(a0, T.Int(0)), NewSpan(T.Int(0), T.Int(0), T.Int(0)), SpanOfArray(a0));
            if (args.Length == 1) return whole;
            return Subspan(NewSpan(a0, T.Int(0), T.Ite(T.Eq(a0, T.Int(0)), T.Int(0), Len(a0))), args[1], args[2], oc.Syntax, $"'{oc.Syntax}'");
        }

        /// <summary><c>stackalloc T[n]</c>: a new base of n cells.</summary>
        private Term StackAlloc(IOperation op, Frame f, SpecEnv spec)
        {
            var sa = (StackAllocArrayCreationExpressionSyntax)op.Syntax;
            var rank = sa.Type is ArrayTypeSyntax at ? at.RankSpecifiers.FirstOrDefault()?.Sizes.FirstOrDefault() : null;
            var size = rank != null && _model.GetOperation(rank) is IOperation n ? T.Coerce(Eval(n, f, spec), Sort.Int) : _z3.Fresh("stackalloc", Sort.Int);
            if (rank != null) Require(T.Le(T.Int(0), size), "CSV1003", op.Syntax, $"'{op.Syntax}': the size might be negative");
            var arr = _z3.Fresh("stackalloc", Sort.Int);
            AssumeSide(T.And(NotNull(arr), T.Eq(Len(arr), size)));
            NewArrayIsDistinct(arr, f);
            return SpanOfArray(arr);
        }
    }
}
