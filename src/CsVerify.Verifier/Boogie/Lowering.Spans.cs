using System.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.Operations;
using static CsVerify.Verifier.Boogie.KernelTypes;
using static CsVerify.Verifier.Boogie.KOp;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>
    /// Spans (Span&lt;T&gt;, ReadOnlySpan&lt;T&gt;) of scalars (StaticChecks.Spans): a value
    /// viewing memory, a base array ($sbase), an offset into it ($soff) and a length (len). s[i] is the base's cell at
    /// offset + i, in its element type's map, so what one span (or the array) writes, another over the same cells sees.
    /// A span made from an array (a conversion, new Span&lt;T&gt;(a, start, length), a.AsSpan(...)) has the array as its
    /// base; Slice keeps the base and moves the offset; CopyTo, Fill and Clear write their cells. A span from elsewhere
    /// (a parameter) has some base and offset, its cells within the base's length.
    /// </summary>
    internal sealed partial class Lowering
    {
        private static KExpr SBase(KExpr s) => new KOp("$sbase", s);
        private static KExpr SOff(KExpr s) => new KOp("$soff", s);

        /// <summary>The array type of a span's cells (whose map they are in).</summary>
        private static ITypeSymbol CellsOf(ITypeSymbol span) => KernelTypes.Compilation.CreateArrayTypeSymbol(SpanElement(span));

        /// <summary>A new span: base, offset, length.</summary>
        private KExpr NewSpan(ITypeSymbol type, KExpr @base, KExpr offset, KExpr length)
        {
            var t = Declare("t$" + _temps++, type);
            Emit(KHavoc.Of(t));
            Emit(KAssume.Of(AndAlso(Eq(SBase(new KVar(t)), @base), AndAlso(Eq(SOff(new KVar(t)), offset), Eq(Length(new KVar(t)), length)))));
            return new KVar(t);
        }

        /// <summary>The span over a whole array (an empty one where it's null, as C# has it).</summary>
        private KExpr SpanOfArray(ITypeSymbol type, KExpr a)
        {
            var t = Declare("t$" + _temps++, type);
            var s = new KVar(t);
            Emit(KHavoc.Of(t));
            Emit(KAssume.Of(
            Ite(IsNull(a), Eq(Length(s), KLit.Zero),
AndAlso(Eq(SBase(s), a), AndAlso(Eq(SOff(s), KLit.Zero), Eq(Length(s), Length(a)))))));
            return s;
        }

        /// <summary>[start, start + length) of span s: checked within it (CSV1001), as C# throws.</summary>
        private KExpr Subspan(ITypeSymbol type, KExpr s, KExpr start, KExpr length, SyntaxNode at)
        {
            Emit(KCheck.Of(
                AndAlso(AndAlso(Le(KLit.Zero, start), Le(KLit.Zero, length)), Le(Plus(start, length), Length(s))),
                "CSV1001",
                at,
                $"'{at}': the range might not be within the span (it would throw ArgumentOutOfRangeException)"));
            return NewSpan(type, SBase(s), Plus(SOff(s), start), length);
        }

        /// <summary>s[i]: i within the span (CSV1003); the base's cell.</summary>
        private (KExpr array, KExpr index) SpanCell(KExpr s, KExpr i, SyntaxNode at, bool inSpec, out KExpr within)
        {
            within = AndAlso(Le(KLit.Zero, i), Lt(i, Length(s)));
            if (!inSpec)
            {
                Emit(KCheck.Of(within, "CSV1003", at, $"index in '{at}' might be out of range"));
            }
            return (SBase(s), Plus(SOff(s), i));
        }

        /// <summary>A span's member or a span made, as a value (code, or a specification's Length and cells); else null.</summary>
        private KExpr SpanExpr(IOperation e, LowerMode mode)
        {
            switch (e)
            {
                case IPropertyReferenceOperation { Property.Name: "Length" or "Count", Instance: { } si } when IsSpan(si.Type):
                    return Length(Lower(si, mode));
                case IPropertyReferenceOperation { Property.Name: "IsEmpty", Instance: { } se } when IsSpan(se.Type):
                    return Eq(Length(Lower(se, mode)), KLit.Zero);
                case IPropertyReferenceOperation { Property.IsIndexer: true, Instance: { } sx, Arguments.Length: 1 } ix when IsSpan(sx.Type):
                {
                    var s = Lower(sx, mode);
                    var (a, i) = SpanCell(s, Lower(ix.Arguments[0].Value, mode), ix.Syntax, mode.InSpec, out var within);
                    var cell = new KElem
                    {
                        Unchecked = true,
                        NoNull = true,
                        Array = a,
                        Index = i,
                        ArrayType = CellsOf(sx.Type),
                        InSpec = mode.InSpec,
                        At = ix.Syntax,
                        ArrayAt = sx.Syntax,
                    };
                    return mode.InSpec ? new KOp("$need", within, cell) : cell;
                }
            }
            if (mode.InSpec)
            {
                return null;
            }
            switch (e)
            {
                // (stackalloc T[n]: a new base of n cells, the size not negative, CSV1003)
                case IConversionOperation { Operand.Syntax: Microsoft.CodeAnalysis.CSharp.Syntax.StackAllocArrayCreationExpressionSyntax } sc when IsSpan(sc.Type):
                    return StackAlloc(sc.Operand, sc.Type);
                case { Syntax: Microsoft.CodeAnalysis.CSharp.Syntax.StackAllocArrayCreationExpressionSyntax } sa when IsSpan(sa.Type):
                    return StackAlloc(sa, sa.Type);
                // (an array as a span; a span as a read-only one)
                case IConversionOperation c when IsSpan(c.Type) && c.Operand.Type is IArrayTypeSymbol && IsElement(((IArrayTypeSymbol)c.Operand.Type).ElementType):
                    return SpanOfArray(c.Type, Lower(c.Operand, mode));
                case IConversionOperation c when IsSpan(c.Type) && IsSpan(c.Operand.Type):
                    return Lower(c.Operand, mode);
                case IObjectCreationOperation oc when IsSpan(oc.Type) && oc.Constructor is { } ctor && ctor.Parameters.Length is 1 or 3 && ctor.Parameters[0].Type is IArrayTypeSymbol &&
                                                      ctor.Parameters.Skip(1).All(p => p.Type.SpecialType == SpecialType.System_Int32) && oc.Initializer == null:
                {
                    var args = Operands(oc.Arguments.OrderBy(a => a.Parameter.Ordinal).Select(a => a.Value).ToArray());
                    var whole = SpanOfArray(oc.Type, args[0]);
                    if (args.Length == 1)
                    {
                        return whole;
                    }
                    return Subspan(oc.Type, whole, args[1], args[2], oc.Syntax);
                }
                case IInvocationOperation inv when inv.TargetMethod.ContainingType?.ToDisplayString() == "System.MemoryExtensions" && inv.TargetMethod.Name == "AsSpan" &&
                                                   inv.TargetMethod.Parameters.Length >= 1 && inv.TargetMethod.Parameters[0].Type is IArrayTypeSymbol at && IsElement(at.ElementType) &&
                                                   inv.TargetMethod.Parameters.Skip(1).All(p => p.Type.SpecialType == SpecialType.System_Int32) && IsSpan(inv.Type):
                {
                    var args = Operands(inv.Arguments.OrderBy(a => a.Parameter.Ordinal).Select(a => a.Value).ToArray());
                    Emit(KCheck.Of(
                        NotNull(args[0]),
                        "CSV1013",
                        inv.Arguments[0].Value.Syntax,
                        $"'{inv.Arguments.OrderBy(a => a.Parameter.Ordinal).First().Value.Syntax}' might be null in '{inv.Syntax}'"));
                    var whole = SpanOfArray(inv.Type, args[0]);
                    if (args.Length == 1)
                    {
                        return whole;
                    }
                    return Subspan(inv.Type, whole, args[1], args.Length == 3 ? args[2] : Minus(Length(args[0]), args[1]), inv.Syntax);
                }
                case IInvocationOperation sl when sl.Instance != null && IsSpan(sl.Instance.Type) && sl.TargetMethod.Name == "Slice" && sl.Arguments.Length is 1 or 2:
                {
                    var s = Lower(sl.Instance, mode);
                    var args = Operands(sl.Arguments.OrderBy(a => a.Parameter.Ordinal).Select(a => a.Value).ToArray());
                    return Subspan(sl.Type, s, args[0], args.Length == 2 ? args[1] : Minus(Length(s), args[0]), sl.Syntax);
                }
                case IInvocationOperation cp when cp.Instance != null && IsSpan(cp.Instance.Type) && cp.TargetMethod.Name is "CopyTo" or "TryCopyTo" && cp.Arguments.Length == 1 && IsSpan(cp.Arguments[0].Value.Type):
                {
                    var s = Lower(cp.Instance, mode);
                    var d = Lower(cp.Arguments[0].Value, mode);
                    var fits = Le(Length(s), Length(d));
                    if (cp.TargetMethod.Name == "CopyTo")
                    {
                        Emit(KCheck.Of(
                            fits,
                            "CSV1001",
                            cp.Syntax,
                            $"'{cp.Syntax}': the destination might be shorter than the source (it would throw ArgumentException)"));
                    }
                    // (as memmove: the source read before anything is written, so overlapping spans copy right)
                    var map = Elements(CellsOf(cp.Instance.Type));
                    var (lo, hi) = (SOff(d), Plus(SOff(d), Length(s)));
                    var y = new KVar("y$");
                    var copied = Ite(AndAlso(Le(lo, y), Lt(y, hi)),
                        Sel(map, SBase(s), Plus(SOff(s), Minus(y, lo))), Sel(map, SBase(d), y));
                    var row = cp.TargetMethod.Name == "CopyTo" ? copied : Ite(fits, copied, Sel(map, SBase(d), y));
                    Emit(KRow.Of(map, SBase(d), MapLambda("y$: int", row), at: cp.Syntax));
                    return cp.TargetMethod.Name == "CopyTo" ? KLit.True : fits;
                }
                // (MemoryExtensions' IndexOf(span, v) and StartsWith(span, prefix) of a scalar span, in code: as their stubs say)
                case IInvocationOperation se when !mode.InSpec && se.TargetMethod.IsStatic && se.TargetMethod.ContainingType?.ToDisplayString() == "System.MemoryExtensions" &&
                                                  se.TargetMethod.Name is "IndexOf" or "StartsWith" && se.Arguments.Length == 2 &&
                                                  IsSpan(Unconverted(se.Arguments.First(a => a.Parameter.Ordinal == 0).Value).Type):
                {
                    var ordered = se.Arguments.OrderBy(a => a.Parameter.Ordinal).ToList();
                    var st = Unconverted(ordered[0].Value).Type;
                    var sp = Lower(Unconverted(ordered[0].Value), mode);
                    var map = Elements(CellsOf(st));
                    var i = new KVar("i$m");
                    var r = Declare("t$" + _temps++, se.Type);
                    Emit(KHavoc.Of(r));
                    var rv = new KVar(r);
                    if (se.TargetMethod.Name == "IndexOf")
                    {
                        if (!IsSpan(st) || IsSpan(Unconverted(ordered[1].Value).Type))
                        {
                            return null;
                        }
                        var v = Lower(ordered[1].Value, mode);
                        Emit(KAssume.Of(AndAlso(Le(KLit.MinusOne, rv), Lt(rv, Length(sp)))));
                        Emit(KAssume.Of(Implies(Ge(rv, KLit.Zero), Eq(SpanElementAt(sp, rv, map), v))));
                        Emit(KSpecStmt.AssumedFree(
                            Within(KLit.Zero, Ite(Lt(rv, KLit.Zero), Length(sp), rv), Ne(SpanElementAt(sp, i, map), v), i),
                            se.Syntax,
                            argumentAt: se.Syntax));
                    }
                    else
                    {
                        if (!IsSpan(Unconverted(ordered[1].Value).Type))
                        {
                            return null;
                        }
                        var pre = Lower(Unconverted(ordered[1].Value), mode);
                        Emit(KSpecStmt.AssumedFree(
                            Eq(rv, AndAlso(Le(Length(pre), Length(sp)), Within(KLit.Zero, Length(pre), Eq(SpanElementAt(sp, i, map), SpanElementAt(pre, i, map)), i))),
                            se.Syntax,
                            argumentAt: se.Syntax));
                    }
                    return rv;
                }
                case IInvocationOperation fl when fl.Instance != null && IsSpan(fl.Instance.Type) && (fl.TargetMethod.Name == "Fill" && fl.Arguments.Length == 1 || fl.TargetMethod.Name == "Clear" && fl.Arguments.Length == 0):
                {
                    var s = Lower(fl.Instance, mode);
                    var v = fl.TargetMethod.Name == "Fill" ? Lower(fl.Arguments[0].Value, mode) : Default(SpanElement(fl.Instance.Type));
                    var map = Elements(CellsOf(fl.Instance.Type));
                    var y = new KVar("y$");
                    var row = Ite(AndAlso(Le(SOff(s), y), Lt(y, Plus(SOff(s), Length(s)))), v, Sel(map, SBase(s), y));
                    Emit(KRow.Of(map, SBase(s), MapLambda("y$: int", row), at: fl.Syntax));
                    return KLit.True;
                }
            }
            return null;
        }

        private KExpr Within(KExpr lo, KExpr hi, KExpr body, KVar i) => KQuant.ForAll(
            "i$m",
            Implies(AndAlso(Le(lo, i), Lt(i, hi)), body));

        private KExpr SpanElementAt(KExpr span, KExpr i, string map) => Sel(map, SBase(span), Plus(SOff(span), i));

        private KExpr StackAlloc(IOperation op, ITypeSymbol spanType)
        {
            var sa = (Microsoft.CodeAnalysis.CSharp.Syntax.StackAllocArrayCreationExpressionSyntax)op.Syntax;
            var rank = sa.Type is Microsoft.CodeAnalysis.CSharp.Syntax.ArrayTypeSyntax at ? at.RankSpecifiers.FirstOrDefault()?.Sizes.FirstOrDefault() : null;
            if (rank == null || !(_model.GetOperation(rank) is IOperation n) || sa.Initializer != null)
            {
                throw new NotTranslated("a stackalloc of no size, or with an initializer");
            }
            var size = Expr(n);
            Emit(KCheck.Of(Le(KLit.Zero, size), "CSV1003", sa, $"'{sa}': the size might be negative"));
            var t = Declare("t$" + _temps++, CellsOf(spanType));
            Emit(KNew.Of(t, CellsOf(spanType), size));
            return SpanOfArray(spanType, new KVar(t));
        }

        /// <summary>s[i] = v of a span: i within it (CSV1003), the base's cell written.</summary>
        private bool SpanAssign(IOperation target, KExpr value)
        {
            if (!(target is IPropertyReferenceOperation { Property.IsIndexer: true, Instance: { } sx, Arguments.Length: 1 } ix) || !IsSpan(sx.Type))
            {
                return false;
            }
            var v = Operands(sx, ix.Arguments[0].Value);
            var (a, i) = SpanCell(v[0], v[1], ix.Syntax, inSpec: false, out _);
            Emit(new KStore
            {
                Unchecked = true,
                NoNull = true,
                Array = a,
                Index = i,
                Value = value,
                ArrayType = CellsOf(sx.Type),
                At = ix.Syntax,
                ArrayAt = sx.Syntax,
            });
            return true;
        }
    }
}
