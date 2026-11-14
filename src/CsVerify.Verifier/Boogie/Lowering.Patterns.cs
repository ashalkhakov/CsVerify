using System;
using System.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.Operations;
using static CsVerify.Verifier.Boogie.KernelTypes;
using static CsVerify.Verifier.Boogie.KOp;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>Patterns: type, constant, relational, list and property patterns; type tests.</summary>
    internal sealed partial class Lowering
    {
        /// <summary>o is C, of a class or an interface: not null, and of a dynamic type below C's.</summary>
        private KExpr ClassTest(KExpr v, ITypeSymbol t)
        {
            _p.AddClassType(t.OriginalDefinition);
            var test = AndAlso(NotNull(v), new KOp("sub", new KOp("dtype", v), new KLit(TypeConst(t))));
            // (an instance of a class with invariants, in code: they hold, as of every one that was built)
            if (HasObjectInvariant(t) && _cfgBlock != null && !_inSpecTest)
            {
                Emit(KAssumeInvariant.Of(v, test, t));
            }
            return test;
        }

        /// <summary>A type test in a specification: nothing emitted for it.</summary>
        private bool _inSpecTest;

        /// <summary>In code: a value of a static type (not null) is an instance of it, as C# has it.</summary>
        private void StaticType(KExpr v, ITypeSymbol type, bool inSpec)
        {
            if (inSpec || !IsModeledClass(type))
            {
                return;
            }
            _p.AddClassType(type.OriginalDefinition);
            Emit(KAssume.Of(Implies(NotNull(v), new KOp("sub", new KOp("dtype", v), new KLit(TypeConst(type))))));
        }

        /// <summary>A pattern, as a condition of the value; the variables it declares bound to their parts.</summary>
        /// <summary>A pattern of a reference that tests only for null: is null, is not null, a discard, a declaration of its own type (x is { } y too).</summary>
        private static bool NullPattern(IPatternOperation p) => p switch
        {
            IConstantPatternOperation cp => cp.Value.ConstantValue is { HasValue: true, Value: null },
            INegatedPatternOperation np => NullPattern(np.Pattern),
            IDiscardPatternOperation _ => true,
            IDeclarationPatternOperation d => SymbolEqualityComparer.Default.Equals(d.MatchedType?.WithNullableAnnotation(NullableAnnotation.None), d.InputType.WithNullableAnnotation(NullableAnnotation.None)),
            IRecursivePatternOperation r => r.DeconstructionSubpatterns.Length == 0 && r.PropertySubpatterns.Length == 0 &&
                                            (r.MatchedType == null || SymbolEqualityComparer.Default.Equals(r.MatchedType.WithNullableAnnotation(NullableAnnotation.None), r.InputType.WithNullableAnnotation(NullableAnnotation.None))),
            _ => false,
        };

        /// <summary>A pattern of a nullable value: null, or a pattern of its value where it has one.</summary>
        private KExpr NullablePattern(IPatternOperation p, KExpr v, ITypeSymbol nullable, LowerMode mode)
        {
            var has = NotNull(v);
            var u = Underlying(nullable);
            switch (p)
            {
                case IDiscardPatternOperation _: return KLit.True;
                case IConstantPatternOperation c when c.Value.ConstantValue is { HasValue: true, Value: null }: return IsNull(v);
                case INegatedPatternOperation n: return Not(SubPattern(n.Pattern, v, nullable, mode, u));
                case IBinaryPatternOperation b: return new KOp(b.OperatorKind == BinaryOperatorKind.And ? "&&" : "||", SubPattern(b.LeftPattern, v, nullable, mode, u), SubPattern(b.RightPattern, v, nullable, mode, u));
                case IDeclarationPatternOperation d when d.MatchesNull:
                    if (d.DeclaredSymbol is ILocalSymbol dl)
                    {
                        Bind(dl, v, mode);
                    }
                    return KLit.True;
                case IDeclarationPatternOperation d:
                    if (d.DeclaredSymbol is ILocalSymbol dv)
                    {
                        Bind(dv, NullableValue(v, nullable), mode);
                    }
                    return has;
                case ITypePatternOperation _: return has;
                default: return AndAlso(has, Pattern(p, NullableValue(v, nullable), u, mode));
            }
        }

        private KExpr SubPattern(IPatternOperation q, KExpr v, ITypeSymbol nullable, LowerMode mode, ITypeSymbol u) => IsNullableValue(q.InputType) ? NullablePattern(q, v, nullable, mode) : Pattern(q, NullableValue(v, nullable), u, mode);

        private KExpr Pattern(IPatternOperation p, KExpr v, ITypeSymbol type, LowerMode mode)
        {
            switch (p)
            {
                case IDiscardPatternOperation _: return KLit.True;
                case IDeclarationPatternOperation d:
                {
                    if (d.DeclaredSymbol is ILocalSymbol l)
                    {
                        Bind(l, v, mode);
                    }
                    return d.MatchesNull ? KLit.True : IsData(d.MatchedType) ? TypeTest(d.MatchedType, type, v) :
                           IsModeledClass(d.MatchedType) && !SymbolEqualityComparer.Default.Equals(d.MatchedType.OriginalDefinition, type.OriginalDefinition) ? ClassTest(v, d.MatchedType) :
                           IsNullable(type) ? NotNull(v) : KLit.True;
                }
                case ITypePatternOperation tp: return TypeTest(tp.MatchedType, type, v);
                case IConstantPatternOperation sc when IsString(type) && sc.Value.ConstantValue is { HasValue: true, Value: string }:
                    return AndAlso(NotNull(v), new KOp("streq", v, Lower(sc.Value, mode)));
                case IConstantPatternOperation cp: return Eq(v, Lower(cp.Value, mode));
                case IRelationalPatternOperation rp:
                {
                    var op = rp.OperatorKind switch
                    {
                        BinaryOperatorKind.LessThan => "<", BinaryOperatorKind.LessThanOrEqual => "<=", BinaryOperatorKind.GreaterThan => ">",
                        BinaryOperatorKind.GreaterThanOrEqual => ">=", BinaryOperatorKind.Equals => "==", BinaryOperatorKind.NotEquals => "!=",
                        _ => throw new NotTranslated("the pattern " + rp.Syntax),
                    };
                    return new KOp(op, v, Lower(rp.Value, mode));
                }
                case INegatedPatternOperation np: return Not(Pattern(np.Pattern, v, type, mode));
                case IBinaryPatternOperation bp:
                    return new KOp(bp.OperatorKind == BinaryOperatorKind.And ? "&&" : "||", Pattern(bp.LeftPattern, v, type, mode), Pattern(bp.RightPattern, v, type, mode));
                // (x is { } y of a reference: not null)
                case IRecursivePatternOperation rn when !IsData(type) && NullPattern(rn):
                    if (rn.DeclaredSymbol is ILocalSymbol rl)
                    {
                        Bind(rl, v, mode);
                    }
                    return NotNull(v);
                // (a class's property pattern, p is { F: 3 }: not null, and each field as its pattern says)
                case IRecursivePatternOperation cp when IsClass(type) && !IsData(type) && cp.DeconstructionSubpatterns.Length == 0 &&
                                                        (cp.MatchedType == null || SymbolEqualityComparer.Default.Equals(cp.MatchedType.WithNullableAnnotation(NullableAnnotation.None), type.WithNullableAnnotation(NullableAnnotation.None))):
                {
                    if (cp.DeclaredSymbol is ILocalSymbol cl)
                    {
                        Bind(cl, v, mode);
                    }
                    KExpr cond = NotNull(v);
                    foreach (var sp in cp.PropertySubpatterns)
                    {
                        var member = sp.Member switch { IFieldReferenceOperation f => (ISymbol)f.Field, IPropertyReferenceOperation pr => pr.Property, _ => null };
                        if (member == null || member.IsStatic || !IsField(member.OriginalDefinition))
                        {
                            throw new NotTranslated("a property pattern of " + sp.Member.Syntax);
                        }
                        var read = new KField
                        {
                            Field = member.OriginalDefinition,
                            Instance = v,
                            NoNull = true,
                            At = sp.Syntax,
                            InstanceAt = sp.Syntax,
                        };
                        cond = AndAlso(cond, Pattern(sp.Pattern, read, FieldType(member), mode));
                    }
                    return cond;
                }
                // (a tuple's positional pattern, (0, var y): each item as its pattern says; a tuple is never null)
                case IRecursivePatternOperation tup when IsTuple(type) && tup.PropertySubpatterns.Length == 0 && tup.DeconstructionSubpatterns.Length == PartsOf(type).Count():
                {
                    if (tup.DeclaredSymbol is ILocalSymbol tl)
                    {
                        Bind(tl, v, mode);
                    }
                    KExpr cond = KLit.True;
                    var parts = PartsOf(type).ToList();
                    for (int k = 0; k < parts.Count; k++)
                    {
                        cond = AndAlso(cond, Pattern(tup.DeconstructionSubpatterns[k], TupleItem(v, type, k), parts[k], mode));
                    }
                    return cond;
                }
                case IRecursivePatternOperation rp when rp.MatchedType == null || IsData(rp.MatchedType):
                {
                    var matched = rp.MatchedType ?? type;
                    if (!IsData(matched))
                    {
                        throw new NotTranslated("a recursive pattern of " + matched);
                    }
                    KExpr cond = TypeTest(matched, type, v);
                    if (rp.DeclaredSymbol is ILocalSymbol l)
                    {
                        Bind(l, v, mode);
                    }
                    for (int k = 0; k < rp.DeconstructionSubpatterns.Length; k++)
                    {
                        var prop = DataTypes.PositionalProperty((INamedTypeSymbol)matched, k) ?? throw new NotTranslated("a deconstruction of " + matched);
                        var actual = Actual(matched, prop.Name);
                        cond = AndAlso(cond, Pattern(rp.DeconstructionSubpatterns[k], FieldOfData(v, prop, matched), actual?.Type ?? prop.Type, mode));
                    }
                    foreach (var sp in rp.PropertySubpatterns)
                    {
                        if (!(sp.Member is IPropertyReferenceOperation { Property: IPropertySymbol member }) || !DataTypes.IsPositional(member.OriginalDefinition))
                        {
                            throw new NotTranslated("a property pattern of " + sp.Member.Syntax);
                        }
                        cond = AndAlso(cond, Pattern(sp.Pattern, FieldOfData(v, member.OriginalDefinition, matched), member.Type, mode));
                    }
                    return cond;
                }
                // (an array's list pattern, [a, .., b]: not null, of a length, each element as its pattern says, those after
                // the slice counted from the end)
                case IListPatternOperation lp when IsArray(type) && type is IArrayTypeSymbol { Rank: 1 } at:
                {
                    // (a is [1, ..] b: b is the array matched)
                    if (lp.DeclaredSymbol is ILocalSymbol whole)
                    {
                        Bind(whole, v, mode);
                    }
                    else if (lp.DeclaredSymbol != null)
                    {
                        throw new NotTranslated("a list pattern that declares its value");
                    }
                    int slice = lp.Patterns.IndexOf(lp.Patterns.FirstOrDefault(x => x is ISlicePatternOperation));
                    var slicePattern = slice >= 0 ? ((ISlicePatternOperation)lp.Patterns[slice]).Pattern : null;
                    // (in a specification a pattern makes nothing: there a slice's own pattern binds the slice itself, of
                    // which Spec reads its Length and elements; only a variable's, .. var rest)
                    bool sliceInSpec = slicePattern != null && _cfgBlock == null;
                    if (sliceInSpec && !(slicePattern is IDeclarationPatternOperation { DeclaredSymbol: ILocalSymbol }))
                    {
                        throw new NotTranslated("a slice pattern with a pattern of its own, in a specification");
                    }
                    int fixedCount = lp.Patterns.Length - (slice >= 0 ? 1 : 0);
                    var len = Length(v);
                    KExpr cond = AndAlso(NotNull(v), new KOp(slice >= 0 ? ">=" : "==", len, new KLit(fixedCount.ToString())));
                    // (.. var rest: a new array of the elements between, as C#'s GetSubArray makes; where v doesn't match
                    // the length, an empty one nothing reads)
                    if (sliceInSpec)
                    {
                        Bind(((IDeclarationPatternOperation)slicePattern).DeclaredSymbol as ILocalSymbol, new KOp("$slice", v, new KLit(slice.ToString()), Minus(len, new KLit(fixedCount.ToString()))), mode);
                    }
                    else if (slicePattern != null)
                    {
                        var between = Ite(cond, Minus(len, new KLit(fixedCount.ToString())), KLit.Zero);
                        var rest = CopyOf(v, new KLit(slice.ToString()), between, type, lp.Syntax);
                        cond = AndAlso(cond, Pattern(slicePattern, rest, type, mode));
                    }
                    for (int k = 0; k < lp.Patterns.Length; k++)
                    {
                        if (k == slice)
                        {
                            continue;
                        }
                        KExpr index = slice < 0 || k < slice ? new KLit(k.ToString()) : Minus(len, new KLit((lp.Patterns.Length - k).ToString()));
                        var element = new KElem
                        {
                            Array = v,
                            Index = index,
                            ArrayType = type,
                            Unchecked = true,
                            NoNull = true,
                            InSpec = true,
                            At = lp.Syntax,
                            ArrayAt = lp.Syntax,
                        };
                        cond = AndAlso(cond, Pattern(lp.Patterns[k], element, at.ElementType, mode));
                    }
                    return cond;
                }
                default: throw new NotTranslated("the pattern " + p.Kind);
            }
        }

        private KExpr TypeTest(ITypeSymbol t, ITypeSymbol type, KExpr v)
        {
            if (t == null || SymbolEqualityComparer.Default.Equals(DataTypes.Def(t), DataTypes.Def(type)) && !IsData(t))
            {
                return KLit.True;
            }
            if (IsData(t))
            {
                Data(t);
                return IsCase(v, t);
            }
            if (Scalar(t) && SymbolEqualityComparer.Default.Equals(t, type))
            {
                return KLit.True;
            }
            if (IsModeledClass(t))
            {
                return ClassTest(v, t);
            }
            throw new NotTranslated("a type test of " + t);
        }
    }
}
