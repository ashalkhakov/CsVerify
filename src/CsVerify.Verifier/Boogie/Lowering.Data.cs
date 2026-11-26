using System;
using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.Operations;
using static CsVerify.Verifier.Boogie.KernelTypes;
using static CsVerify.Verifier.Boogie.KOp;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>Values shared by code and specifications: data types (records), structs, tuples, nullable values, enums.</summary>
    internal sealed partial class Lowering
    {
        // ------------------------------------------------------------------ data types

        /// <summary>Pattern variables in a specification: what they are bound to.</summary>
        private readonly Dictionary<ILocalSymbol, KExpr> _bound = new Dictionary<ILocalSymbol, KExpr>(SymbolEqualityComparer.Default);

        private void BindInCode(ILocalSymbol l, KExpr v)
        {
            Emit(KAssign.Of(Declare(Local(l), l.Type), v));
            // (a value a pattern binds is valid, as every data value is: its invariant was proved where it was built)
            if (HasInvariants(l.Type))
            {
                AssumeValid(new KVar(Local(l)), l.Type);
            }
        }

        /// <summary>A value of a type with invariants: valid (where it isn't null).</summary>
        private void AssumeValid(KExpr v, ITypeSymbol t)
        {
            if (!HasInvariants(t))
            {
                return;
            }
            foreach (var inv in DataTypes.Invariants(DataTypes.Def(t)))
            {
                InvariantBody(inv.OriginalDefinition, _isFunction, _literal, _contractOf);
            }
            Data(t);
            _p.AddValid(DataTypes.Def(t));
            Emit(KAssume.Of(OrElse(IsNull(v), new KOp(ValidName(t), v))));
        }

        private void Data(ITypeSymbol t)
        {
            var def = DataTypes.Def(t);
            _p.AddDataType(def);
            foreach (var c in KernelTypes.Data.KnownCases(def))
            {
                _p.AddDataType(c);
            }
        }

        /// <summary>A data value's field, as the type it's read at has it (unboxed where generic).</summary>
        private KExpr FieldOfData(KExpr v, IPropertySymbol prop, ITypeSymbol at) =>
            Unbox(new KOp(FieldFunction(prop), v), prop.OriginalDefinition.Type, Actual(at, prop.Name)?.Type ?? prop.Type);

        /// <summary>
        /// The data types' operations, in code or in a specification (each lowers its operands its own way): a case's
        /// construction, a field's read, type tests and patterns, casts, a record's ==; null where it is none.
        /// </summary>
        private KExpr DataExpr(IOperation e, LowerMode mode)
        {
            var wasSpec = _inSpecTest;
            _inSpecTest = mode.InSpec;
            try
            {
                return DataExprCore(e, mode);
            }
            finally
            {
                _inSpecTest = wasSpec;
            }
        }

        private KExpr DataExprCore(IOperation e, LowerMode mode)
        {
            // (a span: Lowering.Spans; a decimal: Lowering.Decimals)
            if (SpanExpr(e, mode) is KExpr span)
            {
                return span;
            }
            if (DecimalExpr(e, mode) is KExpr dec)
            {
                return dec;
            }
            if (TimeArith(e, mode) is KExpr time)
            {
                return time;
            }
            switch (e)
            {
                case IArrayElementReferenceOperation: return DataExprCoreOfArrayElementReference(e, mode);
                case IInvocationOperation: return DataExprCoreOfInvocation(e, mode);
                case IPropertyReferenceOperation: return DataExprCoreOfPropertyReference(e, mode);
                case IFieldReferenceOperation: return DataExprCoreOfFieldReference(e, mode);
                case IMethodReferenceOperation: return DataExprCoreOfMethodReference(e, mode);
                case IEventReferenceOperation: return DataExprCoreOfEventReference(e, mode);
                case IDefaultValueOperation: return DataExprCoreOfDefaultValue(e, mode);
                case IObjectCreationOperation: return DataExprCoreOfObjectCreation(e, mode);
                case IConversionOperation: return DataExprCoreOfConversion(e, mode);
                case IBinaryOperation: return DataExprCoreOfBinary(e, mode);
                case IIsPatternOperation: return DataExprCoreOfIsPattern(e, mode);
                case IUnaryOperation: return DataExprCoreOfUnary(e, mode);
                case ITupleBinaryOperation: return DataExprCoreOfTupleBinary(e, mode);
                case IAnonymousObjectCreationOperation: return DataExprCoreOfAnonymousObjectCreation(e, mode);
                case ITupleOperation: return DataExprCoreOfTuple(e, mode);
                case IIsTypeOperation: return DataExprCoreOfIsType(e, mode);
                case ISwitchExpressionOperation: return DataExprCoreOfSwitchExpression(e, mode);
                default: return DataExprCoreOther(e, mode);
            }
        }

        /// <summary>DataExprCore of a array element reference: its forms, in order; any other as DataExprCoreOther.</summary>
        private KExpr DataExprCoreOfArrayElementReference(IOperation e, LowerMode mode)
        {
            switch (e)
            {
                // (a rectangular array's cell: each index within its dimension)
                case IArrayElementReferenceOperation me when IsMultiArray(me.ArrayReference.Type) && me.Indices.Length == ((IArrayTypeSymbol)me.ArrayReference.Type).Rank:
                {
                    var a = Lower(me.ArrayReference, mode);
                    var ix = me.Indices.Select(o => Lower(o, mode)).ToList();
                    var cell = new KElem
                    {
                        Unchecked = true,
                        Array = a,
                        Index = CellOf(ix),
                        ArrayType = me.ArrayReference.Type,
                        InSpec = mode.InSpec,
                        At = me.Syntax,
                        ArrayAt = me.ArrayReference.Syntax,
                    };
                    return MultiIndices(a, ix, me.Syntax, cell, mode.InSpec);
                }
                default: return DataExprCoreOther(e, mode);
            }
        }

        /// <summary>DataExprCore of a invocation: its forms, in order; any other as DataExprCoreOther.</summary>
        private KExpr DataExprCoreOfInvocation(IOperation e, LowerMode mode)
        {
            switch (e)
            {
                // (a with expression's copy of a data value: the value, as a data value has no identity; of null it throws)
                case IInvocationOperation { TargetMethod.Name: "<Clone>$", Instance: { } wi } when IsData(wi.Type):
                {
                    var v = Lower(wi, mode);
                    if (!mode.InSpec)
                    {
                        Emit(KCheck.Of(NotNull(v), "CSV1013", wi.Syntax, $"'{wi.Syntax}' might be null in a with expression"));
                    }
                    return v;
                }
                // (Array.Empty<T>(): an empty array, the same each time)
                case IInvocationOperation { TargetMethod: { Name: "Empty", IsStatic: true, ContainingType.SpecialType: SpecialType.System_Array }, Arguments.Length: 0 }:
                    return new KOp("$aempty");
                // (char.IsAsciiDigit(c) and the other ASCII tests: ranges of its code)
                case IInvocationOperation at when AsciiTest(at.TargetMethod) && at.Arguments.Length == 1:
                {
                    var c = Lower(at.Arguments[0].Value, mode);
                    KExpr In(char lo, char hi) => AndAlso(Le(Number(lo), c), Le(c, Number(hi)));
                    return at.TargetMethod.Name switch
                    {
                        "IsAsciiDigit" => In('0', '9'),
                        "IsAsciiLetterUpper" => In('A', 'Z'),
                        "IsAsciiLetterLower" => In('a', 'z'),
                        "IsAsciiLetter" => OrElse(In('A', 'Z'), In('a', 'z')),
                        "IsAsciiLetterOrDigit" => OrElse(In('0', '9'), OrElse(In('A', 'Z'), In('a', 'z'))),
                        "IsAsciiHexDigit" => OrElse(In('0', '9'), OrElse(In('A', 'F'), In('a', 'f'))),
                        _ => Le(c, Number(127)),
                    };
                }
                // (x.CompareTo(y) of integers, decimals, DateTimes and TimeSpans: the sign of x - y)
                case IInvocationOperation { TargetMethod.Name: "CompareTo", Instance: { } cx, Arguments.Length: 1 } ct when
                    (IsIntegral(cx.Type) || IsDecimal(cx.Type) || IsOpaqueTicks(cx.Type)) &&
                    SymbolEqualityComparer.Default.Equals(cx.Type, ct.Arguments[0].Value.Type) && ct.TargetMethod.DeclaringSyntaxReferences.Length == 0:
                {
                    var (l, r) = (Lower(cx, mode), Lower(ct.Arguments[0].Value, mode));
                    return Ite(Lt(l, r), Minus(KLit.Zero, KLit.One), Ite(Gt(l, r), KLit.One, KLit.Zero));
                }
                // (its length of a dimension, d within its rank; and its Length, their product)
                case IInvocationOperation gl when gl.TargetMethod.Name == "GetLength" && gl.TargetMethod.ContainingType?.SpecialType == SpecialType.System_Array && gl.Instance != null &&
                                                 Unconverted(gl.Instance) is IOperation gli && IsMultiArray(gli.Type) && gl.Arguments.Length == 1:
                    return MultiArrayLength(gl, gli, mode);
                case IInvocationOperation ng when ng.Instance != null && IsNullableValue(ng.Instance.Type) && ng.TargetMethod.Name == "GetValueOrDefault":
                {
                    var v = Lower(ng.Instance, mode);
                    var otherwise = ng.Arguments.Length == 1 ? Lower(ng.Arguments[0].Value, mode) : Default(Underlying(ng.Instance.Type));
                    return Ite(NotNull(v), NullableValue(v, ng.Instance.Type), otherwise);
                }
                case IInvocationOperation fm when FloatMember(fm.TargetMethod) is string member:
                {
                    var args = fm.Arguments.OrderBy(a => a.Parameter.Ordinal).Select(a => Lower(a.Value, mode)).ToArray();
                    return FloatCall(member, fm.TargetMethod.Parameters[0].Type, args, fm.Type, mode.InSpec);
                }
                // (a ghost value: the value itself)
                // (ghost code: mathematics, in code too)
                case IInvocationOperation go when SpecSymbols.IsCsVerifyType(go.TargetMethod.ContainingType, "Ghost") && go.TargetMethod.Name == "Of" && go.Arguments.Length == 1:
                    return mode.InSpec ? Lower(go.Arguments[0].Value, mode) : Spec(go.Arguments[0].Value, null);
                // (a ghost set of objects' members, ObjSet.Empty, ==: mathematics in code too)
                case IInvocationOperation os when !mode.InSpec && IsObjSet(os.TargetMethod.ContainingType):
                    return Spec(os, null);
                default: return DataExprCoreOther(e, mode);
            }
        }

        private KExpr MultiArrayLength(IInvocationOperation gl, IOperation gli, LowerMode mode)
        {
            int rank = ((IArrayTypeSymbol)gli.Type).Rank;
            var a = Lower(gli, mode);
            var d = Lower(gl.Arguments[0].Value, mode);
            KExpr len = new KOp("$dim", a, new KLit((rank - 1).ToString()));
            for (int k = rank - 2; k >= 0; k--)
            {
                len = Ite(Eq(d, new KLit(k.ToString())), new KOp("$dim", a, new KLit(k.ToString())), len);
            }
            return Defined(AndAlso(NotNull(a), AndAlso(Le(KLit.Zero, d), Lt(d, new KLit(rank.ToString())))), len,
                           "CSV1003", gl.Syntax, $"dimension in '{gl.Syntax}' might be out of range", mode.InSpec);
        }

        /// <summary>DataExprCore of a property reference: its forms, in order; any other as DataExprCoreOther.</summary>
        private KExpr DataExprCoreOfPropertyReference(IOperation e, LowerMode mode)
        {
            switch (e)
            {
                case IPropertyReferenceOperation ml when ml.Property.Name == "Length" && ml.Instance != null && IsMultiArray(ml.Instance.Type):
                {
                    var a = Lower(ml.Instance, mode);
                    KExpr len = new KOp("$dim", a, KLit.Zero);
                    for (int k = 1; k < ((IArrayTypeSymbol)ml.Instance.Type).Rank; k++)
                    {
                        len = Times(len, new KOp("$dim", a, new KLit(k.ToString())));
                    }
                    return Defined(NotNull(a), len, "CSV1013", ml.Syntax, $"'{ml.Instance.Syntax}' might be null in '{ml.Syntax}'", mode.InSpec);
                }
                // (a struct's member: its element)
                case IMemberReferenceOperation sm when StructMember(sm) is (IOperation si, int sk):
                    return StructItem(sm, si, sk, mode);
                case IPropertyReferenceOperation np when np.Instance != null && IsNullableValue(np.Instance.Type) && np.Property.Name is "HasValue" or "Value":
                {
                    var v = Lower(np.Instance, mode);
                    if (np.Property.Name == "HasValue")
                    {
                        return NotNull(v);
                    }
                    if (!mode.InSpec)
                    {
                        Emit(KCheck.Of(NotNull(v), "CSV1013", np.Syntax, $"'{np.Syntax}' might be read when '{np.Instance.Syntax}' is null"));
                    }
                    return NullableValue(v, np.Instance.Type);
                }
                case IPropertyReferenceOperation dp when dp.Instance != null && IsData(dp.Instance.Type) && DataTypes.IsDataField(dp.Property.OriginalDefinition):
                    return PositionalProperty(dp, mode);
                case IPropertyReferenceOperation tk when tk.Property.Name == "Ticks" && tk.Instance != null && IsOpaqueTicks(tk.Instance.Type):
                    return Lower(tk.Instance, mode);
                // (a tuple written here: a value of its elements; an element of one: a function of it)
                // (a GroupBy group's Key: its first element's key)
                case IPropertyReferenceOperation { Property.Name: "Key", Instance: ILocalReferenceOperation gk } when IsLinqGroup(gk.Type):
                    return GroupKey(gk.Local);
                // (the first group's key: its first element's; no group, it throws)
                case IPropertyReferenceOperation { Property.Name: "Key", Instance: IInvocationOperation { TargetMethod.Name: "First", Arguments.Length: 1 } fg } when IsLinqGroup(fg.Type) &&
                        Unconverted(fg.Arguments[0].Value) is IInvocationOperation gb && IsEnumerableCall(gb.TargetMethod) && gb.TargetMethod.Name == "GroupBy" && gb.Arguments.Length == 2 && !mode.InSpec:
                    return FirstGroupKey(gb, fg);
                case IPropertyReferenceOperation jrm when jrm.Instance is ILocalReferenceOperation jrl && _joinRows.ContainsKey(jrl.Local) && JoinRowMember(jrm) is KExpr jrv:
                    return jrv;
                case IPropertyReferenceOperation ap when ap.Instance != null && ap.Instance.Type?.IsAnonymousType == true && IsTuple(ap.Instance.Type) && PartIndex(ap.Instance.Type, ap.Property.Name) is int pi && pi >= 0:
                    return TupleItem(Lower(ap.Instance, mode), ap.Instance.Type, pi);
                // (a pointer's or a memory view's ghost property: a function of it)
                case IPropertyReferenceOperation mp when mp.Instance != null && IsMemValue(mp.Instance.Type) && mp.Property.Name is "Addr" or "Length" or "Index" or "Value" or "Elems":
                    _p.MemViews |= IsMemView(mp.Instance.Type);
                    return MemProp(mp.Property.Name, Lower(mp.Instance, mode), mp.Instance.Type);
                // (a sealed value's content: a function of it)
                case IPropertyReferenceOperation sv when sv.Instance != null && IsSealedValue(sv.Instance.Type) && sv.Property.Name == "Content":
                    return SealedContent(Lower(sv.Instance, mode), sv.Instance.Type);
                case IPropertyReferenceOperation { Property.Name: "Empty", Instance: null } oe when !mode.InSpec && IsObjSet(oe.Type):
                    return Spec(oe, null);
                case IPropertyReferenceOperation gv when gv.Property.Name == "Value" && IsGhost(gv.Instance?.Type) &&
                                                         !(gv.Instance is IPropertyReferenceOperation { Property.Name: "Obj" } obj && (IsView(obj.Instance?.Type) || IsShare(obj.Instance?.Type))):
                    return Lower(gv.Instance, mode);
                // (a view's object, v.Obj.Value: the view itself, in code too)
                case IPropertyReferenceOperation { Property.Name: "Value", Instance: IPropertyReferenceOperation { Property.Name: "Obj" } vo } when IsView(vo.Instance?.Type) || IsShare(vo.Instance?.Type):
                    return Lower(vo.Instance, mode);
                default: return DataExprCoreOther(e, mode);
            }
        }

        /// <summary>char's ASCII tests, static and exact.</summary>
        private static bool AsciiTest(IMethodSymbol m) =>
            m.IsStatic && m.ContainingType?.SpecialType == SpecialType.System_Char && m.Parameters.Length == 1 && m.Parameters[0].Type.SpecialType == SpecialType.System_Char &&
            m.Name is "IsAsciiDigit" or "IsAsciiLetterUpper" or "IsAsciiLetterLower" or "IsAsciiLetter" or "IsAsciiLetterOrDigit" or "IsAsciiHexDigit" or "IsAscii";

        /// <summary>
        /// A struct's member: its element. In code, one of a non-nullable reference type is not null, as C#'s nullable
        /// analysis has it (default(S) aside).
        /// </summary>
        private KExpr StructItem(IMemberReferenceOperation sm, IOperation whole, int k, LowerMode mode)
        {
            var item = TupleItem(Lower(whole, mode), whole.Type, k);
            if (!mode.InSpec && !IsData(sm.Type) && IsNullable(sm.Type) && NotNullable(sm.Type))
            {
                Emit(KAssume.Of(NotNull(item)));
            }
            return item;
        }

        /// <summary>DataExprCore of a field reference: its forms, in order; any other as DataExprCoreOther.</summary>
        private KExpr DataExprCoreOfFieldReference(IOperation e, LowerMode mode)
        {
            switch (e)
            {
                // (a struct's member: its element)
                case IMemberReferenceOperation sm when StructMember(sm) is (IOperation si, int sk):
                    return StructItem(sm, si, sk, mode);
                case IFieldReferenceOperation { Instance: null, ConstantValue: { HasValue: true } fcv } ff when IsFloating(ff.Type):
                    return FloatLiteral(fcv.Value, ff.Type);
                case IFieldReferenceOperation tc when TimeConstant(tc) is KExpr ticks:
                    return ticks;
                // (Guid.Empty: the id 0; a new Guid's isn't known, so it may be it)
                case IFieldReferenceOperation { Instance: null, Field.Name: "Empty" } ge when IsOpaqueId(ge.Field.ContainingType):
                    return KLit.Zero;
                case IFieldReferenceOperation tf when tf.Instance != null && IsTuple(tf.Instance.Type) && tf.Field.ContainingType is INamedTypeSymbol { IsTupleType: true } tt &&
                                                      tt.TupleElements.Select(x => x.CorrespondingTupleField ?? x).ToList().FindIndex(x => x.Name == (tf.Field.CorrespondingTupleField ?? tf.Field).Name) is int ti && ti >= 0:
                    return TupleItem(Lower(tf.Instance, mode), tf.Instance.Type, ti);
                default: return DataExprCoreOther(e, mode);
            }
        }

        /// <summary>DataExprCore of a method reference: its forms, in order; any other as DataExprCoreOther.</summary>
        private KExpr DataExprCoreOfMethodReference(IOperation e, LowerMode mode)
        {
            switch (e)
            {
                // (a struct's member: its element)
                case IMemberReferenceOperation sm when StructMember(sm) is (IOperation si, int sk):
                    return StructItem(sm, si, sk, mode);
                default: return DataExprCoreOther(e, mode);
            }
        }

        /// <summary>DataExprCore of a event reference: its forms, in order; any other as DataExprCoreOther.</summary>
        private KExpr DataExprCoreOfEventReference(IOperation e, LowerMode mode)
        {
            switch (e)
            {
                // (a struct's member: its element)
                case IMemberReferenceOperation sm when StructMember(sm) is (IOperation si, int sk):
                    return StructItem(sm, si, sk, mode);
                default: return DataExprCoreOther(e, mode);
            }
        }

        /// <summary>DataExprCore of a default value: its forms, in order; any other as DataExprCoreOther.</summary>
        private KExpr DataExprCoreOfDefaultValue(IOperation e, LowerMode mode)
        {
            switch (e)
            {
                // (a memory value made by default, a forged one (CSV0006): its address, length and index 0, nothing else known)
                case IDefaultValueOperation md when IsMemValue(md.Type) && !mode.InSpec:
                    return ForgedMemValue(md);
                // (a struct made without a constructor of its own, default(S): its default value)
                case IDefaultValueOperation sd when IsStruct(sd.Type):
                    return StructDefault(sd.Type);
                // (default(T) of another type of the kernel's, int? or a reference: null, 0, false; ?. makes one)
                case IDefaultValueOperation dd when dd.Type != null && (IsNullableValue(dd.Type) || Scalar(dd.Type) || IsNullable(dd.Type)) && !IsMemValue(dd.Type):
                    return Default(dd.Type);
                default: return DataExprCoreOther(e, mode);
            }
        }

        private KExpr ForgedMemValue(IDefaultValueOperation md)
        {
            var t = Declare("t$" + _temps++, md.Type);
            Emit(KHavoc.Of(t));
            foreach (var prop in SpecSymbols.IsCsVerifyType(md.Type, "PointsTo`1") || SpecSymbols.IsCsVerifyType(md.Type, "Ptr`1") ? new[] { "Addr" } : new[] { "Addr", "Length" })
            {
                Emit(KAssume.Of(Eq(MemProp(prop, new KVar(t), md.Type), KLit.Zero)));
            }
            return new KVar(t);
        }

        /// <summary>DataExprCore of a object creation: its forms, in order; any other as DataExprCoreOther.</summary>
        private KExpr DataExprCoreOfObjectCreation(IOperation e, LowerMode mode)
        {
            switch (e)
            {
                case IObjectCreationOperation so when IsStruct(so.Type) && so.Initializer == null && (so.Constructor == null || so.Constructor.IsImplicitlyDeclared) && so.Arguments.Length == 0:
                    return StructDefault(so.Type);
                case IObjectCreationOperation oc when IsData(oc.Type) && oc.Constructor != null && (oc.Initializer == null || InitFieldsSet(oc.Initializer) != null):
                    return NewData(oc, mode);
                // (a positional record struct's primary constructor: the struct of its arguments)
                case IObjectCreationOperation ps when IsStruct(ps.Type) && ps.Initializer == null && IsPositionalStruct(ps.Constructor):
                {
                    var ordered = ps.Arguments.OrderBy(a => a.Parameter.Ordinal).Select(a => a.Value).ToArray();
                    var values = mode.InSpec ? ordered.Select(a => Lower(a, mode)).ToArray() : Operands(ordered);
                    return MakeTuple(ps.Type, values);
                }
                default: return DataExprCoreOther(e, mode);
            }
        }

        /// <summary>DataExprCore of a conversion: its forms, in order; any other as DataExprCoreOther.</summary>
        private KExpr DataExprCoreOfConversion(IOperation e, LowerMode mode)
        {
            switch (e)
            {
                // (a nullable value, int?: null, or the reference of its value)
                case IConversionOperation nc when IsNullableValue(nc.Type) && !IsNullableValue(nc.Operand.Type) && nc.OperatorMethod == null:
                    return NullableOfValue(nc, mode);
                // (int? to long?: null stays null, a value widens)
                case IConversionOperation nn when IsNullableValue(nn.Type) && IsNullableValue(nn.Operand.Type) && nn.OperatorMethod == null && nn.Conversion.IsImplicit &&
                                                  IsIntegral(Underlying(nn.Type)) && IsIntegral(Underlying(nn.Operand.Type)):
                {
                    var v = Operand(nn.Operand, mode);
                    return Ite(IsNull(v), KLit.Null, NullableOf(NullableValue(v, nn.Operand.Type), nn.Type));
                }
                case IConversionOperation nu when IsNullableValue(nu.Operand.Type) && !IsNullableValue(nu.Type) && nu.OperatorMethod == null:
                {
                    if (!SymbolEqualityComparer.Default.Equals(nu.Type, Underlying(nu.Operand.Type)))
                    {
                        throw new NotTranslated("a conversion of " + nu.Operand.Type + " to " + nu.Type);
                    }
                    var v = Lower(nu.Operand, mode);
                    if (!mode.InSpec)
                    {
                        Emit(KCheck.Of(NotNull(v), "CSV1013", nu.Syntax, $"'{nu.Operand.Syntax}' might be null where '{nu.Syntax}' unwraps it"));
                    }
                    return NullableValue(v, nu.Operand.Type);
                }
                case IConversionOperation fc when (IsFloating(fc.Type) || IsFloating(fc.Operand.Type)) && fc.Conversion.IsNumeric && fc.OperatorMethod == null:
                    return FloatConversion(fc, Lower(fc.Operand, mode), mode.InSpec);
                case IConversionOperation tc when IsTuple(tc.Type) && Unconverted(tc.Operand) is ITupleOperation tlit && ((INamedTypeSymbol)tc.Type).IsTupleType && tlit.Elements.Length == ((INamedTypeSymbol)tc.Type).TupleElements.Length:
                    return TupleConverted(tc, tlit, mode);
                case IConversionOperation up when up.IsImplicit && IsData(up.Type) && IsData(up.Operand.Type):
                    return Lower(up.Operand, mode);
                // (o as C: o where it's an instance of C, else null)
                case IConversionOperation tc when tc.IsTryCast && tc.Conversion.IsReference && IsModeledClass(tc.Type) && (IsRef(tc.Operand.Type) || IsString(tc.Operand.Type)):
                {
                    var v = Operand(tc.Operand, mode);
                    StaticType(v, tc.Operand.Type, mode.InSpec);
                    return Ite(ClassTest(v, tc.Type), v, KLit.Null);
                }
                // ((C)o, a downcast: o, which must be null or an instance of C)
                case IConversionOperation dc when !dc.IsImplicit && !dc.IsTryCast && dc.Conversion.IsReference && !dc.Conversion.IsImplicit && IsModeledClass(dc.Type) && (IsRef(dc.Operand.Type) || IsString(dc.Operand.Type)):
                    return DataCast(dc, mode);
                // ((object)o, an upcast written as a cast: o)
                // (a string as an object, in code: a reference of its own, which another equal string's may or may not be)
                case IConversionOperation so when !mode.InSpec && so.Conversion.IsReference && IsString(so.Operand.Type) && so.Type.SpecialType == SpecialType.System_Object:
                    return StringUpcast(so, mode);
                // (not a string's: as an object, one isn't its value, which another equal string may be)
                case IConversionOperation uc when !uc.IsImplicit && uc.Conversion.IsReference && uc.Conversion.IsImplicit && (IsRef(uc.Type) || IsString(uc.Type)) && IsRef(uc.Operand.Type):
                    return Lower(uc.Operand, mode);
                // (d as C, of data: d where it's a C, else null; it never throws)
                case IConversionOperation ta when ta.IsTryCast && ta.Conversion.IsReference && IsData(ta.Type) && IsData(ta.Operand.Type):
                {
                    Data(ta.Type);
                    var v = Operand(ta.Operand, mode);
                    return Ite(AndAlso(NotNull(v), IsCase(v, ta.Type)), v, KLit.Null);
                }
                case IConversionOperation down when !down.IsImplicit && down.Conversion.IsReference && IsData(down.Type) && IsData(down.Operand.Type):
                    return DataDownCast(down, mode);
                default: return DataExprCoreOther(e, mode);
            }
        }

        private KExpr NullableOfValue(IConversionOperation nc, LowerMode mode)
        {
            if (nc.Operand.Type == null || nc.Operand.ConstantValue is { HasValue: true, Value: null } || nc.Operand is IDefaultValueOperation)
            {
                return KLit.Null;
            }
            var u = Underlying(nc.Type);
            if (!(SymbolEqualityComparer.Default.Equals(nc.Operand.Type, u) || IsIntegral(u) && IsIntegral(nc.Operand.Type) && nc.Conversion.IsImplicit))
            {
                throw new NotTranslated("a conversion of " + nc.Operand.Type + " to " + nc.Type);
            }
            return NullableOf(Lower(nc.Operand, mode), nc.Type);
        }

        private KExpr DataCast(IConversionOperation dc, LowerMode mode)
        {
            var v = Operand(dc.Operand, mode);
            StaticType(v, dc.Operand.Type, mode.InSpec);
            var castOk = OrElse(IsNull(v), ClassTest(v, dc.Type));
            CastThrows(castOk, mode.InSpec);
            return new KCast
            {
                Value = v,
                Test = castOk,
                At = dc.Syntax,
            };
        }

        private KExpr DataDownCast(IConversionOperation down, LowerMode mode)
        {
            Data(down.Type);
            var v = Operand(down.Operand, mode);
            var downOk = OrElse(IsNull(v), IsCase(v, down.Type));
            CastThrows(downOk, mode.InSpec);
            return new KCast
            {
                Value = v,
                Test = downOk,
                At = down.Syntax,
            };
        }

        /// <summary>DataExprCore of a binary: its forms, in order; any other as DataExprCoreOther.</summary>
        private KExpr DataExprCoreOfBinary(IOperation e, LowerMode mode)
        {
            switch (e)
            {
                // (objects compared in a database query's lambda, with SQL's nulls (UseRelationalNulls): where one that may be
                // null is, SQL's unknown, for each comparison, as for strings; against the literal null, IS NULL, exact)
                case IBinaryOperation rb when _inDatabase > 0 && KernelTypes.Ef?.RelationalNulls == true && rb.OperatorMethod == null &&
                                              rb.OperatorKind is BinaryOperatorKind.Equals or BinaryOperatorKind.NotEquals &&
                                              Unconverted(rb.LeftOperand).Type is { IsReferenceType: true } lt && !IsString(lt) && IsRef(lt) &&
                                              Unconverted(rb.RightOperand).Type is { IsReferenceType: true } rt && !IsString(rt) && IsRef(rt):
                    return RelationalNullsCompared(rb, mode);
                // (lifted: == on the values, or both null; the comparisons false where either is null)
                case IBinaryOperation nb when (nb.OperatorMethod == null || nb.IsLifted && OpaqueOperator(nb.OperatorMethod)) && (IsNullableValue(nb.LeftOperand.Type) || nb.LeftOperand.Type == null) && (IsNullableValue(nb.RightOperand.Type) || nb.RightOperand.Type == null) &&
                                              (IsNullableValue(nb.LeftOperand.Type) || IsNullableValue(nb.RightOperand.Type)):
                    return LiftedBinary(nb, mode);
                // (DateTime and TimeSpan compared: their ticks, the int the kernel keeps for them, are what C# compares)
                case IBinaryOperation dt when IsOpaqueTicks(dt.LeftOperand.Type) && SymbolEqualityComparer.Default.Equals(dt.LeftOperand.Type, dt.RightOperand.Type) &&
                                              dt.OperatorKind is BinaryOperatorKind.Equals or BinaryOperatorKind.NotEquals or BinaryOperatorKind.LessThan or BinaryOperatorKind.LessThanOrEqual
                                                  or BinaryOperatorKind.GreaterThan or BinaryOperatorKind.GreaterThanOrEqual:
                    return TicksCompared(dt, mode);
                // (Guids compared: their ints, one per value)
                case IBinaryOperation gd when IsOpaqueId(gd.LeftOperand.Type) && SymbolEqualityComparer.Default.Equals(gd.LeftOperand.Type, gd.RightOperand.Type) &&
                                              gd.OperatorKind is BinaryOperatorKind.Equals or BinaryOperatorKind.NotEquals:
                    return TicksCompared(gd, mode);
                // (a record struct's synthesized ==: field by field)
                case IBinaryOperation rs when rs.OperatorMethod?.IsImplicitlyDeclared == true && HasStructEquality(rs.LeftOperand.Type) &&
                                              SymbolEqualityComparer.Default.Equals(rs.LeftOperand.Type, rs.RightOperand.Type) && rs.OperatorKind is BinaryOperatorKind.Equals or BinaryOperatorKind.NotEquals:
                {
                    var (l, r) = (Lower(rs.LeftOperand, mode), Lower(rs.RightOperand, mode));
                    KExpr same = KLit.True;
                    for (int k = StructFields(rs.LeftOperand.Type).Count - 1; k >= 0; k--)
                    {
                        same = AndAlso(Eq(TupleItem(l, rs.LeftOperand.Type, k), TupleItem(r, rs.LeftOperand.Type, k)), same);
                    }
                    return rs.OperatorKind == BinaryOperatorKind.Equals ? same : Not(same);
                }
                // (float and double, as IEEE 754: operations round to nearest; == is IEEE's, < and the rest false at NaN)
                case IBinaryOperation fb when fb.OperatorMethod == null && IsFloating(fb.LeftOperand.Type) && IsFloating(fb.RightOperand.Type):
                    return FloatBinary(fb, mode);
                case IBinaryOperation ob when !mode.InSpec && ob.OperatorMethod != null && IsObjSet(ob.OperatorMethod.ContainingType):
                    return Spec(ob, null);
                // (an anonymous object compared with null: its reference, null where an OrDefault found none, never one made)
                case IBinaryOperation an when AnonymousVsNull(an) is var (anon, anonEq):
                    return new KOp(anonEq ? "==" : "!=", Lower(anon, mode), KLit.Null);
                // (a record's == and !=: its values' equality, which is its references', a value being its constructor's)
                case IBinaryOperation eq when eq.OperatorMethod != null && eq.OperatorKind is BinaryOperatorKind.Equals or BinaryOperatorKind.NotEquals &&
                                              IsData(eq.OperatorMethod.ContainingType):
                    return RecordEquality(eq, mode);
                // (a nullable struct's == and !=, the synthesized operator lifted: with null, whether it has a value; else
                // both null, or neither and their values equal)
                case IBinaryOperation ns when ns.OperatorKind is BinaryOperatorKind.Equals or BinaryOperatorKind.NotEquals && ns.IsLifted && ns.OperatorMethod is { IsImplicitlyDeclared: true } &&
                                              (IsNullableStruct(ns.LeftOperand.Type) || IsNullableStruct(ns.RightOperand.Type)):
                {
                    var (l, r) = (LoweredSide(ns.LeftOperand, mode), LoweredSide(ns.RightOperand, mode));
                    bool withNull = Unconverted(ns.LeftOperand).ConstantValue is { HasValue: true, Value: null } || Unconverted(ns.RightOperand).ConstantValue is { HasValue: true, Value: null };
                    var same = withNull ? Eq(l, r) : ValuesEqual(l, r, IsNullableStruct(ns.LeftOperand.Type) ? ns.LeftOperand.Type : ns.RightOperand.Type, ns.Syntax, 0)
                                                     ?? throw new NotTranslated("== of " + ns.OperatorMethod.ContainingType.Name);
                    return ns.OperatorKind == BinaryOperatorKind.Equals ? same : Not(same);
                }
                // (a value object's == and !=: the same object, or two whose fields are equal; not where its own Equals decides)
                case IBinaryOperation vo when vo.OperatorMethod != null && vo.OperatorMethod.IsImplicitlyDeclared && vo.OperatorKind is BinaryOperatorKind.Equals or BinaryOperatorKind.NotEquals &&
                                              IsValueObject(vo.OperatorMethod.ContainingType) && !OwnEquals(vo.OperatorMethod.ContainingType):
                    return ValueObjectEquality(vo, mode);
                // (a record struct's == and !=: each field equal, as its synthesized Equals compares them)
                case IBinaryOperation rs when rs.OperatorMethod != null && rs.OperatorMethod.IsImplicitlyDeclared && rs.OperatorKind is BinaryOperatorKind.Equals or BinaryOperatorKind.NotEquals &&
                                              IsStruct(rs.OperatorMethod.ContainingType) && !OwnEquals(rs.OperatorMethod.ContainingType):
                {
                    var t = rs.OperatorMethod.ContainingType;
                    var same = ValuesEqual(Lower(rs.LeftOperand, mode), Lower(rs.RightOperand, mode), t, rs.Syntax, 0) ?? throw new NotTranslated("== of " + t.Name);
                    return rs.OperatorKind == BinaryOperatorKind.Equals ? same : Not(same);
                }
                default: return DataExprCoreOther(e, mode);
            }
        }

        /// <summary>DataExprCore of a is pattern: its forms, in order; any other as DataExprCoreOther.</summary>
        private KExpr DataExprCoreOfIsPattern(IOperation e, LowerMode mode)
        {
            switch (e)
            {
                case IIsPatternOperation nip when IsNullableValue(Unconverted(nip.Value).Type):
                    return NullablePattern(nip.Pattern, Operand(Unconverted(nip.Value), mode), Unconverted(nip.Value).Type, mode);
                case IIsPatternOperation ip when IsData(Unconverted(ip.Value).Type) || Scalar(ip.Value.Type) ||
                                                 (IsRef(ip.Value.Type) || IsString(ip.Value.Type)) && NullPattern(ip.Pattern) ||
                                                 IsArray(Unconverted(ip.Value).Type) && ip.Pattern is IListPatternOperation ||
                                                 IsTuple(Unconverted(ip.Value).Type) && ip.Pattern is IRecursivePatternOperation || IsStruct(Unconverted(ip.Value).Type) ||
                                                 IsClass(Unconverted(ip.Value).Type) && !IsData(Unconverted(ip.Value).Type) && ip.Pattern is IRecursivePatternOperation ||
                                                 (IsRef(Unconverted(ip.Value).Type) || IsString(Unconverted(ip.Value).Type) || IsException(Unconverted(ip.Value).Type)) && !IsData(Unconverted(ip.Value).Type):
                    return IsPattern(ip, mode);
                default: return DataExprCoreOther(e, mode);
            }
        }

        /// <summary>DataExprCore of a unary: its forms, in order; any other as DataExprCoreOther.</summary>
        private KExpr DataExprCoreOfUnary(IOperation e, LowerMode mode)
        {
            switch (e)
            {
                case IUnaryOperation fu when IsFloating(fu.Operand.Type) && fu.OperatorKind is UnaryOperatorKind.Minus or UnaryOperatorKind.Plus:
                    return fu.OperatorKind == UnaryOperatorKind.Minus ? new KOp("$fp.neg" + FloatSize(fu.Operand.Type), Lower(fu.Operand, mode)) : Lower(fu.Operand, mode);
                default: return DataExprCoreOther(e, mode);
            }
        }

        /// <summary>DataExprCore of a tuple binary: its forms, in order; any other as DataExprCoreOther.</summary>
        private KExpr DataExprCoreOfTupleBinary(IOperation e, LowerMode mode)
        {
            switch (e)
            {
                // (t == u of tuples: the left's elements, then the right's, compared element by element)
                case ITupleBinaryOperation tb when TupleComparable(tb.LeftOperand.Type) && TupleComparable(tb.RightOperand.Type):
                    return TuplesCompared(tb, mode);
                default: return DataExprCoreOther(e, mode);
            }
        }

        private KExpr TuplesCompared(ITupleBinaryOperation tb, LowerMode mode)
        {
            var l = TupleParts(tb.LeftOperand, mode);
            var r = TupleParts(tb.RightOperand, mode);
            KExpr same = KLit.True;
            for (int k = l.Count - 1; k >= 0; k--)
            {
                same = k == l.Count - 1 ? Eq(l[k], r[k]) : AndAlso(Eq(l[k], r[k]), same);
            }
            return tb.OperatorKind == BinaryOperatorKind.Equals ? same : Not(same);
        }

        /// <summary>DataExprCore of a anonymous object creation: its forms, in order; any other as DataExprCoreOther.</summary>
        private KExpr DataExprCoreOfAnonymousObjectCreation(IOperation e, LowerMode mode)
        {
            switch (e)
            {
                // (an anonymous object, new { s, b = e }: a tuple of its members; a member read, an element)
                case IAnonymousObjectCreationOperation ao when IsTuple(ao.Type):
                    return AnonymousObject(ao, mode);
                default: return DataExprCoreOther(e, mode);
            }
        }

        /// <summary>DataExprCore of a tuple: its forms, in order; any other as DataExprCoreOther.</summary>
        private KExpr DataExprCoreOfTuple(IOperation e, LowerMode mode)
        {
            switch (e)
            {
                case ITupleOperation tu when IsTuple(tu.Type):
                    return NewTuple(tu, mode);
                default: return DataExprCoreOther(e, mode);
            }
        }

        /// <summary>DataExprCore of a is type: its forms, in order; any other as DataExprCoreOther.</summary>
        private KExpr DataExprCoreOfIsType(IOperation e, LowerMode mode)
        {
            switch (e)
            {
                // (o is C of a class: not null, an instance of C; a value of its static type is an instance of that)
                case IIsTypeOperation ct when IsModeledClass(ct.TypeOperand) && (IsRef(ct.ValueOperand.Type) || IsString(ct.ValueOperand.Type) || IsException(ct.ValueOperand.Type)):
                {
                    var v = Operand(ct.ValueOperand, mode);
                    StaticType(v, ct.ValueOperand.Type, mode.InSpec);
                    var test = ClassTest(v, ct.TypeOperand);
                    return ct.IsNegated ? Not(test) : test;
                }
                case IIsTypeOperation it when IsData(it.TypeOperand) && !it.IsNegated:
                    Data(it.TypeOperand);
                    return IsCase(Operand(it.ValueOperand, mode), it.TypeOperand);
                default: return DataExprCoreOther(e, mode);
            }
        }

        /// <summary>DataExprCore of a switch expression: its forms, in order; any other as DataExprCoreOther.</summary>
        private KExpr DataExprCoreOfSwitchExpression(IOperation e, LowerMode mode)
        {
            switch (e)
            {
                case ISwitchExpressionOperation sw when mode.InSpec:
                    return SpecSwitchExpression(sw, mode);
                default: return DataExprCoreOther(e, mode);
            }
        }

        /// <summary>DataExprCore of an operation none of the forms above is.</summary>
        private KExpr DataExprCoreOther(IOperation e, LowerMode mode)
        {
            return null;
        }

        private KExpr RelationalNullsCompared(IBinaryOperation rb, LowerMode mode)
        {
            var (l, r) = (Lower(Unconverted(rb.LeftOperand), mode), Lower(Unconverted(rb.RightOperand), mode));
            var same = Eq(l, r);
            return RelationalStrings(rb, rb.OperatorKind == BinaryOperatorKind.Equals ? same : Not(same), l, r);
        }

        private KExpr LiftedBinary(IBinaryOperation nb, LowerMode mode)
        {
            var (l, r) = (LoweredSide(nb.LeftOperand, mode), LoweredSide(nb.RightOperand, mode));
            var t = nb.LeftOperand.Type;
            // (in a database query's lambda, with SQL's nulls (UseRelationalNulls): == and != where either is null are
            // unknown, SQL's unknown, for each comparison; as in C# where neither is)
            if (_inDatabase > 0 && KernelTypes.Ef?.RelationalNulls == true && nb.OperatorKind is BinaryOperatorKind.Equals or BinaryOperatorKind.NotEquals &&
                nb.LeftOperand.Type != null && nb.RightOperand.Type != null && !(Unconverted(nb.LeftOperand).ConstantValue is { HasValue: true, Value: null }) &&
                !(Unconverted(nb.RightOperand).ConstantValue is { HasValue: true, Value: null }))
            {
                var unknown = new KVar(LinqMap("[Ref][Ref]bool"));
                var eq = Ite(OrElse(IsNull(l), IsNull(r)), Sel(unknown, l, r), Eq(l, r));
                return nb.OperatorKind == BinaryOperatorKind.Equals ? eq : Not(eq);
            }
            // (+, -, * of two values of one integral type: null where either is; checked where both have values,
            // their values 0 otherwise, which can't overflow)
            if (nb.OperatorKind is BinaryOperatorKind.Add or BinaryOperatorKind.Subtract or BinaryOperatorKind.Multiply &&
                IsIntegral(Underlying(t)) && SymbolEqualityComparer.Default.Equals(t, nb.RightOperand.Type) && IsNullableValue(nb.Type))
            {
                if (!mode.InSpec)
                {
                    l = Operand(nb.LeftOperand, mode);
                    r = Operand(nb.RightOperand, mode);
                }
                var both = AndAlso(NotNull(l), NotNull(r));
                var u = Underlying(nb.Type);
                var sum = mode.InSpec ? new KOp(Op(nb.OperatorKind), Ite(both, NullableValue(l, t), KLit.Zero), Ite(both, NullableValue(r, t), KLit.Zero)) : Arith(Op(nb.OperatorKind), Ite(both, NullableValue(l, t), KLit.Zero), Ite(both, NullableValue(r, t), KLit.Zero), u, nb.Syntax, nb.IsChecked);
                if (!mode.InSpec)
                {
                    var tv = Declare("t$" + _temps++, u);
                    Emit(KAssign.Of(tv, sum));
                    sum = new KVar(tv);
                }
                return Ite(both, NullableOf(sum, nb.Type), KLit.Null);
            }
            // (&, |, ^ of two values of one integral type: null where either is, else the values' bits')
            if (nb.OperatorKind is BinaryOperatorKind.And or BinaryOperatorKind.Or or BinaryOperatorKind.ExclusiveOr &&
                IsIntegral(Underlying(t)) && SymbolEqualityComparer.Default.Equals(t, nb.RightOperand.Type) && IsNullableValue(nb.Type))
            {
                if (!mode.InSpec)
                {
                    l = Operand(nb.LeftOperand, mode);
                    r = Operand(nb.RightOperand, mode);
                }
                var both = AndAlso(NotNull(l), NotNull(r));
                var u = Underlying(nb.Type);
                var bits = Bitwise(nb.OperatorKind, Ite(both, NullableValue(l, t), KLit.Zero), Ite(both, NullableValue(r, t), KLit.Zero), u, mode.InSpec);
                if (!mode.InSpec)
                {
                    var tv = Declare("t$" + _temps++, u);
                    Emit(KAssign.Of(tv, bits));
                    bits = new KVar(tv);
                }
                return Ite(both, NullableOf(bits, nb.Type), KLit.Null);
            }
            return nb.OperatorKind switch
            {
                BinaryOperatorKind.Equals => Eq(l, r), BinaryOperatorKind.NotEquals => Ne(l, r),
                BinaryOperatorKind.LessThan => LiftedBoth("<", t, nb, l, r), BinaryOperatorKind.LessThanOrEqual => LiftedBoth("<=", t, nb, l, r),
                BinaryOperatorKind.GreaterThan => LiftedBoth(">", t, nb, l, r), BinaryOperatorKind.GreaterThanOrEqual => LiftedBoth(">=", t, nb, l, r),
                _ => throw new NotTranslated("the lifted operator " + nb.OperatorKind),
            };
        }

        /// <summary>DateTime's, TimeSpan's or Guid's own operator (==, &lt;): as the int the kernel keeps for them compares.</summary>
        private static bool OpaqueOperator(IMethodSymbol m) =>
            m.DeclaringSyntaxReferences.Length == 0 && (IsOpaqueTicks(m.ContainingType) || IsOpaqueId(m.ContainingType));

        private KExpr LiftedBoth(string op, ITypeSymbol t, IBinaryOperation nb, KExpr l, KExpr r) => (IsIntegral(Underlying(t)) || IsOpaqueTicks(Underlying(t))) && SymbolEqualityComparer.Default.Equals(t, nb.RightOperand.Type)
            ? AndAlso(AndAlso(NotNull(l), NotNull(r)), new KOp(op, NullableValue(l, t), NullableValue(r, t)))
            : throw new NotTranslated("the lifted operator " + nb.OperatorKind);

        private KExpr LoweredSide(IOperation x, LowerMode mode) => x.Type == null ? KLit.Null : Lower(x, mode);

        /// <summary>A record struct's primary constructor, its fields its positional properties', in its parameters' order: it only stores them.</summary>
        private static bool IsPositionalStruct(IMethodSymbol ctor) =>
            ctor != null && ctor.ContainingType is { IsRecord: true, TypeKind: TypeKind.Struct } t &&
            ctor.DeclaringSyntaxReferences.Any(r => r.GetSyntax() is Microsoft.CodeAnalysis.CSharp.Syntax.RecordDeclarationSyntax) &&
            StructFields(t).Select(f => (f.AssociatedSymbol as IPropertySymbol)?.Name).SequenceEqual(ctor.Parameters.Select(p => p.Name)) &&
            StructFields(t).All(f => f.AssociatedSymbol is IPropertySymbol p && DataTypes.IsPositional(p));

        /// <summary>An object initializer of a case's init properties alone, { Undone = xs }: what it sets them to; else null.</summary>
        private static Dictionary<IPropertySymbol, IOperation> InitFieldsSet(IObjectOrCollectionInitializerOperation init)
        {
            var set = new Dictionary<IPropertySymbol, IOperation>(SymbolEqualityComparer.Default);
            foreach (var x in init.Initializers)
            {
                if (!(x is ISimpleAssignmentOperation { Target: IPropertyReferenceOperation { Instance: IInstanceReferenceOperation, Property: var p } } a) ||
                    !DataTypes.IsInitField(p.OriginalDefinition) || !set.TryAdd(p.OriginalDefinition, a.Value))
                {
                    return null;
                }
            }
            return set;
        }

        /// <summary>An init property's value as given: in code, not null where its type says so.</summary>
        private KExpr InitValue(IOperation given, IPropertySymbol ip, ITypeSymbol actual, LowerMode mode)
        {
            var v = Lower(given, mode);
            if (!mode.InSpec && IsNullable(ip.Type) && NotNullable(ip.Type))
            {
                Emit(KCheck.Of(NotNull(v), "CSV1014", given.Syntax, $"'{given.Syntax}' might be null, but property '{ip.Name}' is not nullable"));
            }
            return v;
        }

        /// <summary>An init property's initializer (a value, as a specification has it), or its type's default.</summary>
        private KExpr InitDefault(IPropertySymbol ip, IMethodSymbol ctor)
        {
            if (!(DataTypes.InitializerOf(ip) is ExpressionSyntax syn))
            {
                return Default(ip.Type);
            }
            var model = KernelTypes.Compilation.ModelOf(syn.SyntaxTree);
            var op = model.GetOperation(syn) ?? throw new NotTranslated("the initializer of " + ip.Name);
            var l = new Lowering(ctor, _contractOf(ctor), syn, model, null, _ => false, _isFunction, _literal, _contractOf);
            return l.Spec(op, null);
        }

        private KExpr NewData(IObjectCreationOperation oc, LowerMode mode)
        {
            Data(oc.Type);
            var ordered = oc.Arguments.OrderBy(a => a.Parameter.Ordinal).ToList();
            var values = mode.InSpec ? ordered.Select(a => Lower(a.Value, mode)).ToArray() : Operands(ordered.Select(a => a.Value).ToArray());
            var def = oc.Constructor.OriginalDefinition;
            // (a non-nullable field isn't null: each construction says so)
            if (!mode.InSpec)
            {
                for (int k = 0; k < ordered.Count; k++)
                {
                    if (IsNullable(def.Parameters[ordered[k].Parameter.Ordinal].Type) && NotNullable(def.Parameters[ordered[k].Parameter.Ordinal].Type))
                    {
                        Emit(KCheck.Of(
                            NotNull(values[k]),
                            "CSV1014",
                            ordered[k].Value.Syntax,
                            $"'{ordered[k].Value.Syntax}' might be null, but parameter '{ordered[k].Parameter.Name}' of '{oc.Type.Name}' is not nullable"));
                    }
                }
            }
            // (a package built: the views that go in are handed over to it)
            if (!mode.InSpec && IsPackage(oc.Type))
            {
                CheckPackage(oc.Type);
                for (int k = 0; k < ordered.Count; k++)
                {
                    if (IsView(def.Parameters[ordered[k].Parameter.Ordinal].Type))
                    {
                        Emit(new KOwn
                        {
                            Kind = "pack",
                            Obj = values[k],
                            Type = ViewOf(ordered[k].Parameter.Type),
                            Into = oc.Type,
                            At = ordered[k].Value.Syntax,
                        });
                    }
                }
            }
            var args = ordered.Select((a, k) => Box(values[k], def.Parameters[a.Parameter.Ordinal].Type, a.Parameter.Type)).ToList();
            // (a case's init properties: as the object initializer sets them, else their initializers)
            var set = oc.Initializer == null ? new Dictionary<IPropertySymbol, IOperation>(SymbolEqualityComparer.Default) : InitFieldsSet(oc.Initializer);
            foreach (var ip in DataTypes.InitFields((INamedTypeSymbol)oc.Type))
            {
                var actual = Actual(oc.Type, ip.Name)?.Type ?? ip.Type;
                args.Add(Box(set.TryGetValue(ip, out var given) ? InitValue(given, ip, actual, mode) : InitDefault(ip, def), ip.Type, actual));
            }
            KExpr made = new KOp(CaseName((INamedTypeSymbol)oc.Type), args.ToArray());
            // (a case whose constructor checks its arguments before it stores them: built where no check throws)
            if (StoredChecksHold(oc, def, ordered, values) is KExpr holds0)
            {
                if (mode.InSpec)
                {
                    made = Ite(holds0, made, Thrown(oc.Type, oc.Syntax));
                }
                else if ((_p.Ghost || _contract.IsPure || _contract.IsLemma) && !(_p.Partial && !_p.Ghost))
                {
                    Emit(KCheck.Of(holds0, "CSV1011", oc.Syntax, $"'{oc.Syntax}' might throw: what {oc.Type.Name}'s constructor checks might not hold"));
                }
                else
                {
                    // (where it throws: to the handlers, or the path ends)
                    var held = Declare("t$" + _temps++, KernelTypes.Compilation.GetSpecialType(SpecialType.System_Boolean));
                    Emit(KAssign.Of(held, holds0));
                    CastThrows(new KVar(held), false);
                    Emit(KAssume.Of(new KVar(held)));
                }
            }
            if (mode.InSpec || !HasInvariants(oc.Type))
            {
                return made;
            }
            // (an immutable value's invariants: proved where it's built, assumed everywhere else)
            var t = Declare("t$" + _temps++, oc.Type);
            Emit(KAssign.Of(t, made));
            foreach (var inv in DataTypes.Invariants(DataTypes.Def(oc.Type)))
            {
                if (!_isFunction(inv.OriginalDefinition))
                {
                    throw new NotTranslated("an invariant that isn't a function: " + inv.Name);
                }
                var holds = new KFnCall
                {
                    Callee = inv.OriginalDefinition,
                    Receiver = new KVar(t),
                    Args = new KExpr[0],
                    At = oc.Syntax,
                };
                Emit(KCheck.Of(holds, "CSV1015", oc.Syntax, $"invariant '{inv.Name}' of {oc.Type.Name} might not hold for '{oc.Syntax}'"));
            }
            AssumeValid(new KVar(t), oc.Type);
            return new KVar(t);
        }

        /// <summary>
        /// What a case's constructor checks of its arguments before it stores them (SpecSymbols.StoredChecks), all
        /// holding, of these arguments; null where it checks nothing.
        /// </summary>
        private KExpr StoredChecksHold(IObjectCreationOperation oc, IMethodSymbol ctor, List<IArgumentOperation> ordered, KExpr[] values)
        {
            var checks = SpecSymbols.StoredChecks(ctor.ContainingType.OriginalDefinition);
            if (checks.Count == 0 || !SymbolEqualityComparer.Default.Equals(ctor, DataTypes.Constructor(ctor.ContainingType.OriginalDefinition)))
            {
                return null;
            }
            KExpr Argument(IParameterSymbol p) => values[ordered.FindIndex(a => a.Parameter.Ordinal == p.Ordinal)];
            KExpr all = KLit.True;
            foreach (var (condition, throwsWhen, isNull) in checks)
            {
                KExpr c;
                if (isNull != null)
                {
                    c = IsNull(Argument(isNull));
                }
                else
                {
                    var model = Compilations.ModelOf(KernelTypes.Compilation, condition.SyntaxTree);
                    c = Spec(model.GetOperation(condition) ?? throw new NotTranslated("a constructor's check: " + condition), null);
                    // (each parameter named apart, then given its argument: an argument may be a variable of a parameter's name)
                    var names = ctor.Parameters.Select(_ => "k$" + _temps++).ToList();
                    foreach (var p in ctor.Parameters)
                    {
                        c = Nameless.Substitute(c, new KVar(Local(p)), new KVar(names[p.Ordinal]));
                    }
                    foreach (var p in ctor.Parameters)
                    {
                        c = Nameless.Substitute(c, new KVar(names[p.Ordinal]), Argument(p));
                    }
                }
                all = AndAlso(all, throwsWhen ? Not(c) : c);
            }
            return all;
        }

        private KExpr PositionalProperty(IPropertyReferenceOperation dp, LowerMode mode)
        {
            Data(dp.Instance.Type);
            var v = Lower(dp.Instance, mode);
            var prop = dp.Property.OriginalDefinition;
            var read = Unbox(new KDataField
            {
                Function = FieldFunction(prop),
                Value = v,
                At = dp.Syntax,
                ValueAt = dp.Instance.Syntax,
                Struct = dp.Instance.Type.IsValueType,
            }, prop.Type, dp.Type);
            // (a non-nullable field isn't null: each construction checked it)
            if (!mode.InSpec && IsNullable(dp.Type) && NotNullable(prop.Type))
            {
                var nn = Declare("t$" + _temps++, dp.Type);
                Emit(KAssign.Of(nn, read));
                Emit(KAssume.Of(NotNull(new KVar(nn))));
                read = new KVar(nn);
            }
            if (mode.InSpec || !HasInvariants(dp.Type))
            {
                return read;
            }
            var t = Declare("t$" + _temps++, dp.Type);
            Emit(KAssign.Of(t, read));
            AssumeValid(new KVar(t), dp.Type);
            return new KVar(t);
        }

        private KExpr TicksCompared(IBinaryOperation dt, LowerMode mode)
        {
            var (l, r) = (Lower(dt.LeftOperand, mode), Lower(dt.RightOperand, mode));
            var op = dt.OperatorKind switch
            {
                BinaryOperatorKind.Equals => "==", BinaryOperatorKind.NotEquals => "!=", BinaryOperatorKind.LessThan => "<",
                BinaryOperatorKind.LessThanOrEqual => "<=", BinaryOperatorKind.GreaterThan => ">", _ => ">=",
            };
            return new KOp(op, l, r);
        }

        private KExpr FloatBinary(IBinaryOperation fb, LowerMode mode)
        {
            var n = FloatSize(fb.LeftOperand.Type);
            var (l, r) = (Lower(fb.LeftOperand, mode), Lower(fb.RightOperand, mode));
            return fb.OperatorKind switch
            {
                BinaryOperatorKind.Add => new KOp("$fp.add" + n, l, r), BinaryOperatorKind.Subtract => new KOp("$fp.sub" + n, l, r),
                BinaryOperatorKind.Multiply => new KOp("$fp.mul" + n, l, r), BinaryOperatorKind.Divide => new KOp("$fp.div" + n, l, r),
                BinaryOperatorKind.Equals => new KOp("$fp.eq" + n, l, r), BinaryOperatorKind.NotEquals => Not(new KOp("$fp.eq" + n, l, r)),
                BinaryOperatorKind.LessThan => new KOp("$fp.lt" + n, l, r), BinaryOperatorKind.LessThanOrEqual => new KOp("$fp.leq" + n, l, r),
                BinaryOperatorKind.GreaterThan => new KOp("$fp.gt" + n, l, r), BinaryOperatorKind.GreaterThanOrEqual => new KOp("$fp.geq" + n, l, r),
                BinaryOperatorKind.Remainder => new KOp("$fp.fmod" + n, l, r),
                _ => throw new NotTranslated("the float operator " + fb.OperatorKind),
            };
        }

        private KExpr FirstGroupKey(IInvocationOperation gb, IInvocationOperation fg)
        {
            var gsrc = Sequence(gb.Arguments.First(a => a.Parameter.Ordinal == 0).Value);
            var gkey = LambdaArg(gb, 1);
            Emit(KCheck.Of(
                Gt(gsrc.Length, KLit.Zero),
                "CSV1001",
                fg.Syntax,
                "precondition 'Q.Count(source) > 0' of 'First' might not hold"));
            var kv = Declare("t$" + _temps++, gkey.body.Type);
            Emit(KHavoc.Of(kv));
            ShapeFact(Eq(new KVar(kv), Apply(gkey, gsrc.Elem.At(KLit.Zero))), fg.Syntax);
            return new KVar(kv);
        }

        private KExpr AnonymousObject(IAnonymousObjectCreationOperation ao, LowerMode mode)
        {
            var items = ao.Initializers.Select(x => Lower(x is IAssignmentOperation asg ? asg.Value : x, mode)).ToList();
            if (mode.InSpec)
            {
                return new KOp(TupleMaker(ao.Type), items.ToArray());
            }
            var t = Declare("t$" + _temps++, ao.Type);
            Emit(KHavoc.Of(t));
            for (int k = 0; k < items.Count; k++)
            {
                Emit(KAssume.Of(Eq(TupleItem(new KVar(t), ao.Type, k), items[k])));
            }
            return new KVar(t);
        }

        private KExpr TupleConverted(IConversionOperation tc, ITupleOperation tlit, LowerMode mode)
        {
            // (a tuple literal at the type it's converted to: (null, k) as (SlNode?, int))
            var items = tlit.Elements.Select(x => x.ConstantValue is { HasValue: true, Value: null } ? KLit.Null : Lower(x, mode)).ToList();
            if (mode.InSpec)
            {
                throw new NotTranslated("a tuple made in a specification");
            }
            var t = Declare("t$" + _temps++, tc.Type);
            Emit(KHavoc.Of(t));
            for (int k = 0; k < items.Count; k++)
            {
                Emit(KAssume.Of(Eq(TupleItem(new KVar(t), tc.Type, k), items[k])));
            }
            return new KVar(t);
        }

        private KExpr NewTuple(ITupleOperation tu, LowerMode mode)
        {
            var items = tu.Elements.Select(x => Lower(x, mode)).ToList();
            // (in a specification, or a lambda: the tuple of its elements, a function of them)
            if (mode.InSpec)
            {
                return new KOp(TupleMaker(tu.Type), items.ToArray());
            }
            var t = Declare("t$" + _temps++, tu.Type);
            Emit(KHavoc.Of(t));
            for (int k = 0; k < items.Count; k++)
            {
                Emit(KAssume.Of(Eq(TupleItem(new KVar(t), tu.Type, k), items[k])));
            }
            return new KVar(t);
        }

        private KExpr IsPattern(IIsPatternOperation ip, LowerMode mode)
        {
            var v = Operand(Unconverted(ip.Value), mode);
            StaticType(v, Unconverted(ip.Value).Type, mode.InSpec);
            return Pattern(ip.Pattern, v, Unconverted(ip.Value).Type, mode);
        }

        private KExpr SpecSwitchExpression(ISwitchExpressionOperation sw, LowerMode mode)
        {
            var v = Lower(sw.Value, mode);
            KExpr acc = null;
            var arms = sw.Arms.Select(arm =>
            {
                // (of a nullable value, int? or an enum's: its patterns are of its value where it has one)
                var cond = PartPattern(arm.Pattern, v, sw.Value.Type, mode);
                if (arm.Guard != null)
                {
                    cond = AndAlso(cond, Lower(arm.Guard, mode));
                }
                return (cond, value: Lower(arm.Value, mode));
            }).ToList();
            // (where no arm matches, the definition throws: its check says so; the value is the last arm's)
            for (int k = arms.Count - 1; k >= 0; k--)
            {
                acc = acc == null ? arms[k].value : Ite(arms[k].cond, arms[k].value, acc);
            }
            if (acc == null)
            {
                throw new NotTranslated("a switch with no arms");
            }
            // (well-defined only where some arm matches, CSV1012, unless the last arm matches everything)
            var last = sw.Arms.Last();
            if (last.Guard == null && last.Pattern is IDiscardPatternOperation or IDeclarationPatternOperation { MatchesNull: true })
            {
                return acc;
            }
            return new KCast
            {
                Value = acc,
                Test = OrAny(arms.Select(a => a.cond)),
                At = sw.Syntax,
            };
        }

        private KExpr StringUpcast(IConversionOperation so, LowerMode mode)
        {
            var sv = HoistedOperand(so.Operand, mode);
            var o = Declare("t$" + _temps++, so.Type);
            Emit(KHavoc.Of(o));
            Emit(KAssume.Of(Eq(IsNull(new KVar(o)), IsNull(sv))));
            // (the object's contents: the same object, the same string)
            Emit(KAssume.Of(Eq(new KOp("$strOf", new KVar(o)), sv)));
            return new KVar(o);
        }

        /// <summary>
        /// A record class's synthesized ==, as C# defines it: the same reference, or neither null and each field equal by
        /// EqualityComparer&lt;T&gt;.Default (the EqualityContracts of a sealed record's two objects are the same).
        /// </summary>
        private KExpr ValueObjectEquality(IBinaryOperation eq, LowerMode mode)
        {
            var l = Lower(eq.LeftOperand, mode);
            var r = Lower(eq.RightOperand, mode);
            bool withNull = Unconverted(eq.LeftOperand).ConstantValue is { HasValue: true, Value: null } || Unconverted(eq.RightOperand).ConstantValue is { HasValue: true, Value: null };
            var same = withNull ? (KExpr)Eq(l, r)
                : OrElse(Eq(l, r), AndAlso(AndAlso(NotNull(l), NotNull(r)), FieldsEqual(l, r, eq.OperatorMethod.ContainingType, eq.Syntax, 0)));
            return eq.OperatorKind == BinaryOperatorKind.Equals ? same : Not(same);
        }

        /// <summary>Each field of two objects of a value object, neither null, equal as EqualityComparer&lt;T&gt;.Default compares it.</summary>
        private KExpr FieldsEqual(KExpr l, KExpr r, ITypeSymbol type, SyntaxNode at, int depth)
        {
            KExpr all = KLit.True;
            foreach (var f in InstanceFields(type))
            {
                var ft = FieldType(f);
                _p.AddField(f);
                KExpr Read(KExpr o) => new KField { Field = f, Instance = o, NoNull = true, At = at, InstanceAt = at };
                var (a, b) = (Read(l), Read(r));
                // (as a record's synthesized Equals compares it: a struct by its fields, a date by its ticks, a nullable value)
                all = AndAlso(all, ValuesEqual(a, b, ft, at, depth + 1) ?? throw new NotTranslated("== of " + type.Name + ", whose field " + f.Name + " is a " + ft));
            }
            return all;
        }

        /// <summary>A type's own Equals of itself, which its == calls instead of comparing its fields.</summary>
        private static bool OwnEquals(INamedTypeSymbol t) =>
            t.GetMembers("Equals").OfType<IMethodSymbol>().Any(m => !m.IsImplicitlyDeclared && m.Parameters.Length == 1 &&
                SymbolEqualityComparer.Default.Equals(m.Parameters[0].Type.OriginalDefinition, t.OriginalDefinition));

        /// <summary>
        /// Two values equal as EqualityComparer&lt;T&gt;.Default compares them, as a record's synthesized Equals does each
        /// field; null where that isn't known (a float's Equals, a type's own Equals, an open data type).
        /// </summary>
        private KExpr ValuesEqual(KExpr a, KExpr b, ITypeSymbol t, SyntaxNode at, int depth)
        {
            // (a nullable struct's: both null, or neither and the structs' values equal)
            if (IsNullableStruct(t))
            {
                return depth < 4 && ValuesEqual(NullableValue(a, t), NullableValue(b, t), Underlying(t), at, depth + 1) is KExpr values
                    ? OrElse(AndAlso(IsNull(a), IsNull(b)), AndAlso(AndAlso(NotNull(a), NotNull(b)), values)) : null;
            }
            // (a DateTime's or a TimeSpan's ticks and a Guid: the ints the kernel keeps for them)
            if (Scalar(t) || IsDecimal(t) || IsOpaqueTicks(t) || IsOpaqueId(t) || IsNullableValue(t) || IsData(t) && KernelTypes.Data.HasValueEquality((INamedTypeSymbol)t))
            {
                return Eq(a, b);
            }
            if (IsString(t))
            {
                return new KOp("streq", a, b);
            }
            // (a type parameter's: its Equals, an equivalence)
            if (IsGenericParameter(t))
            {
                return Law("Equals", new[] { a, b }, t);
            }
            if (depth >= 4 || !(t is INamedTypeSymbol n) || OwnEquals(n))
            {
                return null;
            }
            if (IsStruct(n) && n.IsRecord)
            {
                KExpr all = KLit.True;
                var fields = StructFields(n);
                for (int k = 0; k < fields.Count; k++)
                {
                    if (!(ValuesEqual(TupleItem(a, n, k), TupleItem(b, n, k), fields[k].Type, at, depth + 1) is KExpr e))
                    {
                        return null;
                    }
                    all = AndAlso(all, e);
                }
                return all;
            }
            if (IsData(n) && !n.IsGenericType)
            {
                // (of one case, each of its fields equal: a record's EqualityContract is its type; two of cases not
                // known, of an open data type, some relation not known)
                var def = DataTypes.Def(n);
                bool open = KernelTypes.Data.Cases(def) == null;
                var cases = KernelTypes.Data.KnownCases(def);
                // (a case not sealed may be a subclass's object, of fields and an EqualityContract of its own)
                if (cases.Any(c => !c.IsSealed))
                {
                    return null;
                }
                KExpr any = KLit.False, aKnown = KLit.False, bKnown = KLit.False;
                foreach (var c in cases)
                {
                    var tag = "$is." + CaseName(c).Substring(3);
                    aKnown = OrElse(aKnown, new KOp(tag, a));
                    bKnown = OrElse(bKnown, new KOp(tag, b));
                    KExpr all = AndAlso(new KOp(tag, a), new KOp(tag, b));
                    foreach (var f in KernelTypes.Data.Fields(c))
                    {
                        if (!(ValuesEqual(FieldOfData(a, f, c), FieldOfData(b, f, c), f.Type, at, depth + 1) is KExpr e))
                        {
                            return null;
                        }
                        all = AndAlso(all, e);
                    }
                    any = OrElse(any, all);
                }
                if (open)
                {
                    any = OrElse(any, AndAlso(AndAlso(Not(aKnown), Not(bKnown)), new KOp("$dataEq", a, b)));
                }
                return OrElse(Eq(a, b), AndAlso(AndAlso(NotNull(a), NotNull(b)), any));
            }
            if (IsValueObject(n))
            {
                return OrElse(Eq(a, b), AndAlso(AndAlso(NotNull(a), NotNull(b)), FieldsEqual(a, b, n, at, depth + 1)));
            }
            return null;
        }

        /// <summary>
        /// A record's == of fields the kernel doesn't compare: one reference (two nulls too) is equal, as C#'s synthesized
        /// operator says before it asks Equals; two are some relation not known ($dataEq in a specification, a value not
        /// known in code).
        /// </summary>
        private KExpr EqualityNotKnown(KExpr l, KExpr r, IBinaryOperation eq, LowerMode mode)
        {
            KExpr two;
            if (mode.InSpec)
            {
                two = new KOp("$dataEq", l, r);
            }
            else
            {
                var unknown = Declare("t$" + _temps++, eq.Type);
                Emit(KHavoc.Of(unknown));
                two = new KVar(unknown);
            }
            var same = OrElse(Eq(l, r), two);
            return eq.OperatorKind == BinaryOperatorKind.Equals ? same : Not(same);
        }

        private KExpr RecordEquality(IBinaryOperation eq, LowerMode mode)
        {
            // (with null: whether it is null, whatever its fields are)
            bool withNull = Unconverted(eq.LeftOperand).ConstantValue is { HasValue: true, Value: null } || Unconverted(eq.RightOperand).ConstantValue is { HasValue: true, Value: null };
            // (a record of fields that compare as EqualityComparer<T>.Default does: each equal, of one case)
            if (!withNull && !KernelTypes.Data.HasValueEquality((INamedTypeSymbol)eq.OperatorMethod.ContainingType) && !OwnEquals(eq.OperatorMethod.ContainingType))
            {
                var (dl, dr) = (Lower(eq.LeftOperand, mode), Lower(eq.RightOperand, mode));
                if (ValuesEqual(dl, dr, eq.OperatorMethod.ContainingType, eq.Syntax, 0) is KExpr same)
                {
                    return eq.OperatorKind == BinaryOperatorKind.Equals ? same : Not(same);
                }
                return EqualityNotKnown(dl, dr, eq, mode);
            }
            // (fields that don't compare as values, strings', or the record's own Equals: whether two are equal isn't known)
            if (!withNull && !KernelTypes.Data.HasValueEquality((INamedTypeSymbol)eq.OperatorMethod.ContainingType))
            {
                return EqualityNotKnown(Lower(eq.LeftOperand, mode), Lower(eq.RightOperand, mode), eq, mode);
            }
            var l = Lower(eq.LeftOperand, mode);
            var r = Lower(eq.RightOperand, mode);
            return new KOp(eq.OperatorKind == BinaryOperatorKind.Equals ? "==" : "!=", l, r);
        }
    }
}
