using System;
using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
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
            _p.Valid.Add(DataTypes.Def(t));
            Emit(KAssume.Of(OrElse(IsNull(v), new KOp(ValidName(t), v))));
        }

        private void Data(ITypeSymbol t)
        {
            var def = DataTypes.Def(t);
            _p.DataTypes.Add(def);
            foreach (var c in KernelTypes.Data.KnownCases(def))
            {
                _p.DataTypes.Add(c);
            }
        }

        /// <summary>A data value's field, as the type it's read at has it (unboxed where generic).</summary>
        private KExpr FieldOfData(KExpr v, IPropertySymbol prop, ITypeSymbol at) =>
            Unbox(new KOp(FieldFunction(prop), v), prop.OriginalDefinition.Type, Actual(at, prop.Name)?.Type ?? prop.Type);

        /// <summary>
        /// The data types' operations, in code or in a specification (each lowers its operands its own way): a case's
        /// construction, a field's read, type tests and patterns, casts, a record's ==; null where it is none.
        /// </summary>
        private KExpr DataExpr(IOperation e, Func<IOperation, KExpr> lower, Action<ILocalSymbol, KExpr> bind, bool inSpec = false)
        {
            var wasSpec = _inSpecTest;
            _inSpecTest = inSpec;
            try
            {
                return DataExprCore(e, lower, bind, inSpec);
            }
            finally
            {
                _inSpecTest = wasSpec;
            }
        }

        private KExpr DataExprCore(IOperation e, Func<IOperation, KExpr> lower, Action<ILocalSymbol, KExpr> bind, bool inSpec)
        {
            // (a span: Lowering.Spans)
            if (SpanExpr(e, lower, inSpec) is KExpr span)
            {
                return span;
            }
            switch (e)
            {
                case IArrayElementReferenceOperation: return DataExprCoreOfArrayElementReference(e, lower, bind, inSpec);
                case IInvocationOperation: return DataExprCoreOfInvocation(e, lower, bind, inSpec);
                case IPropertyReferenceOperation: return DataExprCoreOfPropertyReference(e, lower, bind, inSpec);
                case IFieldReferenceOperation: return DataExprCoreOfFieldReference(e, lower, bind, inSpec);
                case IMethodReferenceOperation: return DataExprCoreOfMethodReference(e, lower, bind, inSpec);
                case IEventReferenceOperation: return DataExprCoreOfEventReference(e, lower, bind, inSpec);
                case IDefaultValueOperation: return DataExprCoreOfDefaultValue(e, lower, bind, inSpec);
                case IObjectCreationOperation: return DataExprCoreOfObjectCreation(e, lower, bind, inSpec);
                case IConversionOperation: return DataExprCoreOfConversion(e, lower, bind, inSpec);
                case IBinaryOperation: return DataExprCoreOfBinary(e, lower, bind, inSpec);
                case IIsPatternOperation: return DataExprCoreOfIsPattern(e, lower, bind, inSpec);
                case IUnaryOperation: return DataExprCoreOfUnary(e, lower, bind, inSpec);
                case ITupleBinaryOperation: return DataExprCoreOfTupleBinary(e, lower, bind, inSpec);
                case IAnonymousObjectCreationOperation: return DataExprCoreOfAnonymousObjectCreation(e, lower, bind, inSpec);
                case ITupleOperation: return DataExprCoreOfTuple(e, lower, bind, inSpec);
                case IIsTypeOperation: return DataExprCoreOfIsType(e, lower, bind, inSpec);
                case ISwitchExpressionOperation: return DataExprCoreOfSwitchExpression(e, lower, bind, inSpec);
                default: return DataExprCoreOther(e, lower, bind, inSpec);
            }
        }

        /// <summary>DataExprCore of a array element reference: its forms, in order; any other as DataExprCoreOther.</summary>
        private KExpr DataExprCoreOfArrayElementReference(IOperation e, Func<IOperation, KExpr> lower, Action<ILocalSymbol, KExpr> bind, bool inSpec)
        {
            switch (e)
            {
                // (a rectangular array's cell: each index within its dimension)
                case IArrayElementReferenceOperation me when IsMultiArray(me.ArrayReference.Type) && me.Indices.Length == ((IArrayTypeSymbol)me.ArrayReference.Type).Rank:
                {
                    var a = lower(me.ArrayReference);
                    var ix = me.Indices.Select(lower).ToList();
                    var cell = new KElem
                    {
                        Unchecked = true,
                        Array = a,
                        Index = CellOf(ix),
                        ArrayType = me.ArrayReference.Type,
                        InSpec = inSpec,
                        At = me.Syntax,
                        ArrayAt = me.ArrayReference.Syntax,
                    };
                    return MultiIndices(a, ix, me.Syntax, cell, inSpec);
                }
                default: return DataExprCoreOther(e, lower, bind, inSpec);
            }
        }

        /// <summary>DataExprCore of a invocation: its forms, in order; any other as DataExprCoreOther.</summary>
        private KExpr DataExprCoreOfInvocation(IOperation e, Func<IOperation, KExpr> lower, Action<ILocalSymbol, KExpr> bind, bool inSpec)
        {
            switch (e)
            {
                // (its length of a dimension, d within its rank; and its Length, their product)
                case IInvocationOperation gl when gl.TargetMethod.Name == "GetLength" && gl.TargetMethod.ContainingType?.SpecialType == SpecialType.System_Array && gl.Instance != null &&
                                                 Unconverted(gl.Instance) is IOperation gli && IsMultiArray(gli.Type) && gl.Arguments.Length == 1:
                    return MultiArrayLength(gl, gli, lower, inSpec);
                case IInvocationOperation ng when ng.Instance != null && IsNullableValue(ng.Instance.Type) && ng.TargetMethod.Name == "GetValueOrDefault":
                {
                    var v = lower(ng.Instance);
                    var otherwise = ng.Arguments.Length == 1 ? lower(ng.Arguments[0].Value) : Default(Underlying(ng.Instance.Type));
                    return Ite(NotNull(v), NullableValue(v, ng.Instance.Type), otherwise);
                }
                case IInvocationOperation fm when FloatMember(fm.TargetMethod) is string member:
                {
                    var args = fm.Arguments.OrderBy(a => a.Parameter.Ordinal).Select(a => lower(a.Value)).ToArray();
                    return FloatCall(member, fm.TargetMethod.Parameters[0].Type, args, fm.Type, inSpec);
                }
                // (a ghost value: the value itself)
                // (ghost code: mathematics, in code too)
                case IInvocationOperation go when SpecSymbols.IsCsVerifyType(go.TargetMethod.ContainingType, "Ghost") && go.TargetMethod.Name == "Of" && go.Arguments.Length == 1:
                    return inSpec ? lower(go.Arguments[0].Value) : Spec(go.Arguments[0].Value, null);
                // (a ghost set of objects' members, ObjSet.Empty, ==: mathematics in code too)
                case IInvocationOperation os when !inSpec && IsObjSet(os.TargetMethod.ContainingType):
                    return Spec(os, null);
                default: return DataExprCoreOther(e, lower, bind, inSpec);
            }
        }

        private KExpr MultiArrayLength(IInvocationOperation gl, IOperation gli, Func<IOperation, KExpr> lower, bool inSpec)
        {
            int rank = ((IArrayTypeSymbol)gli.Type).Rank;
            var a = lower(gli);
            var d = lower(gl.Arguments[0].Value);
            KExpr len = new KOp("$dim", a, new KLit((rank - 1).ToString()));
            for (int k = rank - 2; k >= 0; k--)
            {
                len = Ite(Eq(d, new KLit(k.ToString())), new KOp("$dim", a, new KLit(k.ToString())), len);
            }
            return Defined(AndAlso(NotNull(a), AndAlso(Le(KLit.Zero, d), Lt(d, new KLit(rank.ToString())))), len,
                           "CSV1003", gl.Syntax, $"dimension in '{gl.Syntax}' might be out of range", inSpec);
        }

        /// <summary>DataExprCore of a property reference: its forms, in order; any other as DataExprCoreOther.</summary>
        private KExpr DataExprCoreOfPropertyReference(IOperation e, Func<IOperation, KExpr> lower, Action<ILocalSymbol, KExpr> bind, bool inSpec)
        {
            switch (e)
            {
                case IPropertyReferenceOperation ml when ml.Property.Name == "Length" && ml.Instance != null && IsMultiArray(ml.Instance.Type):
                {
                    var a = lower(ml.Instance);
                    KExpr len = new KOp("$dim", a, KLit.Zero);
                    for (int k = 1; k < ((IArrayTypeSymbol)ml.Instance.Type).Rank; k++)
                    {
                        len = Times(len, new KOp("$dim", a, new KLit(k.ToString())));
                    }
                    return Defined(NotNull(a), len, "CSV1013", ml.Syntax, $"'{ml.Instance.Syntax}' might be null in '{ml.Syntax}'", inSpec);
                }
                // (a struct's member: its element)
                case IMemberReferenceOperation sm when StructMember(sm) is (IOperation si, int sk):
                    return TupleItem(lower(si), si.Type, sk);
                case IPropertyReferenceOperation np when np.Instance != null && IsNullableValue(np.Instance.Type) && np.Property.Name is "HasValue" or "Value":
                {
                    var v = lower(np.Instance);
                    if (np.Property.Name == "HasValue")
                    {
                        return NotNull(v);
                    }
                    if (!inSpec)
                    {
                        Emit(KCheck.Of(NotNull(v), "CSV1013", np.Syntax, $"'{np.Syntax}' might be read when '{np.Instance.Syntax}' is null"));
                    }
                    return NullableValue(v, np.Instance.Type);
                }
                case IPropertyReferenceOperation dp when dp.Instance != null && IsData(dp.Instance.Type) && DataTypes.IsPositional(dp.Property.OriginalDefinition):
                    return PositionalProperty(dp, lower, inSpec);
                case IPropertyReferenceOperation tk when tk.Property.Name == "Ticks" && tk.Instance != null && IsOpaqueTicks(tk.Instance.Type):
                    return lower(tk.Instance);
                // (a tuple written here: a value of its elements; an element of one: a function of it)
                // (a GroupBy group's Key: its first element's key)
                case IPropertyReferenceOperation { Property.Name: "Key", Instance: ILocalReferenceOperation gk } when IsLinqGroup(gk.Type):
                    return GroupKey(gk.Local);
                // (the first group's key: its first element's; no group, it throws)
                case IPropertyReferenceOperation { Property.Name: "Key", Instance: IInvocationOperation { TargetMethod.Name: "First", Arguments.Length: 1 } fg } when IsLinqGroup(fg.Type) &&
                        Unconverted(fg.Arguments[0].Value) is IInvocationOperation gb && IsEnumerableCall(gb.TargetMethod) && gb.TargetMethod.Name == "GroupBy" && gb.Arguments.Length == 2 && !inSpec:
                    return FirstGroupKey(gb, fg);
                case IPropertyReferenceOperation jrm when jrm.Instance is ILocalReferenceOperation jrl && _joinRows.ContainsKey(jrl.Local) && JoinRowMember(jrm) is KExpr jrv:
                    return jrv;
                case IPropertyReferenceOperation ap when ap.Instance != null && ap.Instance.Type?.IsAnonymousType == true && IsTuple(ap.Instance.Type) && PartIndex(ap.Instance.Type, ap.Property.Name) is int pi && pi >= 0:
                    return TupleItem(lower(ap.Instance), ap.Instance.Type, pi);
                // (a pointer's or a memory view's ghost property: a function of it)
                case IPropertyReferenceOperation mp when mp.Instance != null && IsMemValue(mp.Instance.Type) && mp.Property.Name is "Addr" or "Length" or "Index" or "Value" or "Elems":
                    _p.MemViews |= IsMemView(mp.Instance.Type);
                    return MemProp(mp.Property.Name, lower(mp.Instance), mp.Instance.Type);
                case IPropertyReferenceOperation { Property.Name: "Empty", Instance: null } oe when !inSpec && IsObjSet(oe.Type):
                    return Spec(oe, null);
                case IPropertyReferenceOperation gv when gv.Property.Name == "Value" && IsGhost(gv.Instance?.Type) &&
                                                         !(gv.Instance is IPropertyReferenceOperation { Property.Name: "Obj" } obj && (IsView(obj.Instance?.Type) || IsShare(obj.Instance?.Type))):
                    return lower(gv.Instance);
                // (a view's object, v.Obj.Value: the view itself, in code too)
                case IPropertyReferenceOperation { Property.Name: "Value", Instance: IPropertyReferenceOperation { Property.Name: "Obj" } vo } when IsView(vo.Instance?.Type) || IsShare(vo.Instance?.Type):
                    return lower(vo.Instance);
                default: return DataExprCoreOther(e, lower, bind, inSpec);
            }
        }

        /// <summary>DataExprCore of a field reference: its forms, in order; any other as DataExprCoreOther.</summary>
        private KExpr DataExprCoreOfFieldReference(IOperation e, Func<IOperation, KExpr> lower, Action<ILocalSymbol, KExpr> bind, bool inSpec)
        {
            switch (e)
            {
                // (a struct's member: its element)
                case IMemberReferenceOperation sm when StructMember(sm) is (IOperation si, int sk):
                    return TupleItem(lower(si), si.Type, sk);
                case IFieldReferenceOperation { Instance: null, ConstantValue: { HasValue: true } fcv } ff when IsFloating(ff.Type):
                    return FloatLiteral(fcv.Value, ff.Type);
                case IFieldReferenceOperation tf when tf.Instance != null && IsTuple(tf.Instance.Type) && tf.Field.ContainingType is INamedTypeSymbol { IsTupleType: true } tt &&
                                                      tt.TupleElements.Select(x => x.CorrespondingTupleField ?? x).ToList().FindIndex(x => x.Name == (tf.Field.CorrespondingTupleField ?? tf.Field).Name) is int ti && ti >= 0:
                    return TupleItem(lower(tf.Instance), tf.Instance.Type, ti);
                default: return DataExprCoreOther(e, lower, bind, inSpec);
            }
        }

        /// <summary>DataExprCore of a method reference: its forms, in order; any other as DataExprCoreOther.</summary>
        private KExpr DataExprCoreOfMethodReference(IOperation e, Func<IOperation, KExpr> lower, Action<ILocalSymbol, KExpr> bind, bool inSpec)
        {
            switch (e)
            {
                // (a struct's member: its element)
                case IMemberReferenceOperation sm when StructMember(sm) is (IOperation si, int sk):
                    return TupleItem(lower(si), si.Type, sk);
                default: return DataExprCoreOther(e, lower, bind, inSpec);
            }
        }

        /// <summary>DataExprCore of a event reference: its forms, in order; any other as DataExprCoreOther.</summary>
        private KExpr DataExprCoreOfEventReference(IOperation e, Func<IOperation, KExpr> lower, Action<ILocalSymbol, KExpr> bind, bool inSpec)
        {
            switch (e)
            {
                // (a struct's member: its element)
                case IMemberReferenceOperation sm when StructMember(sm) is (IOperation si, int sk):
                    return TupleItem(lower(si), si.Type, sk);
                default: return DataExprCoreOther(e, lower, bind, inSpec);
            }
        }

        /// <summary>DataExprCore of a default value: its forms, in order; any other as DataExprCoreOther.</summary>
        private KExpr DataExprCoreOfDefaultValue(IOperation e, Func<IOperation, KExpr> lower, Action<ILocalSymbol, KExpr> bind, bool inSpec)
        {
            switch (e)
            {
                // (a memory value made by default, a forged one (CSV0006): its address, length and index 0, nothing else known)
                case IDefaultValueOperation md when IsMemValue(md.Type) && !inSpec:
                    return ForgedMemValue(md);
                // (a struct made without a constructor of its own, default(S): its default value)
                case IDefaultValueOperation sd when IsStruct(sd.Type):
                    return StructDefault(sd.Type);
                // (default(T) of another type of the kernel's, int? or a reference: null, 0, false; ?. makes one)
                case IDefaultValueOperation dd when dd.Type != null && (IsNullableValue(dd.Type) || Scalar(dd.Type) || IsNullable(dd.Type)) && !IsMemValue(dd.Type):
                    return Default(dd.Type);
                default: return DataExprCoreOther(e, lower, bind, inSpec);
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
        private KExpr DataExprCoreOfObjectCreation(IOperation e, Func<IOperation, KExpr> lower, Action<ILocalSymbol, KExpr> bind, bool inSpec)
        {
            switch (e)
            {
                case IObjectCreationOperation so when IsStruct(so.Type) && so.Initializer == null && (so.Constructor == null || so.Constructor.IsImplicitlyDeclared) && so.Arguments.Length == 0:
                    return StructDefault(so.Type);
                case IObjectCreationOperation oc when IsData(oc.Type) && oc.Initializer == null && oc.Constructor != null:
                    return NewData(oc, lower, inSpec);
                default: return DataExprCoreOther(e, lower, bind, inSpec);
            }
        }

        /// <summary>DataExprCore of a conversion: its forms, in order; any other as DataExprCoreOther.</summary>
        private KExpr DataExprCoreOfConversion(IOperation e, Func<IOperation, KExpr> lower, Action<ILocalSymbol, KExpr> bind, bool inSpec)
        {
            switch (e)
            {
                // (a nullable value, int?: null, or the reference of its value)
                case IConversionOperation nc when IsNullableValue(nc.Type) && !IsNullableValue(nc.Operand.Type) && nc.OperatorMethod == null:
                    return NullableOfValue(nc, lower);
                // (int? to long?: null stays null, a value widens)
                case IConversionOperation nn when IsNullableValue(nn.Type) && IsNullableValue(nn.Operand.Type) && nn.OperatorMethod == null && nn.Conversion.IsImplicit &&
                                                  IsIntegral(Underlying(nn.Type)) && IsIntegral(Underlying(nn.Operand.Type)):
                {
                    var v = Operand(nn.Operand, lower, inSpec);
                    return Ite(IsNull(v), KLit.Null, NullableOf(NullableValue(v, nn.Operand.Type), nn.Type));
                }
                case IConversionOperation nu when IsNullableValue(nu.Operand.Type) && !IsNullableValue(nu.Type) && nu.OperatorMethod == null:
                {
                    if (!SymbolEqualityComparer.Default.Equals(nu.Type, Underlying(nu.Operand.Type)))
                    {
                        throw new NotTranslated("a conversion of " + nu.Operand.Type + " to " + nu.Type);
                    }
                    var v = lower(nu.Operand);
                    if (!inSpec)
                    {
                        Emit(KCheck.Of(NotNull(v), "CSV1013", nu.Syntax, $"'{nu.Operand.Syntax}' might be null where '{nu.Syntax}' unwraps it"));
                    }
                    return NullableValue(v, nu.Operand.Type);
                }
                case IConversionOperation fc when (IsFloating(fc.Type) || IsFloating(fc.Operand.Type)) && fc.Conversion.IsNumeric && fc.OperatorMethod == null:
                    return FloatConversion(fc, lower(fc.Operand), inSpec);
                case IConversionOperation tc when IsTuple(tc.Type) && Unconverted(tc.Operand) is ITupleOperation tlit && ((INamedTypeSymbol)tc.Type).IsTupleType && tlit.Elements.Length == ((INamedTypeSymbol)tc.Type).TupleElements.Length:
                    return TupleConverted(tc, tlit, lower, inSpec);
                case IConversionOperation up when up.IsImplicit && IsData(up.Type) && IsData(up.Operand.Type):
                    return lower(up.Operand);
                // (o as C: o where it's an instance of C, else null)
                case IConversionOperation tc when tc.IsTryCast && tc.Conversion.IsReference && IsModeledClass(tc.Type) && (IsRef(tc.Operand.Type) || IsString(tc.Operand.Type)):
                {
                    var v = Operand(tc.Operand, lower, inSpec);
                    StaticType(v, tc.Operand.Type, inSpec);
                    return Ite(ClassTest(v, tc.Type), v, KLit.Null);
                }
                // ((C)o, a downcast: o, which must be null or an instance of C)
                case IConversionOperation dc when !dc.IsImplicit && !dc.IsTryCast && dc.Conversion.IsReference && !dc.Conversion.IsImplicit && IsModeledClass(dc.Type) && (IsRef(dc.Operand.Type) || IsString(dc.Operand.Type)):
                    return DataCast(dc, lower, inSpec);
                // ((object)o, an upcast written as a cast: o)
                // (a string as an object, in code: a reference of its own, which another equal string's may or may not be)
                case IConversionOperation so when !inSpec && so.Conversion.IsReference && IsString(so.Operand.Type) && so.Type.SpecialType == SpecialType.System_Object:
                    return StringUpcast(so, lower);
                // (not a string's: as an object, one isn't its value, which another equal string may be)
                case IConversionOperation uc when !uc.IsImplicit && uc.Conversion.IsReference && uc.Conversion.IsImplicit && (IsRef(uc.Type) || IsString(uc.Type)) && IsRef(uc.Operand.Type):
                    return lower(uc.Operand);
                case IConversionOperation down when !down.IsImplicit && down.Conversion.IsReference && IsData(down.Type) && IsData(down.Operand.Type):
                    return DataDownCast(down, lower, inSpec);
                default: return DataExprCoreOther(e, lower, bind, inSpec);
            }
        }

        private KExpr NullableOfValue(IConversionOperation nc, Func<IOperation, KExpr> lower)
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
            return NullableOf(lower(nc.Operand), nc.Type);
        }

        private KExpr DataCast(IConversionOperation dc, Func<IOperation, KExpr> lower, bool inSpec)
        {
            var v = Operand(dc.Operand, lower, inSpec);
            StaticType(v, dc.Operand.Type, inSpec);
            var castOk = OrElse(IsNull(v), ClassTest(v, dc.Type));
            CastThrows(castOk, inSpec);
            return new KCast
            {
                Value = v,
                Test = castOk,
                At = dc.Syntax,
            };
        }

        private KExpr DataDownCast(IConversionOperation down, Func<IOperation, KExpr> lower, bool inSpec)
        {
            Data(down.Type);
            var v = Operand(down.Operand, lower, inSpec);
            var downOk = OrElse(IsNull(v), IsCase(v, down.Type));
            CastThrows(downOk, inSpec);
            return new KCast
            {
                Value = v,
                Test = downOk,
                At = down.Syntax,
            };
        }

        /// <summary>DataExprCore of a binary: its forms, in order; any other as DataExprCoreOther.</summary>
        private KExpr DataExprCoreOfBinary(IOperation e, Func<IOperation, KExpr> lower, Action<ILocalSymbol, KExpr> bind, bool inSpec)
        {
            switch (e)
            {
                // (objects compared in a database query's lambda, with SQL's nulls (UseRelationalNulls): where one that may be
                // null is, SQL's unknown, for each comparison, as for strings; against the literal null, IS NULL, exact)
                case IBinaryOperation rb when _inDatabase > 0 && KernelTypes.Ef?.RelationalNulls == true && rb.OperatorMethod == null &&
                                              rb.OperatorKind is BinaryOperatorKind.Equals or BinaryOperatorKind.NotEquals &&
                                              Unconverted(rb.LeftOperand).Type is { IsReferenceType: true } lt && !IsString(lt) && IsRef(lt) &&
                                              Unconverted(rb.RightOperand).Type is { IsReferenceType: true } rt && !IsString(rt) && IsRef(rt):
                    return RelationalNullsCompared(rb, lower);
                // (lifted: == on the values, or both null; the comparisons false where either is null)
                case IBinaryOperation nb when nb.OperatorMethod == null && (IsNullableValue(nb.LeftOperand.Type) || nb.LeftOperand.Type == null) && (IsNullableValue(nb.RightOperand.Type) || nb.RightOperand.Type == null) &&
                                              (IsNullableValue(nb.LeftOperand.Type) || IsNullableValue(nb.RightOperand.Type)):
                    return LiftedBinary(nb, lower, inSpec);
                // (DateTime and TimeSpan compared: their ticks, the int the kernel keeps for them, are what C# compares)
                case IBinaryOperation dt when IsOpaqueTicks(dt.LeftOperand.Type) && SymbolEqualityComparer.Default.Equals(dt.LeftOperand.Type, dt.RightOperand.Type) &&
                                              dt.OperatorKind is BinaryOperatorKind.Equals or BinaryOperatorKind.NotEquals or BinaryOperatorKind.LessThan or BinaryOperatorKind.LessThanOrEqual
                                                  or BinaryOperatorKind.GreaterThan or BinaryOperatorKind.GreaterThanOrEqual:
                    return TicksCompared(dt, lower);
                // (float and double, as IEEE 754: operations round to nearest; == is IEEE's, < and the rest false at NaN)
                case IBinaryOperation fb when fb.OperatorMethod == null && IsFloating(fb.LeftOperand.Type) && IsFloating(fb.RightOperand.Type):
                    return FloatBinary(fb, lower);
                case IBinaryOperation ob when !inSpec && ob.OperatorMethod != null && IsObjSet(ob.OperatorMethod.ContainingType):
                    return Spec(ob, null);
                // (an anonymous object compared with null: its reference, null where an OrDefault found none, never one made)
                case IBinaryOperation an when AnonymousVsNull(an) is var (anon, anonEq):
                    return new KOp(anonEq ? "==" : "!=", lower(anon), KLit.Null);
                // (a record's == and !=: its values' equality, which is its references', a value being its constructor's)
                case IBinaryOperation eq when eq.OperatorMethod != null && eq.OperatorKind is BinaryOperatorKind.Equals or BinaryOperatorKind.NotEquals &&
                                              IsData(eq.OperatorMethod.ContainingType):
                    return RecordEquality(eq, lower, inSpec);
                default: return DataExprCoreOther(e, lower, bind, inSpec);
            }
        }

        /// <summary>DataExprCore of a is pattern: its forms, in order; any other as DataExprCoreOther.</summary>
        private KExpr DataExprCoreOfIsPattern(IOperation e, Func<IOperation, KExpr> lower, Action<ILocalSymbol, KExpr> bind, bool inSpec)
        {
            switch (e)
            {
                case IIsPatternOperation nip when IsNullableValue(Unconverted(nip.Value).Type):
                    return NullablePattern(nip.Pattern, Operand(Unconverted(nip.Value), lower, inSpec), Unconverted(nip.Value).Type, lower, bind);
                case IIsPatternOperation ip when IsData(Unconverted(ip.Value).Type) || Scalar(ip.Value.Type) ||
                                                 (IsRef(ip.Value.Type) || IsString(ip.Value.Type)) && NullPattern(ip.Pattern) ||
                                                 IsArray(Unconverted(ip.Value).Type) && ip.Pattern is IListPatternOperation ||
                                                 IsTuple(Unconverted(ip.Value).Type) && ip.Pattern is IRecursivePatternOperation ||
                                                 IsClass(Unconverted(ip.Value).Type) && !IsData(Unconverted(ip.Value).Type) && ip.Pattern is IRecursivePatternOperation ||
                                                 (IsRef(Unconverted(ip.Value).Type) || IsString(Unconverted(ip.Value).Type) || IsException(Unconverted(ip.Value).Type)) && !IsData(Unconverted(ip.Value).Type):
                    return IsPattern(ip, lower, bind, inSpec);
                default: return DataExprCoreOther(e, lower, bind, inSpec);
            }
        }

        /// <summary>DataExprCore of a unary: its forms, in order; any other as DataExprCoreOther.</summary>
        private KExpr DataExprCoreOfUnary(IOperation e, Func<IOperation, KExpr> lower, Action<ILocalSymbol, KExpr> bind, bool inSpec)
        {
            switch (e)
            {
                case IUnaryOperation fu when IsFloating(fu.Operand.Type) && fu.OperatorKind is UnaryOperatorKind.Minus or UnaryOperatorKind.Plus:
                    return fu.OperatorKind == UnaryOperatorKind.Minus ? new KOp("$fp.neg" + FloatSize(fu.Operand.Type), lower(fu.Operand)) : lower(fu.Operand);
                default: return DataExprCoreOther(e, lower, bind, inSpec);
            }
        }

        /// <summary>DataExprCore of a tuple binary: its forms, in order; any other as DataExprCoreOther.</summary>
        private KExpr DataExprCoreOfTupleBinary(IOperation e, Func<IOperation, KExpr> lower, Action<ILocalSymbol, KExpr> bind, bool inSpec)
        {
            switch (e)
            {
                // (t == u of tuples: the left's elements, then the right's, compared element by element)
                case ITupleBinaryOperation tb when TupleComparable(tb.LeftOperand.Type) && TupleComparable(tb.RightOperand.Type):
                    return TuplesCompared(tb, lower, inSpec);
                default: return DataExprCoreOther(e, lower, bind, inSpec);
            }
        }

        private KExpr TuplesCompared(ITupleBinaryOperation tb, Func<IOperation, KExpr> lower, bool inSpec)
        {
            var l = TupleParts(tb.LeftOperand, lower, inSpec);
            var r = TupleParts(tb.RightOperand, lower, inSpec);
            KExpr same = KLit.True;
            for (int k = l.Count - 1; k >= 0; k--)
            {
                same = k == l.Count - 1 ? Eq(l[k], r[k]) : AndAlso(Eq(l[k], r[k]), same);
            }
            return tb.OperatorKind == BinaryOperatorKind.Equals ? same : Not(same);
        }

        /// <summary>DataExprCore of a anonymous object creation: its forms, in order; any other as DataExprCoreOther.</summary>
        private KExpr DataExprCoreOfAnonymousObjectCreation(IOperation e, Func<IOperation, KExpr> lower, Action<ILocalSymbol, KExpr> bind, bool inSpec)
        {
            switch (e)
            {
                // (an anonymous object, new { s, b = e }: a tuple of its members; a member read, an element)
                case IAnonymousObjectCreationOperation ao when IsTuple(ao.Type):
                    return AnonymousObject(ao, lower, inSpec);
                default: return DataExprCoreOther(e, lower, bind, inSpec);
            }
        }

        /// <summary>DataExprCore of a tuple: its forms, in order; any other as DataExprCoreOther.</summary>
        private KExpr DataExprCoreOfTuple(IOperation e, Func<IOperation, KExpr> lower, Action<ILocalSymbol, KExpr> bind, bool inSpec)
        {
            switch (e)
            {
                case ITupleOperation tu when IsTuple(tu.Type):
                    return NewTuple(tu, lower, inSpec);
                default: return DataExprCoreOther(e, lower, bind, inSpec);
            }
        }

        /// <summary>DataExprCore of a is type: its forms, in order; any other as DataExprCoreOther.</summary>
        private KExpr DataExprCoreOfIsType(IOperation e, Func<IOperation, KExpr> lower, Action<ILocalSymbol, KExpr> bind, bool inSpec)
        {
            switch (e)
            {
                // (o is C of a class: not null, an instance of C; a value of its static type is an instance of that)
                case IIsTypeOperation ct when IsModeledClass(ct.TypeOperand) && (IsRef(ct.ValueOperand.Type) || IsString(ct.ValueOperand.Type) || IsException(ct.ValueOperand.Type)):
                {
                    var v = Operand(ct.ValueOperand, lower, inSpec);
                    StaticType(v, ct.ValueOperand.Type, inSpec);
                    var test = ClassTest(v, ct.TypeOperand);
                    return ct.IsNegated ? Not(test) : test;
                }
                case IIsTypeOperation it when IsData(it.TypeOperand) && !it.IsNegated:
                    Data(it.TypeOperand);
                    return IsCase(Operand(it.ValueOperand, lower, inSpec), it.TypeOperand);
                default: return DataExprCoreOther(e, lower, bind, inSpec);
            }
        }

        /// <summary>DataExprCore of a switch expression: its forms, in order; any other as DataExprCoreOther.</summary>
        private KExpr DataExprCoreOfSwitchExpression(IOperation e, Func<IOperation, KExpr> lower, Action<ILocalSymbol, KExpr> bind, bool inSpec)
        {
            switch (e)
            {
                case ISwitchExpressionOperation sw when inSpec:
                    return SpecSwitchExpression(sw, lower, bind);
                default: return DataExprCoreOther(e, lower, bind, inSpec);
            }
        }

        /// <summary>DataExprCore of an operation none of the forms above is.</summary>
        private KExpr DataExprCoreOther(IOperation e, Func<IOperation, KExpr> lower, Action<ILocalSymbol, KExpr> bind, bool inSpec)
        {
            return null;
        }

        private KExpr RelationalNullsCompared(IBinaryOperation rb, Func<IOperation, KExpr> lower)
        {
            var (l, r) = (lower(Unconverted(rb.LeftOperand)), lower(Unconverted(rb.RightOperand)));
            var same = Eq(l, r);
            return RelationalStrings(rb, rb.OperatorKind == BinaryOperatorKind.Equals ? same : Not(same), l, r);
        }

        private KExpr LiftedBinary(IBinaryOperation nb, Func<IOperation, KExpr> lower, bool inSpec)
        {
            KExpr Side(IOperation x) => x.Type == null ? KLit.Null : lower(x);
            var (l, r) = (Side(nb.LeftOperand), Side(nb.RightOperand));
            var t = nb.LeftOperand.Type;
            KExpr Both(string op) => IsIntegral(Underlying(t)) && SymbolEqualityComparer.Default.Equals(t, nb.RightOperand.Type)
                ? AndAlso(AndAlso(NotNull(l), NotNull(r)), new KOp(op, NullableValue(l, t), NullableValue(r, t)))
                : throw new NotTranslated("the lifted operator " + nb.OperatorKind);
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
                if (!inSpec)
                {
                    l = Operand(nb.LeftOperand, lower, false);
                    r = Operand(nb.RightOperand, lower, false);
                }
                var both = AndAlso(NotNull(l), NotNull(r));
                var u = Underlying(nb.Type);
                KExpr V(KExpr x) => Ite(both, NullableValue(x, t), KLit.Zero);
                var sum = inSpec ? new KOp(Op(nb.OperatorKind), V(l), V(r)) : Arith(Op(nb.OperatorKind), V(l), V(r), u, nb.Syntax, nb.IsChecked);
                if (!inSpec)
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
                if (!inSpec)
                {
                    l = Operand(nb.LeftOperand, lower, false);
                    r = Operand(nb.RightOperand, lower, false);
                }
                var both = AndAlso(NotNull(l), NotNull(r));
                var u = Underlying(nb.Type);
                KExpr V(KExpr x) => Ite(both, NullableValue(x, t), KLit.Zero);
                var bits = Bitwise(nb.OperatorKind, V(l), V(r), u, inSpec);
                if (!inSpec)
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
                BinaryOperatorKind.LessThan => Both("<"), BinaryOperatorKind.LessThanOrEqual => Both("<="),
                BinaryOperatorKind.GreaterThan => Both(">"), BinaryOperatorKind.GreaterThanOrEqual => Both(">="),
                _ => throw new NotTranslated("the lifted operator " + nb.OperatorKind),
            };
        }

        private KExpr NewData(IObjectCreationOperation oc, Func<IOperation, KExpr> lower, bool inSpec)
        {
            Data(oc.Type);
            var ordered = oc.Arguments.OrderBy(a => a.Parameter.Ordinal).ToList();
            var values = inSpec ? ordered.Select(a => lower(a.Value)).ToArray() : Operands(ordered.Select(a => a.Value).ToArray());
            var def = oc.Constructor.OriginalDefinition;
            // (a non-nullable field isn't null: each construction says so)
            if (!inSpec)
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
            if (!inSpec && IsPackage(oc.Type))
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
            var args = ordered.Select((a, k) => Box(values[k], def.Parameters[a.Parameter.Ordinal].Type, a.Parameter.Type)).ToArray();
            var made = new KOp(CaseName((INamedTypeSymbol)oc.Type), args);
            if (inSpec || !HasInvariants(oc.Type))
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
                Emit(KCheck.Of(
                    new KFnCall
             {
                 Callee = inv.OriginalDefinition,
                 Receiver = new KVar(t),
                 Args = new KExpr[0],
                 At = oc.Syntax,
             },
                    "CSV1015",
                    oc.Syntax,
                    $"invariant '{inv.Name}' of {oc.Type.Name} might not hold for '{oc.Syntax}'"));
            }
            AssumeValid(new KVar(t), oc.Type);
            return new KVar(t);
        }

        private KExpr PositionalProperty(IPropertyReferenceOperation dp, Func<IOperation, KExpr> lower, bool inSpec)
        {
            Data(dp.Instance.Type);
            var v = lower(dp.Instance);
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
            if (!inSpec && IsNullable(dp.Type) && NotNullable(prop.Type))
            {
                var nn = Declare("t$" + _temps++, dp.Type);
                Emit(KAssign.Of(nn, read));
                Emit(KAssume.Of(NotNull(new KVar(nn))));
                read = new KVar(nn);
            }
            if (inSpec || !HasInvariants(dp.Type))
            {
                return read;
            }
            var t = Declare("t$" + _temps++, dp.Type);
            Emit(KAssign.Of(t, read));
            AssumeValid(new KVar(t), dp.Type);
            return new KVar(t);
        }

        private KExpr TicksCompared(IBinaryOperation dt, Func<IOperation, KExpr> lower)
        {
            var (l, r) = (lower(dt.LeftOperand), lower(dt.RightOperand));
            var op = dt.OperatorKind switch
            {
                BinaryOperatorKind.Equals => "==", BinaryOperatorKind.NotEquals => "!=", BinaryOperatorKind.LessThan => "<",
                BinaryOperatorKind.LessThanOrEqual => "<=", BinaryOperatorKind.GreaterThan => ">", _ => ">=",
            };
            return new KOp(op, l, r);
        }

        private KExpr FloatBinary(IBinaryOperation fb, Func<IOperation, KExpr> lower)
        {
            var n = FloatSize(fb.LeftOperand.Type);
            var (l, r) = (lower(fb.LeftOperand), lower(fb.RightOperand));
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
            ShapeFact(Eq(new KVar(kv), Apply(gkey, gsrc.Elem(KLit.Zero))), fg.Syntax);
            return new KVar(kv);
        }

        private KExpr AnonymousObject(IAnonymousObjectCreationOperation ao, Func<IOperation, KExpr> lower, bool inSpec)
        {
            var items = ao.Initializers.Select(x => lower(x is IAssignmentOperation asg ? asg.Value : x)).ToList();
            if (inSpec)
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

        private KExpr TupleConverted(IConversionOperation tc, ITupleOperation tlit, Func<IOperation, KExpr> lower, bool inSpec)
        {
            // (a tuple literal at the type it's converted to: (null, k) as (SlNode?, int))
            var items = tlit.Elements.Select(x => x.ConstantValue is { HasValue: true, Value: null } ? KLit.Null : lower(x)).ToList();
            if (inSpec)
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

        private KExpr NewTuple(ITupleOperation tu, Func<IOperation, KExpr> lower, bool inSpec)
        {
            var items = tu.Elements.Select(x => lower(x)).ToList();
            // (in a specification, or a lambda: the tuple of its elements, a function of them)
            if (inSpec)
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

        private KExpr IsPattern(IIsPatternOperation ip, Func<IOperation, KExpr> lower, Action<ILocalSymbol, KExpr> bind, bool inSpec)
        {
            var v = Operand(Unconverted(ip.Value), lower, inSpec);
            StaticType(v, Unconverted(ip.Value).Type, inSpec);
            return Pattern(ip.Pattern, v, Unconverted(ip.Value).Type, lower, bind);
        }

        private KExpr SpecSwitchExpression(ISwitchExpressionOperation sw, Func<IOperation, KExpr> lower, Action<ILocalSymbol, KExpr> bind)
        {
            var v = lower(sw.Value);
            KExpr acc = null;
            var arms = sw.Arms.Select(arm =>
            {
                var cond = Pattern(arm.Pattern, v, sw.Value.Type, lower, bind);
                if (arm.Guard != null)
                {
                    cond = AndAlso(cond, lower(arm.Guard));
                }
                return (cond, value: lower(arm.Value));
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
                Test = arms.Select(a => a.cond).Aggregate((a, b) => OrElse(a, b)),
                At = sw.Syntax,
            };
        }

        private KExpr StringUpcast(IConversionOperation so, Func<IOperation, KExpr> lower)
        {
            var sv = Operand(so.Operand, lower, false);
            var o = Declare("t$" + _temps++, so.Type);
            Emit(KHavoc.Of(o));
            Emit(KAssume.Of(Eq(IsNull(new KVar(o)), IsNull(sv))));
            // (the object's contents: the same object, the same string)
            Emit(KAssume.Of(Eq(new KOp("$strOf", new KVar(o)), sv)));
            return new KVar(o);
        }

        private KExpr RecordEquality(IBinaryOperation eq, Func<IOperation, KExpr> lower, bool inSpec)
        {
            // (with null: whether it is null, whatever its fields are)
            bool withNull = Unconverted(eq.LeftOperand).ConstantValue is { HasValue: true, Value: null } || Unconverted(eq.RightOperand).ConstantValue is { HasValue: true, Value: null };
            // (fields that don't compare as values, strings': in code, whether they're equal isn't known)
            if (!withNull && !KernelTypes.Data.HasValueEquality((INamedTypeSymbol)eq.OperatorMethod.ContainingType))
            {
                // (in a specification: some relation, not known, between them)
                if (inSpec)
                {
                    var eqv = new KOp("$dataEq", lower(eq.LeftOperand), lower(eq.RightOperand));
                    return eq.OperatorKind == BinaryOperatorKind.Equals ? eqv : Not(eqv);
                }
                lower(eq.LeftOperand);
                lower(eq.RightOperand);
                var unknown = Declare("t$" + _temps++, eq.Type);
                Emit(KHavoc.Of(unknown));
                return new KVar(unknown);
            }
            var l = lower(eq.LeftOperand);
            var r = lower(eq.RightOperand);
            return new KOp(eq.OperatorKind == BinaryOperatorKind.Equals ? "==" : "!=", l, r);
        }
    }
}
